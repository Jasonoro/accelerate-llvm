{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.CodeGen.Scan
-- Copyright   : [2016..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.CodeGen.Segscan (

  mkSegscan, mkSegscan',

) where

import Data.Array.Accelerate.AST                                    ( Direction(..) )
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic                as A
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Ptr
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.Compile.Cache
import Data.Array.Accelerate.LLVM.PTX.Analysis.Launch
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Generate
import Data.Array.Accelerate.LLVM.PTX.Target


import LLVM.AST.Type.AddrSpace
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Representation
import qualified LLVM.AST.Type.Instruction.RMW                      as RMW

import qualified Foreign.CUDA.Analysis                              as CUDA
import qualified Debug.Trace                                        as DT

import Control.Applicative
import Control.Monad                                                ( (>=>), void )
import Control.Monad.State                                          ( gets )
import Data.String                                                  ( fromString )
import Data.Coerce                                                  as Safe
import Data.Bits                                                    as P
import Prelude                                                      as P hiding ( last )



-- 'Data.List.scanl' or 'Data.List.scanl1' style exclusive scan, but with the
-- restriction that the combination function must be associative to enable
-- efficient parallel implementation.
--
-- > scanl (+) 10 (use $ fromList (Z :. 10) [0..])
-- >
-- > ==> Array (Z :. 11) [10,10,11,13,16,20,25,31,38,46,55]
--
mkSegscan
    :: forall aenv sh e i.
       UID
    -> Gamma            aenv
    -> ArrayR (Array (sh, Int) e)
    -> IntegralType i
    -> Direction
    -> IRFun2       PTX aenv (e -> e -> e)
    -> Maybe (IRExp PTX aenv e)
    -> MIRDelayed   PTX aenv (Array (sh, Int) e)
    -> MIRDelayed   PTX aenv (Segments i)
    -> CodeGen      PTX      (IROpenAcc PTX aenv (Array (sh, Int) e))
mkSegscan uid aenv repr intTy dir combine seed arr seg
  = foldr1 (+++) <$> sequence (codeScan ++ codeFill)

  where
    codeScan = case repr of
      ArrayR (ShapeRsnoc ShapeRz) tp -> [ mkSegscanPrep dir uid aenv tp   intTy combine seed arr seg,
                                          mkSegscanAll dir uid aenv tp   intTy combine seed arr seg
                                        ]
      _                              -> [ undefined
                                        ]
    codeFill = case seed of
      Just s  -> [ mkSegscanFill uid aenv repr s ]
      Nothing -> []


-- TODO: Rewrite into datatype with conversion functions
scan_initialized     :: Int32
scan_initialized     = 0
scan_exclusive_known :: Int32
scan_exclusive_known = 1
scan_inclusive_known :: Int32
scan_inclusive_known = 2

type OperandsGrouped e = Operands ((((((e, e), e), e), e), e), e)
type OperandsGroupedI e = (Operands e, Operands e, Operands e, Operands e, Operands e, Operands e, Operands e)
type OperandsGroupedS e = Operands (((((((e, e), e), e), e), e), e), Int32)
elementsPerThread   = 7

unpairGrouped :: OperandsGrouped e -> OperandsGroupedI e
unpairGrouped t1 = (a, b, c, d, e, f, g)
  where
   (t2, g) = A.unpair t1
   (t3, f) = A.unpair t2
   (t4, e) = A.unpair t3
   (t5, d) = A.unpair t4
   (t6, c) = A.unpair t5
   (a,  b) = A.unpair t6

pairGrouped :: OperandsGroupedI e -> OperandsGrouped e
pairGrouped (a, b, c, d, e, f, g) = A.pair (A.pair (A.pair (A.pair (A.pair (A.pair a b) c) d) e) f) g

applyToTuple :: forall aenv e a.
                (Operands e -> CodeGen PTX (Operands a))
             -> OperandsGrouped e
             -> CodeGen PTX (OperandsGrouped a)
applyToTuple f tp = do
  let (t1, t2, t3, t4, t5, t6, t7) = unpairGrouped tp
  t1' <- f t1
  t2' <- f t2
  t3' <- f t3
  t4' <- f t4
  t5' <- f t5
  t6' <- f t6
  t7' <- f t7
  return $ pairGrouped (t1', t2', t3', t4', t5', t6', t7')

applyToTupleZip :: forall aenv e f.
                   (Operands e -> Operands f -> CodeGen PTX (Operands (e, Int)))
                 -> TypeR e
                 -> OperandsGrouped e
                 -> OperandsGrouped f
                 -> CodeGen PTX (OperandsGrouped e)
applyToTupleZip f typ tp hp = do
  let (t1, t2, t3, t4, t5, t6, t7) = unpairGrouped tp
  let (h1, h2, h3, h4, h5, h6, h7) = unpairGrouped hp
  let check = \cond func t1 h1 -> if (typ `TupRpair` TupRsingle scalarTypeInt, A.gt singleType cond (liftInt 0)) 
                                    then return $ A.pair t1 cond 
                                    else f t1 h1
  t1' <- check (liftInt 0)    f t1 h1
  t2' <- check (A.snd t1')    f t2 h2
  t3' <- check (A.snd t2')    f t3 h3
  t4' <- check (A.snd t3')    f t4 h4
  t5' <- check (A.snd t4')    f t5 h5
  t6' <- check (A.snd t5')    f t6 h6
  t7' <- check (A.snd t6')    f t7 h7
  return $ pairGrouped (A.fst t1', A.fst t2', A.fst t3', A.fst t4', A.fst t5', A.fst t6', A.fst t7')

typeToTuple :: TypeR a -> TypeR ((((((a, a), a), a), a), a), a)
typeToTuple tp = tp `TupRpair` tp `TupRpair` tp `TupRpair` tp `TupRpair` tp `TupRpair` tp `TupRpair` tp

lastTuple :: OperandsGrouped e -> Operands e
lastTuple t = last
  where (_, _, _, _, _, _, last) = unpairGrouped t


mkSegscanPrep
    :: forall aenv e i.
       Direction
    -> UID
    -> Gamma aenv
    -> TypeR e
    -> IntegralType i
    -> IRFun2 PTX aenv (e -> e -> e) -- ^ combination function
    -> MIRExp PTX aenv e             -- ^ seed element for exclusive scan
    -> MIRDelayed PTX aenv (Vector e) -- ^ input data
    -> MIRDelayed PTX aenv (Segments i) -- ^ head flags
    -> CodeGen PTX (IROpenAcc PTX aenv (Vector e))
mkSegscanPrep dir uid aenv tp intTy combine mseed marr mseg = do
  dev <- liftCodeGen $ gets ptxDeviceProperties
  let
    (arrBlockId, paramBlockId) = mutableArray (ArrayR dim1 (TupRsingle scalarTypeInt)) "blockIdArr"
    (arrTmpStatus, paramTmpStatus)  = mutableVolatileArray (ArrayR dim1 tmpStatusTp) "tmpStatus"
    (arrTmpAgg, paramTmpAgg) = mutableVolatileArray (ArrayR dim1 tmpAggTp) "tmpAgg"
    (arrOut, paramOut) = mutableArray (ArrayR dim1 tp) "out"
    (arrIn, paramIn) = delayedArray "in" marr
    (arrSeg, paramSeg) = delayedArray "seg" mseg
    end = indexHead (irArrayShape arrTmpStatus)
    paramEnv = envParam aenv
    config = launchConfigNoMaxBlocks dev (CUDA.incWarp dev) (\_ -> 0) const [|| const ||] elementsPerThread
    tmpStatusTp = TupRsingle scalarTypeInt32
    tmpAggTp = tp `TupRpair` tp
  makeOpenAccWith config uid "segscanPrep" (paramBlockId ++ paramTmpStatus ++ paramTmpAgg ++ paramOut ++ paramIn ++ paramSeg ++ paramEnv) $ do
    tid <- threadIdx
    bid <- blockIdx
    bid' <- int bid
    bd <- blockDim
    last <- A.sub numType bd (liftInt32 1)
    when (A.eq singleType tid last) $ do
      writeArray TypeInt arrTmpAgg bid' (A.pair (undefT tp) (undefT tp))
      __threadfence_grid
      writeArray TypeInt arrTmpStatus bid' (liftInt32 scan_initialized)
    return_


mkSegscanAll
    :: forall aenv e i.
       Direction
    -> UID
    -> Gamma aenv
    -> TypeR e
    -> IntegralType i
    -> IRFun2 PTX aenv (e -> e -> e) -- ^ combination function
    -> MIRExp PTX aenv e             -- ^ seed element for exclusive scan
    -> MIRDelayed PTX aenv (Vector e) -- ^ input data
    -> MIRDelayed PTX aenv (Segments i) -- ^ head flags
    -> CodeGen PTX (IROpenAcc PTX aenv (Vector e))
mkSegscanAll dir uid aenv tp intTy combine mseed marr mseg = do
  dev <- liftCodeGen $ gets ptxDeviceProperties
  let
    (arrBlockId, paramBlockId) = mutableArray (ArrayR dim1 (TupRsingle scalarTypeInt)) "blockIdArr"
    (arrTmpStatus, paramTmpStatus)  = mutableVolatileArray (ArrayR dim1 tmpStatusTp) "tmpStatus"
    (arrTmpAgg, paramTmpAgg) = mutableVolatileArray (ArrayR dim1 tmpAggTp) "tmpAgg"
    (arrOut, paramOut) = mutableArray (ArrayR dim1 tp) "out"
    (arrIn, paramIn) = delayedArray "in" marr
    (arrSeg, paramSeg) = delayedArray "seg" mseg
    end = indexHead (irArrayShape arrTmpStatus)
    paramEnv = envParam aenv
    config = launchConfigNoMaxBlocks dev (CUDA.incWarp dev) smem const [|| const ||] elementsPerThread
    tmpStatusTp = TupRsingle scalarTypeInt32
    tmpAggTp = tp `TupRpair` tp
    smem n
      | canShfl dev     = warps * bytes + 16 -- Need 8 bytes to save if there was a flag, and 8 to save the incremental counter - TODO: Reduce to 1 per
      | otherwise       = warps * (1 + per_warp) * bytes + 16
      where
        ws        = CUDA.warpSize dev
        warps     = n `P.quot` ws
        per_warp  = ws + ws `P.quot` 2
        bytes     = bytesElt tp + bytesElt (TupRsingle scalarTypeInt32)
  --
  makeOpenAccWith config uid "segscanAll" (paramBlockId ++ paramTmpStatus ++ paramTmpAgg ++ paramOut ++ paramIn ++ paramSeg ++ paramEnv) $ do
    -- Size of the input array
    sz  <- indexHead <$> delayedExtent arrIn
    -- Get all our dimensions
    bd <- blockDim
    bd' <- int bd
    tid <- threadIdx
    tid' <- int tid
    
    -- Create a piece of shared memory to save the incremental block id
    -- The reason for not just using the CUDA block id is that there are no guarantees that block n is scheduled before m
    -- when n < m. This could cause a deadlock since we rely on having the value of block n before we can finish processing m
    blockIdShared <- dynamicSharedMem (TupRsingle scalarTypeInt) TypeInt (liftInt 1) (liftInt 0)
    last <- A.sub numType bd (liftInt32 1)
    when (A.eq singleType tid last) $ do
      bIdPtr <- instr' $ GetElementPtr (asPtr defaultAddrSpace (op integralType (irArrayData arrBlockId))) [op integralType (liftInt 0)]
      -- Increment the counter atomically using the last thread
      bidT    <- instr' $ AtomicRMW (IntegralNumType TypeInt) NonVolatile RMW.Add bIdPtr (op integralType (liftInt 1)) (CrossThread, AcquireRelease)
      -- Save it to the shared memory so all blocks have access to it
      writeArray TypeInt blockIdShared (liftInt 0) (ir integralType bidT)
    
    -- Sync the threads, as we need the value in shared memory before we continue
    __syncthreads
    -- Grab the thread block id from shared memory
    s0  <- readArray TypeInt blockIdShared (liftInt 0)
    gd  <- gridDim
    gd' <- int gd
    bd <- blockDim
    bd' <- int bd
    -- Index this thread block starts at
    inf <- A.mul numType (liftInt elementsPerThread) =<< A.mul numType s0 bd'

    -- index i0 is the index this thread will read from
    i0 <- case dir of
            LeftToRight -> A.add numType inf =<< A.mul numType (liftInt elementsPerThread) tid'
            RightToLeft -> do x <- A.sub numType sz inf
                              y <- A.sub numType x =<< A.mul numType (liftInt elementsPerThread) tid'
                              z <- A.sub numType y (liftInt 1)
                              return z

    -- index j* is the index that we write to. Recall that for exclusive scans
    -- the output array is one larger than the input; the initial element will
    -- be written into this spot by thread 0 of the first thread block.
    j0    <- case mseed of
                Nothing -> return i0
                Just _  -> case dir of
                            LeftToRight -> A.add numType i0 (liftInt 1)
                            RightToLeft -> return i0

    -- If this thread has input, read data and participate in thread-block scan
    let valid i = case dir of
                    LeftToRight -> A.lt  singleType i sz
                    RightToLeft -> A.gte singleType i (liftInt 0)


    when (valid i0) $ do
      let indexFunc = \x y -> case dir of
                          LeftToRight -> A.add numType x (liftInt y)
                          RightToLeft -> A.sub numType x (liftInt y)
      x0 <- app1 (delayedLinearIndex arrIn) =<< (indexFunc i0 0)
      x1 <- app1 (delayedLinearIndex arrIn) =<< (indexFunc i0 1)
      x2 <- app1 (delayedLinearIndex arrIn) =<< (indexFunc i0 2)
      x3 <- app1 (delayedLinearIndex arrIn) =<< (indexFunc i0 3)
      x4 <- app1 (delayedLinearIndex arrIn) =<< (indexFunc i0 4)
      x5 <- app1 (delayedLinearIndex arrIn) =<< (indexFunc i0 5)
      x6 <- app1 (delayedLinearIndex arrIn) =<< (indexFunc i0 6)
      -- TODO: Should this really be done for multiple elements? I think this should only be applied for element 0
      let seedF = \x -> case mseed of
                              Nothing   -> return x
                              Just seed ->
                                if (tp, A.eq singleType tid (liftInt32 0) `A.land'` A.eq singleType s0 (liftInt 0))
                                  then do
                                    z <- seed
                                    case dir of
                                      LeftToRight -> writeArray TypeInt32 arrOut (liftInt32 0) z >> app2 combine z x
                                      RightToLeft -> writeArray TypeInt   arrOut sz            z >> app2 combine x z
                                  else
                                    return x0
      resSeeded <- applyToTuple seedF $ pairGrouped (x0, x1, x2, x3, x4, x5, x6)

      f0 <- app1 (delayedLinearIndex arrSeg) =<< (indexFunc i0 0)
      f1 <- app1 (delayedLinearIndex arrSeg) =<< (indexFunc i0 1)
      f2 <- app1 (delayedLinearIndex arrSeg) =<< (indexFunc i0 2)
      f3 <- app1 (delayedLinearIndex arrSeg) =<< (indexFunc i0 3)
      f4 <- app1 (delayedLinearIndex arrSeg) =<< (indexFunc i0 4)
      f5 <- app1 (delayedLinearIndex arrSeg) =<< (indexFunc i0 5)
      f6 <- app1 (delayedLinearIndex arrSeg) =<< (indexFunc i0 6)
      let resSegments = pairGrouped (f0, f1, f2, f3, f4, f5, f6)

      n  <- A.sub numType sz inf
      n' <- i32 n
      -- The segscanBlock returns the new element value, and the first flag that occured in this block
      -- The first flag value will be used later on to know when we have to stop adding the aggregate
      -- of the previous block to our elements.
      blockRes <- if ((typeToTuple tp) `TupRpair` TupRsingle scalarTypeInt32, A.gte singleType n bd')
              then segscanBlock dir dev tp intTy combine Nothing   resSeeded resSegments
              else segscanBlock dir dev tp intTy combine (Just n') resSeeded resSegments


      -- We now have done block-level scans, so now we need to incorportate previous block(s) into
      -- our application. Communication is done over global memory
      let hadFlag = A.neq singleType (A.snd blockRes) (liftInt32 maxBound)
      let isFirstBlock = A.eq singleType s0 (liftInt 0)
      status <- if (TupRsingle scalarTypeInt32, hadFlag `lor'` isFirstBlock)
                  then return (liftInt32 scan_inclusive_known)
                  else return (liftInt32 scan_exclusive_known)

      -- The last thread also writes its result---the aggregate for this
      -- thread block, and it's corresponding status---to the temporary array. This is only
      -- necessary for full blocks in a multi-block scan; the final
      -- partially-full tile does not have a successor block.
      last <- A.sub numType bd (liftInt32 1)
      when (A.eq singleType tid last) $ do
        writeArray TypeInt arrTmpAgg s0 (A.pair (lastTuple $ A.fst blockRes) (lastTuple $ A.fst blockRes))
        __threadfence_grid
        writeArray TypeInt arrTmpStatus s0 status
      
      __syncthreads

      -- Function to deconstruct the tuple
      let unPair3 e = let (e', z) = A.unpair e
                          (x, y)  = A.unpair e'
                          in (x, y, z)
      let pair3 x y z = A.pair (A.pair x y) z

      let unPair4 e = let (e', y, z) = unPair3 e
                          (w, x) = A.unpair e'
                          in (w, x, y, z)
      let pair4 w x y z = A.pair (pair3 w x y) z
      
      -- We now need to incorporate the previous value up until our first flag. First, we calculate the prefix
      -- using the decoupled look-back algorithm.
      let whileTp = TupRsingle scalarTypeInt32 `TupRpair` TupRsingle scalarTypeInt `TupRpair` tp
      -- The block we start looking back to, which would be the (blockId - 1)
      lookAtBlock <- A.sub numType s0 (liftInt 1)
      let waitForAvailable = while (whileTp `TupRpair` TupRsingle scalarTypeInt32)
                        (\(unPair4 -> (done, _, _, _)) -> A.eq singleType done (liftInt32 0))
                        (\(unPair4 -> (done,blockId,agg,_)) -> do
                            previousStatus <- readArray TypeInt arrTmpStatus blockId
                            let statusIsInit = A.eq singleType previousStatus (liftInt32 scan_initialized)
                            if (whileTp `TupRpair` TupRsingle scalarTypeInt32, statusIsInit)
                              then do
                                return $ pair4 done blockId agg (liftInt32 0)
                              else do
                                -- In the normal single-pass look-back scan, we do not have to check
                                -- whether or not the status is inclusive or exclusive, since we
                                -- can always just use the combine function. This is a bit different
                                -- with this segmented version: if we do not check wheter the status
                                -- is inclusive or exclusive, we might add an exclusive prefix that
                                -- actually had an flag in it, which wouldn't be good
                                previousAggs <- readArray TypeInt arrTmpAgg blockId
                                let (prevAgg, _) = A.unpair previousAggs
                                newAggregate <- if (tp, A.eq singleType blockId lookAtBlock)
                                                  then return prevAgg
                                                  else case dir of
                                                    LeftToRight -> app2 combine prevAgg agg
                                                    RightToLeft -> app2 combine agg prevAgg
                                return $ pair4 (liftInt32 1) blockId newAggregate previousStatus
                        )
      res <- if (typeToTuple tp, A.gt singleType s0 (liftInt 0))
        then do
          r <- while (whileTp) 
                (\(unPair3 -> (done,_,_))         -> A.eq singleType done (liftInt32 0))
                (\(unPair3 -> (done,blockId,agg)) -> do
                          __threadfence_block
                          previousStatus <- readArray TypeInt arrTmpStatus blockId
                          statusIsInclusive <- A.eq singleType previousStatus (liftInt32 scan_inclusive_known)
                          let allThreadsInclusvie = __all_sync (liftWord32 maxBound) statusIsInclusive
                          if (whileTp, allThreadsInclusvie)
                            then do
                              previousAggs <- readArray TypeInt arrTmpAgg blockId
                              let (prevAgg, inclusivePrefix) = A.unpair previousAggs
                              newAggregate <- if (tp, A.eq singleType blockId lookAtBlock)
                                                then return inclusivePrefix
                                                else case dir of 
                                                  LeftToRight -> app2 combine inclusivePrefix agg
                                                  RightToLeft -> app2 combine agg inclusivePrefix
                              return $ pair3 (liftInt32 1) blockId newAggregate
                            else do
                              if (whileTp, A.gt singleType blockId (liftInt 0))
                                then do
                                  waitR <- waitForAvailable $ pair4 done blockId agg (liftInt32 0)
                                  let (_, _, newAggregate, statusFound) = unPair4 waitR
                                  prevBlock <- A.sub numType blockId (liftInt 1)
                                  newDone <- if (TupRsingle scalarTypeInt32, A.eq singleType statusFound (liftInt32 scan_inclusive_known))
                                    then return $ liftInt32 1
                                    else return $ liftInt32 0
                                  return $ pair3 newDone prevBlock newAggregate
                                else return $ pair3 done lookAtBlock (undefT tp)
                )
                (pair3 (liftInt32 0) lookAtBlock (undefT tp))
          -- We're done, so unpack the value and find out what aggregate we have to add
          let (_, _, aggregateToAdd) = unPair3 r
          -- Add the aggregate until we hit the first flag
          let combine' = \x index -> if (tp `TupRpair` TupRsingle scalarTypeInt, flip (A.lt singleType) (A.snd blockRes) =<< A.add numType index =<< A.mul numType tid (liftInt32 $ P.fromIntegral elementsPerThread))
                                then do
                                  res <- case dir of
                                    LeftToRight -> app2 combine aggregateToAdd x
                                    RightToLeft -> app2 combine x aggregateToAdd
                                  return $ A.pair res (liftInt 0)
                                else do
                                  return $ A.pair x (liftInt 1)
          applyToTupleZip combine' tp (A.fst blockRes) $ pairGrouped (liftInt32 0, liftInt32 1, liftInt32 2, liftInt32 3, liftInt32 4, liftInt32 5, liftInt32 6)
        else return $ A.fst blockRes

      -- If we only set an exclusive status, we now need to set the inclusive status.
      when (A.eq singleType status (liftInt32 scan_exclusive_known)) $
        when (A.eq singleType tid last) $ do
          writeArray TypeInt arrTmpAgg s0 (A.pair (lastTuple $ A.fst blockRes) (lastTuple res))
          __threadfence_grid
          writeArray TypeInt arrTmpStatus s0 (liftInt32 scan_inclusive_known)
      
      let (res1, res2, res3, res4, res5, res6, res7) = unpairGrouped res
      let writeArray' = flip $ writeArray TypeInt arrOut
      writeArray' res1 =<< (indexFunc j0 0)
      writeArray' res2 =<< (indexFunc j0 1)
      writeArray' res3 =<< (indexFunc j0 2)
      writeArray' res4 =<< (indexFunc j0 3)
      writeArray' res5 =<< (indexFunc j0 4)
      writeArray' res6 =<< (indexFunc j0 5)
      writeArray' res7 =<< (indexFunc j0 6)

    return_




-- Variant of 'scanl' where the final result is returned in a separate array.
--
-- > scanr' (+) 10 (use $ fromList (Z :. 10) [0..])
-- >
-- > ==> ( Array (Z :. 10) [10,10,11,13,16,20,25,31,38,46]
--       , Array Z [55]
--       )
--
mkSegscan'
    :: forall aenv sh e i.
       UID
    -> Gamma          aenv
    -> ArrayR (Array (sh, Int) e)
    -> IntegralType i
    -> Direction
    -> IRFun2     PTX aenv (e -> e -> e)
    -> IRExp      PTX aenv e
    -> MIRDelayed PTX aenv (Array (sh, Int) e)
    -> MIRDelayed   PTX aenv (Segments i)
    -> CodeGen    PTX      (IROpenAcc PTX aenv (Array (sh, Int) e, Array sh e))
mkSegscan' uid aenv repr intTy dir combine seed arr seg
  | ArrayR (ShapeRsnoc ShapeRz) tp <- repr
  = DT.trace "mkSegscan'" $ undefined
  --
  | otherwise
  = DT.trace "mkSegscan'" $ undefined



-- Parallel scan, auxiliary
--
-- If this is an exclusive scan of an empty array, we just fill the result with
-- the seed element.
--
mkSegscanFill
    :: UID
    -> Gamma aenv
    -> ArrayR (Array sh e)
    -> IRExp PTX aenv e
    -> CodeGen PTX (IROpenAcc PTX aenv (Array sh e))
mkSegscanFill uid aenv repr seed =
  mkGenerate uid aenv repr (IRFun1 (const seed))

mkSegscan'Fill
    :: UID
    -> Gamma aenv
    -> ArrayR (Array (sh, Int) e)
    -> IRExp PTX aenv e
    -> CodeGen PTX (IROpenAcc PTX aenv (Array (sh, Int) e, Array sh e))
mkSegscan'Fill uid aenv repr seed =
  Safe.coerce <$> mkGenerate uid aenv (reduceRank repr) (IRFun1 (const seed))


-- Block wide scan
-- ---------------

segscanBlock
    :: forall aenv e i.
       Direction
    -> DeviceProperties                             -- ^ properties of the target device
    -> TypeR e
    -> IntegralType i
    -> IRFun2 PTX aenv (e -> e -> e)                -- ^ combination function
    -> Maybe (Operands Int32)                       -- ^ number of valid elements (may be less than block size)
    -> OperandsGrouped e                                   -- ^ calling thread's input element
    -> OperandsGrouped i
    -> CodeGen PTX (OperandsGroupedS e)
segscanBlock dir dev
  | canShfl dev = segscanBlockShfl dir dev -- shfl instruction available in compute >= 3.0
 -- | otherwise   = segscanBlockSMem dir dev -- equivalent, slightly slower version


-- Efficient block-wide (inclusive) scan using the specified operator.
--
-- Each block requires (#warps * (1 + 1.5*warp size)) elements of dynamically
-- allocated shared memory.
--
-- Example: https://github.com/NVlabs/cub/blob/1.5.4/cub/block/specializations/block_scan_warp_scans.cuh
--
-- NOTE: [Synchronisation problems with SM_70 and greater]
--
-- This operation uses thread synchronisation. When calling this operation, it
-- is important that all active (that is, non-exited) threads of the thread
-- block participate. It seems that sm_70+ (devices with independent thread
-- scheduling) are stricter about the requirement that all non-existed threads
-- participate in every barrier.
--
-- See: https://github.com/AccelerateHS/accelerate/issues/436
--
segscanBlockSMem
    :: forall aenv e i.
       Direction
    -> DeviceProperties                             -- ^ properties of the target device
    -> TypeR e
    -> IntegralType i
    -> IRFun2 PTX aenv (e -> e -> e)                -- ^ combination function
    -> Maybe (Operands Int32)                       -- ^ number of valid elements (may be less than block size)
    -> Operands e                                   -- ^ calling thread's input element
    -> Operands i
    -> CodeGen PTX (Operands e)
segscanBlockSMem dir dev tp intTy combine nelem nope nflag = (warpScan >=> warpPrefix) nope
  where
    int32 :: Integral a => a -> Operands Int32
    int32 = liftInt32 . P.fromIntegral

    -- Temporary storage required for each warp
    warp_smem_elems = CUDA.warpSize dev + (CUDA.warpSize dev `P.quot` 2)
    warp_smem_bytes = warp_smem_elems  * bytesElt tp

    -- Step 1: Scan in every warp
    warpScan :: Operands e -> CodeGen PTX (Operands e)
    warpScan input = do
      -- Allocate (1.5 * warpSize) elements of shared memory for each warp
      -- (individually addressable by each warp)
      wid   <- warpId
      skip  <- A.mul numType wid (int32 warp_smem_bytes)
      smem  <- dynamicSharedMem tp TypeInt32 (int32 warp_smem_elems) skip
      segscanWarpSMem dir dev tp combine smem input

    -- Step 2: Collect the aggregate results of each warp to compute the prefix
    -- values for each warp and combine with the partial result to compute each
    -- thread's final value.
    warpPrefix :: Operands e -> CodeGen PTX (Operands e)
    warpPrefix input = do
      -- Allocate #warps elements of shared memory
      bd    <- blockDim
      warps <- A.quot integralType bd (int32 (CUDA.warpSize dev))
      skip  <- A.mul numType warps (int32 warp_smem_bytes)
      smem  <- dynamicSharedMem tp TypeInt32 warps skip

      -- Share warp aggregates
      wid   <- warpId
      lane  <- laneId
      when (A.eq singleType lane (int32 (CUDA.warpSize dev - 1))) $ do
        writeArray TypeInt32 smem wid input

      -- Wait for each warp to finish its local scan and share the aggregate
      __syncthreads

      -- Compute the prefix value for this warp and add to the partial result.
      -- This step is not required for the first warp, which has no carry-in.
      if (tp, A.eq singleType wid (liftInt32 0))
        then return input
        else do
          -- Every thread sequentially scans the warp aggregates to compute
          -- their prefix value. We do this sequentially, but could also have
          -- warp 0 do it cooperatively if we limit thread block sizes to
          -- (warp size ^ 2).
          steps  <- case nelem of
                      Nothing -> return wid
                      Just n  -> A.min singleType wid =<< A.quot integralType n (int32 (CUDA.warpSize dev))

          p0     <- readArray TypeInt32 smem (liftInt32 0)
          prefix <- iterFromStepTo tp (liftInt32 1) (liftInt32 1) steps p0 $ \step x -> do
                      y <- readArray TypeInt32 smem step
                      case dir of
                        LeftToRight -> app2 combine x y
                        RightToLeft -> app2 combine y x

          case dir of
            LeftToRight -> app2 combine prefix input
            RightToLeft -> app2 combine input prefix


-- Warp-wide scan
-- --------------

-- Efficient warp-wide (inclusive) scan using the specified operator.
--
-- Each warp requires 48 (1.5 x warp size) elements of shared memory. The
-- routine assumes that it is allocated individually per-warp (i.e. can be
-- indexed in the range [0, warp size)).
--
-- Example: https://github.com/NVlabs/cub/blob/1.5.4/cub/warp/specializations/warp_scan_smem.cuh
--
segscanWarpSMem
    :: forall aenv e.
       Direction
    -> DeviceProperties                             -- ^ properties of the target device
    -> TypeR e
    -> IRFun2 PTX aenv (e -> e -> e)                -- ^ combination function
    -> IRArray (Vector e)                           -- ^ temporary storage array in shared memory (1.5 x warp size elements)
    -> Operands e                                   -- ^ calling thread's input element
    -> CodeGen PTX (Operands e)
segscanWarpSMem dir dev tp combine smem = scan 0
  where
    log2 :: Double -> Double
    log2 = P.logBase 2

    -- Number of steps required to scan warp
    steps     = P.floor (log2 (P.fromIntegral (CUDA.warpSize dev)))
    halfWarp  = P.fromIntegral (CUDA.warpSize dev `P.quot` 2)

    -- Unfold the scan as a recursive code generation function
    scan :: Int -> Operands e -> CodeGen PTX (Operands e)
    scan step x
      | step >= steps = return x
      | otherwise     = do
          let offset = liftInt32 (1 `P.shiftL` step)

          -- share partial result through shared memory buffer
          lane <- laneId
          i    <- A.add numType lane (liftInt32 halfWarp)
          writeArray TypeInt32 smem i x

          __syncwarp

          -- update partial result if in range
          x'   <- if (tp, A.gte singleType lane offset)
                    then do
                      i' <- A.sub numType i offset    -- lane + HALF_WARP - offset
                      x' <- readArray TypeInt32 smem i'
                      case dir of
                        LeftToRight -> app2 combine x' x
                        RightToLeft -> app2 combine x x'

                    else
                      return x

          __syncwarp

          scan (step+1) x'


segscanBlockShfl
    :: forall aenv e i.
       Direction
    -> DeviceProperties                             -- ^ properties of the target device
    -> TypeR e
    -> IntegralType i
    -> IRFun2 PTX aenv (e -> e -> e)                -- ^ combination function
    -> Maybe (Operands Int32)                       -- ^ number of valid elements (may be less than block size)
    -> OperandsGrouped e                                   -- ^ calling thread's input element
    -> OperandsGrouped i
    -> CodeGen PTX (OperandsGroupedS e)
segscanBlockShfl dir dev tp intTy combine nelem nope nflag = (warpScan >=> warpPrefix) nope
  where
    int32 :: Integral a => a -> Operands Int32
    int32 = liftInt32 . P.fromIntegral

    -- Step 1: Scan in every warp
    warpScan :: OperandsGrouped e -> CodeGen PTX (OperandsGrouped e)
    warpScan e = do 
      fFlags <- applyToTuple (\x -> A.fromIntegral intTy numType x) nflag
      segscanWarpShfl dir dev tp combine e fFlags

    -- Step 2: Collect the aggregate results of each warp to compute the prefix
    -- values for each warp and combine with the partial result to compute each
    -- thread's final value.
    warpPrefix :: OperandsGrouped e -> CodeGen PTX (OperandsGroupedS e)
    warpPrefix input = do
      fFlags <- applyToTuple (\x -> A.fromIntegral intTy numType x) nflag
      -- Allocate #warps elements of shared memory
      bd    <- blockDim
      warps <- A.quot integralType bd (int32 (CUDA.warpSize dev))
      
      -- Piece of shared memory to store warp aggregates
      smem  <- dynamicSharedMem tp TypeInt32 warps (liftInt32 16)

      -- Share warp aggregates
      wid   <- warpId
      lane  <- laneId
      when (A.eq singleType lane (int32 $ CUDA.warpSize dev - 1)) $ do
        writeArray TypeInt32 smem wid (lastTuple input)
      
      -- We want to find out for each warp and block, at which index the first reset
      -- happens due to a flag. This is because after this flag, we should
      -- not incorporate the prefix into the elements. As such, create
      -- a shared array for the warp values ...
      skipWarpPrefix <- A.mul numType warps $ liftInt32 $ P.fromIntegral $ bytesElt tp
      skip <- A.add numType (liftInt32 16) skipWarpPrefix
      sflags <- dynamicSharedMem (TupRsingle scalarTypeInt32) TypeInt32 (liftInt32 0) skip

      -- ... and a piece of shared memory for the block total. 
      -- TODO: Figure out what is more performant, keeping two different shared arrays or keeping one,
      -- and then at the end min all the warp values (e.g. by using one thread) and sharing that
      blockHasFlag <- dynamicSharedMem (TupRsingle scalarTypeInt32) TypeWord32 (liftWord32 1) (liftWord32 8)

      -- Set the value of the last flag to the max value, so that the `min` function later can reduce this value
      -- to the first lane that has a flag. If the value stays the same as the warp size, we know
      -- that there is no flag. Lane 0 sets this value, as Lane (warpSize - 1) might have stopped already
      -- because the last block could have less elements than the block size
      -- Finding that bug took like 3 hours...
      when (A.eq singleType lane (int32 $ (0 :: Int32))) $ do
        writeArray TypeInt32 sflags wid (liftInt32 maxBound)
        writeArray TypeInt32 blockHasFlag (liftInt32 0) (liftInt32 maxBound)
      
      -- Make sure that each warps has finished its local scan and its first flag, and it has shared this with
      -- the other threads in the block.
      __syncthreads

      tid <- threadIdx
      
      -- Grab a pointer to the shared flags array, with index the current warp id. Needed to perform the atomic operation
      ptr <- instr' $ GetElementPtr (asPtr defaultAddrSpace (op integralType (irArrayData sflags))) [op integralType wid]
      -- As well as a pointer for the complete block
      ptrBlock <- instr' $ GetElementPtr (asPtr defaultAddrSpace (op integralType (irArrayData blockHasFlag))) [op integralType (liftInt 0)]
      -- TODO: Make better
      let (f1, f2, f3, f4, f5, f6, f7) = unpairGrouped fFlags
      when (A.gt singleType f1 (liftInt32 0)) $ do
        laneId <- A.add numType (liftInt32 0) =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) lane
        tidId <- A.add numType (liftInt32 0) =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) tid
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptr (op integralType laneId) (CrossThread, AcquireRelease)
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptrBlock (op integralType tidId) (CrossThread, AcquireRelease)
      when (A.gt singleType f2 (liftInt32 0)) $ do
        laneId <- A.add numType (liftInt32 1) =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) lane
        tidId <- A.add numType (liftInt32 1) =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) tid
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptr (op integralType laneId) (CrossThread, AcquireRelease)
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptrBlock (op integralType tidId) (CrossThread, AcquireRelease)
      when (A.gt singleType f3 (liftInt32 0)) $ do
        laneId <- A.add numType (liftInt32 2) =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) lane
        tidId <- A.add numType (liftInt32 2) =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) tid
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptr (op integralType laneId) (CrossThread, AcquireRelease)
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptrBlock (op integralType tidId) (CrossThread, AcquireRelease)
      when (A.gt singleType f4 (liftInt32 0)) $ do
        laneId <- A.add numType (liftInt32 3) =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) lane
        tidId <- A.add numType (liftInt32 3) =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) tid
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptr (op integralType laneId) (CrossThread, AcquireRelease)
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptrBlock (op integralType tidId) (CrossThread, AcquireRelease)
      when (A.gt singleType f5 (liftInt32 0)) $ do
        laneId <- A.add numType (liftInt32 4) =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) lane
        tidId <- A.add numType (liftInt32 4) =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) tid
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptr (op integralType laneId) (CrossThread, AcquireRelease)
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptrBlock (op integralType tidId) (CrossThread, AcquireRelease)
      when (A.gt singleType f6 (liftInt32 0)) $ do
        laneId <- A.add numType (liftInt32 5) =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) lane
        tidId <- A.add numType (liftInt32 5) =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) tid
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptr (op integralType laneId) (CrossThread, AcquireRelease)
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptrBlock (op integralType tidId) (CrossThread, AcquireRelease)
      when (A.gt singleType f7 (liftInt32 0)) $ do
        laneId <- A.add numType (liftInt32 6) =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) lane
        tidId <- A.add numType (liftInt32 6) =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) tid
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptr (op integralType laneId) (CrossThread, AcquireRelease)
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptrBlock (op integralType tidId) (CrossThread, AcquireRelease)

      -- Wait for each warp to finish its atomic operations and share that info
      __syncthreads

      -- Compute the prefix value for this warp and add to the partial result.
      -- This step is not required for the first warp, which has no carry-in.
      newVal <- if (typeToTuple tp, A.eq singleType wid (liftInt32 0))
        then return input
        else do
          -- Every thread sequentially scans the warp aggregates to compute
          -- their prefix value. We do this sequentially, but could also have
          -- warp 0 do it cooperatively if we limit thread block sizes to
          -- (warp size ^ 2).
          steps <- case nelem of
                      Nothing -> return wid
                      Just n  -> A.min singleType wid =<< A.quot integralType n (int32 (CUDA.warpSize dev))

          p0     <- readArray TypeInt32 smem (liftInt32 0)
          prefix <- iterFromStepTo tp (liftInt32 1) (liftInt32 1) steps p0 $ \step x -> do
                      y <- readArray TypeInt32 smem step
                      flag <- readArray TypeInt32 sflags step
                      -- If there is no flag in the warp we look at (reprented by the value of warp size),
                      -- we add that warps prefix. If there was a flag, any values before that warp don't matter
                      -- anymore.
                      if (tp, A.eq singleType flag (liftInt32 maxBound))
                        then do
                          case dir of
                            LeftToRight -> app2 combine x y
                            RightToLeft -> app2 combine y x
                        else
                          return y

          -- Now check if we actually should incorporate the prefix values.
          -- This should happen for all lanes before the first flag, because after the first flag
          -- the prefix doesn't matter anymore
          sflagel <- readArray TypeInt32 sflags wid
          let combineF = \input index ->
                          if (tp `TupRpair` TupRsingle scalarTypeInt, flip (A.lt singleType) sflagel =<< A.add numType index =<< A.mul numType (liftInt32 $ P.fromIntegral elementsPerThread) lane)
                            then do
                              combined <- case dir of
                                LeftToRight -> app2 combine prefix input
                                RightToLeft -> app2 combine input prefix
                              return $ A.pair combined (liftInt 0)
                            else 
                              return $ A.pair input (liftInt 1)
          applyToTupleZip combineF tp input $ pairGrouped (liftInt32 0, liftInt32 1, liftInt32 2, liftInt32 3, liftInt32 4, liftInt32 5, liftInt32 6)

      blockHasFlagVal <- readArray TypeInt32 blockHasFlag (liftInt32 0)
      blockHasFlag' <- A.neq singleType blockHasFlagVal (liftInt32 maxBound)
      return (A.pair newVal blockHasFlagVal)

segscanWarpShfl
    :: forall aenv e.
       Direction
    -> DeviceProperties                             -- ^ properties of the target device
    -> TypeR e
    -> IRFun2 PTX aenv (e -> e -> e)                -- ^ combination function
    -> OperandsGrouped e                                   -- ^ calling thread's input element
    -> OperandsGrouped Int
    -> CodeGen PTX (OperandsGrouped e)
segscanWarpShfl dir dev tp combine el flag = do
  newEls <- prescan el flag
  hasFlag' <- hadflag flag
  scan 0 (lastTuple newEls) hasFlag' newEls flag
  where
    log2 :: Double -> Double
    log2 = P.logBase 2

    -- Number of steps required to scan warp
    steps = P.floor (log2 (P.fromIntegral (CUDA.warpSize dev)))

    hadflag :: OperandsGrouped Int -> CodeGen PTX (Operands Int)
    hadflag flags = do
      let (f1, f2, f3, f4, f5, f6, f7) = unpairGrouped flags
      f2' <- A.add numType f1 f2
      f3' <- A.add numType f2' f3
      f4' <- A.add numType f3' f4
      f5' <- A.add numType f4' f5
      f6' <- A.add numType f5' f6
      f7' <- A.add numType f6' f7
      return f7'

    prescan :: OperandsGrouped e -> OperandsGrouped Int -> CodeGen PTX (OperandsGrouped e)
    prescan els flags = do
      let combine' = \x1 x2 flag -> if (tp, A.lte singleType flag (liftInt 0))
                                   then do
                                     case dir of
                                       LeftToRight -> app2 combine x1 x2
                                       RightToLeft -> app2 combine x2 x1
                                    else
                                      return x2
      let (x1, x2, x3, x4, x5, x6, x7) = unpairGrouped els
      let (f1, f2, f3, f4, f5, f6, f7) = unpairGrouped flags
      x2' <- combine' x1 x2 f2
      x3' <- combine' x2' x3 f3
      x4' <- combine' x3' x4 f4
      x5' <- combine' x4' x5 f5
      x6' <- combine' x5' x6 f6
      x7' <- combine' x6' x7 f7
      return $ pairGrouped (x1, x2', x3', x4', x5', x6', x7')

    -- Unfold the scan as a recursive code generation function
    scan :: Int -> Operands e -> Operands Int -> OperandsGrouped e -> OperandsGrouped Int -> CodeGen PTX (OperandsGrouped e)
    scan step x f els flags
      | step >= steps = return els
      | otherwise     = do
          let offset = 1 `P.shiftL` step

          -- share partial result through shared memory buffer
          y    <- __shfl_up tp x (liftWord32 offset)
          g    <- __shfl_up (TupRsingle scalarTypeInt) f (liftWord32 offset)
          lane <- laneId

          let updateFlag = \f g -> if ((TupRsingle scalarTypeInt), A.gte singleType lane (liftInt32 . P.fromIntegral $ offset))
                then do
                  A.add numType f g
                else
                  return f

          -- update partial result if in range
          let updateEl = \x y f -> if (tp `TupRpair` TupRsingle scalarTypeInt, A.gte singleType lane (liftInt32 . P.fromIntegral $ offset))
              then do
                if (tp `TupRpair` TupRsingle scalarTypeInt, A.lte singleType f (liftInt 0))
                  then do
                    combined <- case dir of
                                  LeftToRight -> app2 combine y x
                                  RightToLeft -> app2 combine x y
                    return $ A.pair combined f
                  else
                    return $ A.pair x f
              else
                return $ A.pair x f

          newTuple <- applyToTupleZip (\x f -> updateEl x y f) tp els flags
          newFlags <- applyToTuple (\f -> updateFlag f g) flags
          hasflag <- hadflag newFlags
          scan (step+1) (lastTuple newTuple) hasflag newTuple newFlags

-- Utilities
-- ---------

i32 :: Operands Int -> CodeGen PTX (Operands Int32)
i32 = A.fromIntegral integralType numType

int :: Operands Int32 -> CodeGen PTX (Operands Int)
int = A.fromIntegral integralType numType

