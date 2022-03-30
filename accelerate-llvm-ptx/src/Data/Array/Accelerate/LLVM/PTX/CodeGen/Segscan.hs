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
  = DT.trace "mkSegscan" $ foldr1 (+++) <$> sequence (codeScan ++ codeFill)

  where
    codeScan = case repr of
      ArrayR (ShapeRsnoc ShapeRz) tp -> [ mkSegscanAll dir uid aenv tp   intTy combine seed arr seg
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
mkSegscanAll dir uid aenv tp intTy combine mseed marr mseg = DT.trace "Running mkSegscanAll..." $ do
  dev <- liftCodeGen $ gets ptxDeviceProperties
  let
    (arrTmp, paramTmp)  = mutableArray (ArrayR dim1 tmpTp) "tmp"
    (arrOut, paramOut) = mutableArray (ArrayR dim1 tp) "out"
    (arrIn, paramIn) = delayedArray "in" marr
    (arrSeg, paramSeg) = delayedArray "seg" mseg
    end = indexHead (irArrayShape arrOut)
    paramEnv = envParam aenv
    config = launchConfig dev (CUDA.incWarp dev) smem const [|| const ||]
    tmpTp = TupRsingle scalarTypeInt32 `TupRpair` tp
    smem n
      | canShfl dev     = warps * bytes + 8 -- Need eight bytes to save if there was a flag - TODO: Reduce to 1
      | otherwise       = warps * (1 + per_warp) * bytes + 8
      where
        ws        = CUDA.warpSize dev
        warps     = n `P.quot` ws
        per_warp  = ws + ws `P.quot` 2
        bytes     = bytesElt tp + bytesElt (TupRsingle scalarTypeInt32)
  --
  makeOpenAccWith config uid "segscanAll" (paramTmp ++ paramOut ++ paramIn ++ paramSeg ++ paramEnv) $ do
    -- Size of the input array
    sz  <- indexHead <$> delayedExtent arrIn
    
    -- TODO: Use globally increasing value for this
    bid <- blockIdx
    s0  <- int bid
    gd  <- gridDim
    gd' <- int gd

    imapFromStepTo s0 gd' end $ \chunk -> do
      -- Start by setting the values in global memory
      writeArray TypeInt arrTmp chunk (A.pair (liftInt32 scan_initialized) (undefT tp))
      bd <- blockDim
      bd' <- int bd
      -- Index this thread block starts at
      inf <- A.mul numType chunk bd'

      -- index i0 is the index this thread will read from
      tid <- threadIdx
      tid' <- int tid
      i0 <- case dir of
              LeftToRight -> A.add numType inf tid'
              RightToLeft -> do x <- A.sub numType sz inf
                                y <- A.sub numType x tid'
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
        x0 <- app1 (delayedLinearIndex arrIn) i0
        f0 <- app1 (delayedLinearIndex arrSeg) i0
        x1 <- case mseed of
                Nothing   -> return x0
                Just seed ->
                  if (tp, A.eq singleType tid (liftInt32 0) `A.land'` A.eq singleType chunk (liftInt 0))
                    then do
                      z <- seed
                      case dir of
                        LeftToRight -> writeArray TypeInt32 arrOut (liftInt32 0) z >> app2 combine z x0
                        RightToLeft -> writeArray TypeInt   arrOut sz            z >> app2 combine x0 z
                    else
                      return x0

        n  <- A.sub numType sz inf
        n' <- i32 n
        x2 <- if (tp `TupRpair` TupRsingle scalarTypeInt32, A.gte singleType n bd')
                then segscanBlock dir dev tp intTy combine Nothing   x1 f0
                else segscanBlock dir dev tp intTy combine (Just n') x1 f0


        -- We now have done block-level scans, so now we need to incorportate previous block(s) into
        -- our application. Communication is done over global memory
        let hadFlag = A.neq singleType (A.snd x2) (liftInt32 maxBound)
        let isFirstBlock = A.eq singleType chunk (liftInt 0)
        status <- if (TupRsingle scalarTypeInt32, hadFlag `lor'` isFirstBlock)
                    then return (liftInt32 scan_inclusive_known)
                    else return (liftInt32 scan_exclusive_known)

        -- The last thread also writes its result---the aggregate for this
        -- thread block, and it's corresponding status---to the temporary array. This is only
        -- necessary for full blocks in a multi-block scan; the final
        -- partially-full tile does not have a successor block.
        last <- A.sub numType bd (liftInt32 1)
        when (A.eq singleType tid last) $
          writeArray TypeInt arrTmp chunk (A.pair status (A.fst x2))
        
        -- Threadfence so that the writes and writes are not out-of-order
        __threadfence_grid

        -- Function to deconstruct the tuple in the while loop
        let unPair3 e = let (e', z) = A.unpair e
                            (x, y)  = A.unpair e'
                            in (x, y, z)
        let pair3 x y z = A.pair (A.pair x y) z
        lookAtBlock <- A.sub numType chunk (liftInt 1)
        -- We now need to incorporate the previous value up until our first flag.
        let whileTp = TupRsingle scalarTypeInt32 `TupRpair` TupRsingle scalarTypeInt `TupRpair` tp
        res <- if (tp, A.gt singleType chunk (liftInt 0))
          then do
            r <- while (whileTp) 
                  (\(unPair3 -> (done,_,_))         -> A.eq singleType done (liftInt32 0))
                  (\(unPair3 -> (done,blockId,agg)) -> do
                            previousBlock <- readArray TypeInt arrTmp blockId
                            let (status, prevAgg) = A.unpair previousBlock
                            statusIsInit      <- A.eq singleType status (liftInt32 scan_initialized)
                            statusIsExclusive <- A.eq singleType status (liftInt32 scan_exclusive_known)
                            statusIsInclusive <- A.eq singleType status (liftInt32 scan_inclusive_known)
                            let allThreadsInit      = __all_sync (liftWord32 maxBound) statusIsInit
                            let allThreadsExclusive = __all_sync (liftWord32 maxBound) statusIsExclusive
                            let allThreadsInclusvie = __all_sync (liftWord32 maxBound) statusIsInclusive
                            if (whileTp, allThreadsInit)
                              -- The previous block is only initialized, so look again from the beginning
                              then return $ pair3 done lookAtBlock (undefT tp)
                              else do
                                if (whileTp, allThreadsExclusive)
                                  -- The previous thread has an exclusive prefix. Add that exclusive prefix to our running
                                  -- prefix. If we don't have a current prefix, then set that. Also check if we can actually
                                  -- look back another block. If not, look again from the beginning
                                  then do
                                    -- Can we look back another block?
                                    if (whileTp, A.gt singleType blockId (liftInt 0))
                                      then do
                                        newAggregate <- if (tp, A.eq singleType blockId lookAtBlock)
                                                          then return prevAgg
                                                          -- TODO: Both combine ways
                                                          else app2 combine prevAgg agg
                                        prevBlock <- A.sub numType blockId (liftInt 1)
                                        return $ pair3 done prevBlock newAggregate
                                      -- Cannot look back, so reset
                                      else return $ pair3 done lookAtBlock (undefT tp)
                                  -- Not exclusive, so 2 possibilities left: inclusive or non-synced threads
                                  else do
                                    if (whileTp, allThreadsInclusvie)
                                      -- We have an inclusive prefix, add it and stop
                                      then do
                                        -- Make sure no undefined behaviour happends due to `agg` being undef
                                        newAggregate <- if (tp, A.eq singleType blockId lookAtBlock)
                                                          then return prevAgg
                                                          -- TODO: Both combine ways
                                                          else app2 combine prevAgg agg
                                        return $ pair3 (liftInt32 1) blockId newAggregate
                                      -- If threads aren't synced, reset
                                      else return $ pair3 done lookAtBlock (undefT tp)
                  )
                  (pair3 (liftInt32 0) lookAtBlock (undefT tp))
            let (_, _, aggregateToAdd) = unPair3 r
            if (tp, A.lt singleType tid (A.snd x2))
              then do
                case dir of
                  LeftToRight -> app2 combine aggregateToAdd (A.fst x2)
                  RightToLeft -> app2 combine (A.fst x2) aggregateToAdd
              else do
                return $ A.fst x2
          else return $ A.fst x2

        writeArray TypeInt arrOut j0 res
        -- If we only set an exclusive status, we now need to set the inclusive status.
        when (A.eq singleType status (liftInt32 scan_exclusive_known)) $
          when (A.eq singleType tid last) $
            writeArray TypeInt arrTmp s0 (A.pair (liftInt32 scan_inclusive_known) res)

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
    -> Operands e                                   -- ^ calling thread's input element
    -> Operands i
    -> CodeGen PTX (Operands (e, Int32))
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
    -> Operands e                                   -- ^ calling thread's input element
    -> Operands i
    -> CodeGen PTX (Operands (e, Int32))
segscanBlockShfl dir dev tp intTy combine nelem nope nflag = (warpScan >=> warpPrefix) nope
  where
    int32 :: Integral a => a -> Operands Int32
    int32 = liftInt32 . P.fromIntegral

    -- Step 1: Scan in every warp
    warpScan :: Operands e -> CodeGen PTX (Operands e)
    warpScan e = do 
      fFlag <- A.fromIntegral intTy numType nflag
      segscanWarpShfl dir dev tp combine e fFlag

    -- Step 2: Collect the aggregate results of each warp to compute the prefix
    -- values for each warp and combine with the partial result to compute each
    -- thread's final value.
    warpPrefix :: Operands e -> CodeGen PTX (Operands (e, Int32))
    warpPrefix input = do
      fFlag <- A.fromIntegral intTy numType nflag
      -- Allocate #warps elements of shared memory
      bd    <- blockDim
      warps <- A.quot integralType bd (int32 (CUDA.warpSize dev))
      
      -- Piece of shared memory to store warp aggregates
      smem  <- dynamicSharedMem tp TypeInt32 warps (liftInt32 8)

      -- Share warp aggregates
      wid   <- warpId
      lane  <- laneId
      when (A.eq singleType lane (int32 $ CUDA.warpSize dev - 1)) $ do
        writeArray TypeInt32 smem wid input
      
      -- We want to find out for each warp and block, at which index the first reset
      -- happens due to a flag. This is because after this flag, we should
      -- not incorporate the prefix into the elements. As such, create
      -- a shared array for the warp values ...
      skipWarpPrefix <- A.mul numType warps $ liftInt32 $ P.fromIntegral $ bytesElt tp
      skip <- A.add numType (liftInt32 8) skipWarpPrefix
      sflags <- dynamicSharedMem (TupRsingle scalarTypeInt32) TypeInt32 (liftInt32 0) skip

      -- ... and a piece of shared memory for the block total. 
      -- TODO: Figure out what is more performant, keeping two different shared arrays or keeping one,
      -- and then at the end min all the warp values (e.g. by using one thread) and sharing that
      blockHasFlag <- dynamicSharedMem (TupRsingle scalarTypeInt32) TypeWord32 (liftWord32 1) (liftWord32 0)

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
      when (A.gt singleType fFlag (liftInt32 0)) $ do
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptr (op integralType lane) (CrossThread, AcquireRelease)
        void . instr' $ AtomicRMW (IntegralNumType TypeInt32) NonVolatile RMW.Min ptrBlock (op integralType tid) (CrossThread, AcquireRelease)

      -- Wait for each warp to finish its atomic operations and share that info
      __syncthreads

      -- Compute the prefix value for this warp and add to the partial result.
      -- This step is not required for the first warp, which has no carry-in.
      newVal <- if (tp, A.eq singleType wid (liftInt32 0))
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
          if (tp, A.lt singleType lane sflagel)
            then do
              case dir of
                LeftToRight -> app2 combine prefix input
                RightToLeft -> app2 combine input prefix
            else 
              return input

      blockHasFlagVal <- readArray TypeInt32 blockHasFlag (liftInt32 0)
      blockHasFlag' <- A.neq singleType blockHasFlagVal (liftInt32 maxBound)
      return (A.pair newVal blockHasFlagVal)

segscanWarpShfl
    :: forall aenv e.
       Direction
    -> DeviceProperties                             -- ^ properties of the target device
    -> TypeR e
    -> IRFun2 PTX aenv (e -> e -> e)                -- ^ combination function
    -> Operands e                                   -- ^ calling thread's input element
    -> Operands Int
    -> CodeGen PTX (Operands e)
segscanWarpShfl dir dev tp combine el flag = do
  scan 0 el flag
  ---
  where
    log2 :: Double -> Double
    log2 = P.logBase 2

    -- Number of steps required to scan warp
    steps = P.floor (log2 (P.fromIntegral (CUDA.warpSize dev)))

    -- Unfold the scan as a recursive code generation function
    scan :: Int -> Operands e -> Operands Int -> CodeGen PTX (Operands e)
    scan step x f
      | step >= steps = return x
      | otherwise     = do
          let offset = 1 `P.shiftL` step

          -- share partial result through shared memory buffer
          y    <- __shfl_up tp x (liftWord32 offset)
          g    <- __shfl_up (TupRsingle scalarTypeInt) f (liftWord32 offset)
          lane <- laneId

          f' <- do 
            if ((TupRsingle scalarTypeInt), A.gte singleType lane (liftInt32 . P.fromIntegral $ offset))
                then do
                  A.add numType f g
                else
                  return f

          -- update partial result if in range
          x'   <- if (tp, A.gte singleType lane (liftInt32 . P.fromIntegral $ offset))
                    then do
                      if (tp, A.lte singleType f (liftInt 0))
                        then do
                          case dir of
                            LeftToRight -> app2 combine y x
                            RightToLeft -> app2 combine x y
                        else
                          return x

                    else
                      return x

          scan (step+1) x' f'

-- Utilities
-- ---------

i32 :: Operands Int -> CodeGen PTX (Operands Int32)
i32 = A.fromIntegral integralType numType

int :: Operands Int32 -> CodeGen PTX (Operands Int)
int = A.fromIntegral integralType numType

