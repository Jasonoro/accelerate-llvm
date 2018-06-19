{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.CodeGen.Intrinsic
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.CodeGen.Intrinsic ( )
  where

import LLVM.AST.Type.Name                                           ( Label(..) )

import Data.Array.Accelerate.LLVM.CodeGen.Intrinsic
import Data.Array.Accelerate.LLVM.PTX.Target

import Data.ByteString.Short                                        ( ShortByteString )
import Data.HashMap.Strict                                          ( HashMap )
import Data.Monoid
import qualified Data.HashMap.Strict                                as HashMap
import Prelude                                                      as P


instance Intrinsic PTX where
  intrinsicForTarget = libdeviceIndex

-- The list of functions implemented by libdevice. These are all more-or-less
-- named consistently based on the standard mathematical functions they
-- implement, with the "__nv_" prefix stripped.
--
libdeviceIndex :: HashMap ShortByteString Label
libdeviceIndex =
  let nv base   = (base, Label $ "__nv_" <> base)
  in
  HashMap.fromList $ map nv
    [ "abs"
    , "acos"
    , "acosf"
    , "acosh"
    , "acoshf"
    , "asin"
    , "asinf"
    , "asinh"
    , "asinhf"
    , "atan"
    , "atan2"
    , "atan2f"
    , "atanf"
    , "atanh"
    , "atanhf"
    , "brev"
    , "brevll"
    , "byte_perm"
    , "cbrt"
    , "cbrtf"
    , "ceil"
    , "ceilf"
    , "clz"
    , "clzll"
    , "copysign"
    , "copysignf"
    , "cos"
    , "cosf"
    , "cosh"
    , "coshf"
    , "cospi"
    , "cospif"
    , "dadd_rd"
    , "dadd_rn"
    , "dadd_ru"
    , "dadd_rz"
    , "ddiv_rd"
    , "ddiv_rn"
    , "ddiv_ru"
    , "ddiv_rz"
    , "dmul_rd"
    , "dmul_rn"
    , "dmul_ru"
    , "dmul_rz"
    , "double2float_rd"
    , "double2float_rn"
    , "double2float_ru"
    , "double2float_rz"
    , "double2hiint"
    , "double2int_rd"
    , "double2int_rn"
    , "double2int_ru"
    , "double2int_rz"
    , "double2ll_rd"
    , "double2ll_rn"
    , "double2ll_ru"
    , "double2ll_rz"
    , "double2loint"
    , "double2uint_rd"
    , "double2uint_rn"
    , "double2uint_ru"
    , "double2uint_rz"
    , "double2ull_rd"
    , "double2ull_rn"
    , "double2ull_ru"
    , "double2ull_rz"
    , "double_as_longlong"
    , "drcp_rd"
    , "drcp_rn"
    , "drcp_ru"
    , "drcp_rz"
    , "dsqrt_rd"
    , "dsqrt_rn"
    , "dsqrt_ru"
    , "dsqrt_rz"
    , "erf"
    , "erfc"
    , "erfcf"
    , "erfcinv"
    , "erfcinvf"
    , "erfcx"
    , "erfcxf"
    , "erff"
    , "erfinv"
    , "erfinvf"
    , "exp"
    , "exp10"
    , "exp10f"
    , "exp2"
    , "exp2f"
    , "expf"
    , "expm1"
    , "expm1f"
    , "fabs"
    , "fabsf"
    , "fadd_rd"
    , "fadd_rn"
    , "fadd_ru"
    , "fadd_rz"
    , "fast_cosf"
    , "fast_exp10f"
    , "fast_expf"
    , "fast_fdividef"
    , "fast_log10f"
    , "fast_log2f"
    , "fast_logf"
    , "fast_powf"
    , "fast_sincosf"
    , "fast_sinf"
    , "fast_tanf"
    , "fdim"
    , "fdimf"
    , "fdiv_rd"
    , "fdiv_rn"
    , "fdiv_ru"
    , "fdiv_rz"
    , "ffs"
    , "ffsll"
    , "finitef"
    , "float2half_rn"
    , "float2int_rd"
    , "float2int_rn"
    , "float2int_ru"
    , "float2int_rz"
    , "float2ll_rd"
    , "float2ll_rn"
    , "float2ll_ru"
    , "float2ll_rz"
    , "float2uint_rd"
    , "float2uint_rn"
    , "float2uint_ru"
    , "float2uint_rz"
    , "float2ull_rd"
    , "float2ull_rn"
    , "float2ull_ru"
    , "float2ull_rz"
    , "float_as_int"
    , "floor"
    , "floorf"
    , "fma"
    , "fma_rd"
    , "fma_rn"
    , "fma_ru"
    , "fma_rz"
    , "fmaf"
    , "fmaf_rd"
    , "fmaf_rn"
    , "fmaf_ru"
    , "fmaf_rz"
    , "fmax"
    , "fmaxf"
    , "fmin"
    , "fminf"
    , "fmod"
    , "fmodf"
    , "fmul_rd"
    , "fmul_rn"
    , "fmul_ru"
    , "fmul_rz"
    , "frcp_rd"
    , "frcp_rn"
    , "frcp_ru"
    , "frcp_rz"
    , "frexp"
    , "frexpf"
    , "frsqrt_rn"
    , "fsqrt_rd"
    , "fsqrt_rn"
    , "fsqrt_ru"
    , "fsqrt_rz"
    , "fsub_rd"
    , "fsub_rn"
    , "fsub_ru"
    , "fsub_rz"
    , "hadd"
    , "half2float"
    , "hiloint2double"
    , "hypot"
    , "hypotf"
    , "ilogb"
    , "ilogbf"
    , "int2double_rn"
    , "int2float_rd"
    , "int2float_rn"
    , "int2float_ru"
    , "int2float_rz"
    , "int_as_float"
    , "isfinited"
    , "isinfd"
    , "isinff"
    , "isnand"
    , "isnanf"
    , "j0"
    , "j0f"
    , "j1"
    , "j1f"
    , "jn"
    , "jnf"
    , "ldexp"
    , "ldexpf"
    , "lgamma"
    , "lgammaf"
    , "ll2double_rd"
    , "ll2double_rn"
    , "ll2double_ru"
    , "ll2double_rz"
    , "ll2float_rd"
    , "ll2float_rn"
    , "ll2float_ru"
    , "ll2float_rz"
    , "llabs"
    , "llmax"
    , "llmin"
    , "llrint"
    , "llrintf"
    , "llround"
    , "llroundf"
    , "log"
    , "log10"
    , "log10f"
    , "log1p"
    , "log1pf"
    , "log2"
    , "log2f"
    , "logb"
    , "logbf"
    , "logf"
    , "longlong_as_double"
    , "max"
    , "min"
    , "modf"
    , "modff"
    , "mul24"
    , "mul64hi"
    , "mulhi"
    , "nan"
    , "nanf"
    , "nearbyint"
    , "nearbyintf"
    , "nextafter"
    , "nextafterf"
    , "normcdf"
    , "normcdff"
    , "normcdfinv"
    , "normcdfinvf"
    , "popc"
    , "popcll"
    , "pow"
    , "powf"
    , "powi"
    , "powif"
    , "rcbrt"
    , "rcbrtf"
    , "remainder"
    , "remainderf"
    , "remquo"
    , "remquof"
    , "rhadd"
    , "rint"
    , "rintf"
    , "round"
    , "roundf"
    , "rsqrt"
    , "rsqrtf"
    , "sad"
    , "saturatef"
    , "scalbn"
    , "scalbnf"
    , "signbitd"
    , "signbitf"
    , "sin"
    , "sincos"
    , "sincosf"
    , "sincospi"
    , "sincospif"
    , "sinf"
    , "sinh"
    , "sinhf"
    , "sinpi"
    , "sinpif"
    , "sqrt"
    , "sqrtf"
    , "tan"
    , "tanf"
    , "tanh"
    , "tanhf"
    , "tgamma"
    , "tgammaf"
    , "trunc"
    , "truncf"
    , "uhadd"
    , "uint2double_rn"
    , "uint2float_rd"
    , "uint2float_rn"
    , "uint2float_ru"
    , "uint2float_rz"
    , "ull2double_rd"
    , "ull2double_rn"
    , "ull2double_ru"
    , "ull2double_rz"
    , "ull2float_rd"
    , "ull2float_rn"
    , "ull2float_ru"
    , "ull2float_rz"
    , "ullmax"
    , "ullmin"
    , "umax"
    , "umin"
    , "umul24"
    , "umul64hi"
    , "umulhi"
    , "urhadd"
    , "usad"
    , "y0"
    , "y0f"
    , "y1"
    , "y1f"
    , "yn"
    , "ynf"
    ]

