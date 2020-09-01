{-# LANGUAGE DataKinds #-}
module Language.Yatima.Prim where

import           Prelude                    hiding (floor)
import           Data.Text                  (Text)
import qualified Data.Text                  as T hiding (find)
import           Data.Word
import           Data.Int
import           Data.Bits
import           Data.List
import           Data.Maybe
import           Numeric.Extras
import           Numeric.IEEE
import           GHC.Float

import           Control.Monad.Except
import           Control.Monad

import           Language.Yatima.IEEE754
import qualified Language.Yatima.WASM as WASM
import           Language.Yatima.WASM (asWord64, asInt64)

-- These are the WASM numeric operators for i64 and f64.
-- https://webassembly.github.io/spec/core/appendix/index-instructions.html#index-instr
data Prim1
  = I64_eqz
  | I64_clz
  | I64_ctz
  | I64_popcnt
  | F64_abs
  | F64_neg
  | F64_ceil
  | F64_floor
  | F64_trunc
  | F64_nearest
  | F64_sqrt
  | I64_trunc_f64_s
  | I64_trunc_f64_u
  | F64_convert_i64_s
  | F64_convert_i64_u
  | I64_reinterpret_f64
  | F64_reinterpret_i64
  deriving (Eq, Show)

data Prim2
  = I64_eq
  | I64_ne
  | I64_lt_s
  | I64_lt_u
  | I64_gt_s
  | I64_gt_u
  | I64_le_s
  | I64_le_u
  | I64_ge_s
  | I64_ge_u
  | F64_eq
  | F64_ne
  | F64_lt
  | F64_gt
  | F64_le
  | F64_ge
  | I64_add
  | I64_sub
  | I64_mul
  | I64_div_s
  | I64_div_u
  | I64_rem_s
  | I64_rem_u
  | I64_and
  | I64_or
  | I64_xor
  | I64_shl
  | I64_shr_s
  | I64_shr_u
  | I64_rotl
  | I64_rotr
  | F64_add
  | F64_sub
  | F64_mul
  | F64_div
  | F64_min
  | F64_max
  | F64_copysign
  deriving (Eq, Show)

data PrimType
  = IUna  -- i64 -> i64
  | IRel  -- i64 -> i64 -> i64
  | IBin  -- i64 -> i64 -> i64
  | FUna  -- f64 -> f64
  | FRel  -- f64 -> f64 -> i64
  | FBin  -- f64 -> f64 -> f64
  | ICnv  -- f64 -> i64
  | FCnv  -- i64 -> f64
  deriving (Eq, Show)

prim1s :: [(Prim1,PrimType,Int,Text)]
prim1s =
  [ ( I64_eqz             , IUna, 0x50, "ieqz"         )
  , ( I64_clz             , IUna, 0x79, "iclz"         )
  , ( I64_ctz             , IUna, 0x7A, "ictz"         )
  , ( I64_popcnt          , IUna, 0x7B, "ipopcnt"      )
  , ( F64_abs             , FUna, 0x99, "fabs"         )
  , ( F64_neg             , FUna, 0x9A, "fneg"         )
  , ( F64_ceil            , FUna, 0x9B, "fceil"        )
  , ( F64_floor           , FUna, 0x9C, "ffloor"       )
  , ( F64_trunc           , FUna, 0x9D, "ftrunc"       )
  , ( F64_nearest         , FUna, 0x9E, "fnearest"     )
  , ( F64_sqrt            , FUna, 0x9F, "fsqrt"        )
  , ( I64_trunc_f64_s     , ICnv, 0xB0, "itrunc_s"     )
  , ( I64_trunc_f64_u     , ICnv, 0xB1, "itrunc_u"     )
  , ( F64_convert_i64_s   , FCnv, 0xB4, "fconvert_s"   )
  , ( F64_convert_i64_u   , FCnv, 0xB5, "fconvert_u"   )
  , ( I64_reinterpret_f64 , ICnv, 0xBD, "ireinterpret" )
  , ( F64_reinterpret_i64 , FCnv, 0xBF, "freinterpret" )
  ]

prim2s :: [(Prim2,PrimType,Int, Text)]
prim2s =
  [ ( I64_eq              , IRel, 0x51, "ieq"          )
  , ( I64_ne              , IRel, 0x52, "ine"          )
  , ( I64_lt_s            , IRel, 0x53, "ilt_s"        )
  , ( I64_lt_u            , IRel, 0x54, "ilt_u"        )
  , ( I64_gt_s            , IRel, 0x55, "igt_s"        )
  , ( I64_gt_u            , IRel, 0x56, "igt_u"        )
  , ( I64_le_s            , IRel, 0x57, "ile_s"        )
  , ( I64_le_u            , IRel, 0x58, "ile_u"        )
  , ( I64_ge_s            , IRel, 0x59, "ige_s"        )
  , ( I64_ge_u            , IRel, 0x5A, "ige_u"        )
  , ( F64_eq              , FRel, 0x61, "feq"          )
  , ( F64_ne              , FRel, 0x62, "fne"          )
  , ( F64_lt              , FRel, 0x63, "flt"          )
  , ( F64_gt              , FRel, 0x64, "fgt"          )
  , ( F64_le              , FRel, 0x65, "fle"          )
  , ( F64_ge              , FRel, 0x66, "fge"          )
  , ( I64_add             , IBin, 0x7C, "iadd"         )
  , ( I64_sub             , IBin, 0x7D, "isub"         )
  , ( I64_mul             , IBin, 0x7E, "imul"         )
  , ( I64_div_s           , IBin, 0x7F, "idiv_s"       )
  , ( I64_div_u           , IBin, 0x80, "idiv_u"       )
  , ( I64_rem_s           , IBin, 0x81, "irem_s"       )
  , ( I64_rem_u           , IBin, 0x82, "irem_u"       )
  , ( I64_and             , IBin, 0x83, "iand"         )
  , ( I64_or              , IBin, 0x85, "ior"          )
  , ( I64_xor             , IBin, 0x86, "ixor"         )
  , ( I64_shl             , IBin, 0x87, "ishl"         )
  , ( I64_shr_s           , IBin, 0x88, "ishr_s"       )
  , ( I64_shr_u           , IBin, 0x89, "ishr_u"       )
  , ( I64_rotl            , IBin, 0x8A, "irotl"        )
  , ( I64_rotr            , IBin, 0x8B, "irotr"        )
  , ( F64_add             , FBin, 0xA0, "fadd"         )
  , ( F64_sub             , FBin, 0xA1, "fsub"         )
  , ( F64_mul             , FBin, 0xA2, "fmul"         )
  , ( F64_div             , FBin, 0xA3, "fdiv"         )
  , ( F64_min             , FBin, 0xA4, "fmin"         )
  , ( F64_max             , FBin, 0xA5, "fmax"         )
  , ( F64_copysign        , FBin, 0xA6, "fcopysign"    )
  ]

instance Enum Prim1 where
  toEnum    i = (\(w,x,y,z) -> w) $ fromJust $ find (\(w,x,y,z) -> y == i) prim1s
  fromEnum  p = (\(w,x,y,z) -> y) $ fromJust $ find (\(w,x,y,z) -> w == p) prim1s

instance Enum Prim2 where
  toEnum    i = (\(w,x,y,z) -> w) $ fromJust $ find (\(w,x,y,z) -> y == i) prim2s
  fromEnum  p = (\(w,x,y,z) -> y) $ fromJust $ find (\(w,x,y,z) -> w == p) prim2s

prim1Type :: Prim1 -> PrimType
prim1Type op = (\(w,x,y,z) -> x) $ fromJust $ find (\(w,x,y,z) -> w == op) prim1s

prim2Type :: Prim2 -> PrimType
prim2Type op = (\(w,x,y,z) -> x) $ fromJust $ find (\(w,x,y,z) -> w == op) prim2s

prim1Name :: Prim1 -> Text
prim1Name op = (\(w,x,y,z) -> z) $ fromJust $ find (\(w,x,y,z) -> w == op) prim1s

prim2Name :: Prim2 -> Text
prim2Name op = (\(w,x,y,z) -> z) $ fromJust $ find (\(w,x,y,z) -> w == op) prim2s

prim1Names :: [Text]
prim1Names = (\(w,x,y,z) -> z) <$> prim1s

prim2Names :: [Text]
prim2Names = (\(w,x,y,z) -> z) <$> prim2s

data PrimErr
  = WASMFloatTrap Double
  | WASMDivTrap Word64 Word64

ite :: Bool -> Word64
ite c = if c then 1 else 0

opIUna :: Prim1 -> Word64 -> Word64
opIUna op x = case op of
  I64_eqz    -> ite $ x == 0
  I64_clz    -> fromIntegral $ countLeadingZeros x
  I64_ctz    -> fromIntegral $ countTrailingZeros x
  I64_popcnt -> fromIntegral $ popCount x

opFCnv :: Prim1 -> Word64 -> Double
opFCnv op x = case op of
  F64_convert_i64_s   -> realToFrac $ asInt64 x
  F64_convert_i64_u   -> realToFrac x
  F64_reinterpret_i64 -> utof x

opICnv :: Prim1 -> Double -> Except PrimErr Word64
opICnv op x = case op of
  I64_trunc_f64_s       -> do
    when (isNaN x || isInfinite x || x >= 2^63 || x < -2^63)
      (throwError $ WASMFloatTrap x)
    return (asWord64 $ truncate x)
  I64_trunc_f64_u       -> do
    when (isNaN x || isInfinite x || x >= 2^64 || x <= -1)
      (throwError $ WASMFloatTrap x)
    return (truncate x)
  I64_reinterpret_f64   -> return $ ftou x

opIRel :: Prim2 -> Word64 -> Word64 -> Word64
opIRel op a b = case op of
  I64_eq    -> ite $ a == b
  I64_ne    -> ite $ a /= b
  I64_lt_s  -> ite $ (asInt64 a) < (asInt64 b)
  I64_lt_u  -> ite $ a <  b
  I64_gt_s  -> ite $ (asInt64 a) > (asInt64 b)
  I64_gt_u  -> ite $ a >  b
  I64_le_s  -> ite $ (asInt64 a) <= (asInt64 b)
  I64_le_u  -> ite $ a <= b
  I64_ge_s  -> ite $ (asInt64 a) >= (asInt64 b)
  I64_ge_u  -> ite $ a >= b

opIBin :: Prim2 -> Word64 -> Word64 -> Except PrimErr Word64
opIBin op a b = case op of
  I64_add   -> return $ a + b
  I64_sub   -> return $ a - b
  I64_mul   -> return $ a * b
  I64_div_s -> do
    when (b == 0 || (a == 0x8000000000000000 && b == 0xFFFFFFFFFFFFFFFF))
       (throwError $ WASMDivTrap a b)
    return $ (asWord64 $ asInt64 a `quot` asInt64 b)
  I64_div_u -> do
    when (b == 0) (throwError $ WASMDivTrap a b)
    return (a `quot` b)
  I64_rem_s -> do
    when (b == 0) (throwError $ WASMDivTrap a b)
    return (asWord64 $ asInt64 a `rem` asInt64 b)
  I64_rem_u -> do
    when (b == 0) (throwError $ WASMDivTrap a b)
    return (a `rem` b)
  I64_and   -> return $ a .&. b
  I64_or    -> return $ a .|. b
  I64_xor   -> return $ a `xor` b
  I64_shl   -> return $ shiftL a (fromIntegral (b `rem` 64))
  I64_shr_s ->
    return $ (asWord64 $ asInt64 a `shiftR` (fromIntegral (b `rem` 64)))
  I64_shr_u -> return $ shiftL a (fromIntegral (b `rem` 64))
  I64_rotl  -> return $ rotateL a (fromIntegral b)
  I64_rotr  -> return $ rotateR a (fromIntegral b)

opFRel :: Prim2 -> Double -> Double -> Word64
opFRel op a b = case op of
  F64_eq -> ite $ a == b
  F64_ne -> ite $ a /= b
  F64_lt -> ite $ a <  b
  F64_gt -> ite $ a >  b
  F64_le -> ite $ a <= b
  F64_ge -> ite $ a >= b

opFUna :: Prim1 -> Double -> Double
opFUna p a = case p of
  F64_abs            -> abs a
  F64_neg            -> negate a
  F64_ceil           -> WASM.doubleCeil a
  F64_floor          -> WASM.doubleFloor a
  F64_trunc          -> WASM.doubleTrunc a
  F64_nearest        -> WASM.nearest a
  F64_sqrt           -> sqrt a

opFBin :: Prim2 -> Double -> Double -> Double
opFBin p a b = case p of
  F64_add            -> a + b
  F64_sub            -> a - b
  F64_mul            -> a * b
  F64_div            -> a / b
  F64_min            -> WASM.zeroAwareMin a b
  F64_max            -> WASM.zeroAwareMax a b
  F64_copysign       -> copySign a b

