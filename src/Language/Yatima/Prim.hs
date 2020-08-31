module Language.Yatima.Prim where

import           Prelude                    hiding (floor)
import           Data.Text                  (Text)
import qualified Data.Text                  as T hiding (find)
import           Data.Word
import           Data.Int
import           Data.Bits
import           Numeric.Extras
import           Numeric.IEEE
import           GHC.Float

import           Language.Yatima.IEEE754

-- These are the WASM numeric operators for i64 and f64.
-- https://webassembly.github.io/spec/core/appendix/index-instructions.html#index-instr
data Prim
  = I64_const
  | F64_const
  | I64_eqz
  | I64_eq
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
  | I64_clz
  | I64_ctz
  | I64_popcnt
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
  | F64_abs
  | F64_neg
  | F64_ceil
  | F64_floor
  | F64_trunc
  | F64_nearest
  | F64_sqrt
  | F64_add
  | F64_sub
  | F64_mul
  | F64_div
  | F64_min
  | F64_max
  | F64_copysign
  | I64_trunc_f64_s
  | I64_trunc_f64_u
  | F64_convert_i64_s
  | F64_convert_i64_u
  | I64_reinterpret_f64
  | F64_reinterpret_i64
  deriving (Eq, Show, Ord, Enum)


prettyPrim :: Prim -> Text
prettyPrim op = case op of
  I64_const           -> "iconst"
  F64_const           -> "fconst"
  I64_eqz             -> "ieqz"
  I64_eq              -> "ieq"
  I64_ne              -> "ine"
  I64_lt_s            -> "ilt_s"
  I64_lt_u            -> "ilt_u"
  I64_gt_s            -> "igt_s"
  I64_gt_u            -> "igt_u"
  I64_le_s            -> "ile_s"
  I64_le_u            -> "ile_u"
  I64_ge_s            -> "ige_s"
  I64_ge_u            -> "ige_u"
  F64_eq              -> "feq"
  F64_ne              -> "fne"
  F64_lt              -> "flt"
  F64_gt              -> "fgt"
  F64_le              -> "fle"
  F64_ge              -> "fge"
  I64_clz             -> "iclz"
  I64_ctz             -> "ictz"
  I64_popcnt          -> "ipopcnt"
  I64_add             -> "iadd"
  I64_sub             -> "isub"
  I64_mul             -> "imul"
  I64_div_s           -> "idiv_s"
  I64_div_u           -> "idiv_u"
  I64_rem_s           -> "irem_s"
  I64_rem_u           -> "irem_u"
  I64_and             -> "iand"
  I64_or              -> "ior"
  I64_xor             -> "ixor"
  I64_shl             -> "ishl"
  I64_shr_s           -> "ishr_s"
  I64_shr_u           -> "ishr_u"
  I64_rotl            -> "irotl"
  I64_rotr            -> "irotr"
  F64_abs             -> "fabs"
  F64_neg             -> "fneg"
  F64_ceil            -> "fceil"
  F64_floor           -> "ffloor"
  F64_trunc           -> "ftrunc"
  F64_nearest         -> "fnearest"
  F64_sqrt            -> "fsqrt"
  F64_add             -> "fadd"
  F64_sub             -> "fsub"
  F64_mul             -> "fmul"
  F64_div             -> "fdiv"
  F64_min             -> "fmin"
  F64_max             -> "fmax"
  F64_copysign        -> "fcopysign"
  I64_trunc_f64_s     -> "itrunc_s"
  I64_trunc_f64_u     -> "itrunc_u"
  F64_convert_i64_s   -> "fconvert_s"
  F64_convert_i64_u   -> "fconvert_u"
  I64_reinterpret_f64 -> "ireinterpret"
  F64_reinterpret_i64 -> "freinterpret"

data PrimNum = W Word64 | D Double deriving Show

ite :: Bool -> Word64
ite c = if c then 1 else 0

-- We extend the definition of integer division pointwise to set division by
-- zero equal to zero. This is done to minimize runtime erroring in primitive
-- arithmetic operations.
div' :: Integral a => a -> a -> a
div' a 0 = 0
div' a b = a `div` b

rem' :: Integral a => a -> a -> a
rem' a 0 = 0
rem' a b = a `rem` b

op :: Prim -> PrimNum -> PrimNum -> Maybe PrimNum
op p x y = case (p, x, y) of
  (I64_const,           W a, W b) -> jW a
  (F64_const,           D a, D b) -> jD b
  (I64_eqz,             W a, W b) -> jW $ ite $ b == 0
  (I64_eq,              W a, W b) -> jW $ ite $ a == b
  (I64_ne,              W a, W b) -> jW $ ite $ a /= b
  (I64_lt_s,            W a, W b) -> jW $ ite $ (w2i a) < (w2i b)
  (I64_lt_u,            W a, W b) -> jW $ ite $ a <  b
  (I64_gt_s,            W a, W b) -> jW $ ite $ (w2i a) > (w2i b)
  (I64_gt_u,            W a, W b) -> jW $ ite $ a >  b
  (I64_le_s,            W a, W b) -> jW $ ite $ (w2i a) <= (w2i b)
  (I64_le_u,            W a, W b) -> jW $ ite $ a <= b
  (I64_ge_s,            W a, W b) -> jW $ ite $ (w2i a) >= (w2i b)
  (I64_ge_u,            W a, W b) -> jW $ ite $ a >= b
  (F64_eq,              D a, D b) -> jW $ ite $ a == b
  (F64_ne,              D a, D b) -> jW $ ite (isNaN a || isNaN b || a /= b)
  (F64_lt,              D a, D b) -> jW $ ite $ a <  b
  (F64_gt,              D a, D b) -> jW $ ite $ a >  b
  (F64_le,              D a, D b) -> jW $ ite $ a <= b
  (F64_ge,              D a, D b) -> jW $ ite $ a >= b
  (I64_clz,             W a, W b) -> jW $ fromIntegral $ countLeadingZeros b
  (I64_ctz,             W a, W b) -> jW $ fromIntegral $ countTrailingZeros b
  (I64_popcnt,          W a, W b) -> jW $ fromIntegral $ popCount b
  (I64_add,             W a, W b) -> jW $ a + b
  (I64_sub,             W a, W b) -> jW $ a - b
  (I64_mul,             W a, W b) -> jW $ a * b
  (I64_div_s,           W a, W b) -> jW $ fromIntegral $ (w2i a) `div'` (w2i b)
  (I64_div_u,           W a, W b) -> jW $ a `div'` b
  (I64_rem_s,           W a, W b) -> jW $ fromIntegral $ (w2i a) `rem'` (w2i b)
  (I64_rem_u,           W a, W b) -> jW $ a `rem'` b
  (I64_and,             W a, W b) -> jW $ a .&. b
  (I64_or,              W a, W b) -> jW $ a .|. b
  (I64_xor,             W a, W b) -> jW $ a `xor` b
  (I64_shl,             W a, W b) -> jW $ shiftL b (fromIntegral a)
  (I64_shr_s,           W a, W b) -> jW $ i2w $ shiftR (w2i b) (fromIntegral a)
  (I64_shr_u,           W a, W b) -> jW $ shiftR b (fromIntegral a)
  (I64_rotl,            W a, W b) -> jW $ rotateL b (fromIntegral a)
  (I64_rotr,            W a, W b) -> jW $ rotateR b (fromIntegral a)
  (F64_abs,             D a, D b) -> jD $ abs b
  (F64_neg,             D a, D b) -> jD $ negate b
  (F64_ceil,            D a, D b) -> jD $ ceil b
  (F64_floor,           D a, D b) -> jD $ floor b
  (F64_trunc,           D a, D b) -> jD $ trunc b
  (F64_nearest,         D a, D b) -> jD $ int2Double $ round b
  (F64_sqrt,            D a, D b) -> jD $ sqrt b
  (F64_add,             D a, D b) -> jD $ a + b
  (F64_sub,             D a, D b) -> jD $ a - b
  (F64_mul,             D a, D b) -> jD $ a * b
  (F64_div,             D a, D b) -> jD $ a / b
  (F64_min,             D a, D b) -> jD $ minNum a b
  (F64_max,             D a, D b) -> jD $ maxNum a b
  (F64_copysign,        D a, D b) -> jD $ copySign a b
  (I64_trunc_f64_s,     D a, D b) -> jW $ fromIntegral $ double2Int $ trunc b
  (I64_trunc_f64_u,     D a, D b) -> jW $ fromIntegral $ double2Int $ trunc b
  (F64_convert_i64_s,   D a, D b) -> jD $ negate b
  (F64_convert_i64_u,   D a, D b) -> jD $ negate b
  (I64_reinterpret_f64, D a, D b) -> jW $ ftou b
  (F64_reinterpret_i64, W a, W b) -> jD $ utof b
  _                               -> Nothing
  where
    w2i :: Word64 -> Int64
    w2i = fromIntegral

    i2w :: Int64 -> Word64
    i2w = fromIntegral

    jW = Just . W
    jD = Just . D

primNames :: [Text]
primNames =
  [ "iconst", "fconst", "ieqz", "ieq", "ine", "ilt_s", "ilt_u", "igt_s"
  , "igt_u", "ile_s", "ile_u", "ige_s", "ige_u", "feq", "fne", "flt", "fgt"
  , "fle", "fge", "iclz", "ictz", "ipopcnt", "iadd", "isub", "imul", "idiv_s"
  , "idiv_u", "irem_s", "irem_u", "iand", "ior", "ixor", "ishl", "ishr_s"
  , "ishr_u", "irotl", "irotr", "fabs", "fneg", "fceil", "ffloor", "ftrunc"
  , "fnearest", "fsqrt", "fadd", "fsub", "fmul", "fdiv", "fmin", "fmax"
  , "fcopysign", "itrunc_s", "itrunc_u", "fconvert_s", "fconvert_u"
  , "ireinterpret", "freinterpret"
  ]

--data PrimOpType = WW | DD | WD | DW

--opType :: Prim -> PrimOpType
--opType p = case p of
--  I64_const -> WW
--  F64_const -> DD
--  I64_eqz   -> WW
--  I64_eq    -> WW
--  I64_ne    -> WW
--  I64_lt_s  -> WW
--  I64_lt_u  -> WW
--  I64_gt_s  -> WW
--  I64_gt_u  -> WW
--  I64_le_s  -> WW
--  I64_le_u  -> WW
--  I64_ge_s  -> WW
--  I64_ge_u  -> WW
--  F64_eq    -> DD
--  F64_ne    -> DD
--  F64_lt    -> DD
--  F64_gt    -> DD
--  F64_le    -> DD
--  F64_ge    -> DD
--  I64_clz   -> WW
--  I64_ctz   -> WW
--  I64_popcnt -> WW
--  I64_add    -> WW
--  I64_sub    -> WW
--  I64_mul    -> WW
--  I64_div_s  -> WW
--  I64_div_u  -> WW
--  I64_rem_s  -> WW
--  I64_rem_u  -> WW
--  I64_and    -> WW
--  I64_or     -> WW
--  I64_xor    -> WW
--  I64_shl    -> WW
--  I64_shr_s  -> WW
--  I64_shr_u  -> WW
--  I64_rotl   -> WW
--  I64_rotr   -> WW
--  F64_abs    -> DD
--  F64_neg    -> DD
--  F64_ceil   -> DD
--  F64_floor  -> DD
--  F64_trunc  -> DD
--  F64_nearest -> DD
--  F64_sqrt    -> DD
--  F64_add     -> DD
--  F64_sub     -> DD
--  F64_mul     -> DD
--  F64_div     -> DD
--  F64_min     -> DD
--  F64_max      -> DD
--  F64_copysign  -> DD
--  I64_trunc_f64_s -> DD
--  I64_trunc_f64_u
--  F64_convert_i64_s
--  F64_convert_i64_u
--  I64_reinterpret_f64
--  F64_reinterpret_i64
