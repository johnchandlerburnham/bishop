module Language.Yatima.Prim where

import           Data.Text                  (Text)
import qualified Data.Text                  as T hiding (find)

-- These are the WASM numeric operators for i64 and f64.
-- https://webassembly.github.io/spec/core/appendix/index-instructions.html#index-instr
data Prim
  = Op_i64_const
  | Op_f64_const
  | Op_i64_eqz
  | Op_i64_eq
  | Op_i64_ne
  | Op_i64_lt_s
  | Op_i64_lt_u
  | Op_i64_gt_s
  | Op_i64_gt_u
  | Op_i64_le_s
  | Op_i64_le_u
  | Op_i64_ge_s
  | Op_i64_ge_u
  | Op_f64_eq
  | Op_f64_ne
  | Op_f64_lt
  | Op_f64_gt
  | Op_f64_le
  | Op_f64_ge
  | Op_i64_clz
  | Op_i64_ctz
  | Op_i64_popcnt
  | Op_i64_add
  | Op_i64_sub
  | Op_i64_mul
  | Op_i64_div_s
  | Op_i64_div_u
  | Op_i64_rem_s
  | Op_i64_rem_u
  | Op_i64_and
  | Op_i64_or
  | Op_i64_xor
  | Op_i64_shl
  | Op_i64_shr_s
  | Op_i64_shr_u
  | Op_i64_rotl
  | Op_i64_rotr
  | Op_f64_abs
  | Op_f64_neg
  | Op_f64_ceil
  | Op_f64_floor
  | Op_f64_trunc
  | Op_f64_nearest
  | Op_f64_sqrt
  | Op_f64_add
  | Op_f64_sub
  | Op_f64_mul
  | Op_f64_div
  | Op_f64_min
  | Op_f64_max
  | Op_f64_copysign
  | Op_i64_trunc_f64_s
  | Op_i64_trunc_f64_u
  | Op_f64_convert_i64_s
  | Op_f64_convert_i64_u
  | Op_i64_reinterpret_f64
  | Op_f64_reinterpret_i64
  | Op_i64_extend8_s
  | Op_i64_extend16_s
  | Op_i64_extend32_s
  | Op_i64_trunc_sat_f64_s
  | Op_i64_trunc_sat_f64_u
  deriving (Eq, Show, Ord, Enum)


prettyPrim :: Prim -> Text
prettyPrim op = case op of
  Op_i64_const           -> "iconst"
  Op_f64_const           -> "fconst"
  Op_i64_eqz             -> "ieqz"
  Op_i64_eq              -> "ieq"
  Op_i64_ne              -> "ine"
  Op_i64_lt_s            -> "ilt_s"
  Op_i64_lt_u            -> "ilt_u"
  Op_i64_gt_s            -> "igt_s"
  Op_i64_gt_u            -> "igt_u"
  Op_i64_le_s            -> "ile_s"
  Op_i64_le_u            -> "ile_u"
  Op_i64_ge_s            -> "ige_s"
  Op_i64_ge_u            -> "ige_u"
  Op_f64_eq              -> "feq"
  Op_f64_ne              -> "fne"
  Op_f64_lt              -> "flt"
  Op_f64_gt              -> "fgt"
  Op_f64_le              -> "fle"
  Op_f64_ge              -> "fge"
  Op_i64_clz             -> "iclz"
  Op_i64_ctz             -> "ictz"
  Op_i64_popcnt          -> "ipopcnt"
  Op_i64_add             -> "iadd"
  Op_i64_sub             -> "isub"
  Op_i64_mul             -> "imul"
  Op_i64_div_s           -> "idiv_s"
  Op_i64_div_u           -> "idiv_u"
  Op_i64_rem_s           -> "irem_s"
  Op_i64_rem_u           -> "irem_u"
  Op_i64_and             -> "iand"
  Op_i64_or              -> "ior"
  Op_i64_xor             -> "ixor"
  Op_i64_shl             -> "ishl"
  Op_i64_shr_s           -> "ishr_s"
  Op_i64_shr_u           -> "ishr_u"
  Op_i64_rotl            -> "irotl"
  Op_i64_rotr            -> "irotr"
  Op_f64_abs             -> "fabs"
  Op_f64_neg             -> "fneg"
  Op_f64_ceil            -> "fceil"
  Op_f64_floor           -> "ffloor"
  Op_f64_trunc           -> "ftrunc"
  Op_f64_nearest         -> "fnearest"
  Op_f64_sqrt            -> "fsqrt"
  Op_f64_add             -> "fadd"
  Op_f64_sub             -> "fsub"
  Op_f64_mul             -> "fmul"
  Op_f64_div             -> "fdiv"
  Op_f64_min             -> "fmin"
  Op_f64_max             -> "fmax"
  Op_f64_copysign        -> "fcopysign"
  Op_i64_trunc_f64_s     -> "itrunc_s"
  Op_i64_trunc_f64_u     -> "itrunc_u"
  Op_f64_convert_i64_s   -> "fconvert_s"
  Op_f64_convert_i64_u   -> "fconvert_u"
  Op_i64_reinterpret_f64 -> "ireinterpret"
  Op_f64_reinterpret_i64 -> "freinterpret"
  Op_i64_extend8_s       -> "iextend8"
  Op_i64_extend16_s      -> "iextend16"
  Op_i64_extend32_s      -> "iextend32"
  Op_i64_trunc_sat_f64_s -> "itrunc_sat_s"
  Op_i64_trunc_sat_f64_u -> "itrunc_sat_u"


---- A general principle with `op` is that we should avoid making the
---- implementation (in this case Haskell) runtime error. i.e. all the primitive
---- Formality operations should be total and we should rely on type-safe
---- user-level librarys for partial functions like division. DIV is not division,
---- it is division extended with the points DIV(x,0) = 0.
----
---- See https://www.hillelwayne.com/post/divide-by-zero/ for further discussion
---- of whether this choice is reasonable
--
---- TODO: Find and eliminate other possible runtime errors in this function
--
----op :: Op -> FNum -> FNum -> Term
----op op a b
----  | ADD  <- op, W a <- a, W b <- b = U64 $ a + b
----  | ADD  <- op, D a <- a, D b <- b = F64 $ a + b
----  | SUB  <- op, W a <- a, W b <- b = U64 $ a - b
----  | SUB  <- op, D a <- a, D b <- b = F64 $ a - b
----  | MUL  <- op, W a <- a, W b <- b = U64 $ a * b
----  | MUL  <- op, D a <- a, D b <- b = F64 $ a * b
----  | DIV  <- op, W a <- a, W 0 <- b = U64 $ 0
----  | DIV  <- op, W a <- a, W b <- b = U64 $ a `div` b
----  | DIV  <- op, D a <- a, D b <- b = F64 $ a / b
----  | MOD  <- op, W a <- a, W b <- b = U64 $ a `mod` b
----  | MOD  <- op, D a <- a, D b <- b = F64 $ a `fmod` b
----  | EQL  <- op, W a <- a, W b <- b = U64 $ if a == b then 1 else 0
----  | EQL  <- op, D a <- a, D b <- b = U64 $ if a == b then 1 else 0
----  | GTH  <- op, W a <- a, W b <- b = U64 $ if a > b  then 1 else 0
----  | GTH  <- op, D a <- a, D b <- b = U64 $ if a > b  then 1 else 0
----  | LTH  <- op, W a <- a, W b <- b = U64 $ if a < b  then 1 else 0
----  | LTH  <- op, D a <- a, D b <- b = U64 $ if a < b  then 1 else 0
----  | MIN  <- op, W a <- a, W b <- b = U64 $ a `min` b
----  | MIN  <- op, D a <- a, D b <- b = F64 $ a `minNaN` b
----  | MAX  <- op, W a <- a, W b <- b = U64 $ a `max` b
----  | MAX  <- op, D a <- a, D b <- b = F64 $ a `maxNaN` b
----  | POW  <- op, W a <- a, W b <- b = U64 $ a ^ b
----  | POW  <- op, D a <- a, D b <- b = F64 $ a ** b
----  | AND  <- op, W a <- a, W b <- b = U64 $ a .&. b
----  | BOR  <- op, W a <- a, W b <- b = U64 $ a .|. b
----  | XOR  <- op, W a <- a, W b <- b = U64 $ a `xor` b
----  | NOT  <- op, W b <- b           = U64 $ complement b
----  | SHR  <- op, W a <- a, W b <- b = U64 $ Bits.shiftR b (fromIntegral a)
----  | SHL  <- op, W a <- a, W b <- b = U64 $ Bits.shiftL b (fromIntegral a)
----  | ROR  <- op, W a <- a, W b <- b = U64 $ Bits.rotateR b (fromIntegral a)
----  | ROL  <- op, W a <- a, W b <- b = U64 $ Bits.rotateL b (fromIntegral a)
----  | CLZ  <- op, W b <- b           = U64 $ cst $ Bits.countLeadingZeros b
----  | CTZ  <- op, W b <- b           = U64 $ cst $ Bits.countTrailingZeros b
----  | CNT  <- op, W b <- b           = U64 $ cst $ Bits.popCount b
----  | SQRT <- op, D b <- b           = F64 $ sqrt b
----  | NAN  <- op, D b <- b           = U64 $ if isNaN b then 1 else 0
----  | INF  <- op, D b <- b           = U64 $ if isInfinite b then 1 else 0
----  | COPY <- op, D a <- a, D b <- b = F64 $ copySign a b
----  | EXP  <- op, D b <- b           = F64 $ exp b
----  | EXPM <- op, D b <- b           = F64 $ expm1 b
----  | LOGB <- op, D a <- a, D b <- b = F64 $ logBase a b
----  | LOGP <- op, D b <- b           = F64 $ log1p b
----  | SIN  <- op, D b <- b           = F64 $ sin b
----  | COS  <- op, D b <- b           = F64 $ cos b
----  | TAN  <- op, D b <- b           = F64 $ tan b
----  | ASIN <- op, D b <- b           = F64 $ asin b
----  | ACOS <- op, D b <- b           = F64 $ acos b
----  | ATAN <- op, D b <- b           = F64 $ atan b
----  | SINH <- op, D b <- b           = F64 $ sinh b
----  | COSH <- op, D b <- b           = F64 $ cosh b
----  | TANH <- op, D b <- b           = F64 $ tanh b
----  | ASNH <- op, D b <- b           = F64 $ asinh b
----  | ACSH <- op, D b <- b           = F64 $ acosh b
----  | ATNH <- op, D b <- b           = F64 $ atanh b
----  | CBRT <- op, D b <- b           = F64 $ cbrt b
----  | HYPT <- op, D a <- a, D b <- b = F64 $ hypot a b
----  | ERF  <- op, D b <- b           = F64 $ erf b
----  | NRST <- op, D b <- b           = U64 $ round b
----  | CEIL <- op, D b <- b           = F64 $ ceil b
----  | FLOR <- op, D b <- b           = F64 $ floor b
----  | TRNC <- op, D b <- b           = F64 $ trunc b
----  | CONV <- op, W b <- b           = F64 $ fromIntegral b
----  | UTOF <- op, W b <- b           = F64 $ utof b
----  | FTOU <- op, D b <- b           = U64 $ ftou b
----  | otherwise = error $ "UndefinedArithmetic Op"
----    -- the only error op should raise is when there's an (OP, FNum, FNum)
----    -- combination outside of this set. This is a language implementation error
----    -- and should be impossible to generate from user-space
----  where
----    cst = fromIntegral
----
--
primNames :: [Text]
primNames =
  [ "iconst", "fconst", "ieqz", "ieq", "ine", "ilt_s", "ilt_u", "igt_s"
  , "igt_u", "ile_s", "ile_u", "ige_s", "ige_u", "feq", "fne", "flt", "fgt"
  , "fle", "fge", "iclz", "ictz", "ipopcnt", "iadd", "isub", "imul", "idiv_s"
  , "idiv_u", "irem_s", "irem_u", "iand", "ior", "ixor", "ishl", "ishr_s"
  , "ishr_u", "irotl", "irotr", "fabs", "fneg", "fceil", "ffloor", "ftrunc"
  , "fnearest", "fsqrt", "fadd", "fsub", "fmul", "fdiv", "fmin", "fmax"
  , "fcopysign", "itrunc_s", "itrunc_u", "fconvert_s", "fconvert_u"
  , "ireinterpret", "freinterpret", "iextend8", "iextend16", "iextend32"
  , "itrunc_sat_s", "itrunc_sat_u"
  ]
