module Language.Yatima.WASM where

import           Numeric.IEEE (IEEE, copySign, minNum, maxNum, identicalIEEE)
import           Data.Int
import           Data.Word
import           Language.Yatima.IEEE754

-- This module contains internal code reexported from Ilya Rezvov's Haskell-WASM
-- library: https://github.com/SPY/haskell-wasm, which is released under the
-- following MIT license: https://github.com/SPY/haskell-wasm/blob/master/LICENSE

asInt32 :: Word32 -> Int32
asInt32 w =
    if w < 0x80000000
    then fromIntegral w
    else -1 * fromIntegral (0xFFFFFFFF - w + 1)

asInt64 :: Word64 -> Int64
asInt64 w =
    if w < 0x8000000000000000
    then fromIntegral w
    else -1 * fromIntegral (0xFFFFFFFFFFFFFFFF - w + 1)

asWord32 :: Int32 -> Word32
asWord32 i
    | i >= 0 = fromIntegral i
    | otherwise = 0xFFFFFFFF - (fromIntegral (abs i)) + 1

asWord64 :: Int64 -> Word64
asWord64 i
    | i >= 0 = fromIntegral i
    | otherwise = 0xFFFFFFFFFFFFFFFF - (fromIntegral (abs i)) + 1

nearest :: (IEEE a) => a -> a
nearest f
    | isNaN f = f
    | f >= 0 && f <= 0.5 = copySign 0 f
    | f < 0 && f >= -0.5 = -0
    | otherwise =
        let i = floor f :: Integer in
        let fi = fromIntegral i in
        let r = abs f - abs fi in
        flip copySign f $ (
            if r == 0.5
            then (
                case (even i, f < 0) of
                    (True, _) -> fi
                    (_, True) -> fi - 1.0
                    (_, False) -> fi + 1.0
            )
            else fromIntegral (round f :: Integer)
        )

zeroAwareMin :: IEEE a => a -> a -> a
zeroAwareMin a b
    | identicalIEEE a 0 && identicalIEEE b (-0) = b
    | isNaN a = a
    | isNaN b = b
    | otherwise = minNum a b

zeroAwareMax :: IEEE a => a -> a -> a
zeroAwareMax a b
    | identicalIEEE a (-0) && identicalIEEE b 0 = b
    | isNaN a = a
    | isNaN b = b
    | otherwise = maxNum a b

floatFloor :: Float -> Float
floatFloor a
    | isNaN a = a
    | otherwise = copySign (fromIntegral (floor a :: Integer)) a

doubleFloor :: Double -> Double
doubleFloor a
    | isNaN a = a
    | otherwise = copySign (fromIntegral (floor a :: Integer)) a

floatCeil :: Float -> Float
floatCeil a
    | isNaN a = a
    | otherwise = copySign (fromIntegral (ceiling a :: Integer)) a

doubleCeil :: Double -> Double
doubleCeil a
    | isNaN a = a
    | otherwise = copySign (fromIntegral (ceiling a :: Integer)) a

floatTrunc :: Float -> Float
floatTrunc a
    | isNaN a = a
    | otherwise = copySign (fromIntegral (truncate a :: Integer)) a

doubleTrunc :: Double -> Double
doubleTrunc a
    | isNaN a = a
    | otherwise = copySign (fromIntegral (truncate a :: Integer)) a

