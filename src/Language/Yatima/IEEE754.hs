{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Yatima.IEEE754 where

import           Data.Word              (Word32, Word64, Word8)
import           Foreign.Marshal.Alloc  (alloca)
import           Foreign.Ptr            (Ptr, castPtr)
import           Foreign.Storable       (peek, poke)
import           Numeric.Extras
import           Numeric.IEEE
import           System.IO.Unsafe       (unsafeDupablePerformIO)

import qualified Data.ByteString        as B

import           Data.Serialize
import           Data.Serialize.IEEE754

import           Data.Bits              (complement, xor, (.&.), (.|.))
import qualified Data.Bits              as Bits

wordToDouble :: Word64 -> Double
wordToDouble w = unsafeDupablePerformIO $ alloca $ \(ptr :: Ptr Word64) -> do
    poke ptr w
    peek (castPtr ptr)

bytesToWord64 :: [Word8] -> Word64
bytesToWord64 (b0:b1:b2:b3:b4:b5:b6:b7:_) = 
  sh (f b0) 0  + sh (f b1) 8  + sh (f b2) 16 + sh (f b3) 24 +
  sh (f b4) 32 + sh (f b5) 40 + sh (f b6) 48 + sh (f b7) 56
 where
  f = fromIntegral
  sh = Bits.shift

word64ToBytes :: Word64 -> [Word8]
word64ToBytes n = 
  f <$> [ n .&. 0xFF           , (sh n (-8))  .&. 0xFF
        , (sh n (-16)) .&. 0xFF, (sh n (-24)) .&. 0xFF
        , (sh n (-32)) .&. 0xFF, (sh n (-40)) .&. 0xFF
        , (sh n (-48)) .&. 0xFF, (sh n (-56)) .&. 0xFF
        ]
 where
  f = fromIntegral
  sh = Bits.shift

ftou :: Double -> Word64
ftou n = bytesToWord64 $ B.unpack $ runPut $ putFloat64le n

utof :: Word64 -> Double
utof = wordToDouble
