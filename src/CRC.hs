module CRC where

import Data.List (foldl')
import Data.Word (Word8)
import GF2x
import GF2xQ
import Numeric.Natural

crc :: [Word8] -> GF2x -> Natural
crc b g =
  (fst . unwrapQ') (foldl' (\r m -> (r .*. x_8) .+. π (φ m .*. x_n)) (π zero) b)
  where
    n = deg g
    π = π' g
    x = mono 1
    x_8 = π (mono 8)
    x_n = mono n
