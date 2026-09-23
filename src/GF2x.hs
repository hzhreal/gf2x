module GF2x
  ( GF2x (GF2x),
    zero,
    one,
    iden,
    addInv,
    (.+.),
    (.*.),
    (.-.),
    (.**.),
    (.==.),
    (.!=.),
    (.%.),
    (./.),
    φ,
    unwrap,
    showPoly,
    deg,
    mono,
  )
where

import Algebra
import Data.Bits ((.&.), (.<<.), (.^.))
import Data.List (foldl', iterate')
import GHC.Num.Natural (naturalLog2)
import Numeric.Natural (Natural)

newtype GF2x = GF2x Natural

instance Ring GF2x where
  zero = φ 0
  zero' f = zero
  one = φ 1
  one' f = one

  iden = id

  addInv = id

  (GF2x a) .+. (GF2x b) = φ (a .^. b)
  f .*. g =
    foldl'
      (.+.)
      zero
      (map (\i -> if isTermMono f i then mulByMono g i else zero) [0 .. m])
    where
      m = deg f

  f .-. g = f .+. addInv g
  f .**. n
    | n < 0 = undefined
    | toInteger n > toInteger (maxBound :: Int) = undefined
    | otherwise = iterate' (.*. f) one !! fromIntegral n

  (GF2x a) .==. (GF2x b) = a == b
  f .!=. g = not (f .==. g)

instance EuclidanDomain GF2x where
  f .%. g
    | g .==. zero = undefined
    | m < n = f
    | otherwise = r .%. g
    where
      m = deg f
      n = deg g
      i = m - n
      q_i = mono i
      r = f .-. (g .*. q_i)

  f ./. g
    | g .==. zero = undefined
    | m < n = zero
    | otherwise = q_i .+. (r ./. g)
    where
      m = deg f
      n = deg g
      i = m - n
      q_i = mono i
      r = f .-. (g .*. q_i)

φ :: (Integral a) => a -> GF2x
φ n
  | n < 0 = undefined
  | otherwise = GF2x (fromIntegral n)

unwrap :: GF2x -> Natural
unwrap (GF2x a) = a

showPoly :: GF2x -> String
showPoly f
  | f .==. zero = "0"
  | otherwise =
      foldl'
        ( \s i ->
            if not a_0 && not a_1 && i == j
              then "x^" ++ "{" ++ show i ++ "}"
              else s ++ " + x^" ++ "{" ++ show i ++ "}"
        )
        s'
        (filter (isTermMono f) [2 .. m])
  where
    m = deg f
    j = head (filter (isTermMono f) [2 .. m])
    a_0 = isTermMono f 0
    a_1 = isTermMono f 1
    s'
      | a_0 && a_1 = "1 + x"
      | a_0 = "1"
      | a_1 = "x"
      | otherwise = ""

deg :: GF2x -> Integer
deg f@(GF2x a)
  | f .==. zero = -1
  | otherwise = fromIntegral (naturalLog2 a)

mono :: (Integral a) => a -> GF2x
mono = mulByMono one

mulByMono :: (Integral a) => GF2x -> a -> GF2x
mulByMono (GF2x a) mDeg
  | mDeg < 0 = undefined
  | toInteger mDeg > toInteger (maxBound :: Int) = undefined
  | otherwise = φ (a .<<. fromIntegral mDeg)

isTermMono :: (Integral a) => GF2x -> a -> Bool
isTermMono (GF2x a) i
  | i < 0 = undefined
  | otherwise = a .&. unwrap m /= 0
  where
    m = mono i
