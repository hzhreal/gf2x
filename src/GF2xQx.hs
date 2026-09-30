module GF2xQx
  ( GF2xQx,
    zero',
    one',
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
    φ'',
    ψ',
    deg,
    scale,
  )
where

import Algebra
import Data.List (iterate')
import Data.List.NonEmpty qualified as NE
import GF2x qualified
import GF2xQ
import Numeric.Natural (Natural)

type GF2xQx = NE.NonEmpty GF2xQ

instance Ring GF2xQx where
  zero = undefined
  zero' (f NE.:| fs) = zero' f NE.:| []
  one = undefined
  one' (f NE.:| fs) = one' f NE.:| []

  iden f'@(f NE.:| fs)
    | f .==. zero' f && isNonEmpty fs = iden (NE.fromList fs)
    | otherwise = f'

  addInv f = NE.map addInv (iden f)

  f .+. g
    | m == n = iden (NE.zipWith (.+.) f' g')
    | otherwise = h0 <> NE.zipWith (.+.) h1 i
    where
      f' = iden f
      g' = iden g
      m = NE.length f'
      n = NE.length g'

      a = max m n
      h = if a == m then f' else g'
      b = min m n
      i = if b == m then f' else g'

      h' = NE.splitAt (a - b) h
      h0 = (NE.fromList . fst) h'
      h1 = (NE.fromList . snd) h'

  f .*. g
    | f .==. zero' f && g .==. zero' g && f .!=. g = undefined
    | f .==. zero' f || g .==. zero' g = zero' f
    | m + n > toInteger (maxBound :: Int) = undefined
    | otherwise = foil f' m g' n
    where
      f' = iden f
      g' = iden g
      m = deg f'
      n = deg g'

  f .-. g = f .+. addInv g
  f .**. n
    | n < 0 = undefined
    | toInteger n > toInteger (maxBound :: Int) = undefined
    | otherwise = iterate' (.*. f) (one' f) !! fromIntegral n

  f .==. g = NE.length f' == NE.length g' && and h
    where
      f' = iden f
      g' = iden g
      h = NE.zipWith (.==.) f' g'
  f .!=. g = not (f .==. g)

instance EuclidanDomain GF2xQx where
  f .%. g
    | g .==. zero' g = undefined
    | m < n = f'
    | i > toInteger (maxBound :: Int) = undefined
    | otherwise = r .%. g'
    where
      f' = iden f
      g' = iden g
      m = deg f'
      n = deg g'

      i = m - n
      a_m = NE.head f'
      b_n = NE.head g'
      q_i = (a_m .*. mulInv b_n) NE.:| replicate (fromIntegral i) (zero' a_m)
      r = f' .-. (g' .*. q_i)

  f ./. g
    | g .==. zero' g = undefined
    | m < n = zero
    | i > toInteger (maxBound :: Int) = undefined
    | otherwise = q_i .+. (r ./. g)
    where
      f' = iden f
      g' = iden g
      m = deg f'
      n = deg g'

      i = m - n
      a_m = NE.head f'
      b_n = NE.head g'
      q_i = (a_m .*. mulInv b_n) NE.:| replicate (fromIntegral i) (zero' a_m)
      r = f' .-. (g' .*. q_i)

φ'' :: (Integral a, Integral b) => a -> [b] -> GF2xQx
φ'' p ms = NE.fromList (map (φ' p) ms)

ψ' :: GF2xQx -> [Natural]
ψ' f = NE.toList (NE.map (GF2x.unwrap . ψ) f)

deg :: GF2xQx -> Integer
deg f
  | f' .==. zero' f' = -1
  | otherwise = fromIntegral (NE.length f' - 1)
  where
    f' = iden f

scale :: GF2xQ -> GF2xQx -> GF2xQx
scale s f = NE.fromList [s .*. a | a <- NE.toList f]

showPoly :: GF2xQx -> String
showPoly f = showPoly' f' m
  where
    f' = iden f
    m = fromIntegral (NE.length f' - 1)

isNonEmpty :: [a] -> Bool
isNonEmpty = not . null

add :: GF2xQx -> GF2xQx -> GF2xQx
add f g
  | m == n = NE.zipWith (.+.) f g
  | otherwise = NE.zipWith (.+.) f g <> NE.fromList (NE.drop a h)
  where
    m = NE.length f
    n = NE.length g

    a = min m n
    h = if a /= m then f else g

foil :: GF2xQx -> Integer -> GF2xQx -> Integer -> GF2xQx
foil f'@(f NE.:| fs) m g'@(g NE.:| gs) n
  | n == 0 = scale g f'
  | m == 0 = l
  | otherwise = a NE.:| NE.toList (l' `add` foil (NE.fromList fs) (m - 1) g' n)
  where
    l = scale f g'
    l' = NE.fromList (NE.tail l)
    a = NE.head l

showPoly' :: GF2xQx -> Natural -> String
showPoly' (f NE.:| fs) i
  | isNonEmpty fs && isNonZero f = s ++ " + " ++ showPoly' (NE.fromList fs) (i - 1)
  | isNonEmpty fs = s ++ showPoly' (NE.fromList fs) (i - 1)
  | otherwise = s
  where
    isNonZero = (.!=. zero' f)
    f' = (fst . unwrapQ) f
    s
      | f .==. one' f = "x^{" ++ show i ++ "}"
      | f .!=. zero' f = "(" ++ GF2x.showPoly f' ++ ")" ++ "x^{" ++ show i ++ "}"
      | otherwise = ""
