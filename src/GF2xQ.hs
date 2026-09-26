module GF2xQ
  ( GF2xQ (GF2xQ),
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
    mulInv,
    (.***.),
    φ',
    π',
    ψ,
    unwrapQ,
    unwrapQ',
    showPolyQ,
  )
where

import Algebra
import GF2x
import Numeric.Natural (Natural)

data GF2xQ = GF2xQ GF2x GF2x

instance Ring GF2xQ where
  zero = undefined
  zero' (GF2xQ _ p) = π zero
    where
      π = π' p
  one = undefined
  one' (GF2xQ _ p) = π one
    where
      π = π' p

  iden (GF2xQ f p) = GF2xQ (f .%. p) p

  addInv (GF2xQ f p) = π (addInv f)
    where
      π = π' p

  (GF2xQ f p) .+. (GF2xQ g q)
    | p .!=. q = undefined
    | otherwise = π (f .+. g)
    where
      π = π' p
  (GF2xQ f p) .*. (GF2xQ g q)
    | p .!=. q = undefined
    | otherwise = π (f .*. g)
    where
      π = π' p

  f' .-. g' = f' .+. addInv g'
  (GF2xQ f p) .**. n = π (f .**. n)
    where
      π = π' p

  f'@(GF2xQ f p) .==. g'@(GF2xQ g q)
    | p .!=. q = undefined
    | otherwise = ψ f' .==. ψ g'
  f' .!=. g' = not (f' .==. g')

instance Field GF2xQ where
  mulInv f'@(GF2xQ _ p)
    | f' .==. zero' f' = undefined
    | otherwise = f' .**. (2 ^ deg p - 2)

  f' .***. n
    | n < 0 = mulInv f' .**. n
    | otherwise = f' .**. n

φ' :: (Integral a, Integral b) => (a, b) -> GF2xQ
φ' (n, q) = GF2xQ (φ n) (φ q)

π' :: GF2x -> GF2x -> GF2xQ
π' p f = iden (GF2xQ f p)

ψ :: GF2xQ -> GF2x
ψ (GF2xQ f p) = (fst . unwrapQ . π) f
  where
    π = π' p

unwrapQ :: GF2xQ -> (GF2x, GF2x)
unwrapQ (GF2xQ f p) = (f, p)

unwrapQ' :: GF2xQ -> (Natural, Natural)
unwrapQ' (GF2xQ f p) = (unwrap f, unwrap p)

showPolyQ :: GF2xQ -> String
showPolyQ (GF2xQ f p) = showPoly f ++ " + (" ++ showPoly p ++ ")"
