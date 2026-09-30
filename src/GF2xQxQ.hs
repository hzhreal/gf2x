module GF2xQxQ
  ( GF2xQxQ (GF2xQxQ),
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
    φ''',
    π',
    ψ,
    ψ'',
    unwrapQ,
  )
where

import Algebra
import Data.List.NonEmpty qualified as NE
import GF2xQ qualified
import GF2xQx
import Numeric.Natural (Natural)

data GF2xQxQ = GF2xQxQ GF2xQx GF2xQx

instance Ring GF2xQxQ where
  zero = undefined
  zero' (GF2xQxQ _ p) = π zero
    where
      π = π' p
  one = undefined
  one' (GF2xQxQ _ p) = π one
    where
      π = π' p

  iden (GF2xQxQ f p) = GF2xQxQ (f .%. p) p

  addInv (GF2xQxQ f p) = π (addInv f)
    where
      π = π' p

  (GF2xQxQ f p) .+. (GF2xQxQ g q)
    | p .!=. q = undefined
    | otherwise = π (f .+. g)
    where
      π = π' p
  (GF2xQxQ f p) .*. (GF2xQxQ g q)
    | p .!=. q = undefined
    | otherwise = π (f .*. g)
    where
      π = π' p

  f' .-. g' = f' .+. addInv g'
  (GF2xQxQ f p) .**. n = π (f .**. n)
    where
      π = π' p

  f'@(GF2xQxQ f p) .==. g'@(GF2xQxQ g q)
    | p .!=. q = undefined
    | otherwise = ψ f' .==. ψ g'
  f' .!=. g' = not (f' .==. g')

φ''' :: (Integral a, Integral b, Integral c) => a -> [b] -> [c] -> GF2xQxQ
φ''' p ms ns = GF2xQxQ (φ'' p ns) (φ'' p ms)

π' :: GF2xQx -> GF2xQx -> GF2xQxQ
π' p f = iden (GF2xQxQ f p)

ψ :: GF2xQxQ -> GF2xQx
ψ (GF2xQxQ f p) = (fst . unwrapQ . π) f
  where
    π = π' p

ψ'' :: GF2xQxQ -> [Natural]
ψ'' = ψ' . ψ

unwrapQ :: GF2xQxQ -> (GF2xQx, GF2xQx)
unwrapQ (GF2xQxQ f p) = (f, p)
