module Rijndael (cipher, cipherInv) where

import Data.Bits ((.<<.), (.>>.), (.|.))
import Data.List (foldl', iterate', transpose)
import Data.List.NonEmpty qualified as NE
import Data.Word (Word8)
import GF2x
import GF2xQ
import GF2xQx
import GF2xQxQ qualified

poly = 0x11B

poly' = [1, 0, 0, 0, 1]

sbox :: Word8 -> Word8
sbox n = (fromIntegral . unwrap) d
  where
    f = φ' poly n
    a
      | f .!=. zero' f = (ψ . mulInv) f
      | otherwise = ψ f

    b = map φ (iterate' cyclicLeftShift 0b11110001)
    c = map (`dot` a) b
    d = foldl' (.+.) zero (zipWith (\n i -> if n then mono i else zero) (take 8 c) [0 .. 7]) .+. φ 0b01100011

sboxInv :: Word8 -> Word8
sboxInv n = (fromIntegral . unwrap) d
  where
    π = (π' . φ) poly
    f = φ n

    a = map φ (iterate' cyclicLeftShift 0b10100100)
    b = map (`dot` f) a
    c = π (foldl' (.+.) zero (zipWith (\n i -> if n then mono i else zero) (take 8 b) [0 .. 7]) .+. φ 0b00000101)
    d
      | c .!=. zero' c = (ψ . mulInv) c
      | otherwise = ψ c

byteSub :: [Word8] -> [Word8]
byteSub = map sbox

byteSubInv :: [Word8] -> [Word8]
byteSubInv = map sboxInv

shiftRow :: [Int] -> [Word8] -> [Word8]
shiftRow cs block = fromCol c
  where
    b = toCol 4 block
    c = head b : zipWith cyclicLeftShift'n cs (tail b)

shiftRowInv :: [Int] -> [Word8] -> [Word8]
shiftRowInv cs block = fromCol c
  where
    b = toCol 4 block
    c = head b : zipWith cyclicRightShift'n cs (tail b)

mixColumn :: [Word8] -> [Word8]
mixColumn block = map fromIntegral (fromRow d)
  where
    b = map reverse (toRow 4 block)
    b' = map (GF2xQxQ.φ''' poly poly') b
    c = GF2xQxQ.φ''' poly poly' [0x03, 0x01, 0x01, 0x02]
    d = map (reverse . lpad 0 4 . GF2xQxQ.ψ'' . (GF2xQxQ..*. c)) b'

mixColumnInv :: [Word8] -> [Word8]
mixColumnInv block = map fromIntegral (fromRow d)
  where
    b = map reverse (toRow 4 block)
    b' = map (GF2xQxQ.φ''' poly poly') b
    c = GF2xQxQ.φ''' poly poly' [0x0B, 0x0D, 0x09, 0x0E]
    d = map (reverse . lpad 0 4 . GF2xQxQ.ψ'' . (GF2xQxQ..*. c)) b'

addRoundKey :: [Word8] -> [Word8] -> [Word8]
addRoundKey rk block = zipWith (\a b -> (fromIntegral . unwrap) (φ a .+. φ b)) block rk

addRoundKeyInv :: [Word8] -> [Word8] -> [Word8]
addRoundKeyInv = addRoundKey

rc :: Int -> GF2xQ
rc i
  | i < 1 = undefined
  | otherwise = π' (φ poly) (mono 1) .**. (i - 1)

rcon :: Int -> GF2xQx
rcon i = NE.fromList [x_i, zero' x_i, zero' x_i, zero' x_i]
  where
    x_i = rc i

keyExpansion' :: Int -> Int -> [GF2xQx] -> [GF2xQx]
keyExpansion' kCol i key = key ++ [k]
  where
    f = key !! (i - 1)
    rotf = NE.fromList (cyclicLeftShift' (NE.toList f))
    rc = rcon (i `div` kCol)

    toWord :: GF2xQx -> [Word8]
    toWord f = map fromIntegral (ψ' f)
    fromWord :: [Word8] -> GF2xQx
    fromWord = φ'' poly

    g
      | i `mod` kCol == 0 = (fromWord . byteSub . toWord) rotf .+. rc
      | kCol > 6 && i `mod` kCol == 4 = (fromWord . byteSub . toWord) f
      | otherwise = f
    h = key !! (i - kCol)
    j = h .+. g
    k = NE.fromList (lpad (zero' (NE.head f)) 4 (NE.toList j))

keyExpansion :: Int -> Int -> Int -> [Word8] -> [Word8]
keyExpansion kCol bCol nr key = map fromIntegral (fromRow b')
  where
    k = map (φ'' poly) (toRow 4 key)
    fs = map (keyExpansion' kCol) [kCol .. bCol * (nr + 1) - 1]
    b = foldl' (\x f -> f x) k fs
    b' = map ψ' b

rijndael :: Int -> [Int] -> [Word8] -> [Word8] -> [Word8]
rijndael kCol cs block rk = (addRoundKey rk . mixColumn . shiftRow cs . byteSub) block

rijndaelInv :: Int -> [Int] -> [Word8] -> [Word8] -> [Word8]
rijndaelInv kCol cs block rk = (addRoundKeyInv rk . mixColumnInv . shiftRowInv cs . byteSubInv) block

rijndaelFinal :: Int -> [Int] -> [Word8] -> [Word8] -> [Word8]
rijndaelFinal kCol cs block rk = (addRoundKey rk . shiftRow cs . byteSub) block

rijndaelFinalInv :: Int -> [Int] -> [Word8] -> [Word8] -> [Word8]
rijndaelFinalInv kCol cs block rk = (addRoundKeyInv rk . shiftRowInv cs . byteSubInv) block

cipher :: [Word8] -> [Word8] -> [Word8]
cipher key block
  | kl `notElem` [16, 20, 24, 28, 32] = undefined
  | bl `notElem` [16, 20, 24, 28, 32] = undefined
  | otherwise = rijndaelFinal kCol cs (foldl (rijndael kCol cs) (addRoundKey ek_0 block) ek') ek_r
  where
    kl = length key
    bl = length block

    kCol = kl `div` 4
    bCol = bl `div` 4
    nr = max kCol bCol + 6

    c1
      | bCol == 4 = 1
      | bCol == 5 = 1
      | bCol == 6 = 1
      | bCol == 7 = 1
      | bCol == 8 = 1
      | otherwise = undefined
    c2
      | bCol == 4 = 2
      | bCol == 5 = 2
      | bCol == 6 = 2
      | bCol == 7 = 2
      | bCol == 8 = 3
      | otherwise = undefined
    c3
      | bCol == 4 = 3
      | bCol == 5 = 3
      | bCol == 6 = 3
      | bCol == 7 = 4
      | bCol == 8 = 4
      | otherwise = undefined
    cs = [c1, c2, c3]

    ek = toRow bl (keyExpansion kCol bCol nr key)
    ek_0 = head ek
    ek_r = ek !! nr
    ek' = (init . tail) ek

cipherInv :: [Word8] -> [Word8] -> [Word8]
cipherInv key block
  | kl `notElem` [16, 20, 24, 28, 32] = undefined
  | bl `notElem` [16, 20, 24, 28, 32] = undefined
  | otherwise = rijndaelFinalInv kCol cs (foldl (rijndaelInv kCol cs) (addRoundKeyInv ek_0 block) ek') ek_r
  where
    kl = length key
    bl = length block

    kCol = kl `div` 4
    bCol = bl `div` 4
    nr = max kCol bCol + 6

    c1
      | bCol == 4 = 1
      | bCol == 5 = 1
      | bCol == 6 = 1
      | bCol == 7 = 1
      | bCol == 8 = 1
      | otherwise = undefined
    c2
      | bCol == 4 = 2
      | bCol == 5 = 2
      | bCol == 6 = 2
      | bCol == 7 = 2
      | bCol == 8 = 3
      | otherwise = undefined
    c3
      | bCol == 4 = 3
      | bCol == 5 = 3
      | bCol == 6 = 3
      | bCol == 7 = 4
      | bCol == 8 = 4
      | otherwise = undefined
    cs = [c1, c2, c3]

    ek = toRow bl (keyExpansion kCol bCol nr key)
    ek_0 = ek !! nr
    ek_r = head ek
    ek' = (toRow bl . mixColumnInv . fromRow . tail . reverse . tail) ek

cyclicLeftShift :: Word8 -> Word8
cyclicLeftShift n = (n .<<. 1) .|. b_7
  where
    b_7 = n .>>. 7

cyclicLeftShift' :: [a] -> [a]
cyclicLeftShift' (a : as) = as ++ [a]

cyclicLeftShift'n :: Int -> [a] -> [a]
cyclicLeftShift'n n x = iterate' cyclicLeftShift' x !! n

cyclicRightShift' :: [a] -> [a]
cyclicRightShift' x = last x : init x

cyclicRightShift'n :: Int -> [a] -> [a]
cyclicRightShift'n n x = iterate' cyclicRightShift' x !! n

toRow :: Int -> [a] -> [[a]]
toRow cols x
  | null x = []
  | otherwise = fst s : toRow cols (snd s)
  where
    s = splitAt cols x

toCol :: Int -> [a] -> [[a]]
toCol cols = transpose . toRow cols

fromRow :: [[a]] -> [a]
fromRow = concat

fromCol :: [[a]] -> [a]
fromCol = fromRow . transpose

lpad :: a -> Int -> [a] -> [a]
lpad p n l = [p | _ <- [1 .. n - length l]] ++ l
