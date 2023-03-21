module Hedgehog.Internal.Seed

import Data.Bounded
import Data.Bits
import Data.DPair
import Data.Fin
import Derive.Prelude
import Derive.Pretty

%default total

%language ElabReflection

--------------------------------------------------------------------------------
--          Implementation Utilities
--------------------------------------------------------------------------------

shiftXor : Index {a = Bits32} -> Bits32 -> Bits32
shiftXor n w = w `xor` (w `shiftR` n)

shiftXorMultiply : Index {a = Bits32} -> Bits32 -> Bits32 -> Bits32
shiftXorMultiply n k w = shiftXor n w * k

mix32 : Bits32 -> Bits32
mix32 z0 =
   -- MurmurHash3Mixer 32bit
    let z1 = shiftXorMultiply 16 0x85ebca6b z0
        z2 = shiftXorMultiply 13 0xc2b2ae35 z1
        z3 = shiftXor 16 z2
    in z3

-- used only in mixGamma
mix32variant13 : Bits32 -> Bits32
mix32variant13 z0 =
   -- See avalanche "executable"
    let z1 = shiftXorMultiply 16 0x69ad6ccb z0
        z2 = shiftXorMultiply 13 0xcd9ab5b3 z1
        z3 = shiftXor 16 z2
    in z3

mixGamma : Bits32 -> Bits32
mixGamma z0 =
    let z1 = mix32variant13 z0 .|. 1             -- force to be odd
        n  = popCount (z1 `xor` (z1 `shiftR` 1))
    -- see: http://www.pcg-random.org/posts/bugs-in-splitmix.html
    -- let's trust the text of the paper, not the code.
    in if n >= 12
        then z1
        else z1 `xor` 0xaaaaaaaa


-- | (1 + sqrt 5) / 2 * (2 ^^ bits)
goldenGamma : Bits32
goldenGamma = 0x9e3779b9

bits64ToDouble : Bits64 -> Double
bits64ToDouble = fromInteger . cast

doubleUlp : Double
doubleUlp =  1.0 / bits64ToDouble (1 `shiftL` 53)

mask : Bits32 -> Bits32
mask n = sl 1
       . sl 2
       . sl 4
       . sl 8
       $ sl 16 maxBound
  where sl : Index {a = Bits32} -> Bits32 -> Bits32
        sl s x = let x' = shiftR x s
                  in if x' < n then x else x'

two32 : Integer
two32 = 1 `shiftL` 32

--------------------------------------------------------------------------------
--          Seed
--------------------------------------------------------------------------------

public export
data Seed = MkSeed Bits32 Bits32

%runElab derive "Seed" [Eq,Show,Pretty]

||| Create an Seed from the given seed.
export
smGen : Bits32 -> Seed
smGen s = MkSeed (mix32 s) (mixGamma (s + goldenGamma))

%foreign "scheme:blodwen-random"
         "javascript:lambda:x=>BigInt(Math.floor(Math.random() * Number(x)))"
prim__random_Bits32 : Bits32 -> PrimIO Bits32

||| Initialize 'SMGen' using entropy available on the system (time, ...)
export
initSMGen : HasIO io => io Seed
initSMGen = liftIO
          . map smGen
          $ fromPrim (prim__random_Bits32 maxBound)

||| Split a generator into a two uncorrelated generators.
|||
||| Note: This is `splitSMGen` in Haskell
export
split : Seed -> (Seed, Seed)
split (MkSeed seed gamma) =
  let seed'  = seed  + gamma
      seed'' = seed' + gamma
   in (MkSeed seed'' gamma, MkSeed (mix32 seed') (mixGamma seed''))

||| Generates a 32-bit value
export
nextBits32 : Seed -> (Bits32, Seed)
nextBits32 (MkSeed seed gamma) =
  let seed' = seed + gamma
   in (mix32 seed', MkSeed seed' gamma)

--------------------------------------------------------------------------------
--          Generating Integer Ranges
--------------------------------------------------------------------------------

||| Generates values in the closed interval [0,range].
export
nextBits32R : (range : Bits32) -> Seed -> (Bits32,Seed)
nextBits32R range = go 100 (mask range)
  where
    go : Nat -> Bits32 -> Seed -> (Bits32, Seed)
    go 0 _ gv       = (0,gv)
    go (S k) msk gv =
      let (x,gv') = nextBits32 gv
          x' = x .&. msk
       in if x' > range then go k msk gv' else (x', gv')

-- bitmask with rejection for Integers.
nextIntegerImpl : Integer -> Seed -> (Integer,Seed)
nextIntegerImpl range =
  let (leadMask,restDigits) = calc 0 range
   in loop 100 leadMask restDigits
  where
    calc : Nat -> Integer -> (Bits32,Nat)
    calc n x  = if x < two32
                   then (mask $ cast x, n)
                   else calc (n + 1) (assert_smaller x (x `shiftR` 32))

    go : Integer -> Nat -> Seed -> (Integer, Seed)
    go acc 0     g = (acc, g)
    go acc (S k) g = let (x, g') = nextBits32 g
                      in go (shiftL acc 32 .|. cast x) k g'

    loop : Nat -> Bits32 -> Nat -> Seed -> (Integer,Seed)
    loop 0     _   _ gv = (0,gv)
    loop (S k) bm rd g0 = let (x,g1) = nextBits32 g0
                              (n,g') = go (cast $ x .&. bm) rd g1
                           in if n <= range
                                then (n,g')
                                else loop k bm rd g'

export
nextIntegerR : (Integer,Integer) -> Seed -> (Integer,Seed)
nextIntegerR (x,y) =
  let f = \l,u => mapFst (l+) . nextIntegerImpl (u-l)
   in if x <= y then f x y else f y x

nextBits32_ : Bits32 -> Bits32 -> Seed -> (Bits32,Seed)
nextBits32_ l u s =
  let (v,s) := nextBits32R (u-l) s
   in (l+v, s)

export
nextBits32Range :  Bits32 -> Bits32 -> Seed -> (Bits32,Seed)
nextBits32Range x y s = if x <= y then nextBits32_ x y s else nextBits32_ y x s

||| Generates a 64-bit value
export
nextBits64 : Seed -> (Bits64, Seed)
nextBits64 s =
  let (n,s2) := nextIntegerR (-0x8000_0000_0000_0000, 0x7fff_ffff_ffff_ffff) s
   in (cast n, s)

||| Generate a `Double` in [0, 1) range.
export
nextDouble : Seed -> (Double, Seed)
nextDouble g =
  let (w64,g') = nextBits64 g
   in (bits64ToDouble (w64 `shiftR` 11) * doubleUlp, g')

||| Generate a `Double` in [x, y) range.
export
nextDoubleR : (lower: Double) -> (upper: Double) -> Seed -> (Double, Seed)
nextDoubleR x y = let g = \l,u => let diff = u - l
                                   in mapFst (\f => l + f * diff) . nextDouble
                   in if x <= y then g x y else g y x

