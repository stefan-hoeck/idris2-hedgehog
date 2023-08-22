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

shiftXor : Index {a = Bits64} -> Bits64 -> Bits64
shiftXor n w = w `xor` (w `shiftR` n)

shiftXorMultiply : Index {a = Bits64} -> Bits64 -> Bits64 -> Bits64
shiftXorMultiply n k w = shiftXor n w * k

-- Note: in JDK implementations the mix64 and mix64variant13
-- (which is inlined into mixGamma) are swapped.
mix64 : Bits64 -> Bits64
mix64 z0 =
   -- MurmurHash3Mixer
    let z1 = shiftXorMultiply 33 0xff51afd7ed558ccd z0
        z2 = shiftXorMultiply 33 0xc4ceb9fe1a85ec53 z1
        z3 = shiftXor 33 z2
    in z3

-- used only in mixGamma
mix64variant13 : Bits64 -> Bits64
mix64variant13 z0 =
   -- Better Bit Mixing - Improving on MurmurHash3's 64-bit Finalizer
   -- http://zimbry.blogspot.fi/2011/09/better-bit-mixing-improving-on.html
   --
   -- Stafford's Mix13
    let z1 = shiftXorMultiply 30 0xbf58476d1ce4e5b9 z0 -- MurmurHash3 mix constants
        z2 = shiftXorMultiply 27 0x94d049bb133111eb z1
        z3 = shiftXor 31 z2
    in z3

mixGamma : Bits64 -> Bits64
mixGamma z0 =
    let z1 = mix64variant13 z0 .|. 1             -- force to be odd
        n  = popCount (z1 `xor` (z1 `shiftR` 1))
    -- see: http://www.pcg-random.org/posts/bugs-in-splitmix.html
    -- let's trust the text of the paper, not the code.
    in if n >= 24
        then z1
        else z1 `xor` 0xaaaaaaaaaaaaaaaa

goldenGamma : Bits64
goldenGamma = 0x9e3779b97f4a7c15

bits64ToDouble : Bits64 -> Double
bits64ToDouble = fromInteger . cast

doubleUlp : Double
doubleUlp =  1.0 / bits64ToDouble (1 `shiftL` 53)

mask : Bits64 -> Bits64
mask n = sl 1
       . sl 2
       . sl 4
       . sl 8
       . sl 16
       $ sl 32 maxBound
  where sl : Index {a = Bits64} -> Bits64 -> Bits64
        sl s x = let x' = shiftR x s
                  in if x' < n then x else x'

two64 : Integer
two64 = 1 `shiftL` 64

--------------------------------------------------------------------------------
--          Seed
--------------------------------------------------------------------------------

public export
data Seed = MkSeed Bits64 Bits64

%runElab derive "Seed" [Eq,Show,Pretty]

||| Create an Seed from the given seed.
export
smGen : Bits64 -> Seed
smGen s = MkSeed (mix64 s) (mixGamma (s + goldenGamma))

%foreign "scheme:blodwen-random"
         "javascript:lambda:x=>BigInt(Math.floor(Math.random() * Number(x)))"
         """
         go:
         import "math/rand"

         func (max, world any) uint64 {
           return uint64(rand.Float64() * float64(max.(uint64)))
         }
         """
prim__random_Bits64 : Bits64 -> PrimIO Bits64

||| Describes a context in which some initial seed can be gained
|||
||| In a non-pure context this can rely on some system entropy.
||| In pure contexts this can get a seed from configuration,
||| from a monadic state or from a user at the call-site.
export
interface CanInitSeed m where
  initSMGen : m Seed

export
MaxRobustSmGenNum : Bits64
MaxRobustSmGenNum = 4294967087 -- max number supported by racket

||| Initialize 'SMGen' using entropy available on the system (time, ...)
export
HasIO io => CanInitSeed io where
  initSMGen = liftIO
            . map smGen
            $ fromPrim (prim__random_Bits64 MaxRobustSmGenNum)

||| Initialise the seed for any applicative context
||| by the given particular value
export
Manual : Applicative m => Seed -> CanInitSeed m
Manual seed = S where [S] CanInitSeed m where initSMGen = pure seed

||| Split a generator into a two uncorrelated generators.
|||
||| Note: This is `splitSMGen` in Haskell
export
split : Seed -> (Seed, Seed)
split (MkSeed seed gamma) =
  let seed'  = seed  + gamma
      seed'' = seed' + gamma
   in (MkSeed seed'' gamma, MkSeed (mix64 seed') (mixGamma seed''))

||| Generates a 64-bit value
export
nextBits64 : Seed -> (Bits64, Seed)
nextBits64 (MkSeed seed gamma) = let seed' = seed + gamma
                                  in (mix64 seed', MkSeed seed' gamma)

||| Generate a `Double` in [0, 1) range.
export
nextDouble : Seed -> (Double, Seed)
nextDouble g = let (w64,g') = nextBits64 g
                in (bits64ToDouble (w64 `shiftR` 11) * doubleUlp, g')

||| Generate a `Double` in [x, y) range.
export
nextDoubleR : (lower: Double) -> (upper: Double) -> Seed -> (Double, Seed)
nextDoubleR x y = let g = \l,u => let diff = u - l
                                   in mapFst (\f => l + f * diff) . nextDouble
                   in if x <= y then g x y else g y x

--------------------------------------------------------------------------------
--          Generating Integer Ranges
--------------------------------------------------------------------------------

||| Generates values in the closed interval [0,range].
export
nextBits64R : (range : Bits64) -> Seed -> (Bits64,Seed)
nextBits64R range = go 100 (mask range)
  where go : Nat -> Bits64 -> Seed -> (Bits64, Seed)
        go 0 _ gv       = (0,gv)
        go (S k) msk gv = let (x,gv') = nextBits64 gv
                              x' = x .&. msk
                           in if x' > range
                                then go k msk gv'
                                else (x', gv')

-- bitmask with rejection for Integers.
nextIntegerImpl : Integer -> Seed -> (Integer,Seed)
nextIntegerImpl range = let (leadMask,restDigits) = calc 0 range
                         in loop 100 leadMask restDigits
  where calc : Nat -> Integer -> (Bits64,Nat)
        calc n x  = if x < two64
                       then (mask $ cast x, n)
                       else calc (n + 1) (assert_smaller x (x `shiftR` 64))

        go : Integer -> Nat -> Seed -> (Integer, Seed)
        go acc 0     g = (acc, g)
        go acc (S k) g = let (x, g') = nextBits64 g
                          in go (shiftL acc 64 .|. cast x) k g'

        loop : Nat -> Bits64 -> Nat -> Seed -> (Integer,Seed)
        loop 0     _   _ gv = (0,gv)
        loop (S k) bm rd g0 = let (x,g1) = nextBits64 g0
                                  (n,g') = go (cast $ x .&. bm) rd g1
                               in if n <= range
                                    then (n,g')
                                    else loop k bm rd g'

export
nextIntegerR : (Integer,Integer) -> Seed -> (Integer,Seed)
nextIntegerR (x,y) = let f = \l,u => mapFst (l+) . nextIntegerImpl (u-l)
                      in if x <= y then f x y else f y x
