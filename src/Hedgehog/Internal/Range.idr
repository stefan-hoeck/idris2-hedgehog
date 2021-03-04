module Hedgehog.Internal.Range

import Data.Bounded
import Data.Maybe
import Data.Fin
import Decidable.Equality

import Hedgehog.Internal.Util

%hide Prelude.Range

public export
MaxSizeNat : Nat
MaxSizeNat = 100

||| A wrapper of a natural number plus an erased proof that
||| the value is within its bounds.
|||
||| Unlike the original Hedgehog, we allow values in the range [0,100]
||| treating size as a proper percentage.
public export
record Size where
  constructor MkSize
  size     : Nat
  0 sizeOk : size <= MaxSizeNat = True

public export
mkSize : (n : Nat) -> {auto 0 ok : n <= MaxSizeNat = True} -> Size
mkSize n = MkSize n ok

public export
minSize : Size
minSize = mkSize 0

public export
maxSize : Size
maxSize = mkSize MaxSizeNat

export
mkSizeMay : Nat -> Maybe Size
mkSizeMay n with (decEq (n <= MaxSizeNat) True)
  mkSizeMay n | Yes _ = Just $ mkSize n
  mkSizeMay n | No  c = Nothing

export
mkSizeOrZero : Nat -> Size
mkSizeOrZero = fromMaybe minSize . mkSizeMay

export
mkSizeOrMax : Nat -> Size
mkSizeOrMax = fromMaybe maxSize . mkSizeMay

public export
resize : (Nat -> Nat) -> Size -> Size
resize f s = mkSizeOrMax (f s.size)

--------------------------------------------------------------------------------
--          Interface Implementations
--------------------------------------------------------------------------------

export
Show Size where
  showPrec p (MkSize n _) = showPrec p n

export
Eq Size where
  (==) = (==) `on` size

export
Ord Size where
  compare = compare `on` size

export
MinBound Size where
  minBound = minSize

export
MaxBound Size where
  maxBound = maxSize

export
Num Size where
  a + b = mkSizeOrMax $ size a + size b
  a * b = mkSizeOrMax $ size a * size b
  fromInteger = mkSizeOrMax . fromInteger

public export
ToInteger Size where toInteger = toInteger . size

--------------------------------------------------------------------------------
--          Range
--------------------------------------------------------------------------------

public export
record Range a where
  constructor MkRange
  origin  : a
  bounds' : Size -> (a,a)

export
bounds : Size -> Range a -> (a,a)
bounds s r = r.bounds' s

||| Get the lower bound of a range for the given size.
export
lowerBound : Ord a => Size -> Range a -> a
lowerBound sz = uncurry min . bounds sz

||| Get the lower bound of a range for the given size.
export
upperBound : Ord a => Size -> Range a -> a
upperBound sz = uncurry max . bounds sz

export
Functor Range where
  map f (MkRange origin bounds') =
    MkRange (f origin)
            \si => let (x,y) = bounds' si
                    in (f x, f y)

--------------------------------------------------------------------------------
--          Constant Ranges
--------------------------------------------------------------------------------

||| Construct a range which represents a constant single value.
|||
||| >>> bounds x $ singleton 5
||| (5,5)
|||
||| >>> origin $ singleton 5
||| 5
export
singleton : a -> Range a
singleton x = MkRange x \_ => (x, x)

||| Construct a range which is unaffected by the size parameter with a origin
||| point which may differ from the bounds.
|||
||| A range from @-10@ to @10@, with the origin at @0@:
|||
||| >>> bounds x $ constantFrom 0 (-10) 10
||| (-10,10)
|||
||| >>> origin $ constantFrom 0 (-10) 10
||| 0
|||
||| A range from @1970@ to @2100@, with the origin at @2000@:
|||
||| >>> bounds x $ constantFrom 2000 1970 2100
||| (1970,2100)
|||
||| >>> origin $ constantFrom 2000 1970 2100
||| 2000
export
constantFrom : (origin,lower,upper : a) -> Range a
constantFrom o l u = MkRange o \_ => (l, u)

||| Construct a range which is unaffected by the size parameter.
|||
||| A range from @0@ to @10@, with the origin at @0@:
|||
||| >>> bounds x $ constant 0 10
||| (0,10)
|||
||| >>> origin $ constant 0 10
||| 0
|||
export
constant : a -> a -> Range a
constant x y = constantFrom x x y

||| Construct a range which is unaffected by the size parameter using the full
||| range of a data type.
|||
||| A range from @-128@ to @127@, with the origin at @0@:
|||
||| >>> bounds x (constantBounded :: Range Int8)
||| (-128,127)
|||
||| >>> origin (constantBounded :: Range Int8)
||| 0
export
constantBounded : (MinBound a, MaxBound a, Num a) => Range a
constantBounded = constantFrom 0 minBound maxBound

--------------------------------------------------------------------------------
--          Linear Ranges
--------------------------------------------------------------------------------

||| Truncate a value so it stays within some range.
|||
||| >>> clamp 5 10 15
||| 10
|||
||| >>> clamp 5 10 0
||| 5
export
clamp : Ord a => (lower,upper,val : a) -> a
clamp l u v = if l > u then min l (max u v)
                       else min u (max l v)

||| Scales an integral value linearly with the size parameter.
export
scaleLinear : ToInteger a => Size -> (origin,bound : a) -> a
scaleLinear sz o0 b0 =
  let o    = toInteger o0
      b    = toInteger b0
      rng  = b - o
      diff = (rng * toInteger sz) `safeDiv` 100
   in fromInteger $ o + diff

||| Scales a fractional value linearly with the size parameter.
export
scaleLinearFrac :  (Neg a, Fractional a) => Size -> (origin,bound : a) -> a
scaleLinearFrac sz o b =
  let diff = (b - o) * (fromIntegral sz / 100)
   in o + diff

export %inline
scaled :  Ord a
       => (scale : Size -> (origin,bound : a) -> a)
       -> (origin,lower,upper : a)
       -> Range a
scaled f o l u = MkRange o \sz => let x_sized = clamp l u $ f sz o l
                                      y_sized = clamp l u $ f sz o u
                                   in (x_sized, y_sized)

||| Construct a range which scales the bounds relative to the size parameter.
|||
||| >>> bounds 0 $ linearFrom 0 (-10) 10
||| (0,0)
|||
||| >>> bounds 50 $ linearFrom 0 (-10) 20
||| (-5,10)
|||
||| >>> bounds 100 $ linearFrom 0 (-10) 20
||| (-10,20)
export
linearFrom : Ord a => ToInteger a => (origin,lower,upper : a) -> Range a
linearFrom = scaled scaleLinear

export
linear : Ord a => ToInteger a => (origin,upper : a) -> Range a
linear origin upper = linearFrom origin origin upper

export
linearFin : (n : Nat) -> Range (Fin $ S n)
linearFin n = map toFin $ linearFrom 0 0 (natToInteger n)
  where toFin : Integer -> Fin (S n)
        toFin k = fromMaybe FZ (integerToFin k (S n))

||| Construct a range which scales the bounds relative to the size parameter.
|||
||| This works the same as 'linearFrom', but for fractional values.
export
linearFracFrom :  (Neg a, Ord a, Fractional a)
               => (origin,lower,uppder : a) -> Range a
linearFracFrom = scaled scaleLinearFrac

||| Construct a range which is scaled relative to the size parameter and uses
||| the full range of a data type.
|||
||| >>> bounds 0 (linearBounded :: Range Int8)
||| (0,0)
|||
||| >>> bounds 50 (linearBounded :: Range Int8)
||| (-64,64)
|||
||| >>> bounds 99 (linearBounded :: Range Int8)
|||   (-128,127)
export
linearBounded :  (MinBound a, MaxBound a, Ord a, ToInteger a) => Range a
linearBounded = linearFrom minBound minBound maxBound

--------------------------------------------------------------------------------
--          Exponential Ranges
--------------------------------------------------------------------------------

EulerMinus1 : Double
EulerMinus1 = euler - 1

||| Scale a floating-point number exponentially with the size parameter.
|||
||| Note : This scales the difference between the two values exponentially.
export
scaleExponentialDouble : Size -> (origin,bound : Double) -> Double
scaleExponentialDouble sz o b =
  let e     = fromIntegral sz / 100.0
      delta = b - o
      diff  = pow (abs delta + 1) e - 1
   in o + diff * signum delta

||| Scale an integral exponentially with the size parameter.
export
scaleExponential : ToInteger a => Size -> (origin,bound : a) -> a
scaleExponential sz o b =
  round (scaleExponentialDouble sz (fromIntegral o) (fromIntegral b))

export
exponentialDoubleFrom : (origin,lower,upper : Double) -> Range Double
exponentialDoubleFrom = scaled scaleExponentialDouble

export
exponentialDouble : (lower,upper : Double) -> Range Double
exponentialDouble l u = exponentialDoubleFrom l l u

export
exponentialFrom : Ord a => ToInteger a => (origin,lower,upper : a) -> Range a
exponentialFrom = scaled scaleExponential

export
exponential : Ord a => ToInteger a => (lower,upper : a) -> Range a
exponential l u = exponentialFrom l l u

export
exponentialFin : (n : Nat) -> Range (Fin $ S n)
exponentialFin n = map toFin $ exponentialFrom 0 0 (natToInteger n)
  where toFin : Integer -> Fin (S n)
        toFin k = fromMaybe FZ (integerToFin k (S n))

--------------------------------------------------------------------------------
--          Tests and Proofs
--------------------------------------------------------------------------------

singletonOriginId : origin (singleton x) = x
singletonOriginId = Refl

singletonBoundsId : bounds s (singleton x) = (x,x)
singletonBoundsId = Refl

constantFromOrigin : origin (constantFrom o l u) = o
constantFromOrigin = Refl

constantFromBounds : bounds s (constantFrom o l u) = (l,u)
constantFromBounds = Refl

constantOrigin : origin (constant o u) = o
constantOrigin = Refl

constantBounds : bounds s (constant o u) = (o,u)
constantBounds = Refl

One : Int
One = 1

Zero : Int
Zero = 0

clamp1_100_0 : clamp One 100 0 = One
clamp1_100_0 = Refl

clamp100_1_0 : clamp 100 One 0 = One
clamp100_1_0 = Refl

clamp1_100_150 : clamp One 100 150 = 100
clamp1_100_150 = Refl

clamp100_1_150 : clamp 100 One 150 = 100
clamp100_1_150 = Refl

clamp1_100_50 : clamp One 100 50 = 50
clamp1_100_50 = Refl

clamp100_1_50 : clamp 100 One 50 = 50
clamp100_1_50 = Refl

-- scaleLinear0_100_0 : scaleLinear 0 (the Int 0) 100 = 0
-- scaleLinear0_100_0 = Refl
-- 
-- scaleLinear0_100_50 : scaleLinear 50 (the Int 0) 100 = 50
-- scaleLinear0_100_50 = Refl
-- 
-- scaleLinear0_100_99 : scaleLinear 99 (the Int 0) 100 = 99
-- scaleLinear0_100_99 = Refl
-- 
-- scaleLinear0_100_100 : scaleLinear 100 (the Int 0) 100 = 100
-- scaleLinear0_100_100 = Refl
-- 
-- bounds_linearFrom0_0_10_20 : bounds 0 (linearFrom Zero (-10) 20) = (0,0)
-- bounds_linearFrom0_0_10_20 = Refl
-- 
-- bounds_linearFrom50_0_10_20 : bounds 50 (linearFrom Zero (-10) 20) = (-5,10)
-- bounds_linearFrom50_0_10_20 = Refl
-- 
-- bounds_linearFrom100_0_10_20 : bounds 100 (linearFrom Zero (-10) 20) = (-10,20)
-- bounds_linearFrom100_0_10_20 = Refl
-- 
-- Bits8Full : Range Bits8
-- Bits8Full = linearBounded
-- 
-- bounds_linearBoundedBits8_0 : bounds 0 Bits8Full = (0,0)
-- bounds_linearBoundedBits8_0 = Refl
-- 
-- bounds_linearBoundedBits8_50 : bounds 50 Bits8Full = (0,127)
-- bounds_linearBoundedBits8_50 = Refl
-- 
-- bounds_linearBoundedBits8_100 : bounds 100 Bits8Full = (0,255)
-- bounds_linearBoundedBits8_100 = Refl
-- 
-- IntExp : Range Int
-- IntExp = exponential 1 32
-- 
-- bounds_exp_0_1_32 : bounds 0 IntExp = (1,1)
-- bounds_exp_0_1_32 = Refl
-- 
-- bounds_exp_20_1_32 : bounds 20 IntExp = (1,2)
-- bounds_exp_20_1_32 = Refl
-- 
-- bounds_exp_40_1_32 : bounds 40 IntExp = (1,4)
-- bounds_exp_40_1_32 = Refl
-- 
-- bounds_exp_60_1_32 : bounds 60 IntExp = (1,8)
-- bounds_exp_60_1_32 = Refl
-- 
-- bounds_exp_80_1_32 : bounds 80 IntExp = (1,16)
-- bounds_exp_80_1_32 = Refl
-- 
-- bounds_exp_100_1_32 : bounds 100 IntExp = (1,32)
-- bounds_exp_100_1_32 = Refl
