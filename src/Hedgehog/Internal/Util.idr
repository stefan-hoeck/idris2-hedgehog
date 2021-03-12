module Hedgehog.Internal.Util

import Data.DPair
import Data.List
import Data.Colist

%default total
--------------------------------------------------------------------------------
--          SafeDiv
--------------------------------------------------------------------------------

||| Interface providing a safe (total) division operation
||| by proving that the divisor is non-zero.
public export
interface Neg a => SafeDiv (0 a : Type) (0 pred : a -> Type) | a where
  total safeDiv' : (n,d : a) -> (0 prf : pred d) -> a

public export
SafeDiv Int (\d => d == 0 = False) where
  safeDiv' n d _ = n `div` d

public export
SafeDiv Integer (\d => d == 0 = False) where
  safeDiv' n d _ = n `div` d

public export
SafeDiv Double (\d => d == 0 = False) where
  safeDiv' n d _ = n / d

public export total
safeDiv : SafeDiv a pred => (n,d : a) -> {auto 0 ok : pred d} -> a
safeDiv n d = safeDiv' n d ok

public export total
fromPred : (a -> Bool) -> a -> Maybe a
fromPred p a = guard (p a) $> a

--------------------------------------------------------------------------------
--          ToInteger
--------------------------------------------------------------------------------

public export
interface Num a => ToInteger a where
  toInteger : a -> Integer

  toNat : a -> Nat
  toNat = integerToNat . toInteger

public export
ToInteger Integer where toInteger = id

public export
ToInteger Int where toInteger = cast

public export
ToInteger Bits8 where toInteger = cast

public export
ToInteger Bits16 where toInteger = cast

public export
ToInteger Bits32 where toInteger = cast

public export
ToInteger Bits64 where toInteger = cast

public export
ToInteger Nat where
  toInteger = cast
  toNat = id

public export
ToInteger Double where toInteger = cast

public export
fromIntegral : ToInteger a => Num b => a -> b
fromIntegral = fromInteger . toInteger

public export
round : Num a => Double -> a
round v = let f = floor v
              v' = if v - f < 0.5 then f else ceiling v
           in fromInteger $ cast v'

--------------------------------------------------------------------------------
--          (Lazy) List Utilities
--------------------------------------------------------------------------------

public export
iterateBefore : (p : a -> Bool) -> (a -> a) -> (v : a) -> Colist a
iterateBefore p f = takeBefore p . iterate f

public export
iterateBefore0 : Eq a => Num a => (a -> a) -> (start : a) -> Colist a
iterateBefore0 = iterateBefore (0 ==)

||| Prepends the first list in reverse order to the
||| second list.
public export
prepRev : List a -> List a -> List a
prepRev []        ys = ys
prepRev (x :: xs) ys = prepRev xs (x :: ys)

public export
signum : Ord a => Neg a => a -> a
signum x = if x < 0
              then (-1)
              else if x == 0 then 0 else 1

--------------------------------------------------------------------------------
--          Colists
--------------------------------------------------------------------------------

||| Cons an element on to the front of a list unless it is already there.
public export total
consNub : Eq a => a -> Colist a -> Colist a
consNub x []          = [x]
consNub x l@(y :: xs) = if x == y then l else x :: l

public export
concatColist : Colist (Colist a) -> Colist a
concatColist ((x :: xs) :: ys)       = x :: concatColist (xs :: ys)
concatColist ([] :: (x :: xs) :: ys) = x :: concatColist (xs :: ys)
concatColist _                       = []

public export
concatMapColist : (a -> Colist b) -> Colist a -> Colist b
concatMapColist f = concatColist . map f

public export
fromFoldable : Foldable f => f a -> Colist a
fromFoldable = fromList . toList

--------------------------------------------------------------------------------
--          Numeric Utilities
--------------------------------------------------------------------------------

public export
IsInUnit : Double -> Bool
IsInUnit d = 0.0 < d && d < 1.0

public export
0 InUnit : Type
InUnit = Subset Double (\x => IsInUnit x = True)

export
recipBits64 : Subset Bits64 (\x => x >= 2 = True) -> InUnit
recipBits64 (Element v _) =
  Element (1.0 / fromInteger (cast v)) (believe_me (Refl {x = True} ))

-- Algorithm taken from
-- https://web.archive.org/web/20151110174102/http://home.online.no/~pjacklam/notes/invnorm/
-- Accurate to about one part in 10^9.
--
-- The 'erf' package uses the same algorithm, but with an extra step
-- to get a fully accurate result, which we skip because it requires
-- the 'erfc' function.
export
invnormcdf : (p : InUnit) -> Double
invnormcdf (Element p _) =
  let a1 = -3.969683028665376e+01
      a2 =  2.209460984245205e+02
      a3 = -2.759285104469687e+02
      a4 =  1.383577518672690e+02
      a5 = -3.066479806614716e+01
      a6 =  2.506628277459239e+00

      b1 = -5.447609879822406e+01
      b2 =  1.615858368580409e+02
      b3 = -1.556989798598866e+02
      b4 =  6.680131188771972e+01
      b5 = -1.328068155288572e+01

      c1 = -7.784894002430293e-03
      c2 = -3.223964580411365e-01
      c3 = -2.400758277161838e+00
      c4 = -2.549732539343734e+00
      c5 =  4.374664141464968e+00
      c6 =  2.938163982698783e+00

      d1 =  7.784695709041462e-03
      d2 =  3.224671290700398e-01
      d3 =  2.445134137142996e+00
      d4 =  3.754408661907416e+00

      p_low  = 0.02425
      p_high = 1 - p_low
      q      = sqrt(-2*log(p))

   in if p < p_low
         then (((((c1*q+c2)*q+c3)*q+c4)*q+c5)*q+c6) /
              ((((d1*q+d2)*q+d3)*q+d4)*q+1)
         else
           if p <= p_high
              then
                let
                  q = p - 0.5
                  r = q*q
                in
                  (((((a1*r+a2)*r+a3)*r+a4)*r+a5)*r+a6)*q /
                  (((((b1*r+b2)*r+b3)*r+b4)*r+b5)*r+1)
              else
                let
                  q = sqrt(-2*log(1-p))
                in
                  -(((((c1*q+c2)*q+c3)*q+c4)*q+c5)*q+c6) /
                   ((((d1*q+d2)*q+d3)*q+d4)*q+1)
