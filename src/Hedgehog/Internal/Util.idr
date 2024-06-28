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
ToInteger Int8 where toInteger = cast

public export
ToInteger Int16 where toInteger = cast

public export
ToInteger Int32 where toInteger = cast

public export
ToInteger Int64 where toInteger = cast

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
round v =
  let f  := floor v
      v' := if v - f < 0.5 then f else ceiling v
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
signum x =
  if x < 0 then (-1) else if x == 0 then 0 else 1

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
