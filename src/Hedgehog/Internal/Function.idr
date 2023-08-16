module Hedgehog.Internal.Function

import Data.Colist
import Data.Cotree
import Data.String

import Hedgehog.Internal.Gen
import Hedgehog.Internal.Range
import Hedgehog.Internal.Seed

%default total

export
interface Cogen a where
  constructor MkCogen
  unCogen : a -> Gen b -> Gen b

export
Cast a Nat => Cogen a where
  unCogen = variant . cast

||| Generates a random function being given a generator of codomain type
|||
||| This function takes a co-generator of domain type using `auto`-argument based on the type.
||| This generator does not shrink.
export
function_ : Cogen a => Gen b -> Gen (a -> b)
function_ @{cg} bg = MkGen $ \sz, sd => singleton $ \x => value $ runGen sz sd $ unCogen @{cg} x bg

----------------------------
--- Shrinkable functions ---
----------------------------

-- Claessen, K. (2012, September). Shrinking and showing functions:(functional pearl).
-- In ACM SIGPLAN Notices (Vol. 47, No. 12, pp. 73-80). ACM.

infixr 5 :->

public export
data (:->) : Type -> Type -> Type where
  Unit : c -> () :-> c
  Nil  : a :-> c
  Pair : (assert_total $ a :-> b :-> c) -> (a, b) :-> c
  Sum  : a :-> c -> b :-> c -> Either a b :-> c
  Map  : (a -> b) -> (b -> a) -> b :-> c -> a :-> c

export
Functor ((:->) a) where
  map f $ Unit c    = Unit $ f c
  map _ $ Nil       = Nil
  map f $ Pair a    = Pair $ map (assert_total $ map f) a
  map f $ Sum a b   = Sum (map f a) (map f b)
  map f $ Map a b c = Map a b $ map f c

table : a :-> c -> List (a, c)
table (Unit c) = [((), c)]
table Nil      = []
table (Pair f) = do
  (a, bc) <- table f
  (b, c) <- assert_total table bc
  pure ((a, b), c)
table (Sum a b) = [(Left x, c) | (x, c) <- table a] ++ [(Right x, c) | (x, c) <- table b]
table (Map _ g a) = mapFst g <$> table a

public export
interface Arg a where
  build : (a -> c) -> a :-> c

export
Arg Void where
  build _ = Nil

export
Arg Unit where
  build f = Unit $ f ()

export
Arg a => Arg b => Arg (a, b) where
  build f = Pair . build $ \a => build $ \b => f (a, b)

export
Arg a => Arg b => Arg (Either a b) where
  build f = Sum (build $ f . Left) (build $ f . Right)

-- Note: `via f g` will only be well-behaved if `g . f` and `f . g` are both identity functions.
via : Arg b => (a -> b) -> (b -> a) -> (a -> c) -> a :-> c
via a b f = Map a b . build $ f . b

-- Note: this will work only when two given casts are inverse of each other
[ThruCast] Cast a b => Cast b a => Arg b => Arg a where
  build = via {b} cast cast

apply' : a :-> b -> a -> Maybe b
apply' (Unit c)    ()        = Just c
apply' Nil         _         = Nothing
apply' (Pair f)    (a, b)    = assert_total $ apply' !(apply' f a) b
apply' (Sum f _)   (Left a)  = apply' f a
apply' (Sum _ g)   (Right a) = apply' g a
apply' (Map f _ g) a         = apply' g (f a)

(++) : Colist a -> Inf (Colist a) -> Colist a
[]      ++ ys = ys
(x::xs) ++ ys = x :: (xs ++ ys)

shrinkFn : (b -> Colist b) -> a :-> b -> Colist $ a :-> b
shrinkFn shr (Unit a)  = Unit <$> shr a
shrinkFn _   Nil       = []
shrinkFn shr (Pair f)  = shrinkFn (assert_total $ shrinkFn shr) f <&> \case Nil => Nil; a => Pair a
shrinkFn shr (Sum a b) =
  map (\case Sum Nil Nil => Nil; x => x) $
    (if notNil b then [ Sum a Nil ] else []) ++
    (if notNil a then [ Sum Nil b ] else []) ++
    map (`Sum` b) (shrinkFn shr a) ++
    map (a `Sum`) (shrinkFn shr b)
  where
    notNil : forall a, b. a :-> b -> Bool
    notNil Nil = False
    notNil _   = True
shrinkFn shr (Map f g a) = shrinkFn shr a <&> \case Nil => Nil; x => Map f g x

||| The type for a randomly-generated function
export
data Fn a b = MkFn b (a :-> Cotree b)

export
Show a => Show b => Show (Fn a b) where
  show (MkFn xb xa) = unlines $ (table xa <&> showCase) ++ ["_ -> " ++ show xb] where
    showCase : (a, Cotree b) -> String
    showCase (lhs, rhs) = show lhs ++ " -> " ++ show rhs.value

||| Generates a random function being given a generator of codomain type
|||
||| The generated function is returned in a showable type `Fn a b`.
|||
||| This function takes a co-generator of domain type using `auto`-argument based on the type.
||| This generator is shrinkable. For this, it requires additional `Arg` argument.
export
function : Arg a => Cogen a => Gen b -> Gen (Fn a b)
function @{_} @{cg} gb = [| MkFn gb (genFn $ \a => unCogen @{cg} a gb) |] where

  shrinkTree : Cotree b -> Colist $ Cotree b
  shrinkTree $ MkCotree _ cs = cs

  genFn : (a -> Gen b) -> Gen (a :-> Cotree b)
  genFn g = MkGen $ \sz, sd =>
    unfold (\x => (x, shrinkFn shrinkTree x)) . map (runGen sz sd) $ build g

export
apply : Fn a b -> a -> b
apply (MkFn b f) = maybe b value . apply' f

||| Generates a random function being given a generator of codomain type
|||
||| This generator is shrinkable
|||
||| This is a wrapper of a `function` function.
||| It may be useful sometimes, however, it returnes a non-showable type.
||| To use functions generator in `forAll` in a property, use `function` function.
public export
function' : Arg a => Cogen a => Gen b -> Gen (a -> b)
function' = map apply . function
