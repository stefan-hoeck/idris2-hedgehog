module Hedgehog.Internal.Function

import Data.Colist
import Data.Cotree
import Data.Either
import Data.String

import Hedgehog.Internal.Gen
import Hedgehog.Internal.Range
import Hedgehog.Internal.Seed

%default total

export
interface Cogen a where
  constructor MkCogen
  perturb : a -> Seed -> Seed

||| This function is meant to be used between successive perturbations is different arguments of the same constructor
export
shiftArg : Seed -> Seed
shiftArg = variant 33 . snd . split . variant 31

export
cogen : Cogen a => a -> Gen b -> Gen b
cogen x g = MkGen $ \sz, sd => unGen g sz $ perturb x sd

export
Cogen Unit where
  perturb _ = id

export
Cogen Bool where
  perturb True  = variant 0
  perturb False = variant 1

export
Cogen Nat where
  perturb = variant . cast

export
Cogen Char where
  perturb = variant . cast

export
Cogen Void where
  perturb _ impossible

export
Cogen a => Cogen b => Cogen (a, b) where
  perturb (x, y) = perturb x . shiftArg . perturb y . shiftArg

export
Cogen a => Cogen b => Cogen (Either a b) where
  perturb $ Left  x = perturb x . shiftArg . variant 0
  perturb $ Right y = perturb y . shiftArg . variant 1

export
Cogen a => Cogen (Maybe a) where
  perturb Nothing  = variant 0
  perturb (Just x) = perturb x . shiftArg . variant 1

export
Cogen a => Cogen (List a) where
  perturb []      = variant 0
  perturb (x::xs) = perturb xs . shiftArg . perturb x . shiftArg . variant 1

Integral a => Neg a => Ord a => Cast a (Bool, List Bool) where
  cast n = if n >= 0 then (True, go [] n) else (False, go [] $ -n - 1) where
    go : List Bool -> a -> List Bool
    go bits x = if x == 0 then bits else go ((mod x 2 == 1) :: bits) (assert_smaller x $ div x 2)

Integral a => Neg a => Cast (Bool, List Bool) a where
  cast (sign, bits) = do
    let body = foldl (\acc, b => acc * 2 + if b then 1 else 0) (the a 0) bits
    if sign then body else negate $ body + 1

export
Integral a => Neg a => Ord a => Cogen a where
  perturb = perturb . cast {to=(Bool, List Bool)}

export
Cogen String where
  perturb = perturb . fastUnpack

||| Generates a random function being given a generator of codomain type
|||
||| This function takes a co-generator of domain type using `auto`-argument based on the type.
||| This generator does not shrink.
||| Notice that this generator returns a non-showable value (unless you invent your own implementation).
export
function_ : Cogen a => Gen b -> Gen (a -> b)
function_ @{cg} bg = MkGen $ \sz, sd => singleton $ \x => value $ unGen bg sz $ perturb x sd

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
  Pair : Lazy (a :-> b :-> c) -> (a, b) :-> c
  Sum  : Lazy (a :-> c) -> Lazy (b :-> c) -> Either a b :-> c
  Map  : (a -> b) -> (b -> a) -> Lazy (b :-> c) -> a :-> c

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
interface Cogen a => ShrCogen a where
  build : (a -> c) -> a :-> c

export
ShrCogen Void where
  build _ = Nil

export
ShrCogen Unit where
  build f = Unit $ f ()

export
ShrCogen a => ShrCogen b => ShrCogen (a, b) where
  build f = Pair $ build $ \a => build $ \b => f (a, b)

export
ShrCogen a => ShrCogen b => ShrCogen (Either a b) where
  build f = Sum (build $ f . Left) (build $ f . Right)

-- Note: `via f g` will only be well-behaved if `g . f` and `f . g` are both identity functions.
via : ShrCogen b => (a -> b) -> (b -> a) -> (a -> c) -> a :-> c
via a b f = Map a b $ build $ f . b

export
ShrCogen a => ShrCogen (Maybe a) where
  build = via (maybeToEither ()) eitherToMaybe

export
ShrCogen Bool where
  build = via toEither fromEither where
    toEither : Bool -> Either Unit Unit
    toEither True  = Left ()
    toEither False = Right ()
    fromEither : Either Unit Unit -> Bool
    fromEither $ Left ()  = True
    fromEither $ Right () = False

export
ShrCogen a => ShrCogen (List a) where
  build = assert_total via toEither fromEither where
    toEither : List a -> Either Unit (a, List a)
    toEither []      = Left ()
    toEither (x::xs) = Right (x, xs)
    fromEither : Either Unit (a, List a) -> List a
    fromEither (Left ())       = []
    fromEither (Right (x, xs)) = x::xs

export
Integral a => Neg a => Ord a => ShrCogen a where
  build = via {b=(Bool, List Bool)} cast cast

export
ShrCogen Nat where
  build = via {b=Integer} cast cast

export
ShrCogen Char where
  build = via {b=Integer} cast cast

export
ShrCogen String where
  build = via fastUnpack fastPack

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
function : ShrCogen a => Gen b -> Gen (Fn a b)
function gb = [| MkFn gb (genFn $ \a => cogen a gb) |] where

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
||| This is a wrapper of a `function` generator.
||| It may be useful sometimes, however, it returnes a non-showable type.
||| To use functions generator in `forAll` in a property, use `function` generator.
public export
function' : ShrCogen a => Gen b -> Gen (a -> b)
function' = map apply . function
