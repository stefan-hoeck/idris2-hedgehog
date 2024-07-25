module Hedgehog.Internal.Function

import Data.Colist
import Data.Cotree
import Data.Either
import Data.Nat
import Data.String

import Hedgehog.Internal.Gen
import Hedgehog.Internal.Range
import Hedgehog.Internal.Util

import System.Random.Pure.StdGen

%default total

||| An interface for co-generators, somewhat an inverse of a generator
|||
||| Generators, roughly, using a random seed produce a value of a certain type.
||| Co-generators conversly, roughtly speaking, produce a random seed using
||| a value of a certain type.
|||
||| Due to technical properties of a seed type, instead of generating a seed
||| value from stratch we perturb some existing value.
||| Thus, a function of this interface produces a `StdGen -> StdGen` function
||| being given a value of an appropriate type.
|||
||| In some understanding, co-generators classify values of a given type, which
||| allow to tune generators of other types.
||| This gives an ability to generate functions of type `a -> b` being given
||| a generator of type `b` and a co-generator of type `a`.
||| Having a value of type `a`, co-generator can deterministically tune
||| the generator of type `b` by perturbing a random seed that is used by the
||| generator and use its output as an output for a function.
public export
interface Cogen a where
  constructor MkCogen
  perturb : a -> StdGen -> StdGen

||| This function perturbs the given seed both with `variant` and `split`.
|||
||| This function is meant to be used between successive perturbations
||| of different arguments of the same constructor.
|||
||| It is designed to not commute when perturbation actions of a constructor's
||| arguments do the same.
||| Consider if `Cogen` interface is implemented for `Maybe a` and `Bool`
||| in the following way:
|||
||| ```
||| Cogen a => Cogen (Maybe a) where
|||   perturb (Just x) = perturb x . variant 0
|||   perturb Nothing  = variant 1
|||
||| Cogen Bool where
|||   perturb False = variant 0
|||   perturb True  = variant 1
||| ```
|||
||| In this case values `Nothing` and `Just True` would give the same
||| perturbation to a seed, which is not optimal. Insertion of `shiftArg`
||| before each call for `perturb` of a constructor argument would give
||| different perturbations for different combinations of constructors and
||| their arguments (unless you are very unlucky).
||| Combination of both `variant` and `split` in the `shiftArg` function
||| gives relative independence on how `perturb` of a constructor argument
||| type is implemented.
export
shiftArg : StdGen -> StdGen
shiftArg = variant 33 . snd . split . variant 31

||| Changes random distribution of a generator of type `b`
||| based on a value of type `a`
|||
||| Change of distribution is done by a perturbation of a random seed,
||| which is based on a `Cogen` implementation for the type `a`.
export
cogen : Cogen a => a -> Gen b -> Gen b
cogen x g = MkGen $ \sz, sd => unGen g sz $ perturb x sd

export
Cogen Unit where
  perturb _ = id

export
Cogen (Equal x y) where
  perturb Refl = id

export
Cogen Bool where
  perturb True  = variant 0
  perturb False = variant 1

export
Cogen Nat where
  perturb = variant

export
Cogen Integer where
  perturb = variant . cast

export
Cogen Bits64 where
  perturb = variant . cast

export
Cogen Bits16 where perturb = variant . cast

export
Cogen Bits8 where perturb = variant . cast

export
Cogen Int64 where perturb = variant . cast

export
Cogen Int16 where perturb = variant . cast

export
Cogen Int8 where perturb = variant . cast

export
Cogen Int where perturb = variant . cast

export
Cogen Char where perturb = variant . cast

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

export
Cogen String where
  perturb = perturb . fastUnpack

||| Generates a random function being given a generator of codomain type
|||
||| This function takes a co-generator of domain type using `auto`-argument
||| based on the type.
||| This generator does not shrink.
|||
||| Notice that this generator returns a non-showable value (unless you invent
||| your own implementation).
||| If you need a showable function, you have to use a shrinkable version,
||| which requires more strict implementation on the domain type.
export
function_ : Cogen a => Gen b -> Gen (a -> b)
function_ bg =
  MkGen $ \sz, sd => singleton $ \x => value $ unGen bg sz $ perturb x sd

||| Generates a random dependently typed function being given a generator
||| of codomain type family
|||
||| This function takes a co-generator of domain type using `auto`-argument
||| based on the type.
||| This generator does not shrink.
|||
||| Notice that this generator returns a non-showable value (unless you invent
||| your own implementation).
export
depfun_ :
     {auto _ : Cogen a}
  -> {0 b : a -> Type}
  -> ((x : a) -> Gen $ b x)
  -> Gen ((x : a) -> b x)
depfun_ bg =
  MkGen $ \sz, sd => singleton $ \x => value $ unGen (bg x) sz $ perturb x sd

||| Generates a random function with dependently typed domain being given a
||| generator of codomain type
|||
||| This function takes a co-generator of domain type family using
||| `auto`-argument based on the type.
||| This generator does not shrink.
|||
||| Notice that this generator returns a non-showable value (unless you invent
||| your own implementation).
export
dargfun_ :
     {0 b    : a -> Type}
  -> {auto _ : {0 x : a} -> Cogen (b x)}
  -> Gen c
  -> Gen ({0 x : a} -> b x -> c)
dargfun_ bg =
  MkGen $ \sz, sd => singleton $ \x => value $ unGen bg sz $ perturb x sd

||| Generates a random dependently typed function with dependently typed domain
||| being given a generator of codomain type family
|||
||| This function takes a co-generator of domain type family using
||| `auto`-argument based on the type.
||| This generator does not shrink.
|||
||| Notice that this generator returns a non-showable value (unless you invent
||| your own implementation).
export
dargdepfun_ :
     {0 b : a -> Type}
  -> {0 c : {0 x : a} -> b x -> Type}
  -> {auto _ : {0 x : a} -> Cogen (b x)}
  -> ({0 x : a} -> (y : b x) -> Gen (c y))
  -> Gen ({0 x : a} -> (y : b x) -> c y)
dargdepfun_ bg =
  MkGen $ \sz, sd => singleton $ \x => value $ unGen (bg x) sz $ perturb x sd

----------------------------
--- Shrinkable functions ---
----------------------------

-- Claessen, K. Shrinking and showing functions:(functional pearl).
-- In ACM SIGPLAN Notices (Vol. 47, No. 12, pp. 73-80). ACM. 2012, September

export infixr 5 :->

||| A type of reified partial functions that can be represented isomorphic
||| to a function defined by pattern matching of an ADT
||| or any type that *can* implement `Generic` (but does not have to).
|||
||| This type describes internal structure of such functions,
||| e.g. storing separately "vertical" and "horizontal" matching,
||| thus allowing to inspect, modify and simplify them,
||| for example, for showing and shrinking.
public export
data (:->) : Type -> Type -> Type where
  FUnit : c -> () :-> c
  FNil  : a :-> c
  FPair : Lazy (a :-> b :-> c) -> (a, b) :-> c
  FSum  : Lazy (a :-> c) -> Lazy (b :-> c) -> Either a b :-> c
  FMap  : (a -> b) -> (b -> a) -> Lazy (b :-> c) -> a :-> c

export
Functor ((:->) a) where
  map f $ FUnit c    = FUnit $ f c
  map _ $ FNil       = FNil
  map f $ FPair a    = FPair $ map (assert_total $ map f) a
  map f $ FSum a b   = FSum (map f a) (map f b)
  map f $ FMap a b c = FMap a b $ map f c

table : a :-> c -> List (a, c)
table (FUnit c) = [((), c)]
table FNil      = []
table (FPair f) = do
  (a, bc) <- table f
  (b, c) <- assert_total table bc
  pure ((a, b), c)
table (FSum a b) =
     [(Left x, c)  | (x, c) <- table a]
  ++ [(Right x, c) | (x, c) <- table b]
table (FMap _ g a) = mapFst g <$> table a

public export
interface Cogen a => ShrCogen a where
  constructor MkShrCogen
  build : (a -> c) -> a :-> c

export
ShrCogen Void where
  build _ = FNil

export
ShrCogen Unit where
  build f = FUnit $ f ()

export
ShrCogen a => ShrCogen b => ShrCogen (a, b) where
  build f = FPair $ build $ \a => build $ \b => f (a, b)

export
ShrCogen a => ShrCogen b => ShrCogen (Either a b) where
  build f = FSum (build $ f . Left) (build $ f . Right)

||| Implements `build` function for a type through isomorphism
||| to a type that implements `ShrCogen`
|||
||| Notice that `via f g` will only be well-behaved if
||| `g . f` and `f . g` are both identity functions.
export
via : ShrCogen b => (a -> b) -> (b -> a) -> (a -> c) -> a :-> c
via a b f = FMap a b $ build $ f . b

export
ShrCogen a => ShrCogen (Maybe a) where
  build = via (maybeToEither ()) eitherToMaybe

export
ShrCogen Bool where
  build = via toEither fromEither

    where
      toEither : Bool -> Either Unit Unit
      toEither True  = Left ()
      toEither False = Right ()
      fromEither : Either Unit Unit -> Bool
      fromEither $ Left ()  = True
      fromEither $ Right () = False

export
ShrCogen a => ShrCogen (List a) where
  build = assert_total via toEither fromEither

    where
      toEither : List a -> Either Unit (a, List a)
      toEither []      = Left ()
      toEither (x::xs) = Right (x, xs)
      fromEither : Either Unit (a, List a) -> List a
      fromEither (Left ())       = []
      fromEither (Right (x, xs)) = x::xs

export
ShrCogen (Equal x x) where
  build = via (const ()) (const Refl)

export
ShrCogen Integer where
  build = via toBits fromBits

    where
      toBits : Integer -> (Bool, List Bool)
      toBits n = if n >= 0 then (True, go [] n) else (False, go [] $ -n - 1)

        where
          go : List Bool -> Integer -> List Bool
          go bits x =
            if x == 0
              then bits
              else go ((mod x 2 == 1) :: bits) (assert_smaller x $ div x 2)

      fromBits : (Bool, List Bool) -> Integer
      fromBits (sign, bits) = do
        let body = foldl (\acc, b => acc * the Integer 2 + if b then 1 else 0) 0 bits
        if sign then body else negate $ body + 1

export
ShrCogen Nat where build = via {b=Integer} cast cast

export
ShrCogen Int where build = via {b=Integer} cast cast

export
ShrCogen Int8 where build = via {b=Integer} cast cast

export
ShrCogen Int16 where build = via {b=Integer} cast cast

export
ShrCogen Int64 where build = via {b=Integer} cast cast

export
ShrCogen Bits8 where build = via {b=Nat} cast cast

export
ShrCogen Bits16 where build = via {b=Nat} cast cast

export
ShrCogen Bits64 where build = via {b=Nat} cast cast

export
ShrCogen Char where build = via {b=Nat} cast cast

export
ShrCogen String where build = via fastUnpack fastPack

apply' : a :-> b -> a -> Maybe b
apply' (FUnit c)    ()        = Just c
apply' FNil         _         = Nothing
apply' (FPair f)    (a, b)    = assert_total $ apply' !(apply' f a) b
apply' (FSum f _)   (Left a)  = apply' f a
apply' (FSum _ g)   (Right a) = apply' g a
apply' (FMap f _ g) a         = apply' g (f a)

shrinkFn : (b -> Inf (Colist b)) -> a :-> b -> Colist $ a :-> b
shrinkFn shr (FUnit a)  = FUnit <$> shr a
shrinkFn _   FNil       = []
shrinkFn shr (FPair f)  =
  shrinkFn (delay . assert_total (shrinkFn shr)) f <&>
    \case FNil => FNil; a => FPair a
shrinkFn shr (FSum a b) =
  map (\case FSum FNil FNil => FNil; x => x) $
    (if notFNil b then [ FSum a FNil ] else []) ++
    (if notFNil a then [ FSum FNil b ] else []) ++
    map (`FSum` b) (shrinkFn shr a) ++
    map (a `FSum`) (shrinkFn shr b)

  where
    (++) : forall a. Colist a -> Inf (Colist a) -> Colist a
    []      ++ ys = ys
    (x::xs) ++ ys = x :: (xs ++ ys)

    notFNil : forall a, b. a :-> b -> Bool
    notFNil FNil = False
    notFNil _   = True
shrinkFn shr (FMap f g a) =
  shrinkFn shr a <&> \case FNil => FNil; x => FMap f g x

||| The type for a total randomly-generated function
export
data Fn a b = MkFn b (a :-> Cotree b)

export
Show a => Show b => Show (Fn a b) where
  show (MkFn xb xa) = unlines $ (table xa <&> showCase) ++ ["_ -> " ++ show xb]

    where
      showCase : (a, Cotree b) -> String
      showCase (lhs, rhs) = show lhs ++ " -> " ++ show rhs.value

||| Generates a random function being given a generator of codomain type
|||
||| The generated function is returned in a showable type `Fn a b`.
|||
||| This function takes a co-generator of domain type using `auto`-argument
||| based on the type.
||| This generator is shrinkable. For this, it requires additional `Arg`
||| argument.
export
function : ShrCogen a => Gen b -> Gen (Fn a b)
function gb = [| MkFn gb (genFn $ \a => cogen a gb) |]

  where
    genFn : (a -> Gen b) -> Gen (a :-> Cotree b)
    genFn g = MkGen $ \sz, sd =>
      iterate (shrinkFn forest) . map (runGen sz sd) $ build g

||| Coverts a showable randomly generated function to an actual function
export
apply : Fn a b -> a -> b
apply (MkFn b f) = maybe b value . apply' f

||| Generates a random function being given a generator of codomain type
|||
||| This generator is shrinkable
|||
||| This is a wrapper of a `function` generator.
||| It may be useful sometimes, however, it returnes a non-showable type.
||| To use functions generator in `forAll` in a property, use `function`
||| generator.
public export
function' : ShrCogen a => Gen b -> Gen (a -> b)
function' = map apply . function
