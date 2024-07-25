# An Introduction to Hedgehog

The Haskell library [Hedgehog](https://hedgehog.qa/) is a powerful property
based testing framework in the spirit of
[Quickcheck](https://hackage.haskell.org/package/QuickCheck), but with
integrated shrinking and pretty diff printing.

This is an Idris2 port of the Haskell library with some slight adjustments
(and some limitations). Since this is a literate Idris2 file:

```idris
module Docs.Intro

import Data.List
import Data.SOP
import Data.String
import Data.Vect
import Hedgehog

%default total
```

## A First Example
To give a first example of the capabilities of this library,
we verify that reversing a list twice will lead to the original
list. This is - of course - completely pointless in Idris, since
Idris can prove this at compile time. However, we will soon enough
start with some more real-worldish examples.

First, we need a generator for lists. Generators are defined in
module `Hedgehog.Internal.Gen`, which is reexported by the main `Hedgehog`
module.

```idris
charGen : Gen (List Char)
charGen = list (linear 0 30) alphaNum
```

The above defines a generator for random lists of alpha numeric
characters of length up to 30. For numeric values,
we typically define generators in terms of `Range`s (defined in
module `Hedgehog.Internal.Range`). They scale according to a given
`Size` parameter and shrink towards a predefined origin in case
of a failed test.

We can now specify the property we'd like to proof
and verify by calling `check`:

```idris
propReverse : Property
propReverse = property $ do
  xs <- forAll charGen
  xs === reverse (reverse xs)

checkReverse : IO Bool
checkReverse = check propReverse
```

Running this produces the following output:

```repl
>  ✓ <interactive> passed 100 tests.
```

## Property Groups

OK, let's try something (slightly) more realistic. Property
based testing can be useful in Idris when we are dealing with
functions that are not reduced during unification. The behavior
of such functions cannot be verified at compile time. An example
for this are functions `fastPack` and `fastUnpack` from `Data.String`.
We'd like to verify that the two functions do not modify their
input. String generators are derived from the one for lists,
so their definition is very similar:

```idris
unicodeGen : Gen String
unicodeGen = string (linear 0 30) unicode

propertyFastPack : Property
propertyFastPack = property $ do
  s <- forAll unicodeGen
  s === fastPack (fastUnpack s)
```

We could also check that `fastUnpack` and `unpack` yield the
same result:

```idris
propertyFastUnpack : Property
propertyFastUnpack = property $ do
  s <- forAll unicodeGen
  unpack s === fastUnpack s
```

To generate some nice output, we define a property group
and run these tests together:

```idris
checkPack : IO Bool
checkPack =
  checkGroup $
    MkGroup
      "Fast String Functions"
      [ ("fastPack . fastUnpack = id", propertyFastPack)
      , ("unpack = fastUnpack", propertyFastUnpack)
      ]
```

Running this in the REPL results in the following output:

```repl
> ━━━ Fast String Functions ━━━
>   ✓ fastPack . fastUnpack = id passed 100 tests.
>   ✓ unpack = fastUnpack passed 100 tests.
>   ✓ 2 succeeded.
```

## Failing Tests and Shrinking

Next, we will write a property that does not hold:

```idris
propAddInts : Property
propAddInts =
  let int20 := int $ linear 0 20
   in property $ do
        [a,b,c,d] <- forAll $ np [int20,int20,int20,int20]
        (a + b) === (c + d)
```

Before we look at what happens when we check this property,
I'd like to quickly explain the `np` generator.
The Idris version of Hedgehog supports the heterogeneous
sums of products from the [idris2-sop](https://github.com/stefan-hoeck/idris2-sop)
library via generators `np`, `ns`, and `sop`.
These generators work as expected with good out-of-the box
shrinking. It is therefore advisable to use one of these
when generating several unrelated values in parallel.
As an alternative, we could also have used `vect 4 int20`
in this case.

```idris
checkFailing1 : IO Bool
checkFailing1 = checkNamed "propAddInts" propAddInts
```

Running the above results in output similar to this:

```repl
> ✗ propAddInts failed after 7 tests.
>
>   forAll 0 =
>     [ 0 , 0 , 0 , 1 ]
>
>   ━━━ Failed (- lhs) (+ rhs) ━━━
>   - 0
>   + 1
>
>   This failure can be reproduced by running:
>   > recheck 6 (rawStdGen 13575607214039863170 538475183012815285) propAddInts
```

Here, we are informed about the failed test together with a
properly shrunk minimal test case plus the `Size` and
`Seed` required to rerun the failing test.

## The (broken) Gen Monad

There is a (minor, in my opinion) inconsistency between
`Gen`s `Applicative` and `Monad` implementations. This is the
same in the original Hedgehog, and it is not yet sure whether it
is worth fixing by using either a newtype wrapper for `Gen`
or providing an additional named `Applicative` instance.

In order to understand this inconsistency, we will write the
same failing test twice:

```idris
int1000 : Gen Int
int1000 = int $ constant 0 1000

propIntGreaterApp : Property
propIntGreaterApp = property $ do
  [a,b] <- forAll $ vect 2 int1000
  assert (a < b)

propIntGreaterMonad : Property
propIntGreaterMonad = property $ do
  a <- forAll int1000
  b <- forAll int1000
  assert (a < b)

checkIntGreater : IO ()
checkIntGreater =
     checkNamed "propIntGreaterApp" propIntGreaterApp
  *> checkNamed "propIntGreaterMonad" propIntGreaterMonad
  $> ()
```

Both tests fail, but their shrinking behavior is different.
In the first case, we get output similar to the following:

```repl
> ✗ propIntGreaterApp failed after 1 test.
>
>   forAll 0 =
>     [ 0 , 0 ]
>
>   This failure can be reproduced by running:
>   > recheck 0 (rawStdGen 6832087575862183383 12092602541466451199) propIntGreaterApp
```

As can be seen, the failing test is properly shrunk to the minimal
counter example.

In the second case, however, the output is most likely similar to this:

```repl
> ✗ propIntGreaterMonad failed after 4 tests.
>
>   forAll 0 =
>     188
>
>   forAll 1 =
>     0
>
>   This failure can be reproduced by running:
>   > recheck 0 (rawStdGen 9029460602319538061 261492196152102529) propIntGreaterMonad
```

As can be seen, the first value is not properly shrunk to the minimal
counter example. The reason for this is explained in detail in
[this blog post](https://www.well-typed.com/blog/2019/05/integrated-shrinking/).
The important message is: For optimal shrinking, combine generators using
`Gen`s applicative implementation whenever possible.

## Debugging Generators: Classifiers and Test Coverage

It is often useful to make sure that generators behave correctly.
There are several facilities for this. In the most simple case, we
classify generated values according to one or more criteria,
generating some pretty output. The following runs 10000 tests,
putting generated integers into one of five classes.

```idris
propTwice : Property
propTwice =
  withTests 10000 . property $ do
    n <- forAll int1000
    classify "zero" (n == 0)
    classify "one" (n == 1)
    classify "below 10" (n > 1 && n < 10)
    classify "below 100" (n >= 10 && n < 100)
    classify "above 100" (n >= 100)
    (2 * n) === (n + n)

checkTwice : IO Bool
checkTwice = checkNamed "propTwice" propTwice
```

Eventually, the output will look similar to the one below:

```repl
> ✓ propTwice passed 10000 tests.
>   above 100 90.1% ██████████████████··
>   below 10   0.8% ▏···················
>   below 100  8.9% █▊··················
>   one        0.1% ····················
>   zero       0.1% ····················

```

Sometimes, however, we'd like to have stronger guarantees.
In the following example, the test fails if not at least
five percent of the generated values are in the interval [10,100)
or if not at least eighty percent are in the interval [100,1000]:

```idris
propTwice2 : Property
propTwice2 =
  withTests 10000 . property $ do
    n <- forAll int1000
    cover 5 "[10,100)" (n >= 10 && n < 100)
    cover 80 "[100,1000]" (n >= 100)
    (2 * n) === (n + n)

checkTwice2 : IO Bool
checkTwice2 = checkNamed "propTwice2" propTwice2
```

The output will look similar to this:

```repl
> ✓ propTwice2 passed 10000 tests.
>   [10,100)    9.1% █▊·················· ✓  5.0%
>   [100,1000] 89.9% █████████████████▉·· ✓ 80.0%
```

<!-- vi: filetype=idris2:syntax=markdown
-->
