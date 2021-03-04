## An Introduction to Hedgehog

The Haskell library [Hedgehog](https://hedgehog.qa/) is a powerful property
based testing framework in the spirit of
[Quickcheck](https://hackage.haskell.org/package/QuickCheck), but with
integrated shrinking and pretty diff printing.

This is an Idris2 port of the Haskell library with some slight adjustments.
Since this is a literate Idris2 file:

```idris
module Doc.Intro

import Data.List
import Data.String
import Hedgehog
```

### A Frist Example Test
To give a first example of the capabilities of this library,
we verify the reversing a list twice will lead to the original
list. This is - of course - completely pointless in Idris, since
it can be proven at compile time. However, we will soon enough
start with some more real-worldish examples.

First, we need some generator for lists. These are defined in
module `Hedgehog.Internal.Gen`, which is reexported by the main `Hedgehog`
module.

```idris
charGen : Gen (List Char)
charGen = list (linear 0 30) alphaNum
```

The above defines a generator for random lists of alpha numeric
characters whose length is in the range [0,30]. For numeric values,
we typically define generators in terms of `Range`s (defined in
module `Hedgehog.Internal.Range`). They scale according to a given
`Size` paramter and shrink towards a predefined origin in case
of a failed test.

We can now specify the property we'd like to proof:

```idris
propReverse : Property
propReverse = property $ do xs <- forAll charGen
                            xs === reverse (reverse xs)
```

We are now ready to verify this property by calling `check`:

```idris
checkReverse : IO Bool
checkReverse = check propReverse
```

Running this, produces the following output:

```
>  ✓ <interactive> passed 100 tests.
```

### Failing Tests and Shrinking

OK, let's try something (slightly) more realistic. Property
based testing can be useful in Idris when we are dealing with
functions that are not reduced during unification. An example
for this are functions `fastPack` and `fastUnpack` from `Data.String`.
We'd like to verify, that the two functions to not modify their
input. String generators are derived from the one for `List`s,
so their definition is very similar:

```idris
unicodeGen : Gen String
unicodeGen = string (linear 0 30) unicode

propertyFastPack : Property
propertyFastPack = property $ do s <- forAll unicodeGen
                                 s === fastPack (fastUnpack s)
```

We could also check that `fastUnpack` and `unpack` yield the
same result:

```idris
propertyFastUnpack : Property
propertyFastUnpack = property $ do s <- forAll unicodeGen
                                   unpack s === fastUnpack s
```

To generate some nice output, we define a property group
and run these tests together:

```idris
checkPack : IO Bool
checkPack = checkGroup $
              MkGroup "Fast String Functions"
                      [ ("fastPack . fastUnpack = id", propertyFastPack)
                      , ("unpack = fastUnpack", propertyFastUnpack)
                      ]
```

Running this in the REPL results in the following output:

```
> ━━━ Fast String Functions ━━━
>   ✓ fastPack . fastUnpack = id passed 100 tests.
>   ✓ unpack = fastUnpack passed 100 tests.
>   ✓ 2 succeeded.
```
