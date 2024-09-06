module Basic

import Data.List.Quantifiers
import Hedgehog.Meta

%default total

namespace Assert

  export
  simplePosAssert : Property
  simplePosAssert = checkGivenOutput expected prop

    where
      prop : Property
      prop = property $ assert $ 4 == 4
      expected : String
      expected = "✓ <interactive> passed 100 tests."

  export
  simpleNegAssert : Property
  simpleNegAssert = checkGivenOutput expected prop

    where
      prop : Property
      prop = property $ assert $ 5 == 4
      expected : String
      expected =
        """
        ✗ <interactive> failed after 1 test.
        This failure can be reproduced by running:
          > recheck
        """

namespace NoShrinkGen

  export
  simplePosGeneration : Property
  simplePosGeneration = checkGivenOutput expected prop

    where
      prop : Property
      prop = property $ do
        n <- forAll $ integral_ $ constant 1 999
        let _ : Integer := n
        assert $ n >= 1 && n <= 999
      expected : String
      expected = "✓ <interactive> passed 100 tests."

  export
  simpleNegGeneration : Property
  simpleNegGeneration =
    recheckGivenOutput {checkPrefixOnly=True} expected prop 22 seed

    where
      seed : StdGen
      seed = rawStdGen 16892461356434811776 15079690130578850725
      prop : Property
      prop = property $ do
        n <- forAll $ integral_ $ constant 1 999
        let _ : Integer := n
        assert $ n >= 20
      expected : String
      expected =
        """
        ✗ <interactive> failed after 1 test.
        forAll 0 =
          17
        This failure can be reproduced by running:
          > recheck
        """

  export
  forallsPosGeneration : Property
  forallsPosGeneration = checkGivenOutput expected prop

    where
      prop : Property
      prop = property $ do
        let g = integral_ $ constant 1 999
        [n, m] <- forAlls [g, g]
        let _ : Integer := n
        let _ : Integer := m
        assert $ n >= 1 && n <= 999
        assert $ m >= 1 && m <= 999
      expected : String
      expected = "✓ <interactive> passed 100 tests."

  export
  forallsNegGeneration : Property
  forallsNegGeneration =
    recheckGivenOutput {checkPrefixOnly=True} expected prop 7 seed

    where
      seed : StdGen
      seed = rawStdGen 17390955263926595516 17173145979079339501
      prop : Property
      prop = property $ do
        let g = integral_ $ constant 1 999
        [n, m] <- forAlls [g, g]
        let _ : Integer := n
        let _ : Integer := m
        assert $ n >= 20 && m >= 20
      expected : String
      expected =
        """
        ✗ <interactive> failed after 1 test.
        forAll 0 =
          5
        forAll 1 =
          798
        This failure can be reproduced by running:
          > recheck
        """

namespace ShrinkGen

  export
  simplePosGeneration : Property
  simplePosGeneration = checkGivenOutput expected prop

    where
      prop : Property
      prop = property $ do
        n <- forAll $ integral $ constant 1 999
        let _ : Integer := n
        assert $ n >= 1 && n <= 999
      expected : String
      expected = "✓ <interactive> passed 100 tests."

  export
  simpleNegGeneration : Property
  simpleNegGeneration =
    recheckGivenOutput {checkPrefixOnly=True} expected prop 22 seed

    where
      seed : StdGen
      seed = rawStdGen 16892461356434811776 15079690130578850725

      prop : Property
      prop = property $ do
        n <- forAll $ integral $ constant 1 999
        let _ : Integer := n
        assert $ n >= 20
      expected : String
      expected =
        """
        ✗ <interactive> failed after 1 test.
        forAll 0 =
          1
        This failure can be reproduced by running:
          > recheck
        """

  export
  forallsPosGeneration : Property
  forallsPosGeneration = checkGivenOutput expected prop

    where
      prop : Property
      prop = property $ do
        let g = integral $ constant 1 999
        [n, m, k] <- forAlls [g, g, g]
        let _ : Integer := n
        let _ : Integer := m
        let _ : Integer := k
        assert $ n >= 1 && n <= 999
        assert $ m >= 1 && m <= 999
        assert $ k >= 1 && k <= 999
      expected : String
      expected = "✓ <interactive> passed 100 tests."

  export
  forallsNegGeneration : Property
  forallsNegGeneration =
    recheckGivenOutput {checkPrefixOnly=True} expected prop 7 seed

    where
      seed : StdGen
      seed = rawStdGen 17390955263926595516 17173145979079339501

      prop : Property
      prop = property $ do
        let g = integral $ constant 1 999
        [n, m, k] <- forAlls [g, g, g]
        let _ : Integer := n
        let _ : Integer := m
        let _ : Integer := k
        assert $ n >= 20
        assert $ m >= 20
        assert $ k >= 20
      expected : String
      expected =
        """
        ✗ <interactive> failed after 1 test.
        forAll 0 =
          1
        forAll 1 =
          1
        forAll 2 =
          1
        This failure can be reproduced by running:
          > recheck
        """
