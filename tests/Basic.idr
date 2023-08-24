module Basic

import Common

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
  simpleNegGeneration = recheckGivenOutput expected prop 22 seed

    where
      seed : Seed
      seed = MkSeed 16892461356434811776 15079690130578850725
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
  simpleNegGeneration = recheckGivenOutput expected prop 22 seed

    where
      seed : Seed
      seed = MkSeed 16892461356434811776 15079690130578850725

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
