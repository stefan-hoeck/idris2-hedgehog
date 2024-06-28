module Coverage

import Hedgehog.Meta

%default total

export
simpleCoverage : Property
simpleCoverage = checkGivenOutput expected prop

  where
    prop : Property
    prop = verifiedTermination $ property $ do
      n <- forAll $ integral $ constantFrom 0 (-100) 100
      cover 30 "positive" $ n > 0
      cover 30 "negative" $ n < 0

    expected : String
    expected = """
      ✓ <interactive> passed
      30.0%
      30.0%
      """

failing "Can't find an implementation for So"
  badSimpleCoverage : Property
  badSimpleCoverage = checkGivenOutput expected prop

    where
      prop : Property
      prop = verifiedTermination $ property $ do
        n <- forAll $ integral $ constantFrom 0 (-100) 100
        cover 45 "positive" $ n > 0
        cover 120 "negative" $ n < 0 -- too big value for percentage

      expected : String
      expected = """
        ✓ <interactive> passed
        30.0%
        30.0%
        """

