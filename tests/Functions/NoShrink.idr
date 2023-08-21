module Functions.NoShrink

import Common

[FnStub] Show (Nat -> Nat) where
  show _ = "<fn>"

export
simpleFunPrint : Property
simpleFunPrint = recheckGivenOutput expected prop 4 (smGen 100) where
  prop : Property
  prop = property $ do
    fn <- forAll @{FnStub} $ function_ $ nat $ constant 0 999
    let domain : List _ :=
      [0, 1, 2, 3, 100, 1000, 10000, 100000, 10000000, 100000000]
    let codomain = fn <$> domain
    annotate "args: \{show domain}"
    annotate "vals: \{show codomain}"
    assert False -- to print annotations
  expected : String
  expected = """
    ✗ <interactive> failed after 1 test.
      forAll 0 =
        <fn>
      forAll 1 =
        args: [0, 1, 2, 3, 100, 1000, 10000, 100000, 10000000, 100000000]
      forAll 2 =
        vals: [617, 81, 970, 65, 17, 450, 448, 133, 410, 791]
      This failure can be reproduced by running:
        > recheck
    """

export
simpleFunNeg : Property
simpleFunNeg = recheckGivenOutput expected prop 26 seed where
  seed : Seed
  seed = MkSeed 18147077199939086501 16052916774213148059
  prop : Property
  prop = property $ do
    fn <- forAll @{FnStub} $ function_ $ nat $ constant 0 999
    n  <- forAll $ nat $ constant 0 1000000000
    assert $ fn n >= 100
  expected : String
  expected = """
    ✗ <interactive> failed after 1 test.
      forAll 0 =
        <fn>
      forAll 1 =
        223554967
      This failure can be reproduced by running:
        > recheck
    """

export
simpleFunPos : Property
simpleFunPos = checkGivenOutput expected prop where
  prop : Property
  prop = property $ do
    natList <- forAll $ list (constant 1 10) $ nat $ constant 0 99
    fn <- forAll @{FnStub} $ function_ $ nat $ constant 100 999
    let newList = map fn natList
    annotate $ show newList
    assert $ all (>= 100) newList
  expected : String
  expected = """
    ✓ <interactive> passed 100 tests.
    """
