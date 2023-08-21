module Functions.Shrink

import Common

export
simpleFunPrint : Property
simpleFunPrint = checkGivenOutput expected prop where
  prop : Property
  prop = property $ do
    fn <- forAll $ function $ nat $ constant 0 999
    let domain : List Nat =
      [0, 1, 2, 3, 100, 1000, 10000, 100000, 10000000, 100000000]
    let codomain = apply fn <$> domain
    annotate "args: \{show domain}"
    annotate "vals: \{show codomain}"
    assert False -- to print annotations
  expected : String
  expected = """
    ✗ <interactive> failed after
      forAll 0 =
        _ -> 0
      forAll 1 =
        args: [0, 1, 2, 3, 100, 1000, 10000, 100000, 10000000, 100000000]
      forAll 2 =
        vals: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      This failure can be reproduced by running:
        > recheck
    """

export
fancyFunPrint : Property
fancyFunPrint = checkGivenOutput expected prop where
  prop : Property
  prop = property $ do
    fn <- forAll $ function $ nat $ constant 0 999
    let fn = apply fn
    let domain : List Nat =
      [0, 1, 2, 3, 100, 1000, 10000, 100000, 10000000, 100000000]
    let codomain = fn <$> domain
    annotate "args: \{show domain}"
    annotate "vals: \{show codomain}"
    assert (fn 0 == 0)
  expected : String
  expected = """
    ✗ <interactive> failed after
      forAll 0 =
        0 -> 1
        _ -> 0
      forAll 1 =
        args: [0, 1, 2, 3, 100, 1000, 10000, 100000, 10000000, 100000000]
      forAll 2 =
        vals: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      This failure can be reproduced by running:
        > recheck
    """

export
fancyListFunPrint : Property
fancyListFunPrint = checkGivenOutput expected prop where
  prop : Property
  prop = property $ do
    fn <- forAll $ function $ nat $ constant 0 999
    let fn = apply fn
    let domain : List (List Nat) = [[], [0], [1], [0, 1], [1, 0]]
    let codomain = fn <$> domain
    annotate "args: \{show domain}"
    annotate "vals: \{show codomain}"
    assert (fn [1] == 0)
  expected : String
  expected = """
    ✗ <interactive> failed after
      forAll 0 =
        [1] -> 1
        _ -> 0
      forAll 1 =
        args: [[], [0], [1], [0, 1], [1, 0]]
      forAll 2 =
        vals: [0, 0, 1, 0, 0]
      This failure can be reproduced by running:
        > recheck
    """

export
simpleFunPos : Property
simpleFunPos = checkGivenOutput expected prop where
  prop : Property
  prop = property $ do
    natList <- forAll $ list (constant 1 10) $ nat $ constant 0 99
    fn <- forAll $ function $ nat $ constant 100 999
    let newList = map (apply fn) natList
    annotate $ show newList
    assert $ all (>= 100) newList
  expected : String
  expected = """
    ✓ <interactive> passed 100 tests.
    """

export
simpleFunNeg : Property
simpleFunNeg = checkGivenOutput expected prop where
  prop : Property
  prop = property $ do
    fn <- forAll $ function $ nat $ constant 0 999
    n  <- forAll $ nat $ constant 0 1000000000
    assert $ apply fn n >= 100
  expected : String
  expected = """
    ✗ <interactive> failed after

      forAll 0 =
        _ -> 0

      forAll 1 =
        0

      This failure can be reproduced by running:
        > recheck
    """
