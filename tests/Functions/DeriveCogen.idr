module Functions.DeriveCogen

import Derive.Cogen

import Hedgehog.Meta

%language ElabReflection

data X = A | B Nat | C String

%runElab derive "X" [Cogen]

data Y a = YA a | YB X | YC (Y a) (Y Nat)

%runElab derive "Y" [Cogen]

%runElab derivePattern "Vect" [I, P] [Cogen]

data Z : Nat -> Type -> Type where
  Z1 : Z 1 a
  Z2 : Y a -> Vect n (Z n a) -> Z (S n) a

%runElab derivePattern "Z" [I, P] [Cogen]

export
printZFun : Property
printZFun = recheckGivenOutput expected prop 0 seed where
  seed : Seed
  seed = MkSeed 15646808624686066109 7037936686351694591
  prop : Property
  prop = property $ do
    fn <-
      forAllWith (const "<fn>") $
        dargfun_ {b = \n => Z n String} $ nat $ constant 0 100
    annotate "fn Z1 = \{show $ fn Z1}"
    annotate "fn (Z2 (YA \"foo\") [Z1]) = \{show $ fn (Z2 (YA "foo") [Z1])}"
    annotate "fn (Z2 (YA \"lala\") [Z1]) = \{show $ fn (Z2 (YA "lala") [Z1])}"
    assert $ fn Z1 == 0 || fn (Z2 (YA "lala") [Z1]) == 0
  expected : String
  expected =
    """
    ✗ <interactive> failed after 1 test.
      forAll 0 =
        <fn>
      forAll 1 =
        fn Z1 = 89
      forAll 2 =
        fn (Z2 (YA "foo") [Z1]) = 49
      forAll 3 =
        fn (Z2 (YA "lala") [Z1]) = 56
      This failure can be reproduced by running:
        > recheck
    """
