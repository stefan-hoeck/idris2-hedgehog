module Spec

import Data.List1
import Data.Vect

import Hedgehog

import Language.Reflection
import Language.Reflection.Derive
import Language.Reflection.Syntax
import Language.Reflection.Types

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

print_z_fun : Property
print_z_fun = property $ do
  fn <- forAllWith (const "<fn>") $ dargfun_ {b = \n => Z n String} $ nat $ constant 0 100
  annotate "fn Z1 = \{show $ fn Z1}"
  annotate "fn (Z2 (YA \"foo\") [Z1]) = \{show $ fn (Z2 (YA "foo") [Z1])}"
  annotate "fn (Z2 (YA \"lala\") [Z1]) = \{show $ fn (Z2 (YA "lala") [Z1])}"
  assert $ fn Z1 == 0 || fn (Z2 (YA "lala") [Z1]) == 0

main : IO Unit
main = do
  recheck 0 (MkSeed 15646808624686066109 7037936686351694591) print_z_fun
