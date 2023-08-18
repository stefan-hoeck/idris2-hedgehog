module Spec

import Hedgehog

[FnStub] Show (Nat -> Nat) where
  show _ = "<fn>"

print_a_fun_ : Property
print_a_fun_ = property $ do
  fn <- forAll @{FnStub} $ function_ $ nat $ constant 0 999
  let domain : List _ := [0, 1, 2, 3, 100, 1000, 10000, 100000, 10000000, 100000000]
  let codomain = fn <$> domain
  annotate "args: \{show domain}"
  annotate "vals: \{show codomain}"
  assert False -- to print annotations

badFn_Prop : Property
badFn_Prop = property $ do
  fn <- forAll @{FnStub} $ function_ $ nat $ constant 0 999
  n  <- forAll $ nat $ constant 0 1000000000
  assert $ fn n >= 100

niceFn_Prop : Property
niceFn_Prop = property $ do
  natList <- forAll $ list (constant 1 10) $ nat $ constant 0 99
  fn <- forAll @{FnStub} $ function_ $ nat $ constant 100 999
  let newList = map fn natList
  annotate $ show newList
  assert $ all (>= 100) newList

main : IO Unit
main = do
  recheck 4 (smGen 100) print_a_fun_
  recheck 5 (MkSeed 79087587307652701 813149745268981157) badFn_Prop
  ignore $ check niceFn_Prop
