module Spec

import Hedgehog

print_a_fun : Property
print_a_fun = property $ do
  fn <- forAll $ function $ nat $ constant 0 999
  let domain : List Nat = [0, 1, 2, 3, 100, 1000, 10000, 100000, 10000000, 100000000]
  let codomain = apply fn <$> domain
  annotate "args: \{show domain}"
  annotate "vals: \{show codomain}"
  assert False -- to print annotations

print_a_fun_fun : Property
print_a_fun_fun = property $ do
  fn <- forAll $ function $ nat $ constant 0 999
  let fn = apply fn
  let domain : List Nat = [0, 1, 2, 3, 100, 1000, 10000, 100000, 10000000, 100000000]
  let codomain = fn <$> domain
  annotate "args: \{show domain}"
  annotate "vals: \{show codomain}"
  assert (fn 0 == 0)

print_a_fun_list_fun : Property
print_a_fun_list_fun = property $ do
  fn <- forAll $ function $ nat $ constant 0 999
  let fn = apply fn
  let domain : List (List Nat) = [[], [0], [1], [0, 1], [1, 0]]
  let codomain = fn <$> domain
  annotate "args: \{show domain}"
  annotate "vals: \{show codomain}"
  assert (fn [1] == 0)

niceFnProp : Property
niceFnProp = property $ do
  natList <- forAll $ list (constant 1 10) $ nat $ constant 0 99
  fn <- forAll $ function $ nat $ constant 100 999
  let newList = map (apply fn) natList
  annotate $ show newList
  assert $ all (>= 100) newList

badFnProp : Property
badFnProp = property $ do
  fn <- forAll $ function $ nat $ constant 0 999
  n  <- forAll $ nat $ constant 0 1000000000
  assert $ apply fn n >= 100

main : IO Unit
main = do
  ignore $ check print_a_fun
  ignore $ check print_a_fun_fun
  ignore $ check print_a_fun_list_fun
  ignore $ check badFnProp
  ignore $ check niceFnProp
