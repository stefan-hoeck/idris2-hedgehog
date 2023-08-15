module Hedgehog.Internal.Function

import Data.Colist
import Data.Cotree

import Hedgehog.Internal.Gen
import Hedgehog.Internal.Range
import Hedgehog.Internal.Seed

%default total

export
interface CoGen a where
  constructor MkCoGen
  unCoGen : a -> Gen b -> Gen b

export
Cast a Nat => CoGen a where
  unCoGen = variant . cast

||| Generates a random function being given a generator of codomain type
|||
||| This function takes a co-generator of domain type using `auto`-argument based on the type.
||| This generator does not shrink.
export
function_ : CoGen a => Gen b -> Gen (a -> b)
function_ @{cg} bg = MkGen $ \sz, sd => singleton $ \x => value $ runGen sz sd $ unCoGen @{cg} x bg
