module Hedgehog.Internal.Seed

import public System.Random.Pure.StdGen

%default total

public export
0 Seed : Type
Seed = StdGen

||| Describes a context in which some initial seed can be gained
|||
||| In a non-pure context this can rely on some system entropy.
||| In pure contexts this can get a seed from configuration,
||| from a monadic state or from a user at the call-site.
export
interface CanInitSeed m where
  initSMGen : m Seed

||| Initialize 'SMGen' using entropy available on the system (time, ...)
export
HasIO io => CanInitSeed io where
  initSMGen = initStdGen

||| Initialise the seed for any applicative context
||| by the given particular value
export
Manual : Applicative m => Seed -> CanInitSeed m
Manual seed = S where [S] CanInitSeed m where initSMGen = pure seed
