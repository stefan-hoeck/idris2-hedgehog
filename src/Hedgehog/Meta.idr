||| Facilities for testing Hedgehog using Hedgehog
|||
||| Module contains properties to check how Hedgehog behaves on given properties
module Hedgehog.Meta

import Control.Monad.Identity
import Control.Monad.Writer

import Data.List
import Data.String

import public Hedgehog

%default total

trimDeep : List String -> List String
trimDeep = filter (not . null) . map trim

annotateSeedIfNeeded : List String -> PropertyT ()
annotateSeedIfNeeded outs = do
  let seeds = filter (isInfixOf "MkSeed") outs
  for_ seeds $ footnote . delay

containsEach : List String -> List String -> Bool
containsEach []      (_::_)  = False
containsEach (_::_)  []      = False
containsEach []      []      = True
containsEach (o::os) (i::is) = (i `isInfixOf` o) && containsEach os is

doCheck :
     (expected : String)
  -> (forall m. HasTerminal m => Monad m => m ())
  -> PropertyT ()
doCheck expected checker = do
  let actual = trimDeep $ (>>= lines) $ execWriter $ checker @{StdoutOnly}
  annotateSeedIfNeeded actual
  diff actual containsEach (trimDeep $ lines expected)

||| A property checking that Hedgehog being run on a particular property
||| with particular configuration prints expected string.
|||
||| The check passes if every line of Hedgehog's output contains a corresponding
||| line of `expected` string as a substring. Empty lines, leading and traling
||| spaces are ignored in both the `expected` string, and Hedgehog's output.
export
recheckGivenOutput :
     (expected : String)
  -> (prop : Property)
  -> Size
  -> Seed
  -> Property
recheckGivenOutput expected prop sz sd = property $
  doCheck expected $ recheck @{DefaultConfig} sz sd prop

||| A property checking that Hedgehog being run on a default configuration
||| and a random seed prints expected string.
|||
||| The check passes if every line of Hedgehog's output contains a corresponding
||| line of `expected` string as a substring. Empty lines, leading and traling
||| spaces are ignored in both the `expected` string, and Hedgehog's output.
export
checkGivenOutput : (expected : String) -> (prop : Property) -> Property
checkGivenOutput expected prop = property $ do
  initSeed <- forAll $ integral_ $ constant 0 MaxRobustSmGenNum
  doCheck expected $
    ignore $ check @{Manual $ smGen initSeed} @{DefaultConfig} prop
