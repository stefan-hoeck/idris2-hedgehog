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
  let seeds = filter (isInfixOf "rawStdGen") outs
  for_ seeds $ footnote . delay

containsEach :
     (checkPrefixOnly : Bool)
  -> (actual, expected : List String)
  -> Bool
containsEach _               []      (_::_)  = False
containsEach checkPrefixOnly (_::_)  []      = checkPrefixOnly
containsEach _               []      []      = True
containsEach checkPrefixOnly (o::os) (i::is) =
  (i `isInfixOf` o) && containsEach checkPrefixOnly os is

doCheck :
     (checkPrefixOnly : Bool)
  -> (expected : String)
  -> (forall m. HasTerminal m => Monad m => m ())
  -> PropertyT ()
doCheck checkPrefixOnly expected checker = do
  let actual = trimDeep $ (>>= lines) $ execWriter $ checker @{StdoutOnly}
  annotateSeedIfNeeded actual
  diff actual (containsEach checkPrefixOnly) (trimDeep $ lines expected)

||| A property checking that Hedgehog being run on a particular property
||| with particular configuration prints expected string.
|||
||| The check passes if every line of Hedgehog's output contains a corresponding
||| line of `expected` string as a substring. Empty lines, leading and traling
||| spaces are ignored in both the `expected` string, and Hedgehog's output.
export
recheckGivenOutput :
     {default False checkPrefixOnly : Bool}
  -> (expected : String)
  -> (prop : Property)
  -> Size
  -> StdGen
  -> Property
recheckGivenOutput expected prop sz sd = property $
  doCheck checkPrefixOnly expected $ recheck sz sd prop

||| A property checking that Hedgehog being run on a default configuration
||| and a random seed prints expected string.
|||
||| The check passes if every line of Hedgehog's output contains a corresponding
||| line of `expected` string as a substring. Empty lines, leading and traling
||| spaces are ignored in both the `expected` string, and Hedgehog's output.
export
checkGivenOutput :
     {default False checkPrefixOnly : Bool}
  -> (expected : String)
  -> (prop : Property)
  -> Property
checkGivenOutput expected prop = property $ do
  initSeed <- forAll anyBits64
  doCheck checkPrefixOnly expected $
    ignore $ check @{ConstSeed $ mkStdGen initSeed} prop
