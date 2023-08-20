module Common

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

export
recheckGivenOutput :
     (expected : String)
  -> (prop : Property)
  -> Size
  -> Seed
  -> Property
recheckGivenOutput expected prop sz sd = property $
  doCheck expected $ recheck @{DefaultConfig} sz sd prop

export
checkGivenOutput : (expected : String) -> (prop : Property) -> Property
checkGivenOutput expected prop = property $ do
  initSeed <- forAll $ integral_ $ constant 0 MaxRobustSmGenNum
  doCheck expected $
    ignore $ check @{DefaultConfig} @{Manual $ smGen initSeed} prop
