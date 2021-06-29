module Hedgehog.Internal.Options

import Data.String
import Decidable.Equality
import Hedgehog.Internal.Property
import System.Console.GetOpt

public export
data NumTest = Relaxed TestLimit | Forced TestLimit

public export
record Config where
  constructor MkConfig
  printHelp  : Bool
  numTests   : Maybe NumTest
  numShrinks : Maybe ShrinkLimit
  confidence : Maybe Confidence

export
init : Config
init = MkConfig False Nothing Nothing Nothing

parseNat : String -> Either (List String) Nat
parseNat s =
  maybe (Left [#"Not a natural number: \#{s}"#]) Right $ parsePositive s

toConfidence : Nat -> Either (List String) Confidence
toConfidence n =
  let c = cast {to = Bits64} n
   in case decEq (c >= 2) True of
        (Yes prf)   => Right $ MkConfidence c prf
        (No contra) => Left [ #"Not a valid confidence value: \#{show n}"# ]

setTests : String -> Config -> Either (List String) Config
setTests s c =
  map (\n => record { numTests = Just $ Relaxed $ MkTagged n} c)
      (parseNat s)

setShrinks : String -> Config -> Either (List String) Config
setShrinks s c =
  map (\n => record { numShrinks = Just $ MkTagged n} c)
      (parseNat s)

setConfidence : String -> Config -> Either (List String) Config
setConfidence s c =
  map (\n => record { confidence = Just n} c)
      (parseNat s >>= toConfidence)

setTestsForced : String -> Config -> Either (List String) Config
setTestsForced s c =
  map (\n => record { numTests = Just $ Forced $ MkTagged n} c)
      (parseNat s)

setHelp : Config -> Either (List String) Config
setHelp = Right . record { printHelp = True }

descs : List $ OptDescr (Config -> Either (List String) Config)
descs = [ MkOpt ['n'] ["testlimit"] (ReqArg setTests "<tests>")
            "number of tests to be passed by each property"
        , MkOpt ['N'] ["testlimit!"] (ReqArg setTestsForced "<tests>")
            "like -n but includes tests that are only run once"
        , MkOpt ['s'] ["shrinklimit"] (ReqArg setShrinks "<shrinks>")
            "maximal number of shrinks in case of a failed test"
        , MkOpt ['c'] ["confidence"] (ReqArg setConfidence "<confidence>")
            "acceptable occurence of false positives"
        , MkOpt [] ["--help"] (NoArg setHelp)
            "print this help text"
        ]



export
info : String
info = usageInfo "Hedgehog command line args:\n" descs

export
applyArgs : List String -> Either (List String) Config
applyArgs args =
  case getOpt Permute descs args of
       MkResult opts _ _ [] => foldl (>>=) (Right init) opts
       MkResult _    _ _ e  => Left e

export
applyConfig : Config -> Group -> Group
applyConfig (MkConfig _ nt ns c) =
  maybe id adjTests nt . maybe id withShrinks ns . maybe id withConfidence c

  where
    adjPropTests : NumTest -> Property -> Property
    adjPropTests (Forced x)  = withTests x
    adjPropTests (Relaxed x) = mapTests \n => if n > 1 then x else n

    adjTests : NumTest -> Group -> Group
    adjTests = mapProperty . adjPropTests
