module Tests

import Hedgehog

-- Modules with particluar tests:

import Basic
import Coverage
import Functions.NoShrink
import Functions.Shrink
import Functions.DeriveCogen

main : IO Unit
main =
  test
    [ "very basic tests" `MkGroup`
      [ ("simplePosAssert", Basic.Assert.simplePosAssert)
      , ("simpleNegAssert", Basic.Assert.simpleNegAssert)
      ]
    , "basic non-shrinking generation" `MkGroup`
      [ ("simplePosGeneration", Basic.NoShrinkGen.simplePosGeneration)
      , ("simpleNegGeneration", Basic.NoShrinkGen.simpleNegGeneration)
      , ("forallsPosGeneration", Basic.NoShrinkGen.forallsPosGeneration)
      , ("forallsNegGeneration", Basic.NoShrinkGen.forallsNegGeneration)
      ]
    , "basic shrinking generation" `MkGroup`
      [ ("simplePosGeneration", Basic.ShrinkGen.simplePosGeneration)
      , ("simpleNegGeneration", Basic.ShrinkGen.simpleNegGeneration)
      , ("forallsPosGeneration", Basic.ShrinkGen.forallsPosGeneration)
      , ("forallsNegGeneration", Basic.ShrinkGen.forallsNegGeneration)
      ]
    , "coverage checking" `MkGroup`
      [ ("simpleCoverage", Coverage.simpleCoverage)
      ]
    , "non-shrinking function generaton" `MkGroup`
      [ ("simpleFunPrint", Functions.NoShrink.simpleFunPrint)
      , ("simpleFunPos"  , Functions.NoShrink.simpleFunPos)
      , ("simpleFunNeg"  , Functions.NoShrink.simpleFunNeg)
      ]
    , "shrinking function generaton" `MkGroup`
      [ ("simpleFunPrint"   , Functions.Shrink.simpleFunPrint)
      , ("fancyFunPrint"    , Functions.Shrink.fancyFunPrint)
      , ("fancyListFunPrint", Functions.Shrink.fancyListFunPrint)
      , ("simpleFunPos"     , Functions.Shrink.simpleFunPos)
      , ("simpleFunNeg"     , Functions.Shrink.simpleFunNeg)
      ]
    , "cogen derivation" `MkGroup`
      [ ("printZFun", Functions.DeriveCogen.printZFun)
      ]
    ]
