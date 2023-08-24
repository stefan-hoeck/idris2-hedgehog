module Tests

import Hedgehog

-- Modules with particluar tests:

import Basic
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
      ]
    , "basic shrinking generation" `MkGroup`
      [ ("simplePosGeneration", Basic.ShrinkGen.simplePosGeneration)
      , ("simpleNegGeneration", Basic.ShrinkGen.simpleNegGeneration)
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
