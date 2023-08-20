module Tests

import Hedgehog

-- Modules with particluar tests:

import Basic

main : IO Unit
main = test
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
  ]
