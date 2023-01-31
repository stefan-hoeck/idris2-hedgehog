# Writing a SMILES Parser

In this tutorial, we look at a real world example.
We are going to write a (simplified) parser for SMILES strings
([OpenSMILES specification](http://opensmiles.org/opensmiles.html))
testing its behavior on the run. SMILES is a compact string encoding
for molecular graphs in Cheminformatics. We are going to keep things
simple here, dealing only with the organic subset atoms, thus ignoring
the possibility to specify concrete isotopes, charged atoms,
and stereochemic information.

```idris
module Docs.Smiles

import Data.String
import Data.Cotree
import Data.Vect
import Derive.Prelude
import Text.Lex

import Hedgehog

%default total
%language ElabReflection
```

## Bonds and Atoms

We first need to define the necessary data types.
To keep things simple, we only support the most common
bond types:

```idris
public export
data Bond = Sngl | Dbl | Trpl

%runElab derive "Bond" [Show,Eq,Ord]

namespace Bond
  public export
  encode : Bond -> String
  encode Sngl     = "-"
  encode Dbl      = "="
  encode Trpl     = "#"
```

In terms of chemical elements, we only support the *organic subset*
as per the specification:


```idris
data Elem = B | C | N | O | F | S | Cl | P | Br | I

%runElab derive "Docs.Smiles.Elem" [Show,Eq,Ord]
```

## Writing the Lexer

We use the utilities from `Text.Lexer` to cut a SMILES string into
appropriate tokens. In addition to a data type for SMILES tokens,
we also write a function for encoding lists of tokens back into
SMILES representation.

```idris
data Token : Type where
  Organic : (elem : Elem)  -> (aromatic : Bool) -> Token
  SBond   : (bond : Bond) -> Token
  POpen   : Token
  PClose  : Token
  Ring    : Int -> Token
  Invalid : String -> Token

%runElab derive "Smiles.Token" [Eq,Show]

encode : Token -> String
encode (Organic elem True)  = toLower $ show elem
encode (Organic elem False) = show elem
encode (SBond bond)         = encode bond
encode POpen                = "("
encode PClose               = ")"
encode (Invalid x)          = "Invalid " ++ x
encode (Ring x)             = if x >= 10 then "%" ++ show x else show x
```

We are now ready to implement the lexer itself:

```idris
bond : String -> Token
bond "-"  = SBond Sngl
bond "="  = SBond Dbl
bond "#"  = SBond Trpl
bond s    = Invalid $ "Bond: " ++ s

aromaticOrganic : String -> Token
aromaticOrganic "b" = Organic B True
aromaticOrganic "c" = Organic C True
aromaticOrganic "n" = Organic N True
aromaticOrganic "o" = Organic O True
aromaticOrganic "s" = Organic S True
aromaticOrganic "p" = Organic P True
aromaticOrganic s   = Invalid $ "Subset Atom: " ++ s

organic : String -> Token
organic "B"  = Organic B False
organic "C"  = Organic C False
organic "N"  = Organic N False
organic "O"  = Organic O False
organic "S"  = Organic S False
organic "P"  = Organic P False
organic "F"  = Organic F False
organic "Cl" = Organic Cl False
organic "Br" = Organic Br False
organic "I"  = Organic I False
organic s    = aromaticOrganic s


ring : String -> Token
ring s = case fastUnpack s of
              [a]       => Ring $ calc a
              ['%',a,b] => Ring $ calc a * 10 + calc b
              _         => Invalid $ "Ring: " ++ s
  where calc : Char -> Int
        calc c = ord c - 48

toks : TokRes b cs StopReason a -> List (Bounded a)
toks (TR l c st _ _ _) = st <>> []

export
lexSmiles1 : (s : String) -> List (Bounded Token)
lexSmiles1 s = toks $ lex (Match
  [ (pred isLower <|> (pred isUpper <+> opt (pred isLower)), organic . cast)
  , (oneOf (unpack "-=#"), bond . cast)
  , (digit <|> (is '%' <+> digit <+> digit), ring . cast)
  , (is '(', const POpen)
  , (is ')', const PClose)
  ]) s
```

## Testing the Lexer

Since the functions from `Text.Lexer` are not publicly exported,
we cannot test the lexer at compile time. We will therefore
write a simple Hedgehog test to verify the lexer's correct behavior.
First, we are going to need a bunch of generators:

```idris
genBond : Gen Bond
genBond = element [Sngl,Dbl,Trpl]

-- element paired with aromaticity
genAtom : Gen (Elem,Bool)
genAtom = element $  map (,False) [B,C,N,O,F,S,Cl,P,Br,I]
                  ++ map (,True)  [B,C,N,O,S,P]

-- this does not generate Invalid tokens
token : Gen Token
token = frequency [ (10, uncurry Organic <$> genAtom)
                  , (2,  SBond <$> genBond)
                  , (1,  Ring <$> int (linear 1 99))
                  , (1,  pure POpen)
                  , (1,  pure PClose)
                  ]

tokens : Gen (List Token)
tokens = list (linear 1 50) token
```

For token we use the `frequency` generator, which
allows us to specify, how often a generator in the list will be
chosen. All generators used above shrink towards the first elements
in the given vectors.

We can now specify the actual property. We'd like to verify, that
roundtripping via `lex` and `encode` gives back the original
list of valid tokens.

```idris
prop_lex1 : Property
prop_lex1 = property $ do ts <- forAll tokens

                          let enc : String
                              enc = concatMap encode ts

                              lexed : List Token
                              lexed = map val $ lexSmiles1 enc

                          footnote $ "Encoded: " ++ enc
                          lexed === ts
```

We annotate the property with a footnote of the encoded
SMILES string. This will help us understand what's going on
in case of a test failure.

Running `:exec check prop_lex1` will lead to output similar
to the following (if in a Unix shell, use `export HEDGEHOG_COLOR="1"` to
enable nicely colorized output):

```repl
> ✗ <interactive> failed after 11 tests.

>   forAll 0 =
>     [ Organic { elem = B  , aromatic = False  }
>     , Organic { elem = B  , aromatic = True  }
>     ]

>   Encoded: Bb
>   ━━━ Failed (- lhs) (+ rhs) ━━━
>   - [ Invalid "Subset Atom: Bb" ]
>   + [ Organic { elem = B  , aromatic = False  }
>   + , Organic { elem = B  , aromatic = True  }
>   + ]

>   This failure can be reproduced by running:
>   > recheck 10 (MkSeed 17955597067191004859 1876035156183501547) <property>
```

So, there is a problem with our lexer. Note, how Hedgehog yields a properly
shrunk minimal example. The problem at hand: The string "Bb" is
treated as a single chemical element instead of two atoms of boron
(one aliphatic, the other aromatic).

The following version fixes this issue, as can be shown by
checking `prop_lex`:

```idris
lexSmiles : (s : String) -> List (Bounded Token)
lexSmiles s = toks $lex (Match
  [ (exact "Cl" <|> exact "Br" <|> pred isAlpha, organic . cast)
  , (oneOf (unpack "-=#"), bond . cast)
  , (digit <|> (is '%' <+> digit <+> digit), ring . cast)
  , (is '(', const POpen)
  , (is ')', const PClose)
  ]) s

prop_lex : Property
prop_lex = property $ do ts <- forAll tokens

                         let enc : String
                             enc = concatMap encode ts

                             lexed : List Token
                             lexed = map val $ lexSmiles enc

                         footnote $ "Encoded: " ++ enc
                         lexed === ts
```
