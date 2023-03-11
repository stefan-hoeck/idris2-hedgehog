module Hedgehog.Internal.Gen

import Data.Bounded
import Data.Colist
import Data.Cotree
import Data.Fin
import Data.List
import Data.List1
import Data.Nat
import Data.SOP
import Data.String
import Data.Tree
import Data.Vect

import Control.Monad.Maybe

import Hedgehog.Internal.Range
import Hedgehog.Internal.Seed
import Hedgehog.Internal.Shrink
import Hedgehog.Internal.Util

%hide Prelude.Range

%default total

--------------------------------------------------------------------------------
--          Random Value Generator with Integrated Shrinking
--------------------------------------------------------------------------------

||| Generates random values of type `a`
public export
record Gen (a : Type) where
  constructor MkGen
  unGen   : Size -> Seed -> Cotree a

public export %inline
runGen : Size -> Seed -> Gen a -> Cotree a
runGen si se g = unGen g si se

public export %inline
mapGen :  (f : Cotree a -> Cotree b) -> Gen a -> Gen b
mapGen f (MkGen run) = MkGen $ \si,se => f (run si se)

||| Lift a predefined shrink tree in to a generator, ignoring the seed and the
||| size.
public export %inline
fromTree : Cotree a -> Gen a
fromTree ct = MkGen $ \_,_ => ct

||| Observe a generator's shrink tree.
public export %inline
toTree : Gen a -> Gen (Cotree a)
toTree (MkGen unGen) = MkGen $ \si,se => pure (unGen si se)

--------------------------------------------------------------------------------
--          Interface Implementations
--------------------------------------------------------------------------------

public export
Functor Gen where
  map f (MkGen g) = MkGen $ \si,se => map f (g si se)

public export
Applicative Gen where
  pure a = MkGen $ \_,_ => pure a

  MkGen ff <*> MkGen fa =
    MkGen $ \si,se => let (se1,se2) = split se
                     in interleave (ff si se1) (fa si se2)

public export
Monad Gen where
  MkGen run >>= f =
    MkGen $ \si,se => let (se1,se2) = split se
                          ta        = run si se1
                       in bind ta (runGen si se2 . f)

--------------------------------------------------------------------------------
--          Combinators
--------------------------------------------------------------------------------

public export %inline
generate : (Size -> Seed -> a) -> Gen a
generate  f = MkGen $ \si,se => pure (f si se)

--------------------------------------------------------------------------------
--          Shrinking
--------------------------------------------------------------------------------

public export %inline
shrink : (a -> Colist a) -> Gen a -> Gen a
shrink f = mapGen (expand f)

public export %inline
prune : Gen a -> Gen a
prune = mapGen prune

--------------------------------------------------------------------------------
--          Size
--------------------------------------------------------------------------------

||| Construct a generator that depends on the size parameter.
public export %inline
sized : (Size -> Gen a) -> Gen a
sized f = generate (\si,_ => si) >>= f

||| Adjust the size parameter by transforming it with the given function.
public export %inline
scale : (Size -> Size) -> Gen a -> Gen a
scale f (MkGen run) = MkGen $ \si,se => run (f si) se

||| Override the size parameter. Returns a generator which uses the given size
||| instead of the runtime-size parameter.
public export %inline
resize : Size -> Gen a -> Gen a
resize size = scale (const size)

||| Scale a size using the golden ratio.
|||
|||   > golden x = x / φ
|||   > golden x = x / 1.61803..
public export %inline
golden : Size -> Size
golden = resize $ \n => round (0.61803398875 * cast n)

||| Make a generator smaller by scaling its size parameter.
public export %inline
small : Gen a -> Gen a
small = scale golden

--------------------------------------------------------------------------------
--          Integral
--------------------------------------------------------------------------------

||| Generates a random integral number in the [inclusive,inclusive] range.
|||
||| This generator does not shrink.
public export
integral_ : ToInteger a => Range a -> Gen a
integral_ range = generate $ \si,se =>
    let (x, y) = bounds si range
     in fromInteger . fst $ nextIntegerR (toInteger x, toInteger y) se

||| Generates a random integral number in the given @[inclusive,inclusive]@ range.
|||
||| When the generator tries to shrink, it will shrink towards the
||| 'Range.origin' of the specified 'Range'.
|||
||| For example, the following generator will produce a number between @1970@
||| and @2100@, but will shrink towards @2000@:
|||
||| ```
||| integral (Range.'Range.constantFrom' 2000 1970 2100) :: 'Gen' 'Int'
||| ```
|||
|||   Some sample outputs from this generator might look like:
|||
|||   > === Outcome ===
|||   > 1973
|||   > === Shrinks ===
|||   > 2000
|||   > 1987
|||   > 1980
|||   > 1976
|||   > 1974
|||
|||   > === Outcome ===
|||   > 2061
|||   > === Shrinks ===
|||   > 2000
|||   > 2031
|||   > 2046
|||   > 2054
|||   > 2058
|||   > 2060
|||
public export %inline
integral : ToInteger a => Range a -> Gen a
integral range = shrink (towards $ origin range) (integral_ range)

||| Generates a random machine integer in the given range.
|||
||| This is a specialization of `integral`, offered for convenience.
public export %inline
int : Range Int -> Gen Int
int = integral

||| Generates a random 8-bit integer in the given range.
|||
||| This is a specialization of `integral`, offered for convenience.
public export %inline
int8 : Range Int8 -> Gen Int8
int8 = integral

||| Generates a random 8-bit integer in the full available range.
|||
||| This shrinks exponentially towards 0.
public export %inline
anyInt8 : Gen Int8
anyInt8 = int8 (exponentialFrom 0 minBound maxBound)

||| Generates a random 16-bit integer in the given range.
|||
||| This is a specialization of `integral`, offered for convenience.
public export %inline
int16 : Range Int16 -> Gen Int16
int16 = integral

||| Generates a random 16-bit integer in the full available range.
|||
||| This shrinks exponentially towards 0.
public export %inline
anyInt16 : Gen Int16
anyInt16 = int16 (exponentialFrom 0 minBound maxBound)

||| Generates a random 32-bit integer in the given range.
|||
||| This is a specialization of `integral`, offered for convenience.
public export %inline
int32 : Range Int32 -> Gen Int32
int32 = integral

||| Generates a random 32-bit integer in the full available range.
|||
||| This shrinks exponentially towards 0.
public export %inline
anyInt32 : Gen Int32
anyInt32 = int32 (exponentialFrom 0 minBound maxBound)

||| Generates a random 64-bit integer in the given range.
|||
||| This is a specialization of `integral`, offered for convenience.
public export %inline
int64 : Range Int64 -> Gen Int64
int64 = integral

||| Generates a random 64-bit integer in the full available range.
|||
||| This shrinks exponentially towards 0.
public export %inline
anyInt64 : Gen Int64
anyInt64 = int64 (exponentialFrom 0 minBound maxBound)

||| Generates a random 8-bit integer in the given range.
|||
||| This is a specialization of 'integral', offered for convenience.
public export %inline
bits8 : Range Bits8 -> Gen Bits8
bits8 = integral

||| Generates a random 8-bit signed integer in the full available range.
|||
||| This shrinks exponentially towards 0.
public export %inline
anyBits8 : Gen Bits8
anyBits8 = bits8 (exponential 0 maxBound)

||| Generates a random 16-bit integer in the given range.
|||
||| This is a specialization of 'integral', offered for convenience.
public export %inline
bits16 : Range Bits16 -> Gen Bits16
bits16 = integral

||| Generates a random 16-bit signed integer in the full available range.
|||
||| This shrinks exponentially towards 0.
public export %inline
anyBits16 : Gen Bits16
anyBits16 = bits16 (exponential 0 maxBound)

||| Generates a random 32-bit integer in the given range.
|||
||| This is a specialization of 'integral', offered for convenience.
public export %inline
bits32 : Range Bits32 -> Gen Bits32
bits32 = integral

||| Generates a random 32-bit signed integer in the full available range.
|||
||| This shrinks exponentially towards 0.
public export %inline
anyBits32 : Gen Bits32
anyBits32 = bits32 (exponential 0 maxBound)

||| Generates a random 64-bit integer in the given range.
|||
||| This is a specialization of 'integral', offered for convenience.
public export %inline
bits64 : Range Bits64 -> Gen Bits64
bits64 = integral

||| Generates a random 64-bit signed integer in the full available range.
|||
||| This shrinks exponentially towards 0.
public export %inline
anyBits64 : Gen Bits64
anyBits64 = bits64 (exponential 0 maxBound)

||| Generates a random Integer in the given range.
|||
||| This is a specialization of 'integral', offered for convenience.
public export %inline
integer : Range Integer -> Gen Integer
integer = integral

||| Generates a random Nat in the given range.
|||
||| This is a specialization of 'integral', offered for convenience.
public export %inline
nat : Range Nat -> Gen Nat
nat = integral

||| Generates a random Size in the given range.
|||
||| This is a specialization of 'integral', offered for convenience.
public export %inline
size : Range Size -> Gen Size
size = integral

||| Generates a random (Fin n) in the given range.
public export %inline
fin : {n : _} -> Range (Fin n) -> Gen (Fin n)
fin range = let rangeInt = map finToInteger range
             in map toFin (integer rangeInt)
  where toFin : Integer -> Fin n
        toFin k = fromMaybe range.origin (integerToFin k n)

--------------------------------------------------------------------------------
--          Floating Point
--------------------------------------------------------------------------------

||| Generates a random fractional number in the [inclusive,exclusive) range.
|||
||| This generator does not shrink.
export %inline
double_ : Range Double -> Gen Double
double_ range = generate $ \si,se => let (x, y) = bounds si range
                                      in fst $ nextDoubleR x y se

||| Generates a random floating-point number in the given range.
|||
||| This generator works the same as 'integral', but for floating point numbers.
|||
export %inline
double : Range Double -> Gen Double
double range = shrink (towardsDouble $ origin range) (double_ range)

--------------------------------------------------------------------------------
--          Choice
--------------------------------------------------------------------------------

||| Trivial generator that always produces the same element.
|||
||| This is another name for `pure`.
public export %inline
constant : a -> Gen a
constant = pure

||| Randomly selects one of the elements in the vector.
|||
||| This generator shrinks towards the first element in the vector.
public export %inline
element : {k : _} -> Vect (S k) a -> Gen a
element vs = map (`index` vs) (fin $ constant FZ last)

||| Randomly selects one of the elements in the vector.
|||
||| This generator does not shrink.
public export %inline
element_ : {k : _} -> Vect (S k) a -> Gen a
element_ = prune . element

||| Randomly selects one of the generators in the vector.
|||
||| This generator shrinks towards the first generator in the vector.
public export %inline
choice : {k : _} -> Vect (S k) (Gen a) -> Gen a
choice vs = element vs >>= id

||| Randomly selects one of the generators in the vector.
|||
||| This generator does not shrink towards a particular
||| generator in the vector
public export %inline
choice_ : {k : _} -> Vect (S k) (Gen a) -> Gen a
choice_ vs = element_ vs >>= id

||| Uses a weighted distribution to randomly select one of the generators in
||| the vector.
|||
||| This generator shrinks towards the first generator in the vector.
|||
||| Note that if the given frequencies sum up to 0, the first element
||| of the vector
public export %inline
frequency : Vect (S k) (Nat, Gen a) -> Gen a
frequency ps =
  let acc    = scanl1 addFst $ map (mapFst toInteger) ps
      gen    = integral_ . constant 0 . fst $ last acc
      lower  = \n => takeWhile (< n) (fromFoldable $ map fst acc)

  in shrink lower gen >>= choose acc
  where addFst : (Integer,x) -> (Integer,x) -> (Integer,x)
        addFst (x,_) (y,v) = (x + y,v)

        choose : Vect n (Integer, Gen a) -> Integer -> Gen a
        choose []             _ = snd $ head ps
        choose ((i, v) :: ps) k = if i >= k then v else choose ps k

||| Generates a random boolean.
|||
||| This generator shrinks to `False`.
public export %inline
bool : Gen Bool
bool = element [False,True]

--------------------------------------------------------------------------------
--          Character
--------------------------------------------------------------------------------

||| Generates a character in the given `Range`.
|||
||| Shrinks towards the origin of the range.
export %inline
char : Range Char -> Gen Char
char = map chr . int . map ord

||| Generates a character in the interval [lower,uppper].
|||
||| Shrinks towards the lower value.
export %inline
charc : (lower : Char) -> (upper : Char) -> Gen Char
charc l u = char $ constant l u


||| Generates an ASCII binit: `'0'..'1'`
export %inline
binit : Gen Char
binit = charc '0' '1'

||| Generates an ASCII octit: `'0'..'7'`
export %inline
octit : Gen Char
octit = charc '0' '7'

||| Generates an ASCII digit: `'0'..'9'`
export %inline
digit : Gen Char
digit = charc '0' '9'

||| Generates an ASCII hexit: `'0'..'9', 'a'..'f', 'A'..'F'`
export %inline
hexit : Gen Char
hexit = frequency [(10, digit),(6, charc 'a' 'f'),(6, charc 'A' 'F')]

||| Generates an ASCII lowercase letter: `'a'..'z'`
export %inline
lower : Gen Char
lower = charc 'a' 'z'

||| Generates an ASCII uppercase letter: `'A'..'Z'`
export %inline
upper : Gen Char
upper = charc 'A' 'Z'

||| Generates an ASCII letter: `'a'..'z', 'A'..'Z'`
export %inline
alpha : Gen Char
alpha = choice [lower,upper]

||| Generates an ASCII letter or digit: `'a'..'z', 'A'..'Z', '0'..'9'`
export %inline
alphaNum : Gen Char
alphaNum = frequency [(10,digit),(24,lower),(24,upper)]

||| Generates an ASCII character: `'\0'..'\127'`
export %inline
ascii : Gen Char
ascii = charc '\0' '\127'

||| Generates an printable ASCII character: `'\32'..'\126'`
||| Note: This includes the space character but no
|||       line breaks or tabs
export %inline
printableAscii : Gen Char
printableAscii = charc '\32' '\126'

||| Generates a latin character: `'\0'..'\255'`
export %inline
latin : Gen Char
latin = charc '\0' '\255'

||| Generates a printable latin character: `'\32'..'\126'` and `'\160'..'\255'`
export %inline
printableLatin : Gen Char
printableLatin = frequency [ (95, printableAscii), (96, charc '\160' '\255') ]

||| Generates a Unicode character, excluding noncharacters
||| and invalid standalone surrogates:
||| `'\0'..'\1114111'` (excluding '\55296'..'\57343', '\65534', '\65535')`
export %inline
unicode : Gen Char
unicode = frequency [ (55296, charc '\0' '\55295')
                    , (8190, charc '\57344' '\65533')
                    , (1048576, charc '\65536' '\1114111')
                    ]

||| Generates a printable Unicode character, excluding noncharacters
||| and invalid standalone surrogates:
||| `'\0'..'\1114111'` (excluding '\0' .. '\31', '\127' .. '\159',
||| '\55296'..'\57343', and '\65534', '\65535')`
export %inline
printableUnicode : Gen Char
printableUnicode =
  frequency
    [ (95, printableAscii)
    , (55136, charc '\160' '\55295')
    , (8190, charc '\57344' '\65533')
    , (1048576, charc '\65536' '\1114111')
    ]

||| Generates a Unicode character, including noncharacters
||| and invalid standalone surrogates: `'\0'..'\1114111'`
export %inline
unicodeAll : Gen Char
unicodeAll = charc '\0' '\1114111'

--------------------------------------------------------------------------------
--          Containers
--------------------------------------------------------------------------------

||| Generates a 'Nothing' some of the time.
export %inline
maybe : Gen a -> Gen (Maybe a)
maybe gen = sized $ \s => frequency [ (2, constant Nothing)
                                    , (S s.size, Just <$> gen)
                                    ]

||| Generates either an 'a' or a 'b'.
|||
||| As the size grows, this generator generates @Right@s more often than @Left@s.
export %inline
either : Gen a -> Gen b -> Gen (Either a b)
either genA genB = sized $ \s => frequency [ (2, Left <$> genA)
                                           , (S s.size, Right <$> genB)
                                           ]
||| Generates either an 'a' or a 'b', without bias.
|||
||| This generator generates as many @Right@s as it does @Left@s.
export %inline
either_ : Gen a -> Gen b -> Gen (Either a b)
either_ genA genB = choice [Left <$> genA, Right <$> genB]

||| Generates a list using a 'Range' to determine the length.
export %inline
vect : (n : Nat) -> Gen a -> Gen (Vect n a)
vect 0     _ = pure []
vect (S k) g = [| g :: vect k g |]

||| Generates a list using a 'Range' to determine the length.
export %inline
list : Range Nat -> Gen a -> Gen (List a)
list range gen =
  sized $ \si => let minLength = lowerBound si range
                  in  mapGen (interleave minLength . value)
                    $ integral_ range >>= (\n => map toList (vect n (toTree gen)))
||| Generates a non-empty list using a `Range` to determine the length.
export %inline
list1 : Range Nat -> Gen a -> Gen (List1 a)
list1 range gen = [| gen ::: list (map pred range) gen |]

||| Generates a string using 'Range' to determine the length.
export %inline
string : Range Nat -> Gen Char -> Gen String
string range = map fastPack . list range

--------------------------------------------------------------------------------
--          SOP
--------------------------------------------------------------------------------

collapseNPV : NP (K a) ks -> {auto 0 _ : NonEmpty ks} -> (k ** Vect (S k) a)
collapseNPV {ks = _} [] impossible
collapseNPV {ks = _} (v::[]) = (0 ** [v])
collapseNPV {ks = t::t2::ts}(v::v2::vs) =
  let (k ** vs2) = collapseNPV {ks = t2 :: ts} (v2 :: vs)
   in (S k ** (v :: vs2))

||| Turns an n-ary product of generators into a generator
||| of n-ary products of the same type.
export %inline
np : NP Gen ts -> Gen (NP I ts)
np = sequenceNP

||| Turns an n-ary product of generators into a generator
||| of n-ary sums of the same type. This is a generalisation
||| of choice and shrinks towards the first sum type
||| in the list.
export %inline
ns : NP Gen ts -> {auto 0 prf : NonEmpty ts} -> Gen (NS I ts)
ns np = let (_ ** vs) = collapseNPV (apInjsNP_ np)
         in choice (map sequenceNS vs)

||| Turns an n-ary product of generators into a generator
||| of n-ary sums of the same type. This is a generalisation
||| of `choice_` and does not shrink towards a particular
||| sum type.
export %inline
ns_ : NP Gen ts -> {auto 0 prf : NonEmpty ts} -> Gen (NS I ts)
ns_ np = let (_ ** vs) = collapseNPV (apInjsNP_ np)
         in choice_ (map sequenceNS vs)

export %inline
sop : POP Gen tss -> {auto 0 prf : NonEmpty tss} -> Gen (SOP I tss)
sop p = let (_ ** vs) = collapseNPV {a = SOP Gen tss} (apInjsPOP_ p)
         in choice (map sequenceSOP vs)

--------------------------------------------------------------------------------
--          Sampling
--------------------------------------------------------------------------------

||| Print the value produced by a generator, and the first level of shrinks,
||| for the given size and seed.
|||
||| Use 'print' to generate a value from a random seed.
export
printWith : (HasIO io, Show a) => Size -> Seed -> Gen a -> io ()
printWith si se gen = let (MkCotree v fo) = runGen si se gen
                          shrinks         = value <$> take 1000 fo
                       in do putStrLn "=== Outcome ==="
                             putStrLn (show v)
                             putStrLn "=== Shrinks ==="
                             traverse_ printLn shrinks
||| Run a generator with a random seed and print the outcome, and the first
||| level of shrinks.
|||
||| @
||| Gen.print (Gen.'enum' \'a\' \'f\')
||| @
|||
|||   > === Outcome ===
|||   > 'd'
|||   > === Shrinks ===
|||   > 'a'
|||   > 'b'
|||   > 'c'
export
print : Show a => HasIO io => Gen a -> io ()
print gen = initSMGen >>= \se => printWith 100 se gen

||| Generate a sample from a generator.
export
sample : HasIO io => Gen a -> io a
sample gen = (value . gen.unGen 100) <$> initSMGen

||| Render the shrink tree produced by a generator, for the given size and
||| seed up to the given depth and width.
export
renderTree :  Show a
           => (maxDepth : Nat)
           -> (maxWidth : Nat)
           -> Size
           -> Seed
           -> Gen a
           -> String
renderTree md mw si se = drawTree
                       . map show
                       . toTree md mw
                       . runGen si se

||| Print the shrink tree produced by a generator, for the given size and
||| seed.
|||
||| Use 'printTree' to generate a value from a random seed.
export
printTreeWith :  Show a
              => HasIO io
              => (maxDepth : Nat)
              -> (maxWidth : Nat)
              -> Size
              -> Seed
              -> Gen a
              -> io ()
printTreeWith md mw si se = putStrLn . renderTree md mw si se

||| Run a generator with a random seed and print the resulting shrink tree.
|||
||| @
||| Gen.printTree (Gen.'enum' \'a\' \'f\')
||| @
|||
|||   > 'd'
|||   >  ├╼'a'
|||   >  ├╼'b'
|||   >  │  └╼'a'
|||   >  └╼'c'
|||   >     ├╼'a'
|||   >     └╼'b'
|||   >        └╼'a'
|||
|||   /This may not terminate when the tree is very large./
|||
export
printTree :  Show a
          => HasIO io
          => (maxDepth : Nat)
          -> (maxWidth : Nat)
          -> Gen a
          -> io ()
printTree md mw gen = initSMGen >>= \se => printTreeWith md mw 100 se gen
