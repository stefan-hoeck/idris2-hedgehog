module Hedgehog.Internal.Property

import Control.Monad.Either
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Monad.Writer
import Data.DPair
import Data.Lazy
import Derive.Prelude
import Hedgehog.Internal.Gen
import Hedgehog.Internal.Util
import Text.Show.Diff
import Text.Show.Pretty

%language ElabReflection

%default total

--------------------------------------------------------------------------------
--          Tagged Primitives
--------------------------------------------------------------------------------

public export
data Tag = ConfidenceTag
         | CoverCountTag
         | CoverPercentageTag
         | GroupNameTag
         | LabelNameTag
         | PropertyCountTag
         | PropertyNameTag
         | ShrinkCountTag
         | ShrinkLimitTag
         | TestCountTag
         | TestLimitTag

%runElab derive "Tag" [Show,Eq,Ord]

public export
record Tagged (tag : Tag) (t : Type) where
  constructor MkTagged
  unTag : t

%runElab derivePattern "Tagged" [I,P]
  [Show,Eq,Ord,Num,FromString,Semigroup,Monoid]

public export %inline
Semigroup (Tagged t Nat) where (<+>) = (+)

public export %inline
Monoid (Tagged t Nat) where neutral = 0

||| The total number of tests which are covered by a classifier.
|||
||| Can be constructed using numeric literals.
public export
0 CoverCount : Type
CoverCount = Tagged CoverCountTag Nat

||| The name of a group of properties.
public export
0 GroupName : Type
GroupName = Tagged GroupNameTag String

||| The number of properties in a group.
public export
0 PropertyCount : Type
PropertyCount = Tagged PropertyCountTag Nat

||| The numbers of times a property was able to shrink after a failing test.
public export
0 ShrinkCount : Type
ShrinkCount = Tagged ShrinkCountTag Nat

||| The number of shrinks to try before giving up on shrinking.
|||
||| Can be constructed using numeric literals:
public export
0 ShrinkLimit : Type
ShrinkLimit = Tagged ShrinkLimitTag Nat

||| The number of tests a property ran successfully.
public export
0 TestCount : Type
TestCount = Tagged TestCountTag Nat

||| The number of successful tests that need to be run before a property test
||| is considered successful.
|||
||| Can be constructed using numeric literals.
public export
0 TestLimit : Type
TestLimit = Tagged TestLimitTag Nat

||| The name of a property.
public export
0 PropertyName : Type
PropertyName = Tagged PropertyNameTag String

||| The acceptable occurrence of false positives
|||
||| Example, `the Confidence 1000000000` would mean that
||| you'd accept a false positive
||| for 1 in 10^9 tests.
public export
record Confidence where
  constructor MkConfidence
  confidence : Bits64
  0 inBound    : confidence >= 2 = True

%runElab derive "Confidence" [Show,Eq,Ord]

namespace Confidence
  public export
  fromInteger :  (n : Integer)
              -> {auto 0 prf : the Bits64 (fromInteger n) >= 2 = True}
              -> Confidence
  fromInteger n = MkConfidence (fromInteger n) prf

||| The relative number of tests which are covered by a classifier.
public export
0 CoverPercentage : Type
CoverPercentage = Tagged CoverPercentageTag Double

||| The name of a classifier.
public export
0 LabelName : Type
LabelName = Tagged LabelNameTag String

--------------------------------------------------------------------------------
--          Journal
--------------------------------------------------------------------------------

||| The difference between some expected and actual value.
public export
record Diff where
  constructor MkDiff
  diffPrefix  : String
  diffRemoved : String
  diffInfix   : String
  diffAdded   : String
  diffSuffix  : String
  diffValue   : ValueDiff

%runElab derive "Hedgehog.Internal.Property.Diff" [Show,Eq]

||| Whether a test is covered by a classifier, and therefore belongs to a
||| 'Class'.
public export
data Cover = NotCovered | Covered

%runElab derive "Cover" [Show,Eq,Ord]

public export
Semigroup Cover where
  NotCovered <+> NotCovered = NotCovered
  _          <+> _          = Covered

public export
Monoid Cover where
  neutral = NotCovered

public export
toCoverCount : Cover -> CoverCount
toCoverCount NotCovered = 0
toCoverCount Covered    = 1

||| The extent to which a test is covered by a classifier.
|||
||| When a classifier's coverage does not exceed the required minimum, the
||| test will be failed.
public export
record Label a where
  constructor MkLabel
  labelName       : LabelName
  labelMinimum    : CoverPercentage
  labelAnnotation : a

%runElab derive "Label" [Show,Eq]

public export
Functor Label where
  map f = {labelAnnotation $= f}

public export
Foldable Label where
  foldl f a l = f a l.labelAnnotation
  foldr f a l = f l.labelAnnotation a
  null _ = False

public export
Traversable Label where
  traverse f l = (\v => {labelAnnotation := v} l) <$>
                 f l.labelAnnotation

||| This semigroup is right biased. The name, location and percentage from the
||| rightmost `Label` will be kept. This shouldn't be a problem since the
||| library doesn't allow setting multiple classes with the same 'ClassifierName'.
export
Semigroup a => Semigroup (Label a) where
  ll <+> lr = { labelAnnotation $= (ll.labelAnnotation <+>) } lr

||| Log messages which are recorded during a test run.
public export
data Log = Annotation (Lazy String)
         | Footnote (Lazy String)
         | LogLabel (Label Cover)

%runElab derive "Log" [Show,Eq]

||| A record containing the details of a test run.
public export
record Journal where
  constructor MkJournal
  journalLogs : List (Lazy Log)

%runElab derive "Journal" [Show,Eq,Semigroup,Monoid]

||| Details on where and why a test failed.
public export
record Failure where
  constructor MkFailure
  message : String
  diff    : Maybe Diff

%runElab derive "Failure" [Show,Eq]

||| The extent to which all classifiers cover a test.
|||
||| When a given classification's coverage does not exceed the required/
||| minimum, the test will be failed.
export
record Coverage a where
  constructor MkCoverage
  coverageLabels : List (LabelName, Label a)

%runElab derive "Coverage" [Show,Eq]

export %inline
names : Coverage a -> List LabelName
names = map fst . coverageLabels

export %inline
labels : Coverage a -> List (Label a)
labels = map snd . coverageLabels

export %inline
annotations : Coverage a -> List a
annotations = map (labelAnnotation . snd) . coverageLabels

mergeWith :
     Ord k
  => SnocList (k,v)
  -> (v -> v -> v)
  -> List (k,v)
  -> List (k,v)
  -> List (k,v)
mergeWith sp _ [] ys               = sp <>> ys
mergeWith sp _ xs []               = sp <>> xs
mergeWith sp f (x :: xs) (y :: ys) = case compare (fst x) (fst y) of
  LT => mergeWith (sp :< x) f xs (y :: ys)
  EQ => mergeWith (sp :< (fst x, f (snd x) (snd y))) f xs ys
  GT => mergeWith (sp :< y) f (x::xs) ys

export %inline
Semigroup a => Semigroup (Coverage a) where
  MkCoverage x <+> MkCoverage y =
    MkCoverage $ mergeWith [<] (<+>) x y

export %inline
Semigroup a => Monoid (Coverage a) where
  neutral = MkCoverage []

export
Functor Coverage where
  map f = {coverageLabels $= map (mapSnd $ map f) }

export
Foldable Coverage where
  foldl f acc = foldl f acc . annotations
  foldr f acc = foldr f acc . annotations
  null = null . coverageLabels

export
Traversable Coverage where
  traverse f (MkCoverage sm) =
    MkCoverage <$> traverse ((traverse . traverse) f) sm

--------------------------------------------------------------------------------
--          Config
--------------------------------------------------------------------------------

public export
data TerminationCriteria =
    EarlyTermination Confidence TestLimit
  | NoEarlyTermination Confidence TestLimit
  | NoConfidenceTermination TestLimit

%runElab derive "TerminationCriteria" [Show,Eq]

public export
unCriteria : TerminationCriteria -> (Maybe Confidence, TestLimit)
unCriteria (EarlyTermination c t)      = (Just c, t)
unCriteria (NoEarlyTermination c t)    = (Just c, t)
unCriteria (NoConfidenceTermination t) = (Nothing, t)


||| Configuration for a property test.
public export
record PropertyConfig where
  constructor MkPropertyConfig
  shrinkLimit         : ShrinkLimit
  terminationCriteria : TerminationCriteria

%runElab derive "PropertyConfig" [Show,Eq]

||| The minimum amount of tests to run for a 'Property'
public export
defaultMinTests : TestLimit
defaultMinTests = 100

||| The default confidence allows one false positive in 10^9 tests
public export
defaultConfidence : Confidence
defaultConfidence = Confidence.fromInteger 1000000000

||| The default configuration for a property test.
public export
defaultConfig : PropertyConfig
defaultConfig =
  MkPropertyConfig {
      shrinkLimit = 1000
    , terminationCriteria = NoConfidenceTermination defaultMinTests
    }

--------------------------------------------------------------------------------
--          Test
--------------------------------------------------------------------------------

||| A test monad transformer allows the assertion of expectations.
public export
0 TestT : (Type -> Type) -> Type -> Type
TestT m = EitherT Failure (WriterT Journal m)

public export
0 Test : Type -> Type
Test = TestT Identity

export
mkTestT : Functor m => m (Either Failure a, Journal) -> TestT m a
mkTestT = MkEitherT . writerT

export
mkTest : (Either Failure a, Journal) -> Test a
mkTest = mkTestT . Id

export
runTestT : TestT m a -> m (Either Failure a, Journal)
runTestT = runWriterT . runEitherT

export
runTest : Test a -> (Either Failure a, Journal)
runTest = runIdentity . runTestT

||| Log some information which might be relevant to a potential test failure.
export
writeLog : Applicative m => Lazy Log -> TestT m ()
writeLog x = mkTestT $ pure (Right (), MkJournal [x])

||| Fail the test with an error message, useful for building other failure
||| combinators.
export
failWith : Applicative m => Maybe Diff -> String -> TestT m a
failWith diff msg = mkTestT $ pure (Left $ MkFailure msg diff, neutral)

||| Annotates the source code with a message that might be useful for
||| debugging a test failure.
export %inline
annotate : Applicative m => Lazy String -> TestT m ()
annotate v = writeLog $ Annotation v

||| Annotates the source code with a value that might be useful for
||| debugging a test failure.
export %inline
annotateShow : Show a => Applicative m => a -> TestT m ()
annotateShow v = annotate $ ppShow v

||| Logs a message to be displayed as additional information in the footer of
||| the failure report.
export %inline
footnote : Applicative m => Lazy String -> TestT m ()
footnote v = writeLog $ Footnote v

||| Logs a value to be displayed as additional information in the footer of
||| the failure report.
export %inline
footnoteShow : Show a => Applicative m => a -> TestT m ()
footnoteShow v = writeLog (Footnote $ ppShow v)

||| Fails with an error that shows the difference between two values.
export %inline
failDiff : Show a => Show b => Applicative m => a -> b -> TestT m ()
failDiff x y =
  case valueDiff <$> reify x <*> reify y of
    Nothing =>
        failWith Nothing $
        unlines $ [
            "Failed"
          , "━━ lhs ━━"
          , ppShow x
          , "━━ rhs ━━"
          , ppShow y
          ]

    Just vdiff@(Same _) =>
        failWith (Just $
          MkDiff "━━━ Failed ("  "" "no differences" "" ") ━━━" vdiff) ""

    Just vdiff =>
        failWith (Just $
          MkDiff "━━━ Failed (" "- lhs" ") (" "+ rhs" ") ━━━" vdiff) ""

||| Causes a test to fail.
export %inline
failure : Applicative m => TestT m a
failure = failWith Nothing ""

||| Another name for `pure ()`.
export %inline
success : Monad m => TestT m ()
success = pure ()

||| Fails the test if the condition provided is 'False'.
export %inline
assert : Monad m => Bool -> TestT m ()
assert ok = if ok then success else failure

||| Fails the test and shows a git-like diff if the comparison operation
||| evaluates to 'False' when applied to its arguments.
|||
||| The comparison function is the second argument, which may be
||| counter-intuitive to Haskell programmers. However, it allows operators to
||| be written infix for easy reading:
|||
||| This function behaves like the unix @diff@ tool, which gives a 0 exit
||| code if the compared files are identical, or a 1 exit code code
||| otherwise. Like unix @diff@, if the arguments fail the comparison, a
||| /diff is shown.
|||
export %inline
diff :  Show a
     => Show b
     => Monad m
     => a -> (a -> b -> Bool) -> b -> TestT m ()
diff x op y = if x `op` y then success else failDiff x y

infix 4 ===

||| Fails the test if the two arguments provided are not equal.
export %inline
(===) : Eq a => Show a => Monad m => a -> a -> TestT m ()
(===) x y = diff x (==) y

infix 4 /==

||| Fails the test if the two arguments provided are equal.
export %inline
(/==) : Eq a => Show a => Monad m => a -> a -> TestT m ()
(/==) x y = diff x (/=) y


||| Fails the test if the 'Either' is 'Left', otherwise returns the value in
||| the 'Right'.
export
evalEither : Show x => Monad m => Either x a -> TestT m a
evalEither (Left x)  = failWith Nothing (ppShow x)
evalEither (Right x) = pure x

||| Fails the test if the 'Maybe' is 'Nothing', otherwise returns the value in
||| the 'Just'.
export
evalMaybe : Monad m => Maybe a -> TestT m a
evalMaybe Nothing = failWith Nothing "the value was Nothing"
evalMaybe (Just x) = pure x

--------------------------------------------------------------------------------
--          PropertyT
--------------------------------------------------------------------------------

||| The property monad allows both the generation of test inputs
|||  and the assertion of expectations.
public export
0 PropertyT : Type -> Type
PropertyT = TestT Gen

||| Generates a random input for the test by running the provided generator.
|||
||| This is a the same as 'forAll' but allows the user to provide a custom
||| rendering function. This is useful for values which don't have a
||| 'Show' instance.
export
forAllWith : (a -> String) -> Gen a -> PropertyT a
forAllWith render gen = do x <- lift (lift gen)
                           annotate (render x)
                           pure x

||| Generates a random input for the test by running the provided generator.
export %inline
forAll : Show a => Gen a -> PropertyT a
forAll = forAllWith ppShow

||| Lift a test in to a property.
export
test : Test a -> PropertyT a
test = mapEitherT $ mapWriterT (pure . runIdentity)

--------------------------------------------------------------------------------
--          Property
--------------------------------------------------------------------------------

||| A property test, along with some configurable limits like how many times
||| to run the test.
public export
record Property where
  constructor MkProperty
  config : PropertyConfig
  test   : PropertyT ()

namespace Property
  ||| Map a config modification function over a property.
  export
  mapConfig : (PropertyConfig -> PropertyConfig) -> Property -> Property
  mapConfig f p = { config $= f } p

  verifiedTermination : Property -> Property
  verifiedTermination =
    mapConfig $ \config =>
      let
        newTerminationCriteria = case config.terminationCriteria of
          NoEarlyTermination c tests    => EarlyTermination c tests
          NoConfidenceTermination tests => EarlyTermination defaultConfidence tests
          EarlyTermination c tests      => EarlyTermination c tests
      in { terminationCriteria := newTerminationCriteria } config

  ||| Adjust the number of times a property should be executed before it is considered
  ||| successful.
  export
  mapTests : (TestLimit -> TestLimit) -> Property -> Property
  mapTests f = mapConfig {terminationCriteria $= setLimit}
    where setLimit : TerminationCriteria -> TerminationCriteria
          setLimit (NoEarlyTermination c n)    = NoEarlyTermination c (f n)
          setLimit (NoConfidenceTermination n) = NoConfidenceTermination (f n)
          setLimit (EarlyTermination c n)      = EarlyTermination c (f n)

  ||| Set the number of times a property should be executed before it is considered
  ||| successful.
  |||
  ||| If you have a test that does not involve any generators and thus does not
  ||| need to run repeatedly, you can use @withTests 1@ to define a property that
  ||| will only be checked once.
  export
  withTests : TestLimit -> Property -> Property
  withTests = mapTests . const

  ||| Set the number of times a property is allowed to shrink before the test
  ||| runner gives up and prints the counterexample.
  export
  withShrinks : ShrinkLimit -> Property -> Property
  withShrinks n = mapConfig { shrinkLimit := n }

  ||| Make sure that the result is statistically significant in accordance to
  ||| the passed 'Confidence'
  export
  withConfidence : Confidence -> Property -> Property
  withConfidence c = mapConfig { terminationCriteria $= setConfidence }
    where setConfidence : TerminationCriteria -> TerminationCriteria
          setConfidence (NoEarlyTermination _ n)    = NoEarlyTermination c n
          setConfidence (NoConfidenceTermination n) = NoConfidenceTermination n
          setConfidence (EarlyTermination _ n)      = EarlyTermination c n

||| Creates a property with the default configuration.
export
property : PropertyT () -> Property
property = MkProperty defaultConfig

||| A named collection of property tests.
public export
record Group where
  constructor MkGroup
  name       : GroupName
  properties : List (PropertyName, Property)

namespace Group
  export
  mapProperty : (Property -> Property) -> Group -> Group
  mapProperty f = { properties $= map (mapSnd f) }

  ||| Map a config modification function over all
  ||| properties in a `Group`.
  export
  mapConfig : (PropertyConfig -> PropertyConfig) -> Group -> Group
  mapConfig = mapProperty . mapConfig

  ||| Set the number of times the properties in a `Group`
  ||| should be executed before they are considered
  ||| successful.
  export
  withTests : TestLimit -> Group -> Group
  withTests = mapProperty . withTests

  ||| Set the number of times the properties in a `Group`
  ||| are allowed to shrink before the test
  ||| runner gives up and prints the counterexample.
  export
  withShrinks : ShrinkLimit -> Group -> Group
  withShrinks = mapProperty . withShrinks

  ||| Make sure that the results of a `Group` are statistically
  ||| significant in accordance to the passed 'Confidence'
  export
  withConfidence : Confidence -> Group -> Group
  withConfidence = mapProperty . withConfidence

--------------------------------------------------------------------------------
--          Coverage
--------------------------------------------------------------------------------

export
coverPercentage : TestCount -> CoverCount -> CoverPercentage
coverPercentage (MkTagged tests) (MkTagged count) =
  let percentage  = the Double (cast count / cast tests * 100)
      thousandths = round {a = Double} $ percentage * 10
  in MkTagged (thousandths / 10)

export
labelCovered : TestCount -> Label CoverCount -> Bool
labelCovered tests (MkLabel _ min population) =
  coverPercentage tests population >= min

export
coverageFailures : TestCount -> Coverage CoverCount -> List $ Label CoverCount
coverageFailures tests kvs =
  filter (not . labelCovered tests) (labels kvs)

||| All labels are covered
export
coverageSuccess : TestCount -> Coverage CoverCount -> Bool
coverageSuccess tests c = null $ coverageFailures tests c

||| Require a certain percentage of the tests to be covered by the
||| classifier.
|||
||| ```idris
|||    prop_with_coverage : Property
|||    prop_with_coverage =
|||      property $ do
|||        match <- forAll Gen.bool
|||        cover 30 "True" $ match
|||        cover 30 "False" $ not match
||| ```
|||
||| The example above requires a minimum of 30% coverage for both
||| classifiers. If these requirements are not met, it will fail the test.
export
cover : Monad m => CoverPercentage -> LabelName -> Bool -> TestT m ()
cover min name covered =
  let cover = if covered then Covered else NotCovered
   in writeLog $ LogLabel (MkLabel name min cover)

||| Records the proportion of tests which satisfy a given condition.
|||
||| ```idris example
|||    prop_with_classifier : Property
|||    prop_with_classifier =
|||      property $ do
|||        xs <- forAll $ Gen.list (Range.linear 0 100) Gen.alpha
|||        for_ xs $ \\x -> do
|||          classify "newborns" $ x == 0
|||          classify "children" $ x > 0 && x < 13
|||          classify "teens" $ x > 12 && x < 20
||| ```
export
classify : Monad m => LabelName -> Bool -> TestT m ()
classify name covered = cover 0 name covered

||| Add a label for each test run. It produces a table showing the percentage
||| of test runs that produced each label.
export
label : Monad m => LabelName -> TestT m ()
label name = cover 0 name True

||| Like 'label', but uses 'Show' to render its argument for display.
export
collect : Show a => Monad m => a -> TestT m ()
collect x = cover 0 (MkTagged $ show x) True


fromLabel : Label a -> Coverage a
fromLabel x = MkCoverage $ [(labelName x, x)]

unionsCoverage : Semigroup a => List (Coverage a) -> Coverage a
unionsCoverage = MkCoverage . concatMap coverageLabels

export
journalCoverage : Journal -> Coverage CoverCount
journalCoverage = map toCoverCount
                . unionsCoverage
                . (>>= fromLog)
                . journalLogs
  where fromLog : Lazy Log -> List (Coverage Cover)
        fromLog (LogLabel x)   = [fromLabel x]
        fromLog (Footnote _)   = []
        fromLog (Annotation _) = []

--------------------------------------------------------------------------------
--          Confidence
--------------------------------------------------------------------------------

-- not strictly true, but holds for the values we generate
-- in this module
times : InUnit -> InUnit -> InUnit
times (Element x _) (Element y _) =
  Element (x * y) (believe_me (Refl {x = True}))

oneMin : InUnit -> InUnit
oneMin (Element v _) = Element (1.0 - v) (believe_me (Refl {x = True} ))

half : InUnit -> InUnit
half = times (Element 0.5 Refl)

-- In order to get an accurate measurement with small sample sizes, we're
-- using the Wilson score interval
-- (<https://en.wikipedia.org/wiki/Binomial_proportion_confidence_interval#Wilson_score_interval wikipedia>) instead of a normal approximation interval.
wilsonBounds : Nat -> Nat -> InUnit -> (Double, Double)
wilsonBounds positives count acceptance =
  let
    p = the Double (cast positives / cast count)
    n = the Double (cast count)
    z = invnormcdf $ oneMin (half acceptance)

    midpoint = p + z * z / (2 * n)

    offset = z / (1 + z * z / n) * sqrt (p * (1 - p) / n + z * z / (4 * n * n))

    denominator = 1 + z * z / n

    low = (midpoint - offset) / denominator

    high = (midpoint + offset) / denominator
  in (low, high)

boundsForLabel : TestCount -> Confidence -> Label CoverCount -> (Double, Double)
boundsForLabel (MkTagged tests) (MkConfidence c ib) lbl =
  wilsonBounds (unTag lbl.labelAnnotation) tests (recipBits64 (Element c ib))

||| Is true when the test coverage satisfies the specified 'Confidence'
||| contstraint for all 'Coverage CoverCount's
export
confidenceSuccess : TestCount -> Confidence -> Coverage CoverCount -> Bool
confidenceSuccess tests confidence =
  all assertLow . labels
  where assertLow : Label CoverCount -> Bool
        assertLow cc =
          fst (boundsForLabel tests confidence cc) >=
          unTag cc.labelMinimum / 100.0

||| Is true when there exists a label that is sure to have failed according to
||| the 'Confidence' constraint
export
confidenceFailure : TestCount -> Confidence -> Coverage CoverCount -> Bool
confidenceFailure tests confidence =
  any assertHigh . labels
  where assertHigh : Label CoverCount -> Bool
        assertHigh cc =
          snd (boundsForLabel tests confidence cc) <
          (unTag cc.labelMinimum / 100.0)

export
multOf100 : TestCount -> Bool
multOf100 (MkTagged n) = natToInteger n `mod` 100 == 0

export
failureVerified : TestCount -> Coverage CoverCount -> Maybe Confidence -> Bool
failureVerified count cover conf =
  multOf100 count &&
  maybe False (\c => confidenceFailure count c cover) conf

export
successVerified : TestCount -> Coverage CoverCount -> Maybe Confidence -> Bool
successVerified count cover conf =
  multOf100 count &&
  maybe False (\c => confidenceSuccess count c cover) conf

export
abortEarly :  TerminationCriteria
           -> TestCount
           -> Coverage CoverCount
           -> Maybe Confidence
           -> Bool
abortEarly (EarlyTermination _ _) tests cover conf =
  let coverageReached     = successVerified tests cover conf
      coverageUnreachable = failureVerified tests cover conf
   in unTag tests >= unTag defaultMinTests &&
      (coverageReached || coverageUnreachable)

abortEarly _ _ _ _ = False
