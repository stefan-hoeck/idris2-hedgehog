module Hedgehog.Internal.Report

import Data.Lazy
import Data.Nat
import Derive.Prelude
import Hedgehog.Internal.Config
import Hedgehog.Internal.Property
import Hedgehog.Internal.Range
import Hedgehog.Internal.Util
import System.Random.Pure.StdGen
import Text.Show.Diff
import Text.PrettyPrint.Bernardy.ANSI

%default total

%language ElabReflection

--------------------------------------------------------------------------------
--          Reporting
--------------------------------------------------------------------------------

public export
record FailedAnnotation where
  constructor MkFailedAnnotation
  failedValue : String

%runElab derive "FailedAnnotation" [Show,Eq]

public export
record FailureReport where
  constructor MkFailureReport
  size        : Size
  seed        : StdGen
  shrinks     : ShrinkCount
  coverage    : Maybe (Coverage CoverCount)
  annotations : List (Lazy FailedAnnotation)
  message     : String
  diff        : Maybe Diff
  footnotes   : List (Lazy String)

%runElab derive "FailureReport" [Show,Eq]

||| The status of a running property test.
public export
data Progress = Running | Shrinking FailureReport

%runElab derive "Progress" [Show,Eq]

||| The status of a completed property test.
|||
||| In the case of a failure it provides the seed used for the test, the
||| number of shrinks, and the execution log.
public export
data Result = Failed FailureReport | OK

%runElab derive "Result" [Show,Eq]

public export
isFailure : Result -> Bool
isFailure (Failed _) = True
isFailure OK         = False

public export
isSuccess : Result -> Bool
isSuccess = not . isFailure

||| A report on a running or completed property test.
public export
record Report a where
  constructor MkReport
  tests    : TestCount
  coverage : Coverage CoverCount
  status   : a

%runElab derive "Report" [Show,Eq]

export
Functor Report where
  map f = {status $= f}

export
Foldable Report where
  foldl f acc   = f acc . status
  foldr f acc r = f r.status acc
  null _        = False

export
Traversable Report where
  traverse f (MkReport t c a) = MkReport t c <$> f a

||| A summary of all the properties executed.
public export
record Summary where
  constructor MkSummary
  waiting : PropertyCount
  running : PropertyCount
  failed  : PropertyCount
  ok      : PropertyCount

%runElab derive "Summary" [Show,Eq,Semigroup,Monoid]

record ColumnWidth where
  constructor MkColumnWidth
  widthPercentage : Nat
  widthMinimum    : Nat
  widthName       : Nat
  widthNameFail   : Nat

Semigroup ColumnWidth where
  MkColumnWidth p0 m0 n0 f0 <+> MkColumnWidth p1 m1 n1 f1 =
    MkColumnWidth (max p0 p1) (max m0 m1) (max n0 n1) (max f0 f1)

Monoid ColumnWidth where
  neutral = MkColumnWidth 0 0 0 0

||| Construct a summary from a single result.
export
fromResult : Result -> Summary
fromResult (Failed _) = { failed := 1} neutral
fromResult OK         = { ok := 1} neutral

export
summaryCompleted : Summary -> PropertyCount
summaryCompleted (MkSummary _ _ x3 x4) = x3 + x4

export
summaryTotal : Summary -> PropertyCount
summaryTotal (MkSummary x1 x2 x3 x4) = x1 + x2 + x3 + x4

export
takeAnnotation : Lazy Log -> Maybe $ Lazy FailedAnnotation
takeAnnotation (Annotation x) = Just $ MkFailedAnnotation x
takeAnnotation (Footnote _  ) = Nothing
takeAnnotation (LogLabel _  ) = Nothing

export
takeFootnote : Lazy Log -> Maybe $ Lazy String
takeFootnote (Footnote x)   = Just x
takeFootnote (Annotation _) = Nothing
takeFootnote (LogLabel _)   = Nothing

export
mkFailure :
     Size
  -> StdGen
  -> ShrinkCount
  -> Maybe (Coverage CoverCount)
  -> String
  -> Maybe Diff
  -> List (Lazy Log)
  -> FailureReport
mkFailure size seed shrinks mcoverage message diff logs =
  let inputs    := mapMaybe takeAnnotation logs
      footnotes := mapMaybe takeFootnote logs
   in MkFailureReport size seed shrinks mcoverage inputs message diff footnotes

--------------------------------------------------------------------------------
--          Pretty Printing
--------------------------------------------------------------------------------

public export
data MarkupStyle = StyleDefault | StyleAnnotation | StyleFailure

export
Semigroup MarkupStyle where
  StyleFailure    <+> _               = StyleFailure
  _               <+> StyleFailure    = StyleFailure
  StyleAnnotation <+> _               = StyleAnnotation
  _               <+> StyleAnnotation = StyleAnnotation
  StyleDefault    <+> _               = StyleDefault

%runElab derive "MarkupStyle" [Show,Eq,Ord]

public export
data Markup =
    WaitingIcon
  | WaitingHeader
  | RunningIcon
  | RunningHeader
  | ShrinkingIcon
  | ShrinkingHeader
  | FailedIcon
  | FailedText
  | SuccessIcon
  | SuccessText
  | CoverageIcon
  | CoverageText
  | CoverageFill
  | StyledBorder MarkupStyle
  | AnnotationValue
  | DiffPrefix
  | DiffInfix
  | DiffSuffix
  | DiffSame
  | DiffRemoved
  | DiffAdded
  | ReproduceHeader
  | ReproduceGutter
  | ReproduceSource

%runElab derive "Markup" [Show,Eq,Ord]

color : Color -> List SGR
color c = [SetForeground c]

toAnsi : Markup -> List SGR
toAnsi (StyledBorder StyleAnnotation) = []
toAnsi (StyledBorder StyleDefault)    = []
toAnsi (StyledBorder StyleFailure)    = []
toAnsi AnnotationValue                = color Magenta
toAnsi CoverageFill                   = color BrightBlack
toAnsi CoverageIcon                   = color Yellow
toAnsi CoverageText                   = color Yellow
toAnsi DiffAdded                      = color Green
toAnsi DiffInfix                      = []
toAnsi DiffPrefix                     = []
toAnsi DiffRemoved                    = color Red
toAnsi DiffSame                       = []
toAnsi DiffSuffix                     = []
toAnsi FailedIcon                     = color BrightRed
toAnsi FailedText                     = color BrightRed
toAnsi ReproduceGutter                = []
toAnsi ReproduceHeader                = []
toAnsi ReproduceSource                = []
toAnsi RunningHeader                  = []
toAnsi RunningIcon                    = []
toAnsi ShrinkingHeader                = color BrightRed
toAnsi ShrinkingIcon                  = color BrightRed
toAnsi SuccessIcon                    = color Green
toAnsi SuccessText                    = color Green
toAnsi WaitingHeader                  = []
toAnsi WaitingIcon                    = []

testCount : TestCount -> String
testCount (MkTagged 1) = "1 test"
testCount (MkTagged n) = show n ++ " tests"

shrinkCount : ShrinkCount -> String
shrinkCount (MkTagged 1) = "1 shrink"
shrinkCount (MkTagged n) = show n ++ " shrinks"

%inline propertyCount : PropertyCount -> String
propertyCount (MkTagged n) = show n

renderCoverPercentage : CoverPercentage -> String
renderCoverPercentage (MkTagged p) =
  show (round {a = Double} (p * 10.0) / 10.0) ++ "%"

labelWidth : TestCount -> Label CoverCount -> ColumnWidth
labelWidth tests x =
  let percentage :=
        length . renderCoverPercentage $
        coverPercentage tests x.labelAnnotation

      minimum :=
        if x.labelMinimum == 0
           then the Nat 0
           else length . renderCoverPercentage $ x.labelMinimum

      name := length . unTag $ x.labelName

      nameFail = if labelCovered tests x then the Nat 0 else name

  in MkColumnWidth percentage minimum name nameFail

coverageWidth : TestCount -> Coverage CoverCount -> ColumnWidth
coverageWidth tests = concatMap (labelWidth tests) . labels

full : Char
full = '█'

parts : List Char
parts = ['·', '▏','▎','▍','▌','▋','▊','▉']

parameters {opts : LayoutOpts} (useColor : UseColor)
  markup : Markup -> Doc opts -> Doc opts
  markup m d = case useColor of
    DisableColor => d
    EnableColor  => decorate (toAnsi m) d

  %inline markupLine : Markup -> String -> Doc opts
  markupLine m = markup m . line

  gutter : Markup -> Doc opts -> Doc opts
  gutter m x = markup m rangle <++> x

  icon : Markup -> Char -> Doc opts -> Doc opts
  icon m i x = markup m (symbol i) <++> x

  lineDiff : LineDiff -> Doc opts
  lineDiff (LineSame x)    = markup DiffSame    $ "  " <+> pretty x
  lineDiff (LineRemoved x) = markup DiffRemoved $ "- " <+> pretty x
  lineDiff (LineAdded x)   = markup DiffAdded   $ "+ " <+> pretty x

  diff : Diff -> List (Doc opts)
  diff (MkDiff pre removed inf added suffix df) =
    ( markup DiffPrefix (line pre)      <+>
      markup DiffRemoved (line removed) <+>
      markup DiffInfix (line inf)       <+>
      markup DiffAdded (line added)     <+>
      markup DiffSuffix (line suffix)
    ) :: map lineDiff (toLineDiff df)

  reproduce : Maybe PropertyName -> Size -> StdGen -> Doc opts
  reproduce name size seed =
    let prop  := line $ maybe "<property>" unTag name
        instr := prettyCon Open "recheck" [prettyArg size, prettyArg seed, prop]
     in vsep
          [ markupLine ReproduceHeader "This failure can be reproduced by running:"
          , gutter ReproduceGutter $ markup ReproduceSource instr
          ]

  textLines : String -> List (Doc opts)
  textLines = map line . lines

  failedInput : Nat -> FailedAnnotation -> Doc opts
  failedInput ix (MkFailedAnnotation val) =
    vsep
      [ line "forAll \{show ix} ="
      , indent 2 . vsep . map (markup AnnotationValue . line) $ lines val
      ]

  failureReport :
       Maybe PropertyName
    -> TestCount
    -> FailureReport
    -> List (Doc opts)
  failureReport nm tests (MkFailureReport si se _ mcover inputs msg mdiff msgs0) =
      whenSome (empty ::)
    . whenSome (++ [empty])
    . intersperse empty
    . map (vsep . map (indent 2))
    . filter (\xs => not $ null xs)
    $ [intersperse empty args, coverage, docs, bottom]

    where
      whenSome : Foldable t => (t a -> t a) -> t a -> t a
      whenSome f xs = if null xs then xs else f xs

      bottom : List (Doc opts)
      bottom = maybe [reproduce nm si se] (const Nil) mcover

      docs : List (Doc opts)
      docs =
        concatMap
          textLines
          (map force msgs0 ++ if msg == "" then [] else [msg])
        <+> maybe [] diff mdiff

      args : List (Doc opts)
      args = zipWith failedInput [0 .. length inputs] (reverse $ map force inputs)

      coverage : List (Doc opts)
      coverage =
        case mcover of
          Nothing => []
          Just c  => do
            MkLabel _ _ count <- coverageFailures tests c
            pure $
                  line "Failed ("
              <+> markupLine CoverageText
                    (renderCoverPercentage (coverPercentage tests count))
              <+> " coverage)"

  ppName : Maybe PropertyName -> Doc opts
  ppName Nothing                = "<interactive>"
  ppName (Just $ MkTagged name) = text name

  leftPad : Nat -> Doc opts -> Doc opts
  leftPad n doc = doc >>= \l => pure $ indent (n `minus` width l) l

  coverBar : CoverPercentage -> CoverPercentage -> Doc opts
  coverBar (MkTagged percentage) (MkTagged minimum) =
    let barWidth         := the Nat 20
        coverageRatio    := percentage / 100.0
        coverageWidth    := toNat . floor $ coverageRatio * cast barWidth
        minimumRatio     := minimum / 100.0
        minimumWidth     := toNat . floor $ minimumRatio * cast barWidth
        fillWidth        := barWidth `minus` S coverageWidth
        fillErrorWidth   := minimumWidth `minus` S coverageWidth
        fillSurplusWidth := fillWidth `minus` fillErrorWidth

        ix :=
          toNat . floor $
          ((coverageRatio * cast barWidth) - cast coverageWidth) *
          cast (length parts)

        part :=
          symbol $
            case inBounds ix parts of
              Yes ib => index ix parts
              No  _  => head parts

     in hcat [ line $ replicate coverageWidth full
             , if coverageWidth < barWidth then
                 if ix == 0 then
                   if fillErrorWidth > 0 then markup FailedText part
                   else markup CoverageFill part
                 else part
               else empty
             , markupLine FailedText $ replicate fillErrorWidth (head parts)
             , markupLine CoverageFill $ replicate fillSurplusWidth (head parts)
             ]

  label : TestCount -> ColumnWidth -> Label CoverCount -> Doc opts
  label tests w x@(MkLabel name minimum count) =
    let covered  := labelCovered tests x
        ltext    := if not covered then markup CoverageText else id
        lborder  := markup (StyledBorder StyleDefault)
        licon    := if not covered then markup CoverageText "⚠ " else "  "
        lname    := padRight (cast w.widthName) ' ' (unTag name)
        wminimum := leftPad w.widthMinimum . line $ renderCoverPercentage minimum
        lcover   := wcover

        lminimum =
          if w.widthMinimum == 0 then empty
          else if not covered then " ✗ " <+> wminimum
          else if minimum == 0 then "   " <+> leftPad w.widthMinimum ""
          else " ✓ " <+> wminimum


     in hcat
          [ licon
          , ltext (line lname)
          , lborder " "
          , ltext lcover
          , lborder " "
          , ltext $ coverBar (coverPercentage tests count) minimum
          , lborder ""
          , ltext lminimum
          ]


    where wcover : Doc opts
          wcover =
            leftPad w.widthPercentage . line $
            renderCoverPercentage (coverPercentage tests count)

  coverage : TestCount -> Coverage CoverCount -> List (Doc opts)
  coverage tests x = map (label tests (coverageWidth tests x)) $ labels x

  whenNonZero : Doc opts -> PropertyCount -> Maybe (Doc opts)
  whenNonZero _      0 = Nothing
  whenNonZero suffix n = Just $ line (propertyCount n) <++> suffix

  export
  ppProgress : Maybe PropertyName -> Report Progress -> Doc opts
  ppProgress name (MkReport tests cov status) =
    case status of
       Running =>
         vsep $
           [ icon RunningIcon '●' . markup RunningHeader $
             ppName name <++> line "passed \{testCount tests} (running)"
           ] ++ coverage tests cov

       Shrinking failure =>
         icon ShrinkingIcon '↯' . markup ShrinkingHeader $
           ppName name <++> line "failed after \{testCount tests}"

  annotateSummary : Summary -> Doc opts -> Doc opts
  annotateSummary summary =
    if summary.failed > 0 then
      icon FailedIcon '✗' . markup FailedText
    else if summary.waiting > 0 || summary.running > 0 then
      icon WaitingIcon '○' . markup WaitingHeader
    else
      icon SuccessIcon '✓' . markup SuccessText

  ppResult : Maybe PropertyName -> Report Result -> Doc opts
  ppResult name (MkReport tests cov result) =
    case result of
      Failed failure =>
        vsep $
        [ icon FailedIcon '✗' . markup FailedText $
          ppName name <++>
          line "failed after \{testCount tests}."
        ] ++
        coverage tests cov ++
        failureReport name tests failure

      OK =>
        vsep $
          [ icon SuccessIcon '✓' . markup SuccessText $
            ppName name <++> line "passed \{testCount tests}."
          ] ++
          coverage tests cov

  export
  ppSummary : Summary -> Doc opts
  ppSummary summary =
    let complete := summaryCompleted summary == summaryTotal summary
        suffix   := if complete then line "." else line " (running)"

     in annotateSummary summary .
          (<+> suffix)
        . hcat
        . addPrefix complete
        . intersperse (line ", ")
        $ catMaybes [
            whenNonZero "failed" summary.failed
          , if complete then
              whenNonZero "succeeded" summary.ok
            else
              Nothing
        ]

    where
      doPrefix : Bool -> Doc opts -> Doc opts
      doPrefix True _    = empty
      doPrefix False end =
        let pc1 := propertyCount (summaryCompleted summary)
            pc2 := propertyCount (summaryTotal summary)
         in line "\{pc1} / \{pc2} complete" <+> end

      addPrefix : Bool -> List (Doc opts) -> List (Doc opts)
      addPrefix complete [] = [doPrefix complete empty]
      addPrefix complete xs = doPrefix complete ": " :: xs

public export
LL80 : LayoutOpts
LL80 = Opts 80

export
renderDoc : Doc LL80 -> String
renderDoc = render LL80 . indent 2

export
renderProgress : UseColor -> Maybe PropertyName -> Report Progress -> String
renderProgress color name = renderDoc . ppProgress color name

export
renderResult : UseColor -> Maybe PropertyName -> Report Result -> String
renderResult color name = renderDoc . ppResult color name

export
renderSummary : UseColor -> Summary -> String
renderSummary color = renderDoc . ppSummary color

--------------------------------------------------------------------------------
--          Test Report
--------------------------------------------------------------------------------

export
report :
     (aborted : Bool)
  -> TestCount
  -> Size
  -> StdGen
  -> Coverage CoverCount
  -> Maybe Confidence
  -> Report Result
report aborted tests size seed cover conf =
  let failureReport := \msg =>
        MkReport tests cover . Failed $
          mkFailure size seed 0 (Just cover) msg Nothing []

      coverageReached := successVerified tests cover conf

      labelsCovered := coverageSuccess tests cover

      successReport := MkReport tests cover OK

      confidenceReport =
        if coverageReached && labelsCovered
           then successReport
           else
             failureReport
               "Test coverage cannot be reached after \{tests} tests"

  in if aborted then confidenceReport
     else if labelsCovered then successReport
     else
       failureReport $
         "Labels not sufficently covered after \{tests} tests"
