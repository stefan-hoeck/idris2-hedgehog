module Hedgehog.Internal.Report

import Data.List1
import Data.Nat
import Data.SortedMap
import Generics.Derive
import Hedgehog.Internal.Config
import Hedgehog.Internal.Property
import Hedgehog.Internal.Range
import Hedgehog.Internal.Seed
import Hedgehog.Internal.Util
import Text.Show.Diff
import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Render.Terminal as Term
import Text.PrettyPrint.Prettyprinter.Render.String   as Str

%default total

%language ElabReflection

--------------------------------------------------------------------------------
--          Reporting
--------------------------------------------------------------------------------

public export
record FailedAnnotation where
  constructor MkFailedAnnotation
  failedValue : String

%runElab derive "FailedAnnotation" [Generic,Meta,Show,Eq]

public export
record FailureReport where
  constructor MkFailureReport
  size        : Size
  seed        : Seed
  shrinks     : ShrinkCount
  coverage    : Maybe (Coverage CoverCount)
  annotations : List FailedAnnotation
  message     : String
  diff        : Maybe Diff
  footnotes   : List String

%runElab derive "FailureReport" [Generic,Meta,Show,Eq]

||| The status of a running property test.
public export
data Progress = Running | Shrinking FailureReport

%runElab derive "Progress" [Generic,Meta,Show,Eq]

||| The status of a completed property test.
|||
||| In the case of a failure it provides the seed used for the test, the
||| number of shrinks, and the execution log.
public export
data Result = Failed FailureReport | OK

%runElab derive "Result" [Generic,Meta,Show,Eq]

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

%runElab derive "Report" [Generic,Meta,Show,Eq]

export
Functor Report where
  map f = record {status $= f}

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

%runElab derive "Summary" [Generic,Meta,Show,Eq,Semigroup,Monoid]

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
fromResult (Failed _) = record { failed = 1} neutral
fromResult OK         = record { ok = 1} neutral

export
summaryCompleted : Summary -> PropertyCount
summaryCompleted (MkSummary _ _ x3 x4) = x3 + x4

export
summaryTotal : Summary -> PropertyCount
summaryTotal (MkSummary x1 x2 x3 x4) = x1 + x2 + x3 + x4

export
takeAnnotation : Lazy Log -> Maybe FailedAnnotation
takeAnnotation (Annotation x) = Just $ MkFailedAnnotation x
takeAnnotation (Footnote _  ) = Nothing
takeAnnotation (LogLabel _  ) = Nothing

export
takeFootnote : Lazy Log -> Maybe String
takeFootnote (Footnote x)   = Just x
takeFootnote (Annotation _) = Nothing
takeFootnote (LogLabel _)   = Nothing

export
mkFailure :  Size
          -> Seed
          -> ShrinkCount
          -> Maybe (Coverage CoverCount)
          -> String
          -> Maybe Diff
          -> List (Lazy Log)
          -> FailureReport
mkFailure size seed shrinks mcoverage message diff logs =
  let inputs    = mapMaybe takeAnnotation logs
      footnotes = mapMaybe takeFootnote logs
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

%runElab derive "MarkupStyle" [Generic,Meta,Show,Eq]

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

ppShow : Show x => x -> Doc ann
ppShow = pretty . show

markup : Markup -> Doc Markup -> Doc Markup
markup = annotate

gutter : Markup -> Doc Markup -> Doc Markup
gutter m x = markup m ">" <++> x

icon : Markup -> Char -> Doc Markup -> Doc Markup
icon m i x = markup m (pretty i) <++> x

ppTestCount : TestCount -> Doc ann
ppTestCount (MkTagged 1) = "1 test"
ppTestCount (MkTagged n) = ppShow n <++> "tests"

ppShrinkCount : ShrinkCount -> Doc ann
ppShrinkCount (MkTagged 1) = "1 shrink"
ppShrinkCount (MkTagged n) = ppShow n <++> "shrinks"

ppRawPropertyCount : PropertyCount -> Doc ann
ppRawPropertyCount (MkTagged n) = ppShow n

ppLineDiff : LineDiff -> Doc Markup
ppLineDiff (LineSame x)    = markup DiffSame    $ "  " <+> pretty x
ppLineDiff (LineRemoved x) = markup DiffRemoved $ "- " <+> pretty x
ppLineDiff (LineAdded x)   = markup DiffAdded   $ "+ " <+> pretty x

ppDiff : Diff -> List (Doc Markup)
ppDiff (MkDiff pre removed inf added suffix diff) =
    ( markup DiffPrefix (pretty pre)      <+>
      markup DiffRemoved (pretty removed) <+>
      markup DiffInfix (pretty inf)       <+>
      markup DiffAdded (pretty added)     <+>
      markup DiffSuffix (pretty suffix)
    ) :: map ppLineDiff (toLineDiff diff)

ppLabelName : LabelName -> Doc ann
ppLabelName = pretty . unTag

renderCoverPercentage : CoverPercentage -> String
renderCoverPercentage (MkTagged p) = show (round (p * 10.0) / 10.0) <+> "%"

ppCoverPercentage : CoverPercentage -> Doc Markup
ppCoverPercentage = pretty . renderCoverPercentage

ppReproduce : Maybe PropertyName -> Size -> Seed -> Doc Markup
ppReproduce name size seed =
  vsep [
    markup ReproduceHeader "This failure can be reproduced by running:"
  , gutter ReproduceGutter . markup ReproduceSource $
        "recheck" <++>
        pretty (showPrec App size) <++>
        pretty (showPrec App seed) <++>
        maybe "<property>" (pretty . unTag) name
  ]

ppTextLines : String -> List (Doc Markup)
ppTextLines = map pretty . lines

ppFailedInput : Nat -> FailedAnnotation -> Doc Markup
ppFailedInput ix (MkFailedAnnotation val) =
  vsep [
    "forAll" <++> ppShow ix <++> "="
  , indent 2 . vsep . map (markup AnnotationValue . pretty) $ lines val
  ]

ppFailureReport :  Maybe PropertyName
                -> TestCount
                -> FailureReport
                -> List (Doc Markup)
ppFailureReport nm tests (MkFailureReport si se _ mcover inputs msg mdiff msgs0) =
  whenSome (neutral ::)         .
  whenSome (++ [neutral])       .
  punctuate line                .
  map (vsep . map (indent 2))   .
  filter (\xs => not $ null xs) $
  [punctuate line args, coverage, docs, bottom]

  where whenSome : Foldable t => (t a -> t a) -> t a -> t a
        whenSome f xs = if null xs then xs else f xs

        bottom : List (Doc Markup)
        bottom = maybe [ppReproduce nm si se] (const Nil) mcover

        docs : List (Doc Markup)
        docs = concatMap ppTextLines (msgs0 ++ if msg == "" then [] else [msg])
             <+> maybe [] ppDiff mdiff

        args : List (Doc Markup)
        args = zipWith ppFailedInput [0 .. length inputs] (reverse inputs)

        coverage : List (Doc Markup)
        coverage =
          case mcover of
            Nothing => []
            Just c  => do MkLabel _ _ count <- coverageFailures tests c
                          pure $
                            cat [ "Failed ("
                                , annotate CoverageText $
                                    ppCoverPercentage (coverPercentage tests count)
                                    <+> " coverage"
                                , ")"
                                ]

ppName : Maybe PropertyName -> Doc ann
ppName Nothing                = "<interactive>"
ppName (Just $ MkTagged name) = pretty name

labelWidth : TestCount -> Label CoverCount -> ColumnWidth
labelWidth tests x =
  let percentage = length .
                   renderCoverPercentage $
                   coverPercentage tests x.labelAnnotation

      minimum = if x.labelMinimum == 0
                   then the Nat 0
                   else length .
                        renderCoverPercentage $
                        x.labelMinimum

      name = length . unTag $ x.labelName

      nameFail = if labelCovered tests x then the Nat 0 else name

  in MkColumnWidth percentage minimum name nameFail

coverageWidth : TestCount -> Coverage CoverCount -> ColumnWidth
coverageWidth tests (MkCoverage labels) = concatMap (labelWidth tests) labels

ppLeftPad : Nat -> Doc ann -> Doc ann
ppLeftPad n doc =
  let ndoc = length (show doc)
      pad  = pretty . pack $ replicate (n `minus` ndoc) ' '
   in pad <+> doc

ppCoverBar : CoverPercentage -> CoverPercentage -> Doc Markup
ppCoverBar (MkTagged percentage) (MkTagged minimum) =
  let barWidth         = the Nat 20
      coverageRatio    = percentage / 100.0
      coverageWidth    = toNat . floor $ coverageRatio * cast barWidth
      minimumRatio     = minimum / 100.0
      minimumWidth     = toNat . floor $ minimumRatio * cast barWidth
      fillWidth        = pred $ barWidth `minus` coverageWidth
      fillErrorWidth   = pred $ minimumWidth `minus` coverageWidth
      fillSurplusWidth = fillWidth `minus` fillErrorWidth
      full             = '█'
      parts1           = '·' ::: ['▏','▎','▍','▌','▋','▊','▉']
      parts            = forget parts1

      ix               = toNat . floor $
                         ((coverageRatio * cast barWidth) - cast coverageWidth)
                         * cast (length parts)

      part             = case inBounds ix parts of
                              Yes ib => index ix parts
                              No  _  => head parts1

   in hcat [ pretty . pack $ replicate coverageWidth full
           , if coverageWidth < barWidth then
               if ix == 0 then
                 if fillErrorWidth > 0 then annotate FailedText $ pretty part
                 else annotate CoverageFill $ pretty part
               else pretty part
             else ""
           , annotate FailedText . pretty  . pack $
               replicate fillErrorWidth (head parts1)
           , annotate CoverageFill . pretty . pack $
               replicate fillSurplusWidth (head parts1)
           ]

ppLabel : TestCount -> ColumnWidth -> Label CoverCount -> Doc Markup
ppLabel tests w x@(MkLabel name minimum count) =
  let covered  = labelCovered tests x
      ltext    = if not covered then annotate CoverageText else id
      lborder  = annotate (StyledBorder StyleDefault)
      licon    = if not covered then annotate CoverageText "⚠ " else "  "
      lname    = fill (cast w.widthName) (ppLabelName name)
      wminimum = ppLeftPad w.widthMinimum $ ppCoverPercentage minimum
      lcover   = wcover ""

      lminimum =
        if w.widthMinimum == 0 then neutral
        else if not covered then " ✗ " <+> wminimum
        else if minimum == 0 then "   " <+> ppLeftPad w.widthMinimum ""
        else " ✓ " <+> wminimum


   in hcat [ licon
           , ltext lname
           , lborder " "
           , ltext lcover
           , lborder " "
           , ltext $ ppCoverBar (coverPercentage tests count) minimum
           , lborder ""
           , ltext lminimum
           ]


  where wcover : String -> Doc Markup
        wcover i = ppLeftPad (w.widthPercentage + length i) $
                   pretty i <+>
                   ppCoverPercentage (coverPercentage tests count)

ppCoverage : TestCount -> Coverage CoverCount -> List (Doc Markup)
ppCoverage tests x =
  map (ppLabel tests (coverageWidth tests x)) $
  values x.coverageLabels

ppWhenNonZero : Doc ann -> PropertyCount -> Maybe (Doc ann)
ppWhenNonZero _      0 = Nothing
ppWhenNonZero suffix n = Just $ ppRawPropertyCount n <++> suffix

export
ppProgress : Maybe PropertyName -> Report Progress -> Doc Markup
ppProgress name (MkReport tests coverage status) =
  case status of
     Running =>
       vsep $ [ icon RunningIcon '●' . annotate RunningHeader $
                ppName name <++>
                "passed" <++>
                ppTestCount tests <+> "(running)"
              ] ++ ppCoverage tests coverage

     Shrinking failure =>
       icon ShrinkingIcon '↯' . annotate ShrinkingHeader $
         ppName name <++> "failed after" <++> ppTestCount tests

annotateSummary : Summary -> Doc Markup -> Doc Markup
annotateSummary summary =
  if summary.failed > 0 then
    icon FailedIcon '✗' . annotate FailedText
  else if summary.waiting > 0 || summary.running > 0 then
    icon WaitingIcon '○' . annotate WaitingHeader
  else
    icon SuccessIcon '✓' . annotate SuccessText

ppResult : Maybe PropertyName -> Report Result -> Doc Markup
ppResult name (MkReport tests coverage result) =
  case result of
    Failed failure =>
      vsep $ [ icon FailedIcon '✗' . align . annotate FailedText $
               ppName name <++>
               "failed after" <++>
               ppTestCount tests <+>
               "."
             ] ++
             ppCoverage tests coverage ++
             ppFailureReport name tests failure

    OK => vsep $ [ icon SuccessIcon '✓' . annotate SuccessText $
                   ppName name <++>
                   "passed" <++>
                   ppTestCount tests <+>
                   "."
                 ] ++
                 ppCoverage tests coverage

export
ppSummary : Summary -> Doc Markup
ppSummary summary =
  let complete = summaryCompleted summary == summaryTotal summary
      suffix = if complete then the (Doc Markup) "." else " (running)"

   in annotateSummary summary .
      (<+> suffix) .
      hcat .
      addPrefix complete .
      punctuate ", " $
      catMaybes [
          ppWhenNonZero "failed" summary.failed
        , if complete then
            ppWhenNonZero "succeeded" summary.ok
          else
            Nothing
      ]

  where doPrefix : Bool -> Doc Markup -> Doc Markup
        doPrefix True _    = neutral
        doPrefix False end =
          ppRawPropertyCount (summaryCompleted summary) <+>
          "/" <+>
          ppRawPropertyCount (summaryTotal summary) <++>
          "complete" <+> end

        addPrefix : Bool -> List (Doc Markup) -> List (Doc Markup)
        addPrefix complete [] = [doPrefix complete neutral]
        addPrefix complete xs = doPrefix complete ": " :: xs

toAnsi : Markup -> AnsiStyle
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

export
renderDoc : UseColor -> Doc Markup -> String
renderDoc usecol doc =
  let stream = layoutSmart defaultLayoutOptions
             $ indent 2 doc

   in case usecol of
           DisableColor => Str.renderString stream
           EnableColor  => Term.renderString $ reAnnotateS toAnsi stream

export
renderProgress : UseColor -> Maybe PropertyName -> Report Progress -> String
renderProgress color name = renderDoc color . ppProgress name

export
renderResult : UseColor -> Maybe PropertyName -> Report Result -> String
renderResult color name = renderDoc color . ppResult name

export
renderSummary : UseColor -> Summary -> String
renderSummary color = renderDoc color . ppSummary

--------------------------------------------------------------------------------
--          Test Report
--------------------------------------------------------------------------------

export
report :  (aborted : Bool)
       -> TestCount
       -> Size
       -> Seed
       -> Coverage CoverCount
       -> Maybe Confidence
       -> Report Result
report aborted tests size seed cover conf =
  let failureReport = \msg =>
        MkReport tests cover . Failed $
          mkFailure size seed 0 (Just cover) msg Nothing []

      coverageReached = successVerified tests cover conf

      labelsCovered = coverageSuccess tests cover

      successReport = MkReport tests cover OK

      confidenceReport =
        if coverageReached && labelsCovered
           then successReport
           else failureReport $
                  "Test coverage cannot be reached after " <+>
                  show tests <+>
                  " tests"

  in if aborted then confidenceReport
     else if labelsCovered then successReport
     else failureReport $
          "Labels not sufficently covered after " <+>
          show tests <+>
          " tests"
