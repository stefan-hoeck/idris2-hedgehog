module Hedgehog.Internal.Runner

import Data.Colist
import Data.Cotree
import Data.IORef
import Data.List
import Hedgehog.Internal.Config
import Hedgehog.Internal.Gen
import Hedgehog.Internal.Property
import Hedgehog.Internal.Range
import Hedgehog.Internal.Report
import Hedgehog.Internal.Seed
import Hedgehog.Internal.Terminal

%default total

public export
TestRes : Type
TestRes = (Either Failure (), Journal)

findM : Monad m => Nat -> Coforest a -> b -> (Nat -> a -> m (Maybe b)) -> m b
findM _     []        b _ = pure b
findM 0 _             b _ = pure b
findM (S k) (t :: ts) b f = do Just b2 <- f (S k) t.value 
                                 | Nothing => findM k ts b f
                               findM k t.forest b2 f

multOf100 : TestCount -> Bool
multOf100 (MkTagged n) = natToInteger n `mod` 100 == 0

takeSmallest :
     Monad m
  => Size
  -> Seed
  -> ShrinkLimit
  -> (Progress -> m ())
  -> Cotree TestRes
  -> m Result
takeSmallest si se slimit updateUI t =
  do res <- run (MkTagged $ unTag slimit) t.value
     if isFailure res
        then findM (unTag slimit) t.forest res runMaybe
        else pure res

  where
    calcShrinks : Nat -> ShrinkCount
    calcShrinks n = MkTagged $ (unTag slimit `minus` n) + 1

    run : ShrinkCount -> TestRes -> m Result
    run shrinks t =
      case t of
        (Left $ MkFailure err diff, MkJournal logs) =>
           let fail = mkFailure si se shrinks Nothing err diff (reverse logs)
            in updateUI (Shrinking fail) $> Failed fail

        (Right x, _) => pure OK

    runMaybe : Nat -> TestRes -> m (Maybe Result)
    runMaybe shrinksLeft testRes =
      do res <- run (calcShrinks shrinksLeft) testRes
         if isFailure res then pure (Just res) else pure Nothing

covering
checkReport :
     Monad m
  => PropertyConfig
  -> Size
  -> Seed
  -> PropertyT ()
  -> (Report Progress -> m ())
  -> m (Report Result)
checkReport cfg size0 seed0 test updateUI =
  let (confidence, minTests) =
        case cfg.terminationCriteria of
          EarlyTermination c t      => (Just c, t)
          NoEarlyTermination c t    => (Just c, t)
          NoConfidenceTermination t => (Nothing, t)

   in loop 0 size0 seed0 neutral confidence minTests
  where successVerified : TestCount -> Coverage CoverCount -> Maybe Confidence -> Bool
        successVerified count coverage confidence =
          multOf100 count &&
          maybe False (\c => confidenceSuccess count c coverage) confidence

        failureVerified : TestCount -> Coverage CoverCount -> Maybe Confidence -> Bool
        failureVerified count coverage confidence =
          multOf100 count &&
          maybe False (\c => confidenceFailure count c coverage) confidence

        covering
        loop :  TestCount
             -> Size
             -> Seed
             -> Coverage CoverCount
             -> Maybe Confidence
             -> TestLimit
             -> m (Report Result)
        loop tests size seed coverage0 confidence minTests =
          let coverageReached     = successVerified tests coverage0 confidence

              coverageUnreachable = failureVerified tests coverage0 confidence

              enoughTestsRun =
                case cfg.terminationCriteria of
                  EarlyTermination _ _ =>
                    unTag tests >= unTag defaultMinTests &&
                    (coverageReached || coverageUnreachable)
                  NoEarlyTermination _ _    => unTag tests >= unTag minTests
                  NoConfidenceTermination _ => unTag tests >= unTag minTests

              labelsCovered = coverageSuccess tests coverage0

              successReport = MkReport tests coverage0 OK

              failureReport = \msg =>
                MkReport tests coverage0 . Failed $
                  mkFailure size seed 0 (Just coverage0) msg Nothing []

              confidenceReport =
                if coverageReached && labelsCovered
                   then successReport
                   else failureReport $
                          "Test coverage cannot be reached after " <+>
                          show tests <+>
                          " tests"

           in do updateUI $ MkReport tests coverage0 Running
                 if size == maxSize
                    then loop tests 0 seed coverage0 confidence minTests
                    else if enoughTestsRun
                      then
                         -- at this point, we know that enough
                         -- tests have been run in order to
                         -- make a decision on if this was a
                         -- successful run or not
                         --
                         -- If we have early termination, then we need
                         -- to check coverageReached / coverageUnreachable
                         pure $ case cfg.terminationCriteria of
                           EarlyTermination _ _ => confidenceReport
                           NoEarlyTermination _ _ => confidenceReport
                           NoConfidenceTermination _ =>
                             if labelsCovered then
                               successReport
                             else
                               failureReport $
                                 "Labels not sufficently covered after " <+>
                                 show tests <+>
                                 " tests"
                      else
                        let (s0,s1) = split seed
                            tr      = runGen size s0 $ runTestT test
                         in case tr.value of
                                 (Left x, _)  =>
                                    map (MkReport (tests+1) coverage0) $
                                      takeSmallest
                                        size
                                        seed
                                        cfg.shrinkLimit
                                        (updateUI . MkReport (tests+1) coverage0)
                                        tr

                                 (Right x, journal) =>
                                   let coverage = journalCoverage journal <+> coverage0
                                    in loop (tests + 1) (size + 1) s1 coverage confidence minTests
                        

covering
checkTerm :  HasIO io
          => Terminal
          -> UseColor
          -> Maybe PropertyName
          -> Size
          -> Seed
          -> Property
          -> io (Report Result)
checkTerm term color name si se prop =
  do result <- checkReport {m = io} prop.config si se prop.test \prog =>
               if multOf100 prog.tests
                  then let ppprog = renderProgress color name prog
                        in case prog.status of
                               Running     => putTmp term ppprog
                               Shrinking _ => putTmp term ppprog
                  else pure ()

     let ppresult : String
         ppresult = renderResult color name result

     case result.status of
          Failed f => putOut term ppresult
          OK       => putOut term ppresult

     pure result

covering
checkWith :  HasIO io
          => Terminal
          -> UseColor
          -> Maybe PropertyName
          -> Property
          -> io (Report Result)
checkWith term color name prop =
  do seed <- initSMGen
     checkTerm term color name 0 seed prop

||| Check a property.
export covering
checkNamed : HasIO io => PropertyName -> Property -> io Bool
checkNamed name prop = do
  color <- detectColor
  term  <- console
  rep   <- checkWith term color (Just name) prop
  pure $ rep.status == OK

||| Check a property.
export covering
check : HasIO io => Property -> io Bool
check prop = do
  color <- detectColor
  term  <- console
  rep   <- checkWith term color Nothing prop
  pure $ rep.status == OK

||| Check a property using a specific size and seed.
export covering
recheck : HasIO io => Size -> Seed -> Property -> io ()
recheck size seed prop = do
  color <- detectColor
  term  <- console
  _     <- checkTerm term color Nothing size seed (withTests 1 prop)
  pure ()

covering
checkGroupWith :  Terminal
               -> UseColor
               -> List (PropertyName, Property)
               -> IO Summary
checkGroupWith term color = run neutral
  where run : Summary -> List (PropertyName, Property) -> IO Summary
        run s [] = pure s
        run s ((pn,p) :: ps) = do rep  <- checkWith term color (Just pn) p
                                  run (s <+> fromResult rep.status) ps
  
export covering
checkGroup : HasIO io => Group -> io Bool
checkGroup (MkGroup group props) =
  do term    <- console
     putOut term $ "━━━ " ++ unTag group ++ " ━━━"
     color   <- detectColor
     summary <- liftIO $ checkGroupWith term color props
     putOut term (renderSummary color summary)
     pure $ summary.failed == 0
