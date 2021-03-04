module Hedgehog.Internal.Config

import Generics.Derive
import System

%language ElabReflection

%default total

--------------------------------------------------------------------------------
--          Config
--------------------------------------------------------------------------------

||| Whether to render output using ANSI colors or not.
public export
data UseColor = DisableColor | EnableColor

%runElab derive "UseColor" [Generic,Meta,Show,Eq,Ord]

||| How verbose should the report output be.
public export
data Verbosity = Quiet | Normal

%runElab derive "Verbosity" [Generic,Meta,Show,Eq,Ord]

--------------------------------------------------------------------------------
--          Detecting Config Settings
--------------------------------------------------------------------------------

lookupBool : HasIO io => String -> io (Maybe Bool)
lookupBool key =
  getEnv key >>= \case Just "0"     => pure $ Just False
                       Just "no"    => pure $ Just False
                       Just "false" => pure $ Just False

                       Just "1"     => pure $ Just True
                       Just "yes"   => pure $ Just True
                       Just "true"  => pure $ Just True

                       _            => pure Nothing

export
detectColor : HasIO io => io UseColor
detectColor =
  do Just True <- lookupBool "HEDGEHOG_COLOR"
       | _ => pure DisableColor
     pure EnableColor

export
detectVerbosity : HasIO io => io Verbosity
detectVerbosity =
  do Just "0" <- getEnv "HEDGEHOG_VERBOSITY"
       | _ => pure Normal
     pure Quiet

export
resolveColor : HasIO io => Maybe UseColor -> io UseColor
resolveColor = maybe detectColor pure

export
resolveVerbosity : HasIO io => Maybe Verbosity -> io Verbosity
resolveVerbosity = maybe detectVerbosity pure
