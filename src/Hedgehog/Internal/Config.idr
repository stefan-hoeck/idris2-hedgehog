module Hedgehog.Internal.Config

import Derive.Prelude
import System

%language ElabReflection

%default total

--------------------------------------------------------------------------------
--          Config
--------------------------------------------------------------------------------

||| Whether to render output using ANSI colors or not.
public export
data UseColor = DisableColor | EnableColor

%runElab derive "UseColor" [Show,Eq,Ord]

||| How verbose should the report output be.
public export
data Verbosity = Quiet | Normal

%runElab derive "Verbosity" [Show,Eq,Ord]

--------------------------------------------------------------------------------
--          Detecting Config Settings
--------------------------------------------------------------------------------

||| Defines points of an global configuration for a Hedgehog run
public export
interface HasConfig m where
  constructor MkHasConfig
  detectColor     : m UseColor
  detectVerbosity : m Verbosity

export
resolveColor : HasConfig m => Applicative m => Maybe UseColor -> m UseColor
resolveColor = maybe detectColor pure

export
resolveVerbosity : HasConfig m => Applicative m => Maybe Verbosity -> m Verbosity
resolveVerbosity = maybe detectVerbosity pure

lookupBool : HasIO io => String -> io (Maybe Bool)
lookupBool key =
  getEnv key >>= \case Just "0"     => pure $ Just False
                       Just "no"    => pure $ Just False
                       Just "false" => pure $ Just False

                       Just "1"     => pure $ Just True
                       Just "yes"   => pure $ Just True
                       Just "true"  => pure $ Just True

                       _            => pure Nothing

||| Reads the global configuration from environment variables
export
HasIO io => HasConfig io where
  detectColor =
    do Just True <- lookupBool "HEDGEHOG_COLOR"
         | _ => pure DisableColor
       pure EnableColor

  detectVerbosity =
    do Just "0" <- getEnv "HEDGEHOG_VERBOSITY"
         | _ => pure Normal
       pure Quiet

||| Uses the most conservative configuration
|||
||| This implementation is applicable for any applicative context,
||| including pure ones.
export -- should be a `%defaulthint`, but does not work due to issue #2850
[DefaultConfig] Applicative m => HasConfig m where
  detectColor     = pure DisableColor
  detectVerbosity = pure Normal
