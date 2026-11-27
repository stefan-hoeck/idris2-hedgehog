module Hedgehog.Internal.Terminal

import Control.Monad.Writer.Interface

import Text.ANSI.CSI
import Data.IORef
import Data.String
import System.File

||| Interface showing that in the given monadic context `m` user can
||| initialise terminal and use it for printing temporary and permanent info.
public export
interface HasTerminal m where

  ||| Type of initialised terminal
  0 TermTy : Type

  ||| Return new initialised terminal
  |||
  ||| Notice that usage of several initalised terminals is not supposed
  ||| and may lead to unexpected behaviour.
  console  : m TermTy

  ||| Put temporary info into the terminal
  |||
  ||| Any successive putting temporary or permanent info into the terminal
  ||| makes any previously put temporary info disappear.
  putTmp   : TermTy -> String -> m ()

  ||| Put permanent info into the terminal
  |||
  ||| This action makes previously put temporary info disappear
  putOut   : TermTy -> String -> m ()

||| Returns the type of initialised terminal
||| for the explicitly given context `m`
public export
0 Terminal : (0 m : _) -> HasTerminal m => Type
Terminal m = TermTy {m}

putStrErr : HasIO io => String -> io ()
putStrErr s = fPutStr stderr s $> ()

replicate : Monoid m => Nat -> m -> m
replicate Z     x = neutral
replicate (S n) x = x <+> replicate n x

clearIOTmp : IORef Nat -> IO ()
clearIOTmp tmp = do
  linesCnt <- readIORef tmp
  putStrErr $ Terminal.replicate linesCnt $ cursorUp1 <+> eraseLine End
  writeIORef tmp 0

||| Uses system stdout for permanent printing and stderr for temporary printing
export
HasIO io => HasTerminal io where
  TermTy  = IORef Nat
  console = liftIO $ newIORef 0
  putTmp t str = liftIO $ do
    clearIOTmp t
    writeIORef t $ length $ lines str
    putStrErr str
  putOut t str = liftIO $ clearIOTmp t *> putStr str

||| Uses monadic writer to remember everything
||| written permanently to the terminal
|||
||| This implementation does not use any type of actual printing to any
||| real terminal, this is completely pure.
export
[StdoutOnly] MonadWriter (List String) m => HasTerminal m where
  TermTy       = Unit
  console      = pure ()
  putTmp _ _   = pure ()
  putOut _ str = tell [str]

public export
data StdoutOrTmp = Stdout | Tmp

||| Uses monadic writer to remember everything
||| written temporarily and permanently to the terminal
|||
||| The order of writes is completely preserved.
||| Type of the write is determined by the `StdoutOrTmp` discriminator.
|||
||| This implementation does not use any type of actual printing to any
||| real terminal, this is completely pure.
export
[StdoutAndTmp] MonadWriter (List (StdoutOrTmp, String)) m => HasTerminal m where
  TermTy       = Unit
  console      = pure ()
  putTmp _ str = tell [(Tmp, str)]
  putOut _ str = tell [(Stdout, str)]
