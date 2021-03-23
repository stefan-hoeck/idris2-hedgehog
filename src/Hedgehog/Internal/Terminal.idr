module Hedgehog.Internal.Terminal

import Control.ANSI.CSI
import Data.IORef
import Data.String
import System.File

public export
record Terminal where
  constructor MkTerminal
  tmp      : IORef (List String)
  out      : String -> IO ()
  err      : String -> IO ()

putStrErr : HasIO io => String -> io ()
putStrErr s = fPutStr stderr s $> ()

export
console : HasIO io => io Terminal
console = do ref <- newIORef []
             pure $ MkTerminal ref putStr putStrErr

clearTmp : Terminal -> IO ()
clearTmp t = do ls <- readIORef t.tmp
                t.err $ concatMap (\_ => cursorUp1 <+> eraseLine End) ls
                writeIORef t.tmp []

export
putTmp : HasIO io => Terminal -> String -> io ()
putTmp t str =
  let ls = lines str
   in liftIO $ do clearTmp t
                  writeIORef t.tmp ls
                  t.err (str <+> "\n")

export
putOut : HasIO io => Terminal -> String -> io ()
putOut t str = liftIO $ do clearTmp t
                           t.out (str <+> "\n")
