module Development.Shake.Command.Extra
  ( mSilent
  ) where

import Control.Monad (when)
import Development.Shake
import System.IO (hPutStr, stderr)

mSilent :: Action (Stdout String, Stderr String) -> Action ()
mSilent cmdAction = do
  (Stdout msg, Stderr err) <- cmdAction
  ShakeOptions { shakeVerbosity } <- getShakeOptions
  when (shakeVerbosity > Silent)
    $ liftIO $ putStr msg >> hPutStr stderr err
