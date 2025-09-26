module Development.Shake.Command.Extra
  ( mSilent
  ) where

import Control.Monad (when)
import Development.Shake
import System.IO (hPutStr, stderr)

-- | Runs a command without leaking any output to stdout or stderr, if
-- the shake verbosity option is set to 'Silent'.
mSilent :: Action (Stdout String, Stderr String) -> Action ()
mSilent cmdAction = do
  (Stdout msg, Stderr err) <- cmdAction
  ShakeOptions{..} <- getShakeOptions
  when (shakeVerbosity > Silent)
    $ liftIO $ putStr msg >> hPutStr stderr err
