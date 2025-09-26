module Development.Shake.Config.Extra
  ( readConfigFile
  , readConfigFileWithEnv
  , usingConfigFiles
  , getConfig
  , getConfigFile
  , getProjectRootDir
  , configLookup
  , configLookupMaybe
  , getConfigFiles
  , getConfigParameter
  , getConfigCmd
  ) where

import Control.Applicative ((<|>))
import Control.Monad (forM, void, when)
import Control.Monad.IO.Class (liftIO, MonadIO)

import Development.Shake
  (RuleResult, Rules, Action, newCache, need, addOracle, askOracle)
import Development.Shake.Classes (Typeable, Hashable, Binary, NFData)
import Development.Shake.Config (readConfigFile, readConfigFileWithEnv)

import System.Directory (doesFileExist, getCurrentDirectory, findExecutable, withCurrentDirectory)
import System.FilePath ((</>), isDrive, takeDirectory)

import qualified Data.HashMap.Strict as HashMap (lookup)
import Data.Maybe (catMaybes, fromJust)

newtype Config = Config String
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
newtype ConfigFile = ConfigFile String
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult Config = Maybe String
type instance RuleResult ConfigFile = Maybe String

-- | An extension of 'Development.Shake.Command.usingConfigFile',
-- which supports more than a single configuration file. If a key is
-- present in multiple files, then the value of the file containing
-- the key listed the earliest is taken.
usingConfigFiles :: [FilePath] -> Rules ()
usingConfigFiles files = do
  hashmaps <- forM files $ \file ->
    fmap (file, ) $ newCache $ \() ->
      need [file] >> liftIO (readConfigFile file)

  void $ addOracle $ findKey hashmaps
  void $ addOracle $ findKeyFile hashmaps
 where
  findKey [] _ = return Nothing
  findKey ((_, hm) : mr) (Config x) =
    (<|>) <$> (HashMap.lookup x <$> hm ())
          <*> findKey mr (Config x)

  findKeyFile [] _ = return Nothing
  findKeyFile ((f, hm) : mr) (ConfigFile x) =
    (<|>) <$> (fmap (const f) . HashMap.lookup x <$> hm ())
          <*> findKeyFile mr (ConfigFile x)

-- | An extension of 'Development.Shake.Config.getConfig' returning
-- the value bound to the key and the file, where the key has been
-- read from.
getConfig :: String -> Action (Maybe String)
getConfig = askOracle . Config

getConfigFile :: String -> Action (Maybe String)
getConfigFile = askOracle . ConfigFile

-- | Starts searching for the @cabal.project@ file in the current
-- working directory and traverses up the directory tree until it
-- finds it. Just returns the absolute path to the directory of the
-- file or nothing, if it cannot find @cabal.project@ anywhere.
getProjectRootDir :: IO (Maybe FilePath)
getProjectRootDir = getCurrentDirectory >>= findFile
 where
  findFile path
    | isDrive path = return Nothing
    | otherwise    = doesFileExist (path </> projectFilename)
        >>= \case True -> return $ Just path
                  _    -> findFile $ takeDirectory path
  projectFilename = "cabal.project"

-- | Reads the config value of @key@ from the configuration
-- files. This lookup does not interfer with the shake build system
-- and is intended to be used by external APIs that need access to the
-- configuration variables as well. The method fails with an error if
-- the requested key does not exist. Use 'configLookupMaybe' for safe
-- alternatives.
configLookup :: IO (String -> String)
configLookup = configLookupMaybe >>= \lkup ->
  return $ \key -> case lkup key of
    Nothing -> fail $ "Cannot find " <> key <> " in your 'build.cfg(.local).'"
    Just x  -> x

-- | A more safe version of 'configLookup'.
configLookupMaybe :: IO (String -> Maybe String)
configLookupMaybe = do
  aprPath <- liftIO getProjectRootDir >>= \case
    Nothing -> fail "Cannot find cabal.project"
    Just x -> return x

  withCurrentDirectory aprPath
    $ getConfigFiles >>= configsLookup
 where
  configsLookup [] = return (const Nothing)
  configsLookup (c:cr) = do
    hm <- readConfigFile c
    lkup <- configsLookup cr
    return $ \key ->
      HashMap.lookup key hm <|> lkup key

getConfigFiles :: MonadIO m => m [FilePath]
getConfigFiles = liftIO $ do
  cfgs <- fmap catMaybes $ forM [local, shared] $ \x ->
    liftIO $ doesFileExist x >>= \case
      True  -> return $ Just x
      False -> return Nothing

  when (null cfgs) $ fail "Missing 'build.cfg(.local)'"
  return cfgs
 where
  shared = "build.cfg"
  local  = "build.cfg.local"

getConfigParameter :: String -> Action String
getConfigParameter key = getConfig key >>= \case
  Nothing -> fail $ "Cannot find " <> key <> " in your 'build.cfg(.local).'"
  Just x  -> return x

getConfigCmd :: String -> Action FilePath
getConfigCmd key = do
  cmdName <- getConfigParameter key
  liftIO (findExecutable cmdName) >>= \case
    Just x  -> return x
    Nothing -> getConfigFile key >>= \mFile -> fail
      $ "Cannot find executable '" <> cmdName <> "' set via " <> key <>
        " in '" <> fromJust mFile <> "'"
