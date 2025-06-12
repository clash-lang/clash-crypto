module Development.Shake.Config.Extra
  ( readConfigFile
  , readConfigFileWithEnv
  , usingConfigFiles
  , getConfig
  , getConfigFile
  ) where

import Control.Applicative ((<|>))
import Control.Monad (forM, void)
import Control.Monad.IO.Class (liftIO)

import Development.Shake
  (RuleResult, Rules, Action, newCache, need, addOracle, askOracle)
import Development.Shake.Classes (Typeable, Hashable, Binary, NFData)
import Development.Shake.Config (readConfigFile, readConfigFileWithEnv)

import qualified Data.HashMap.Strict as HashMap (lookup)

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
