{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Development.Shake.Clash.Formal
  -- * Cabal
  ( getProjectRootDir
  , requireProjectRootDir
  , cabalOracles
  , getCabal
  , getCabalBinPath
  , TargetSelector
  , getSources
  , buildBinariesWithCabal
  , defaultRules
  -- * Configuration
  , configLookup
  , configLookupMaybe
  , getConfigFiles
  , getConfigOrElse
  , getConfigParameter
  , getConfigCmd
  , SynthConfig
    ( clashBin
    , clashFlags
    , yosysBin
    , yosysFlags
    , yosysSynthFlags
    , nextpnrBin
    , nextpnrFlags
    , ecppackBin
    , ecppackFlags
    , ecpprogBin
    , ecpprogFlags
    , dfuSuffixBin
    , dfuSuffixFlags
    )
  , synthConfig
  -- * Actions and Rules
  , synthRules
  ) where

import Prelude hiding (mod)

import Control.Applicative ((<|>))
import Control.Exception (Exception)
import Control.Exception.Base (throw)
import Control.Monad (forM, when, void, unless)
import Control.Monad.IO.Class (MonadIO)

import Data.Char (isSpace)
import Data.Functor ((<&>))
import Data.Foldable (find)
import qualified Data.HashMap.Strict as HashMap
import Data.List (singleton)
import Data.Maybe (catMaybes, fromJust, fromMaybe)

import System.Directory
  ( withCurrentDirectory, findExecutable, doesFileExist, getCurrentDirectory
  , createDirectoryIfMissing, listDirectory, renamePath
  )

import Development.Shake hiding (doesFileExist)
import Development.Shake.Config.Extra
import Development.Shake.Command
import Development.Shake.Classes
import Development.Shake.FilePath
import Development.Shake.Yosys
import Development.Shake.Clash

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

requireProjectRootDir :: IO FilePath
requireProjectRootDir = getProjectRootDir >>= \case
  Nothing -> fail "Cannot find cabal.project"
  Just x -> return x

stripIfPrefixed :: Eq a => [a] -> [a] -> [a]
stripIfPrefixed prefix as
  | as `startsWith` prefix = drop (length prefix) as
  | otherwise              = as

cabalOracles :: (?pkgName :: String) => Rules ()
cabalOracles = do
  aprPath <- liftIO requireProjectRootDir
  void $ addOracle $ \(CabalApp ()) -> quietly $ getConfigCmd "CABAL"
  void $ addOracle $ \(AppName name) -> do
    cabal <- getCabal
    out <- quietly $ cmd cabal "list-bin" "-v0" (?pkgName <> ":" <> name)
    return $ makeRelative aprPath $ init $ fromStdout out
  void $ addOracle $ \(CabalSDistSources (target, prefix)) -> do
    cabal <- getCabal
    out <- quietly $ cmd cabal "sdist" "-v0" "--list-only" target
    let allSources = map (stripIfPrefixed "./") $ lines $ fromStdout out
    return $ filter (startsWith prefix) allSources

  return ()

argument :: String -> CmdArgument
argument = toCmdArgument . singleton

getCabal :: Action CmdArgument
getCabal = argument <$> askOracle (CabalApp ())

getCabalBinPath :: String -> Action FilePath
getCabalBinPath app = askOracle (AppName app)

type TargetSelector = String

getSources :: TargetSelector -> FilePath -> Action [FilePath]
getSources = (askOracle .) . curry CabalSDistSources

newtype CabalApp = CabalApp ()
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
type instance RuleResult CabalApp = String

newtype CabalBinPath = AppName String
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
type instance RuleResult CabalBinPath = String

newtype CabalSDistSources = CabalSDistSources (TargetSelector, FilePath)
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
type instance RuleResult CabalSDistSources = [String]

buildBinariesWithCabal ::
  (?pkgName :: String) =>
  (?before :: Action ()) =>
  (?config :: SynthConfig Action) =>
  Rules ()
buildBinariesWithCabal = do
  withoutTargets $ do
    "" <//> "clash" </> "build" </> "clash" </> "clash" %> \out -> do
      ?before
      sources <- getSources ("pkg:" <> ?pkgName) "app/clash"
      need sources
      appPath <- getCabalBinPath "clash"
      unless (appPath == out) $ fail "internal error: invalid need"
      cabal <- getCabal
      quietly $ cmd_ cabal "build" (?pkgName <> ":" <> "clash")

    "" <//> "shake" </> "build" </> "shake" </> "shake" %> \out -> do
      sources <- getSources ("pkg:" <> ?pkgName) "app/shake"
      need sources
      -- ??? shaTypes <- getSources "src/Clash/Crypto/Hash/SHA.hs"
      shakePath <- getCabalBinPath "shake"
      unless (shakePath == out) $ fail "internal error: invalid need"
      cabal <- getCabal
      Stdout msg <- quietly
        $ cmd cabal "build" (?pkgName <> ":shake") "--dry-run"
      unless (startsWith "Up to date" msg) $ liftIO $ do
        putStr msg
        throw $ ShakeOutOfDate { artifact = ?pkgName <> ":shake" }

defaultRules ::
  (?pkgName :: String) =>
  (?before :: Action ()) =>
  (?config :: SynthConfig Action) =>
  Rules ()
defaultRules = do
  cabalOracles
  buildBinariesWithCabal


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

startsWith :: Eq a => [a] -> [a] -> Bool
startsWith prefix = and . zipWith (==) prefix

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

getConfigOrElse :: String -> String -> Action String
getConfigOrElse def key = fromMaybe def <$> getConfig key

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

data SynthConfig m =
  SynthConfig
  { clashBin :: m FilePath
  , clashFlags :: m [String]
  , yosysBin :: m CmdArgument
  , yosysFlags :: m [String]
  , yosysSynthFlags :: m [String]
  , nextpnrBin :: m CmdArgument
  , nextpnrFlags :: m [String]
  , ecppackBin :: m CmdArgument
  , ecppackFlags :: m [String]
  , ecpprogBin :: m CmdArgument
  , ecpprogFlags :: m [String]
  , dfuSuffixBin :: m CmdArgument
  , dfuSuffixFlags :: m [String]
  }

synthConfig :: SynthConfig Action
synthConfig =
  SynthConfig
  { clashBin        = getCabalBinPath "clash"
  , clashFlags      = words    <$> getConfigOrElse ""            "CLASH_FLAGS"
  , yosysBin        = argument <$> getConfigOrElse "yosys"       "YOSYS"
  , yosysFlags      = words    <$> getConfigOrElse ""            "YOSYS_FLAGS"
  , yosysSynthFlags = words    <$> getConfigOrElse ""            "YOSYS_SYNTH_FLAGS"
  , nextpnrBin      = argument <$> getConfigOrElse "nextpnr"     "PNR"
  , nextpnrFlags    = words    <$> getConfigOrElse ""            "PNR_FLAGS"
  , ecppackBin      = argument <$> getConfigOrElse "ecppack"     "PACK"
  , ecppackFlags    = words    <$> getConfigOrElse "--freq 38.8" "PACK_FLAGS"
  , ecpprogBin      = argument <$> getConfigOrElse "ecpprog"     "PROG"
  , ecpprogFlags    = words    <$> getConfigOrElse ""            "PROG_FLAGS"
  , dfuSuffixBin    = argument <$> getConfigOrElse "dfu-suffix"  "DFUSUFFIX"
  , dfuSuffixFlags  = words    <$> getConfigOrElse ""            "DFUSUFFIX_FLAGS"
  }

endsWith :: Eq a => [a] -> [a] -> Bool
endsWith suffix = startsWith (reverse suffix) . reverse

orangeCrab0_2_1 :: Chip
orangeCrab0_2_1 = ("85k", "CSFBGA285")

data ShakeOutOfDate = ShakeOutOfDate { artifact :: String }
instance Exception ShakeOutOfDate
instance Show ShakeOutOfDate where
  show ShakeOutOfDate { artifact } = unlines
    [ ""
    , "The project's 'shake' binary is out of date!"
    , "You need to run 'cabal build " <> artifact <> "first."
    ]

synthRules ::
  (?before :: Action ()) =>
  (?beforeClash :: Action ()) =>
  (?config :: SynthConfig Action) =>
  (?buildDir :: String) =>
  (?phonyPrefix :: String) =>
  FilePath ->
  -- ^ Path of the directory that contains a GHC environment file for the top
  -- entity module
  String ->
  -- ^ File path to, or the name of, the module that contains the top entity for
  -- synthesis
  String ->
  -- ^ Name of the top entity
  Rules ()
synthRules environment mod top = do
  let sub = (?phonyPrefix <>)

  sub "clean" ~> do
    putInfo "Cleaning ..."
    removeFilesAfter ?buildDir ["//"]

  let uploadTo target = do
        let inp = ?buildDir </> "04-bitstream" </> top <.> "bit"
        need [ inp ]
        putInfo "Uploading bitstream ..."
        let ?ecpprogBin   = ?config.ecpprogBin
            ?ecpprogFlags = ?config.ecpprogFlags

        ecpprog inp target

  sub "upload" ~> uploadTo Sram

  sub "bitstream" ~> need [ ?buildDir </> "04-bitstream" </> top <.> "bit"    ]
  sub "netlist"   ~> need [ ?buildDir </> "04-bitstream" </> top <.> "config" ]
  sub "synth"     ~> need [ ?buildDir </> "03-net"       </> top <.> "json"   ]
  sub "hdl"       ~> need [ ?buildDir </> "02-hdl"       </> top <.> "v"      ]

  withoutTargets $ do
    ?buildDir </> "04-bitstream" </> top <.> "dfu" %> \out -> do
      ?before
      let inp = out -<.> "bit"
      need [ inp ]
      copyFileChanged inp out

      let ?bin = ?config.dfuSuffixBin
          ?flags = ?config.dfuSuffixFlags

      undefined {- TODO -}
      -- cmd_ bin
      --   flags
      --   "-v 1209"
      --   "-p 5af0"
      --   "-a" out

    ?buildDir </> "04-bitstream" </> top <.> "bit" %> \out -> do
      ?before
      let inp = out -<.> "config"
      need [ inp ]
      putInfo "Generating bitstream with ecppack ..."

      let ?ecppackBin   = ?config.ecppackBin
          ?ecppackFlags = ?config.ecppackFlags

      ecppack inp out

    ?buildDir </> "04-bitstream" </> top <.> "config" %> \out -> do
      ?before
      let inp = ?buildDir </> "03-net" </> top <.> "json"
      need [ inp ]
      putInfo "Generating configuration with nextpnr ..."
      (show <$> ?config.nextpnrBin) >>= putInfo

      liftIO $ createDirectoryIfMissing True
        $ ?buildDir </> "04-bitstream"

      let ?nextpnrEcp5Bin   = ?config.nextpnrBin
          ?nextpnrEcp5Flags = ?config.nextpnrFlags
          ?nextpnrEcp5Chip  = pure orangeCrab0_2_1

      nextpnrEcp5 inp out

    ?buildDir </> "03-net" </> top <.> "json" %> \out -> do
      ?before
      let inp = ?buildDir </> "02-hdl" </> top <.> "v"
      need [inp]
      putInfo "Generating netlist with yosys ..."

      liftIO $ mapM_ (createDirectoryIfMissing True)
        $ fmap (?buildDir </>) [ "03-net", "log" ]

      let logFile          = ?buildDir </> "log" </> "synth.log"
      let ?yosysBin        = ?config.yosysBin
          ?yosysFlags      = ?config.yosysFlags <&> (<> ["-l", logFile])
          ?synthFlags      = ?config.yosysSynthFlags <&> (<> ["-top", top])

      synthEcp5 [inp] out

    ?buildDir </> "02-hdl" </> top <.> "v" %> \_ -> do
      ?before
      ?beforeClash
      (singleton <$> getCabalBinPath "clash") >>= need
      putInfo "Generating HDL with clash ..."

      ghcVersion <- quietly $ takeWhile (not . isSpace) . fromStdout
        <$> cmd "ghc --numeric-version" :: Action String

      ghcEnv <- do
        files <- liftIO $ listDirectory environment
        let environmentFiles =
              filter (startsWith ".ghc.environment." . takeFileName) files

        case find (endsWith ghcVersion) environmentFiles of
          Nothing -> fail $ "Cannot find GHC environment file for GHC"
                      <> ghcVersion
          Just f -> return f

      liftIO $ createDirectoryIfMissing True
          $ ?buildDir </> "01-clash"

      let ?clashBin   = argument <$> ?config.clashBin
          ?clashFlags = ?config.clashFlags

      clashVerilog ghcEnv mod (?buildDir </> "01-clash")

      liftIO $ do
        removeFiles (?buildDir </> "02-hdl") ["//"]
        renamePath
          (?buildDir </> "01-clash" </> (takeBaseName mod) <.> "topEntity")
          (?buildDir </> "02-hdl")
