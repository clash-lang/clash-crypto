{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MagicHash #-}

module Shake
  ( ShakeOptions(..)
  , CmdOption(..)
  , Verbosity(..)
  , Rebuild(..)
  , Change(..)
  , Progress(..)
  , shakeOptions
  , shakeApp
  , shakeBuild
  , configLookup
  , configLookupMaybe
  ) where

import Control.Applicative ((<|>))
import Control.Exception (Exception, throw)
import Control.Monad (forM, forM_, unless, when)
import Control.Monad.IO.Class (MonadIO)
import Data.Char (isSpace)
import Data.List (intercalate, find)
import Data.Maybe (catMaybes, fromJust)
import System.IO (hPutStr, stderr)
import System.Directory
  ( createDirectoryIfMissing, doesFileExist, listDirectory
  , findExecutable, renamePath, withCurrentDirectory
  )

import qualified Data.HashMap.Strict as HashMap (lookup)

import Development.Shake hiding (doesFileExist, need)
import Development.Shake.Classes
import Development.Shake.Command
import Development.Shake.Config.Extra
import Development.Shake.FilePath

import qualified Development.Shake as Shake (need)

import Clash.Crypto.Hash.SHA (SHA)

pkgName, top :: String
pkgName = "clash-crypto"
top     = "topEntity"

shakeApp :: ShakeOptions -> [String] -> IO ()
shakeApp = shakeBuild# True

shakeBuild :: ShakeOptions -> [String] -> IO ()
shakeBuild = shakeBuild# False

{-# INLINE shakeBuild# #-}
shakeBuild# :: Bool -> ShakeOptions -> [String] -> IO ()
shakeBuild# withBinary options wanted = do
  aprPath <- liftIO getProjectRootDir >>= \case
    Nothing -> fail "Cannot find cabal.project"
    Just x -> return x

  withCurrentDirectory aprPath $ do
    cfgs <- getConfigFiles

    let ?aprPath = aprPath
    let ?withBinary = withBinary

    shakeArgs options
      { shakeFiles   = "_build"
      , shakeThreads = 1
      }
      $ shakeRules cfgs wanted

shakeRules ::
  (?aprPath :: FilePath) =>
  (?withBinary :: Bool) =>
  [FilePath] ->
  [String] ->
  Rules ()
shakeRules cfgs wanted = do
  want wanted

  usingConfigFiles cfgs
  buildDir <- shakeFiles <$> getShakeOptionsRules
  let ?buildDir = buildDir

  -- oracles

  getCabal <- do
    oracle <- addOracle $ \(CabalApp ()) -> quietly $ getConfigCmd "CABAL"
    return $ CmdArgument . return . Right <$> oracle (CabalApp ())
  let ?getCabal = getCabal

  getCabalBinPath <- fmap (. AppName) $ addOracle $ \(AppName name) -> do
    cabal <- getCabal
    out <- quietly $ cmd cabal "--verbose=0" "list-bin" (pkgName <> ":" <> name)
    return $ makeRelative ?aprPath $ takeWhile (not . isSpace) $ fromStdout out
  let ?getCabalBinPath = getCabalBinPath

  getSources <- fmap (. CabalSDistSources)
    $ addOracle $ \(CabalSDistSources prefix) -> do
      cabal <- getCabal
      allSources <- quietly $ lines . fromStdout
        <$> cmd cabal "--verbose=0" "sdist" "--list-only" :: Action [String]
      return $ drop 2 <$> filter (startsWith ("./" <> prefix)) allSources
  let ?getSources = getSources

  -- SHA HITLT rules

  forM_ [minBound :: SHA .. maxBound] $ \alg ->
    hitltRules "SHA" (show alg) [("HITLT_SHA", show alg)]

  hitltRules "BEA" "BEA" []
  hitltRules "FastGCD" "FastGCD" []
  hitltRules "FltCtmi" "FltCtmi" []
  hitltRules "Karatsuba" "Karatsuba" []
  hitltRules "Modulo" "Modulo" []
  hitltRules "SictMi" "SictMi" []

  -- project apps

  withoutTargets $ do
    "" <//> "clash" </> "build" </> "clash" </> "clash" %> \out -> do
      sources <- getSources "app/clash"
      if ?withBinary
        then getCabalBinPath "shake" >>= Shake.need . (: sources)
        else Shake.need sources
      appPath <- getCabalBinPath "clash"
      unless (appPath == out) $ fail "internal error: invalid need"
      cabal <- getCabal
      quietly $ cmd_ cabal "--verbose=0" "build" (pkgName <> ":" <> "clash")

    when ?withBinary
      $ "" <//> "shake" </> "build" </> "shake" </> "shake" %> \out -> do
        sources <- getSources "app/shake"
        shaTypes <- getSources "src/Clash/Crypto/Hash/SHA.hs"
        Shake.need $ shaTypes <> sources
        shakePath <- getCabalBinPath "shake"
        unless (shakePath == out) $ fail "internal error: invalid need"
        cabal <- getCabal
        Stdout msg <- quietly
          $ cmd cabal "--verbose=0" "build" (pkgName <> ":shake") "--dry-run"
        unless (startsWith "Up to date" msg) $ liftIO $ do
          putStr msg
          throw ShakeOutOfDate

  -- clean

  "clean" ~> do
    putInfo "Cleaning ..."
    removeFilesAfter buildDir ["//"]

-- | Hardware-in-the-loop test specific rules.
hitltRules ::
  (?withBinary :: Bool) =>
  (?buildDir :: String) =>
  (?getCabal :: Action CmdArgument) =>
  (?getCabalBinPath :: String -> Action String) =>
  (?getSources :: String -> Action [String]) =>
  String ->
  -- ^ The name of the tested component group. It must match with the
  -- file name (without the @.hs@) of the top entity in @tests/hitl/top@
  String ->
  -- ^ The name of the individual component within that group.
  [(String, String)] ->
  -- ^ A list of CPP defines that are passed to clash when compiling the
  -- respective top entity in @tests/hitl/top@
  Rules ()
hitltRules group component defines = do
  let bdir = ?buildDir </> group </> component
      sub = ((component <> ":") <>)
      need
        | ?withBinary = \xs -> ?getCabalBinPath "shake" >>= Shake.need . (: xs)
        | otherwise  = Shake.need

  sub "hdl"       ~> need [ bdir </> "02-hdl" </> top <.> "v" ]
  sub "synth"     ~> need [ bdir </> "03-net" </> top <.> "json" ]
  sub "netlist"   ~> need [ bdir </> "04-bitstream" </> top <.> "config" ]
  sub "bitstream" ~> need [ bdir </> "04-bitstream" </> top <.> "bit" ]

  sub "upload" ~> do
    let inp = bdir </> "04-bitstream" </> top <.> "bit"
    need [ inp ]
    programDevice <- getConfigCmd "PROG"
    putInfo "Uploading bitstream ..."
    mSilent $ cmd programDevice "-S" inp

  sub "clean" ~> do
    putInfo "Cleaning ..."
    removeFilesAfter ?buildDir ["//"]

  withoutTargets $ do
    bdir </> "04-bitstream" </> top <.> "dfu" %> \out -> do
      let inp = out -<.> "bit"
      need [ inp ]
      copyFileChanged inp out
      dfuSuffix <- getConfigCmd "DFUSUFFIX"
      cmd_ dfuSuffix
        "-v 1209"
        "-p 5af0"
        "-a" out

    bdir </> "04-bitstream" </> top <.> "bit" %> \out -> do
      let inp = out -<.> "config"
      need [ inp ]
      putInfo "Generating bitstream with ecppack ..."

      packBitstream <- getConfigCmd "PACK"
      cmd_ packBitstream
        "--compress"
        "--freq 38.8"
        "--inp" inp
        "--bit" out

    bdir </> "04-bitstream" </> top <.> "config" %> \out -> do
      let inp = bdir </> "03-net" </> top <.> "json"
      need [ inp ]
      putInfo "Generating configuration with nextpnr ..."

      liftIO $ createDirectoryIfMissing True
        $ bdir </> "04-bitstream"

      placeAndRoute <- getConfigCmd "PNR"
      pnrFlags <- getConfigParameter "PNR_FLAGS"

      cmd_ placeAndRoute
        "--json" inp
        "--textcfg" out
        pnrFlags

    bdir </> "03-net" </> top <.> "json" %> \out -> do
      let inp = bdir </> "02-hdl" </> top <.> "v"
      need [ inp ]
      putInfo "Generating netlist with yosys ..."

      liftIO $ mapM_ (createDirectoryIfMissing True)
        $ fmap (bdir </>) [ "03-net", "log" ]
      yosys <- getConfigCmd "YOSYS"
      cmd_ yosys
        "-l" (bdir </> "log" </> "synth.log")
        "-p" [ intercalate "; "
                 [ unwords
                     [ "read_verilog"
                     ,   takeDirectory inp </> "*.v"
                     ]
                 , unwords
                     [ "synth_ecp5"
                     ,   "-top", top
                     ,   "-json", out
                     ]
                 ]
             ]

    bdir </> "02-hdl" </> top <.> "v" %> \_ -> do
      projectShake <- ?getCabalBinPath "shake"
      projectClash <- ?getCabalBinPath "clash"
      cabalFile    <- ?getSources "clash-crypto.cabal"
      libSources   <- ?getSources "src"
      hitltSources <- ?getSources "tests/hitl/lib"
      let inp = "tests" </> "hitl" </> "top" </> group <.> "hs"

      need $ [ projectShake, projectClash, inp ]
        <> cabalFile <> libSources <> hitltSources

      putInfo "Generating HDL with clash ..."

      cabal <- ?getCabal
      cmd_ cabal "--verbose=0" "build" (pkgName <> ":hitlt-instances")
      liftIO $ createDirectoryIfMissing True
        $ bdir </> "01-clash"

      ghcVersion <- quietly $ takeWhile (not . isSpace) . fromStdout
        <$> cmd "ghc --numeric-version" :: Action String

      ghcEnv <- do
        files <- liftIO $ listDirectory "."
        let environmentFiles =
              filter (startsWith ".ghc.environment." . takeFileName) files
        case find (endsWith ghcVersion) environmentFiles of
          Nothing -> fail $ "Cannot find GHC environment file for GHC "
                       <> ghcVersion
          Just f -> return f

      serialSpeed <- getConfigParameter "SERIAL_SPEED"

      cmd_ projectClash
        "-package-env" ghcEnv
        ("-DHITLT_BAUD=" <> serialSpeed)
        ((\(x,y) -> "-D" <> x <> "=" <> y) <$> defines)
        "--verilog"
        "-fclash-clear"
        "-fclash-spec-limit=100"
        "-fclash-inline-limit=100"
        "-fconstraint-solver-iterations=20"
        "-outputdir" (bdir </> "01-clash")
        inp

      liftIO $ do
        removeFiles (bdir </> "02-hdl") ["//"]
        renamePath
          (bdir </> "01-clash" </> group <.> "topEntity")
            $ bdir </> "02-hdl"

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

endsWith :: Eq a => [a] -> [a] -> Bool
endsWith suffix = startsWith (reverse suffix) . reverse

-- | Runs a command without leaking any output to stdout or stderr, if
-- the shake verbosity option is set to 'Silent'.
mSilent :: Action (Stdout String, Stderr String) -> Action ()
mSilent cmdAction = do
  (Stdout msg, Stderr err) <- cmdAction
  ShakeOptions{..} <- getShakeOptions
  when (shakeVerbosity > Silent)
    $ liftIO $ putStr msg >> hPutStr stderr err

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

data ShakeOutOfDate = ShakeOutOfDate
instance Exception ShakeOutOfDate
instance Show ShakeOutOfDate where
  show _ = unlines
    [ ""
    , "The project's 'shake' binary is out of date!"
    , "You need to run 'cabal build " <> (pkgName <> ":shake' ") <> "first."
    ]

newtype CabalApp = CabalApp ()
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
type instance RuleResult CabalApp = String

newtype CabalBinPath = AppName String
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
type instance RuleResult CabalBinPath = String

newtype CabalSDistSources = CabalSDistSources String
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
type instance RuleResult CabalSDistSources = [String]
