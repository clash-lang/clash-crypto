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

import Control.Exception (Exception, throw)
import Control.Monad (forM_, unless, when)
import Data.Char (isSpace)
import System.Directory (withCurrentDirectory)

import Development.Shake hiding (doesFileExist, need)
import Development.Shake.Classes
import Development.Shake.Command
import Development.Shake.FilePath
import qualified Development.Shake as Shake (need)

import Development.Shake.Config.Extra

import Clash.Crypto.Hash.SHA (SHA)
import Development.Shake.Clash.ECP5

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

  synthRules need sub bdir pkgName group top defines

startsWith :: Eq a => [a] -> [a] -> Bool
startsWith prefix = and . zipWith (==) prefix

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
