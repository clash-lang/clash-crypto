{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedRecordDot #-}

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
  ) where

import Control.Monad (forM_, when)
import Data.List (singleton)
import System.Directory (withCurrentDirectory)

import Development.Shake hiding (doesFileExist)
import Development.Shake.Config.Extra
import Development.Shake.FilePath

import Clash.Crypto.Hash.SHA (SHA)
import Development.Shake.Clash.Formal

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
  aprPath <- liftIO requireProjectRootDir

  withCurrentDirectory aprPath $ do
    cfgs <- getConfigFiles

    let ?aprPath = aprPath
    let ?withBinary = withBinary
    let ?pkgName = pkgName
    let ?config = hitlConfig

    shakeArgs options
      { shakeFiles   = "_build"
      , shakeThreads = 1
      }
      $ shakeRules cfgs wanted

shakeRules ::
  (?aprPath :: FilePath) =>
  (?pkgName :: String) =>
  (?withBinary :: Bool) =>
  (?config :: SynthConfig Action) =>
  [FilePath] ->
  [String] ->
  Rules ()
shakeRules cfgs wanted = do
  want wanted

  usingConfigFiles cfgs
  buildDir <- shakeFiles <$> getShakeOptionsRules
  let ?buildDir = buildDir

  let ?before = when ?withBinary $ (singleton <$> getCabalBinPath "shake") >>= need

  defaultRules

  "clean" ~> do
    putInfo "Cleaning ..."
    removeFilesAfter buildDir ["//"]

  -- SHA HITLT rules

  forM_ [minBound :: SHA .. maxBound] $ \alg ->
    hitltRules "SHA" (show alg) [("HITLT_SHA", show alg)]

  hitltRules "BEA" "BEA" []
  hitltRules "FastGCD" "FastGCD" []
  hitltRules "FltCtmi" "FltCtmi" []
  hitltRules "Karatsuba" "Karatsuba" []
  hitltRules "Modulo" "Modulo" []
  hitltRules "SictMi" "SictMi" []

hitlConfig :: SynthConfig Action
hitlConfig =
  synthConfig
  { clashFlags =
      synthConfig.clashFlags <> clashFlags <> serialSpeedFlags
  }
 where
  clashFlags = pure $
    [ "-fclash-clear"
    , "-fclash-spec-limit=100"
    , "-fclash-inline-limit=100"
    , "-fconstraint-solver-iterations=20"
    ]
  serialSpeedFlags = do
    serialSpeed <- getConfigParameter "SERIAL_SPEED"
    return ["-DHITLT_SPEED=" <> serialSpeed]

-- | Hardware-in-the-loop test specific rules.
hitltRules ::
  (?before :: Action ()) =>
  (?buildDir :: String) =>
  (?config :: SynthConfig Action) =>
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
  let inp = "tests" </> "hitl" </> "top" </> group <.> "hs"
      buildDir = ?buildDir </> group </> component
      phonyPrefix = component <> ":"
      defineFlags = (\(x,y) -> "-D" <> x <> "=" <> y) <$> defines

  let ?buildDir = buildDir
      ?phonyPrefix = phonyPrefix
      ?config = ?config { clashFlags = ?config.clashFlags <> pure defineFlags }

  let getPackageSources = getSources ("pkg:" <> pkgName)
  let ?beforeClash = do
        projectShake <- getCabalBinPath "shake"
        projectClash <- getCabalBinPath "clash"
        cabalFile    <- getPackageSources "clash-crypto.cabal"
        libSources   <- getPackageSources "src"
        hitltSources <- getPackageSources "tests/hitl/lib"

        need $ [ projectShake, projectClash, inp ]
          <> cabalFile <> libSources <> hitltSources

        cabal <- getCabal
        cmd_ cabal "build" (pkgName <> ":hitlt-instances")

  synthRules "." inp top
