{-# LANGUAGE ImplicitParams #-}

module Development.Shake.Clash.ECP5
  ( synthRules
  ) where

import Development.Shake hiding (need)
import Development.Shake.Command
import Development.Shake.FilePath

import Development.Shake.Config.Extra
import Development.Shake.Command.Extra

import System.Directory (createDirectoryIfMissing, listDirectory, renamePath)
import Data.List (intercalate)
import Data.Char (isSpace)
import Data.Foldable (find)

startsWith :: Eq a => [a] -> [a] -> Bool
startsWith prefix = and . zipWith (==) prefix

endsWith :: Eq a => [a] -> [a] -> Bool
endsWith suffix = startsWith (reverse suffix) . reverse

synthRules ::
  ( ?buildDir :: FilePath
  , ?getCabalBinPath :: String -> Action FilePath
  , ?getSources :: String -> Action [FilePath]
  , ?getCabal :: Action CmdArgument
  ) =>
  ([FilePath] -> Action ()) ->
  (String -> String) ->
  FilePath ->
  String ->
  FilePath ->
  FilePath ->
  [(String, String)] ->
  Rules ()
synthRules need sub bdir pkgName group top defines = do
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
