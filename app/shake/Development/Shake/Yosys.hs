{-# LANGUAGE ImplicitParams #-}

module Development.Shake.Yosys
  ( yosys
  , YosysScript
  , YosysCommand
  , synthEcp5
  , nextpnrEcp5
  , Chip
  , Package
  , ChipType
  , ecppack
  , ProgTarget(Sram)
  , ecpprog
  ) where

import Data.List (intercalate, isSubsequenceOf)

import Development.Shake
import Development.Shake.Command
import Development.Shake.Command.Extra

type YosysCommand = [String]
type YosysScript = [YosysCommand]

-- | Escape the arguments to a Yosys command. Arguments, e.g. paths, that
-- contain a space can be surrounded in quotes. If the argument contains a quote
-- character there is no further way to escape it, but quote characters not
-- followed by a space are considered part of the string anyway. Arguments that
-- contain the sequence @" @ are thus not representable.
escape :: MonadFail m => YosysCommand -> m [String]
escape []       = return []
escape (c:args) = (c :) <$> mapM escapeArg args
 where
  escapeArg arg
    | "\" " `isSubsequenceOf` arg = fail ("Unrepresentable in yosys: `" <> arg <> "`")
    | any (`elem` [' ', '"']) arg = return $ "\"" <> arg <> "\""
    | otherwise                   = return $ arg

inlineScript :: MonadFail m => YosysScript -> m String
inlineScript script = intercalate "; " . map unwords <$> mapM escape script

yosys ::
  (?yosysBin :: Action CmdArgument) =>
  (?yosysFlags :: Action [String]) =>
  (?readCommand :: Action YosysCommand) =>
  (?synthScript :: Action YosysScript) =>
  (?writeCommand :: Action YosysCommand) =>
  [FilePath] ->
  -- ^ Input files, which must be in the format expected by @?readCommand@
  FilePath ->
  -- ^ Output path
  Action ()
yosys inp out = do
  yosysBin <- ?yosysBin
  yosysFlags <- ?yosysFlags
  readCommand <- ?readCommand
  synthScript <- ?synthScript
  writeCommand <- ?writeCommand

  let script =
        [readCommand <> inp] <>
        synthScript <>
        [writeCommand <> [out]]
  scriptText <- inlineScript script

  cmd_ yosysBin
    yosysFlags
    "-p" [scriptText]

synthEcp5 ::
  (?yosysBin :: Action CmdArgument) =>
  (?yosysFlags :: Action [String]) =>
  (?synthFlags :: Action [String]) =>
  [FilePath] ->
  -- ^ Input verilog files
  FilePath ->
  -- ^ Output path in JSON netlist format
  Action ()
synthEcp5 inp out = do
  synthFlags <- ?synthFlags
  let ?readCommand  = pure ["read_verilog"]
      ?synthScript  = pure ["synth_ecp5" : synthFlags]
      ?writeCommand = pure ["write_json"]

  yosys inp out

type Package = String
type ChipType = String
type Chip = (ChipType, Package)

nextpnrEcp5 ::
  (?nextpnrEcp5Bin :: Action CmdArgument) =>
  (?nextpnrEcp5Flags :: Action [String]) =>
  (?nextpnrEcp5Chip :: Action Chip) =>
  FilePath ->
  FilePath ->
  Action ()
nextpnrEcp5 inp out = do
  bin <- ?nextpnrEcp5Bin
  flags <- ?nextpnrEcp5Flags
  (chipType, package) <- ?nextpnrEcp5Chip
  cmd_ bin
    flags
    ("--" <> chipType)
    "--package" [package]
    "--json" [inp]
    "--textcfg" [out]

ecppack ::
  (?ecppackBin :: Action CmdArgument) =>
  (?ecppackFlags :: Action [String]) =>
  FilePath ->
  FilePath ->
  Action ()
ecppack inp out = do
  bin <- ?ecppackBin
  flags <- ?ecppackFlags
  cmd_ bin
    flags
    "--compress"
    "--input" [inp]
    "--bit" [out]

data ProgTarget = Sram | Flash

progTargetFlags :: ProgTarget -> [String]
progTargetFlags Sram  = ["-S"]
progTargetFlags Flash = []

ecpprog ::
  (?ecpprogBin :: Action CmdArgument) =>
  (?ecpprogFlags :: Action [String]) =>
  FilePath ->
  ProgTarget ->
  Action ()
ecpprog inp target = do
  bin <- ?ecpprogBin
  flags <- ?ecpprogFlags
  mSilent $ cmd bin
    flags
    (progTargetFlags target)
    inp
