{-# LANGUAGE ImplicitParams #-}

module Development.Shake.Clash
  ( clash
  , clashVerilog
  ) where

import Prelude hiding (mod)
import Development.Shake
import Development.Shake.Command

clash ::
  (?clashBin :: Action CmdArgument) =>
  (?clashFlags :: Action [String]) =>
  String ->
  -- ^ Backend
  FilePath ->
  -- ^ GHC environment file containing the module for synthesis
  String ->
  -- ^ Name of the module to run clash on
  FilePath ->
  -- ^ Directory in which to write HDL files
  Action ()
clash backend env mod out = do
  bin <- ?clashBin
  flags <- ?clashFlags

  cmd_ bin
    flags
    "-package-env" [env]
    ("--" <> backend)
    "-outputdir" [out]
    mod

clashVerilog ::
  (?clashBin :: Action CmdArgument) =>
  (?clashFlags :: Action [String]) =>
  FilePath ->
  -- ^ GHC environment file containing the module for synthesis
  String ->
  -- ^ Name of the module to run clash on
  FilePath ->
  -- ^ Directory in which to write HDL files
  Action ()
clashVerilog = clash "verilog"
