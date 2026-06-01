{-|
Module      : Hitl.Clash.Cores.LatticeSemi.ECP5.Pll
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Some PLLs that are supported by Lattice's ECP5 FPGA.
-}

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Hitl.Clash.Cores.LatticeSemi.ECP5.Pll where

import Prelude

import Hitl.Clash.Cores.LatticeSemi.ECP5.Domain

import Clash.Annotations.Primitive (Primitive(..), HDL(..), hasBlackBox)
import Clash.Backend (Backend)
import Clash.Netlist.Types (TemplateFunction(..), BlackBoxContext)
import Clash.Signal.Internal
  ( Signal, Clock(..), Reset(..), clockGen, resetGen
  , unsafeToActiveLow, unsafeFromActiveLow
  )

import qualified Clash.Netlist.Id as Id
import qualified Clash.Netlist.Types as N
import qualified Clash.Primitives.DSL as DSL

import Control.Arrow (second)
import Control.Monad.State (State)
import Data.List.Infinite (Infinite(..), (...))
import Data.String.Interpolate (__i)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc.Extra (Doc)
import Text.Show.Pretty (ppShow)

orangePll24 ∷ Clock Dom48 → (Clock Dom24, Reset Dom24)
orangePll24 clkIn =
  let (clkOut, lock) = orangePLL24# clkIn
   in (clkOut, unsafeFromActiveLow lock)

orangePLL24# ∷ Clock Dom48 → (Clock Dom24, Signal Dom24 Bool)
orangePLL24# Clock {} = (clockGen, unsafeToActiveLow resetGen)
{-# OPAQUE orangePLL24# #-}
{-# ANN orangePLL24# hasBlackBox #-}
{-# ANN orangePLL24#
  let
    primName = show 'orangePLL24#
    tfName = show 'orangePLL24TF
  in InlineYamlPrimitive [Verilog, SystemVerilog] [__i|
    BlackBox:
      name: #{primName}
      kind: Declaration
      format: Haskell
      templateFunction: #{tfName}
  |] #-}

orangePLL24TF ∷ TemplateFunction
orangePLL24TF = TemplateFunction [clkSrc] (const True) orangePLL24TF#
 where
  clkSrc :< _ = (0...)

-- | Output of @ecppll -i 48 -o 24@
orangePLL24TF# ∷ Backend backend ⇒ BlackBoxContext → State backend Doc
orangePLL24TF# bbCtx
  | [ srcClk ]  ← fst <$> DSL.tInputs bbCtx
  , [ results ] ← DSL.tResults bbCtx
  = do
    let componentName = ("EHXPLLL" ∷ Text)

    instanceName ← Id.make $ componentName <> "_inst"
    DSL.declaration (componentName <> "_block") $ do
      (dstClk, locked) ←
        DSL.untuple results ["pll_clk_out", "pll_lock_out"] >>= \case
          [a, b] → pure (a, b)
          _ → error $ ppShow bbCtx

      cLow  ← DSL.assign "pll_cLow"  DSL.Low
      cHigh ← DSL.assign "pll_cHigh" DSL.High

      let
        generics ∷ [(Text, DSL.TExpr)]
        generics = second DSL.litTExpr <$>
          [ ("PLLRST_ENA",      "DISABLED")
          , ("INTFB_WAKE",      "DISABLED")
          , ("STDBY_ENABLE",    "DISABLED")
          , ("DPHASE_SOURCE",   "DISABLED")
          , ("OUTDIVIDER_MUXA",     "DIVA")
          , ("OUTDIVIDER_MUXB",     "DIVB")
          , ("OUTDIVIDER_MUXC",     "DIVC")
          , ("OUTDIVIDER_MUXD",     "DIVD")
          , ("CLKI_DIV",                 2)
          , ("CLKOP_ENABLE",     "ENABLED")
          , ("CLKOP_DIV",               25)
          , ("CLKOP_CPHASE",            12)
          , ("CLKOP_FPHASE",             0)
          , ("FEEDBK_PATH",        "CLKOP")
          , ("CLKFB_DIV",                1)
          ]

        inPorts ∷ [(Text, DSL.TExpr)]
        inPorts =
          [ ("CLKI",         srcClk)
          , ("CLKFB",        dstClk)
          , ("PHASESEL0",      cLow)
          , ("PHASESEL1",      cLow)
          , ("PHASEDIR",      cHigh)
          , ("PHASESTEP",     cHigh)
          , ("PHASELOADREG",  cHigh)
          , ("STDBY",          cLow)
          , ("PLLWAKESYNC",    cLow)
          , ("RST",            cLow)
          , ("ENCLKOP",        cLow)
          ]

        outPorts ∷ [(Text, DSL.TExpr)]
        outPorts =
          [ ("CLKOP", dstClk)
          , ("LOCK",  locked)
          ]

      DSL.instDecl
        N.Empty
        (Id.unsafeMake componentName)
        instanceName
        generics
        inPorts
        outPorts

orangePLL24TF# bbCtx = error (ppShow bbCtx)

orangePll12 ∷ Clock Dom48 → (Clock Dom12, Reset Dom12)
orangePll12 clkIn =
  let (clkOut, lock) = orangePLL12# clkIn
   in (clkOut, unsafeFromActiveLow lock)

orangePLL12# ∷ Clock Dom48 → (Clock Dom12, Signal Dom12 Bool)
orangePLL12# Clock {} = (clockGen, unsafeToActiveLow resetGen)
{-# OPAQUE orangePLL12# #-}
{-# ANN orangePLL12# hasBlackBox #-}
{-# ANN orangePLL12#
  let
    primName = show 'orangePLL12#
    tfName = show 'orangePLL12TF
  in InlineYamlPrimitive [Verilog, SystemVerilog] [__i|
    BlackBox:
      name: #{primName}
      kind: Declaration
      format: Haskell
      templateFunction: #{tfName}
  |] #-}

orangePLL12TF ∷ TemplateFunction
orangePLL12TF = TemplateFunction [clkSrc] (const True) orangePLL12TF#
 where
  clkSrc :< _ = (0...)

-- | Output of @ecppll -i 48 -o 12@
orangePLL12TF# ∷ Backend backend ⇒ BlackBoxContext → State backend Doc
orangePLL12TF# bbCtx
  | [ srcClk ]  ← fst <$> DSL.tInputs bbCtx
  , [ results ] ← DSL.tResults bbCtx
  = do
    let componentName = ("EHXPLLL" ∷ Text)

    instanceName ← Id.make $ componentName <> "_inst"
    DSL.declaration (componentName <> "_block") $ do
      (dstClk, locked) ←
        DSL.untuple results ["pll_clk_out", "pll_lock_out"] >>= \case
          [a, b] → pure (a, b)
          _ → error $ ppShow bbCtx

      cLow  ← DSL.assign "pll_cLow"  DSL.Low
      cHigh ← DSL.assign "pll_cHigh" DSL.High

      let
        generics ∷ [(Text, DSL.TExpr)]
        generics = second DSL.litTExpr <$>
          [ ("PLLRST_ENA",      "DISABLED")
          , ("INTFB_WAKE",      "DISABLED")
          , ("STDBY_ENABLE",    "DISABLED")
          , ("DPHASE_SOURCE",   "DISABLED")
          , ("OUTDIVIDER_MUXA",     "DIVA")
          , ("OUTDIVIDER_MUXB",     "DIVB")
          , ("OUTDIVIDER_MUXC",     "DIVC")
          , ("OUTDIVIDER_MUXD",     "DIVD")
          , ("CLKI_DIV",                 4)
          , ("CLKOP_ENABLE",     "ENABLED")
          , ("CLKOP_DIV",               50)
          , ("CLKOP_CPHASE",            12)
          , ("CLKOP_FPHASE",             0)
          , ("FEEDBK_PATH",        "CLKOP")
          , ("CLKFB_DIV",                1)
          ]

        inPorts ∷ [(Text, DSL.TExpr)]
        inPorts =
          [ ("CLKI",         srcClk)
          , ("CLKFB",        dstClk)
          , ("PHASESEL0",      cLow)
          , ("PHASESEL1",      cLow)
          , ("PHASEDIR",      cHigh)
          , ("PHASESTEP",     cHigh)
          , ("PHASELOADREG",  cHigh)
          , ("STDBY",          cLow)
          , ("PLLWAKESYNC",    cLow)
          , ("RST",            cLow)
          , ("ENCLKOP",        cLow)
          ]

        outPorts ∷ [(Text, DSL.TExpr)]
        outPorts =
          [ ("CLKOP", dstClk)
          , ("LOCK",  locked)
          ]

      DSL.instDecl
        N.Empty
        (Id.unsafeMake componentName)
        instanceName
        generics
        inPorts
        outPorts

orangePLL12TF# bbCtx = error (ppShow bbCtx)

orangePll8 ∷ Clock Dom48 → (Clock Dom8, Reset Dom8)
orangePll8 clkIn =
  let (clkOut, lock) = orangePLL8# clkIn
   in (clkOut, unsafeFromActiveLow lock)

orangePLL8# ∷ Clock Dom48 → (Clock Dom8, Signal Dom8 Bool)
orangePLL8# Clock {} = (clockGen, unsafeToActiveLow resetGen)
{-# OPAQUE orangePLL8# #-}
{-# ANN orangePLL8# hasBlackBox #-}
{-# ANN orangePLL8#
  let
    primName = show 'orangePLL8#
    tfName = show 'orangePLL8TF
  in InlineYamlPrimitive [Verilog, SystemVerilog] [__i|
    BlackBox:
      name: #{primName}
      kind: Declaration
      format: Haskell
      templateFunction: #{tfName}
  |] #-}

orangePLL8TF ∷ TemplateFunction
orangePLL8TF = TemplateFunction [clkSrc] (const True) orangePLL8TF#
 where
  clkSrc :< _ = (0...)

-- | Output of @ecppll -i 48 -o 8@
orangePLL8TF# ∷ Backend backend ⇒ BlackBoxContext → State backend Doc
orangePLL8TF# bbCtx
  | [ srcClk ]  ← fst <$> DSL.tInputs bbCtx
  , [ results ] ← DSL.tResults bbCtx
  = do
    let componentName = ("EHXPLLL" ∷ Text)

    instanceName ← Id.make $ componentName <> "_inst"
    DSL.declaration (componentName <> "_block") $ do
      (dstClk, locked) ←
        DSL.untuple results ["pll_clk_out", "pll_lock_out"] >>= \case
          [a, b] → pure (a, b)
          _ → error $ ppShow bbCtx

      cLow  ← DSL.assign "pll_cLow"  DSL.Low
      cHigh ← DSL.assign "pll_cHigh" DSL.High

      let
        generics ∷ [(Text, DSL.TExpr)]
        generics = second DSL.litTExpr <$>
          [ ("PLLRST_ENA",      "DISABLED")
          , ("INTFB_WAKE",      "DISABLED")
          , ("STDBY_ENABLE",    "DISABLED")
          , ("DPHASE_SOURCE",   "DISABLED")
          , ("OUTDIVIDER_MUXA",     "DIVA")
          , ("OUTDIVIDER_MUXB",     "DIVB")
          , ("OUTDIVIDER_MUXC",     "DIVC")
          , ("OUTDIVIDER_MUXD",     "DIVD")
          , ("CLKI_DIV",                 6)
          , ("CLKOP_ENABLE",     "ENABLED")
          , ("CLKOP_DIV",               75)
          , ("CLKOP_CPHASE",            37)
          , ("CLKOP_FPHASE",             0)
          , ("FEEDBK_PATH",        "CLKOP")
          , ("CLKFB_DIV",                1)
          ]

        inPorts ∷ [(Text, DSL.TExpr)]
        inPorts =
          [ ("CLKI",         srcClk)
          , ("CLKFB",        dstClk)
          , ("PHASESEL0",      cLow)
          , ("PHASESEL1",      cLow)
          , ("PHASEDIR",      cHigh)
          , ("PHASESTEP",     cHigh)
          , ("PHASELOADREG",  cHigh)
          , ("STDBY",          cLow)
          , ("PLLWAKESYNC",    cLow)
          , ("RST",            cLow)
          , ("ENCLKOP",        cLow)
          ]

        outPorts ∷ [(Text, DSL.TExpr)]
        outPorts =
          [ ("CLKOP", dstClk)
          , ("LOCK",  locked)
          ]

      DSL.instDecl
        N.Empty
        (Id.unsafeMake componentName)
        instanceName
        generics
        inPorts
        outPorts

orangePLL8TF# bbCtx = error (ppShow bbCtx)
