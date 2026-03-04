{-|
Module      : Hitl.Clash.Cores.LatticeSemi.ECP5.Domain
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Some clock domains that are supported by Lattice's ECP5 FPGA.
-}

{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Hitl.Clash.Cores.LatticeSemi.ECP5.Domain where

import Clash.Prelude.Safe

-- | 48 MHz oscillator clock of the OrangeCrab board.
createDomain vSystem
  { vName = "Dom48"
  , vResetPolarity = ActiveLow
  , vPeriod = hzToPeriod 48_000_000
  }

-- | 24 MHz clock
createDomain vSystem
  { vName="Dom24"
  , vPeriod = hzToPeriod 24_000_000
  }

-- | 12 MHz clock
createDomain vSystem
  { vName="Dom12"
  , vPeriod = hzToPeriod 12_000_000
  }

-- | 8 MHz clock
createDomain vSystem
  { vName="Dom8"
  , vPeriod = hzToPeriod 8_000_000
  }
