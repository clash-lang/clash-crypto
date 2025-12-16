{-# LANGUAGE NumericUnderscores #-}

{-# OPTIONS_GHC -Wno-orphans #-}
module Hitl.Clash.Cores.LatticeSemi.ECP5.Domain where

import Clash.Prelude

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

-- | 24 MHz clock
createDomain vSystem
  { vName="Dom12"
  , vPeriod = hzToPeriod 12_000_000
  }
