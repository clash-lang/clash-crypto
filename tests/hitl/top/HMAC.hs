{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE RequiredTypeArguments #-}
module HMAC where

import Clash.Prelude

import Control.Monad (forM)
import qualified Data.Foldable as F
import Language.Haskell.TH

import Clash.Annotations.TH (makeTopEntity)
import Clash.Signal.Channel (newsfeed)
import Clash.Signal.DataStream (DataStream, Frame(..))

import Clash.Crypto.MAC.HMAC (hmac)
import Clash.Crypto.Hash.SHA (SHA(..), BlockSize)

import Hitl.Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom24)
import Hitl.Clash.Cores.LatticeSemi.ECP5.Pll (orangePll24)
import Hitl.Clash.Cores.Uart.Extra (Byte, withUartRequestResponseHandler)

import SHA.TH

-- allows to select the UART baud via a CPP define
#ifndef HITLT_BAUD
type BAUD = 9600
#else
type BAUD = HITLT_BAUD
#endif

data NextExpectedDataFrame = S Byte | M | E
  deriving (Generic, NFDataX)

$(
  do
    es <- hmacEntities
    trees <- forM es $ \(name, t, e) -> do
      decls0 <- [d|
        topEntity ∷
          "CLK" ::: Clock Dom48 →
          "PMOD1_6" ::: Signal Dom24 Bit →
          "PMOD1_5" ::: Signal Dom24 Bit
        topEntity (orangePll24 → (clk, rst))
          = withUartRequestResponseHandler clk rst (SNat @BAUD)
          $ newsfeed . $(pure e) . descape
         where
          descape ∷
            HiddenClockResetEnable dom ⇒
            Signal dom (Maybe Byte) →
            DataStream dom (Index ((BlockSize $(pure t) `Div` BitSize Byte) + 1)) () Byte
          descape = mealy (~~>) (False, S 0 ∷ NextExpectedDataFrame)
           where
            (esc,   nef) ~~> Nothing   = ((esc,   nef     ), emptyFrame nef)
            (False, nef) ~~> Just 0x00 = ((True,  nef     ), emptyFrame nef)
            (False, nef) ~~> Just byte = ((False, next nef), frame nef byte)
            (True,  nef) ~~> Just 0x00 = ((False, next nef), frame nef 0x00)
            (True,  nef) ~~> Just 0xFF = ((False, E       ), emptyFrame nef)
            (True,  nef) ~~> Just byte = ((False, S byte  ), emptyFrame nef)

            frame = \case
              S x → Start $ unpack $ truncateB x
              M   → Middle
              E   → End ()

            next = \case
              E → S 0
              _ → M

            emptyFrame = \case
              S _ → Idle
              _   → NoData |]
      let topName = mkName $ "topEntity" <> name
          decls = fmap rename decls0
          rename (SigD _ t)  = SigD topName t
          rename (FunD _ cs) = FunD topName cs
          rename _           = error "wrong declaration"
      return decls
    return (F.concat trees)
 )

$(do
  es <- hmacEntities
  anns <- forM es $ \(name, _, _) -> makeTopEntity $ mkName $ "topEntity" <> name
  return (F.concat anns)
 )
