module Clash.Crypto.Hitlt.Uart
  ( bulkRead
  , withUartRequestResponseHandler
  ) where

import Clash.Prelude
import Clash.Cores.Uart (ValidBaud, uart)
import Clash.Crypto.Hitlt.Shared (Byte, ByteSize, isReadyIndicator)

import Data.Constraint.Nat.Extra (CancelMultiple)
import GHC.TypeNats.Proof (Rewrite(..), using)

-- | Exends a circuit receiving a byte stream and computing a response
-- with a UART interface providing the input stream and passing back the
-- respone.
withUartRequestResponseHandler ∷
  ∀ baud dom a.
  ( KnownDomain dom, ValidBaud dom baud, NFDataX a, BitPack a
  , BitSize a `Mod` BitSize Byte ~ 0, 1 <= ByteSize a
  ) ⇒
  Clock dom →
  -- ^ clock
  Reset dom →
  -- ^ reset
  SNat baud →
  -- ^ the baud
  ( HiddenClockResetEnable dom ⇒
    Signal dom (Maybe Byte) →
    Signal dom (Maybe a)
  ) →
  -- ^ the DUT request response handler
  Signal dom Bit →
  -- ^ UART receive line
  Signal dom Bit
  -- ^ UART transmit line
withUartRequestResponseHandler clk rst baud requestResponseHandler rx
  = withClockResetEnable clk rst enableGen
  $ let
      (rxData, tx, ack) = uart baud rx txReq

      result ∷ Signal dom (Maybe (Vec (ByteSize a - 1 + 1) Byte))
      result | Rewrite ← using @(CancelMultiple (BitSize a) (BitSize Byte))
             = fmap (bitCoerce . pack) <$> requestResponseHandler rxData

      txReq = mealyB
        (~~>)
        -- send an 'isReadyIndicator' byte once after leaving the
        -- reset state to signal the host that the device is ready now
        (repeat isReadyIndicator, 1 ∷ Index (ByteSize a + 1))
        (result, ack)
       where
        -- wait for the response from the crypto core
        s@(_, 0) ~~> (Nothing, _) = (s, Nothing)
        -- response received, start sending bytes
        (_, 0)   ~~> (Just h,  _) = ((h, maxBound), Just $ head h)
        -- wait for the UART ack of the byte previously sent
        s@(h, _) ~~> (_,   False) = (s, Just $ head h)
        -- UART ack received
        (h, n)   ~~> (_,    True) = ((h <<+ undefined, n - 1), Just $ head h)
    in
      tx

-- | Reads a block of 'Just'-wrapped bytes until they sum up to requested
-- @a@-typed value.
bulkRead ∷
  ∀ a dom.
  ( HiddenClockResetEnable dom, BitPack a
  , BitSize a `Mod` BitSize Byte ~ 0, 1 <= ByteSize a
  ) ⇒
  Signal dom (Maybe Byte) →
  Signal dom (Maybe a)
bulkRead = mealy (~~>) ival
 where
  ival ∷ (Index (ByteSize a), Vec (ByteSize a) Byte)
  ival = (0, def)

  (n, v) ~~> Just ((v <<+) → nv)
    | Rewrite ← using @(CancelMultiple (BitSize a) (BitSize Byte))
    = if n < maxBound
        then ((n + 1, nv ), Nothing            )
        else ((0,     def), Just $ bitCoerce nv)

  s ~~> Nothing
    = (s, Nothing)
