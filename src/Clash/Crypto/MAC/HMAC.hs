{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Clash.Crypto.MAC.HMAC
  ( hmacWrapper
  , HmacInput (..)
  , SuitableDivisorForHMAC
  , WellDefinedAlg
  ) where

import Clash.Prelude
import Clash.Crypto.Hash.SHA

import Numeric (showHex)

-- Constraint alias for any hashing `alg` used by HMAC
-- (required until I switch to let and pattern guards for knownSHA)
type WellDefinedAlg alg =
  ( KnownNat (MessageDigestSize alg)
  , KnownNat (BlockSize alg)
  , KnownSHA alg
  )

-- Constraint alias for `n` (parametric on `alg`) used by HMAC.
-- Given an n (the number of bits in each HmacInput payload), constrain n
-- such that we can guarantee n will work with our HMAC implementation.
type SuitableDivisorForHMAC n alg =
  ( -- For a given n
    KnownNat n
  , -- `n` has to be between `1` and `min (BlockSize alg, MessageDigestSize alg)`
    -- inclusive
    1 <= n, n <= BlockSize alg, n <= MessageDigestSize alg
  , -- Ensure n can evenly divide `BlockSize alg`
    Mod (BlockSize alg) n ~ 0
  )

-- | A wrapper (for convenience) around `hmac` which couples it with the
-- corresponding `sha` core and wires everything up automatically.
hmacWrapper ::
  forall (n :: Nat) (alg :: SHA) (dom :: Domain) (m :: Nat).
  -- Constraints on n
  (SuitableDivisorForHMAC n alg, KnownNat m, m*8 ~ n) =>
  -- Contraints on alg
  WellDefinedAlg alg =>
  HiddenClockResetEnable dom =>
  -- Input
  Signal dom (Maybe (HmacInput n)) ->
  ( Signal dom (Maybe (BitVector (MessageDigestSize alg)))
  , Signal dom Bool
  )
hmacWrapper input = (output, hmacReady)
 where
  (shaInput, output, hmacReady) = hmac @n @alg input shaOutput
  shaOutput = sha @alg shaInput

-- HMAC values taken from rfc2104 (https://datatracker.ietf.org/doc/html/rfc2104)
padByte, innerPadByte, outerPadByte :: Unsigned 8
padByte      = 0x00
innerPadByte = 0x36
outerPadByte = 0x5c


-- | HMAC circuit described in rfc2104 (https://datatracker.ietf.org/doc/html/rfc2104).
-- The circuit receives HmacInput and outputs a response and a boolean flag if it's
-- ready for more data. The HmacInput is expected to be in the form of
--    `[HmacKey][HmacKey]...[HmacKeyEnd][HmacMsg][HmacMsg]...[HmacMsgEnd]`
--
-- Any number of `Nothing`s can be intersperced between the `Just` inputs, but a `Just`
-- value should not be passed when the `isReady` flag is `False`. The message can be
-- arbitrarily large. The key is expected to be less than or equal to `BlockSize alg`.
--
-- Note: HMAC requires the key to be `BlockSize alg` long. The HMAC specification
-- says if the key is shorter, it should be padded with 0s, and if the key is longer,
-- the key should be run through SHA to create a new key of size `BlockSize alg`.
-- The circuit WILL pad the key if required, but WILL NOT hash the key if the key
-- is too large. The key sender is required to handle that (if applicable). If a key is
-- too big, the circuit will throw a simulation Error.
hmac ::
  forall n alg dom m.
  -- Function constraints
  ( SuitableDivisorForHMAC n alg, KnownNat m, m*8 ~ n
  , WellDefinedAlg alg
  , HiddenClockResetEnable dom
  ) =>
  -- | Input
  Signal dom (Maybe (HmacInput n)) ->
  -- | SHA output
  Signal dom (Maybe (BitVector (MessageDigestSize alg))) ->
  -- | Sha input
  ( Signal dom (Maybe (ShaInput n))
  -- | Output
  , Signal dom (Maybe (BitVector (MessageDigestSize alg)))
  -- | isReady signal
  , Signal dom Bool
  )
hmac inputS shaS = mealyB step initState (inputS, shaS)
 where
  initState = ReadKey dummyInfo 0
  dummyInfo = HmacInfo
    { key = 0 :: (BitVector (BlockSize alg))
    , innerHash = 0 :: (BitVector (MessageDigestSize alg))
    }

  step ::
    (HmacState alg n) ->
    (Maybe (HmacInput n), Maybe (BitVector (MessageDigestSize alg))) ->
    (HmacState alg n, ( Maybe (ShaInput n)
                    , Maybe (BitVector (MessageDigestSize alg))
                    , Bool
                    )
    )
  step state (maybeInput, maybeSha) = case (state, maybeInput, maybeSha) of
    (ReadKey _ _, Nothing, _) -> (state, noOut)
    (ReadKey hmacInfo cnt, Just (HmacKey keyData), _)
      | cnt < maxBound -> (ReadKey newInfo (cnt+1), shaOut innerKeyData)
      | otherwise -> errorX ("Did not terminate HMAC key, but key size limit reached.")
     where
      newInfo = hmacInfo {key = shiftLeftOr hmacInfo.key keyData}

      -- xor the key with inner padding
      innerKeyData :: BitVector n
      innerKeyData = keyData `xor` pack (repeat innerPadByte)

    (ReadKey hmacInfo cnt, Just (HmacKeyEnd keyData), _)
      | cnt == maxBound -> (ReadMsg newInfo, shaOut innerKeyData)
      | otherwise -> (SendKeyInnerPad newInfo (cnt+1), shaOutBusy innerKeyData)
     where
      newInfo = hmacInfo {key = shiftLeftOr hmacInfo.key keyData}
      innerKeyData = keyData `xor` pack (repeat innerPadByte)

    (SendKeyInnerPad hmacInfo cnt, _, _)
      | cnt < maxBound -> (SendKeyInnerPad newInfo (cnt+1), shaOutBusy paddingOut)
      | otherwise -> (ReadMsg hmacInfo, noOutBusy)
     where
      newInfo = hmacInfo {key = shiftLeftOr hmacInfo.key padding}

      padding :: BitVector n
      padding = pack (repeat padByte)
      paddingOut = padding `xor` pack (repeat innerPadByte)

    (ReadMsg _, Nothing, _) -> (state, noOut)
    (ReadMsg info, Just (HmacMsg msg), _) -> (ReadMsg info, shaOut msg)
    (ReadMsg info, Just (HmacMsgEnd msg extraBytes), _)
      | extraBytes == 0 -> (SendMsgInnerBugFix info, shaOut msg)
      | otherwise -> (ReceiveMsgInner info, shaOutCnt msg extraBytes)

    -- This workaround is required until
    -- https://github.com/QBayLogic/clash-crypto/issues/13 is fixed
    (SendMsgInnerBugFix info, _, _) -> (ReceiveMsgInner info, shaOutEnd)
     where
      shaOutEnd = (Just (0 :: BitVector n, Just maxBound), Nothing, False)

    (ReceiveMsgInner _info, _, Nothing) -> (state, noOutBusy)
    (ReceiveMsgInner info, _, Just innerMsg) -> (SendKeyOuter newInfo 0, noOutBusy)
     where
      newInfo = info {innerHash = innerMsg}

    (SendKeyOuter info cnt, _, _)
      -- Note: it's `maxBound-1` because if this predicate fails, we still send out a
      -- byte in `otherwise`. It could be changed to not send out a byte and then
      -- the predicate could be just `cnt < maxBound`.
      | cnt < maxBound-1 -> (SendKeyOuter newInfo (cnt+1), shaOutBusy outerKeyChunk)
      | otherwise -> (SendMsgOuter newInfo 0, shaOutBusy outerKeyChunk)
     where
      newKey = info.key `rotateL` (natToNum @n)
      outerKeyChunk = (resize newKey) `xor` pack (repeat outerPadByte)
      newInfo = info {key = newKey}

    (SendMsgOuter info cnt, _, _)
      | cnt < maxBound-1 -> (SendMsgOuter newInfo (cnt+1), shaOutBusy outerMsgChunk)
      | otherwise -> (SendMsgOuterBugFix newInfo, shaOutBusy outerMsgChunk)
     where
      newHash = info.innerHash `rotateL` (natToNum @n)
      outerMsgChunk = (resize newHash)
      newInfo = info {innerHash = newHash}

    -- This workaround is required until
    -- https://github.com/QBayLogic/clash-crypto/issues/13 is resolved
    (SendMsgOuterBugFix info, _, _) -> (ReceiveMsgOuter info, shaOutEnd)
     where
      shaOutEnd = (Just (0 :: BitVector n, Just maxBound), Nothing, False)

    (ReceiveMsgOuter _info, _, Nothing) -> (state, noOutBusy)
    (ReceiveMsgOuter _info, _, Just outerMsg) -> (initState, hmacOut outerMsg)

    (_, _, _) -> errorX
      ( "Case fell through: "
        <> show state
        <> ", input: "
        <> show maybeInput
      )

  noOut = (Nothing, Nothing, True)
  noOutBusy = (Nothing, Nothing, False)
  shaOut d = (Just (d, Nothing), Nothing, True)
  shaOutBusy d = (Just (d, Nothing), Nothing, False)
  shaOutCnt d extraBytes = (Just (d, Just extraBytes), Nothing, True)
  hmacOut d = (Nothing, Just d, False)


shiftLeftOr :: (KnownNat n, KnownNat m) => BitVector n -> BitVector m -> BitVector n
shiftLeftOr a b = resize (a ++# b)


type ShaInput n = (BitVector n, Maybe (Index (n+1)))
data HmacInput n
  = HmacKey    (BitVector n)
  | HmacKeyEnd (BitVector n)
  | HmacMsg    (BitVector n)
  | HmacMsgEnd (BitVector n) (Index (n+1))
 deriving (Generic, Eq, ShowX, NFDataX)

instance (KnownNat n) => Show (HmacInput n) where
  show (HmacKey d) = "HmacKey 0x" <> showHex d ""
  show (HmacKeyEnd d) = "HmacKeyEnd 0x" <> showHex d ""
  show (HmacMsg d) = "HmacMsg 0x" <> showHex d ""
  show (HmacMsgEnd d i) = "HmacMsgEnd 0x" <> showHex d "" <> ", " <> show i

data HmacInfo alg =
  HmacInfo
  { key :: BitVector (BlockSize alg)
  , innerHash :: BitVector (MessageDigestSize alg)
  } deriving (Generic)

deriving instance ( KnownNat (MessageDigestSize alg)
                  , KnownNat (BlockSize alg)
                  ) => NFDataX (HmacInfo alg)
deriving instance ( KnownNat (MessageDigestSize alg)
                  , KnownNat (BlockSize alg)
                  ) => Eq (HmacInfo alg)


instance ( KnownNat (BlockSize alg)
         , KnownNat (MessageDigestSize alg)
         ) => Show (HmacInfo alg) where
  show (HmacInfo k h) =
    "HmacInfo {key=0x"
      <> showHex k ""
      <> ", innerHash=0x"
      <> showHex h ""
      <> "}"

type NumBlockIter alg n = (BlockSize alg `Div` n)+1
type NumMsgDigestIter alg n = (MessageDigestSize alg `Div` n)+1
data HmacState alg n
  -- | Read key in
  = ReadKey (HmacInfo alg) (Index (NumBlockIter alg n))
  | SendKeyInnerPad (HmacInfo alg) (Index (NumBlockIter alg n))
  -- | Read msg in
  | ReadMsg (HmacInfo alg)
  | SendMsgInnerBugFix (HmacInfo alg)
  -- Receive inner hash
  | ReceiveMsgInner (HmacInfo alg)
  -- Computer outer hash
  | SendKeyOuter (HmacInfo alg) (Index (NumBlockIter alg n))
  | SendMsgOuter (HmacInfo alg) (Index (NumMsgDigestIter alg n))
  | SendMsgOuterBugFix (HmacInfo alg)
  -- Receive outer hash
  | ReceiveMsgOuter (HmacInfo alg)
 deriving (Generic)

deriving instance ( KnownNat (MessageDigestSize alg)
                  , KnownNat (BlockSize alg)
                  ) => Show (HmacState alg n)
deriving instance ( KnownNat (MessageDigestSize alg)
                  , KnownNat (BlockSize alg)
                  ) => NFDataX (HmacState alg n)
deriving instance ( KnownNat (MessageDigestSize alg)
                  , KnownNat (BlockSize alg)
                  ) => Eq (HmacState alg n)

