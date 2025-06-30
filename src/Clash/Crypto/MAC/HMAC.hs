{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Clash.Crypto.MAC.HMAC where

import Clash.Prelude
import Data.Maybe (isJust)
import Clash.Crypto.Hash.SHA

-- HMAC values taken from rfc2104 (https://www.rfc-editor.org/info/rfc2104).
padByte, innerPadByte, outerPadByte :: BitVector 8
padByte      = 0x00
innerPadByte = 0x36
outerPadByte = 0x5c

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
  , Mod (MessageDigestSize alg) n ~ 0
    -- The following constraints are all implied by SuitableDivisorForHMAC, but our
  -- constraint solver is not strong enough to solve for them. If we improve the
  -- power of the constraint solver, the below can be removed.
  --
  -- | The below constraint logically follows from `MessageDigestSize alg `Mod` 8 ~ 0`
  , MessageDigestSize alg `Div` 8 * 8 ~ MessageDigestSize alg
  -- | The below constraint logically follows from `BlockSize alg `Mod` 8 ~ 0`
  , BlockSize alg `Div` 8 * 8 ~ BlockSize alg
  -- | The below constraint logically follows from `MessageDigestSize alg <= BlockSize alg`
  -- (added to SHAFacts)
  , MessageDigestSize alg `Div` 8 <= BlockSize alg `Div` 8
  )

hmacNew ::
  forall (alg :: SHA) dom m.
  (KnownNat (BlockSize alg), KnownNat (MessageDigestSize alg)) =>
  SuitableDivisorForHMAC 8 alg =>
  (BlockSize alg `Div` 8) * 8 ~ BlockSize alg =>
  MessageDigestSize alg <= BlockSize alg =>
  MessageDigestSize alg `Div` 8 <= BlockSize alg `Div` 8 =>
  (MessageDigestSize alg `Div` 8) * 8 ~ MessageDigestSize alg =>
  (KnownNat m, (MessageDigestSize alg `Div` 8) + m ~ BlockSize alg `Div` 8) =>
  KnownSHA alg =>
  HiddenClockResetEnable dom =>
  Signal dom Bool ->
  Signal dom (Maybe (BitVector 8)) ->
  Signal dom (Maybe (BitVector (MessageDigestSize alg)))
hmacNew isKey dataIn = output
 where
  hashOutput = sha @alg @_ @8 hashInputBugFix
  hashInputBugFix = hmacBugFix isEndMsg' hashInput
  (isEndMsg', hashInput, output) = (hmacController @alg) isEndMsg paddedData hashOutput
  (isEndMsg, paddedData) = (keyPad @alg) isKey dataIn


hmacBugFix ::
  HiddenClockResetEnable dom =>
  Signal dom Bool ->
  Signal dom (Maybe (BitVector 8)) ->
  Signal dom (Maybe (ShaInput 8))
hmacBugFix isEndS inputS = mealy step (False, False) $ bundle (isEndS, inputS)
 where
  step (prevEnd, wasEnd) (isEnd, input) = (newState, output)
   where
    newState = (wasEnd, isEnd)
    output
      | not prevEnd && wasEnd = Just (0, Just maxBound)
      | Just d <- input = Just (d, Nothing)
      | otherwise = Nothing


-- | Key padding for HMAC. If the key is finished but the key size has not been
-- reached, the circuit will add `0x00`s. If the key is larger than key size, the
-- circuit will leave it untouched. The circuit will also leave any non-key bytes
-- untouched.
keyPad ::
  forall (alg :: SHA) dom.
  KnownNat (BlockSize alg) =>
  HiddenClockResetEnable dom =>
  Signal dom Bool ->
  Signal dom (Maybe (BitVector 8)) ->
  ( Signal dom Bool
  , Signal dom (Maybe (BitVector 8))
  )
keyPad isKeyS inputS = mealyB step (True, 0 :: Index (BlockSize alg + 1)) (isKeyS, inputS)
 where
  step (wasKey, n) (isKey, input) = (newState, (isEndMsg, output))
   where
    output
      | not isKey && n < keySize = Just padByte
      | otherwise = input

    newState
      | -- If it's a new key, reset the padding state
        isEndMsg = (isKey, 0)
      | -- Otherwise, increment the keySize iff we pass out a byte (either from input or padding)
        isJust output && n < keySize = (isKey, n+1)
      | -- Otherwise, don't touch the state
        otherwise = (isKey, n)

    keySize = natToNum @(BlockSize alg `Div` 8)
    -- If isKey goes from low->high, we know the msg is finished
    isEndMsg = not wasKey && isKey


type ShaInput n = (BitVector n, Maybe (Index (n+1)))
data HmacAlgorithmState
  = HashKey
  | InnerHash
  | OuterHash
  deriving (Generic, Eq, NFDataX)

data HmacInfo alg =
  HmacInfo
  { key :: Vec (BlockSize alg `Div` 8) (BitVector 8)
  , msgHash :: Vec (MessageDigestSize alg `Div` 8) (BitVector 8)
  } deriving (Generic)

deriving instance ( KnownNat (MessageDigestSize alg)
                  , KnownNat (BlockSize alg)
                  ) => NFDataX (HmacInfo alg)
deriving instance ( KnownNat (MessageDigestSize alg)
                  , KnownNat (BlockSize alg)
                  ) => Eq (HmacInfo alg)


hmacController ::
  forall alg dom m.
  (KnownNat (BlockSize alg), KnownNat (MessageDigestSize alg)) =>
  MessageDigestSize alg <= BlockSize alg =>
  HiddenClockResetEnable dom =>
  Div (BlockSize alg) 8 * 8 ~ BlockSize alg =>
  (MessageDigestSize alg `Div` 8) + 0 <= BlockSize alg `Div` 8 =>
  MessageDigestSize alg `Mod` 8 ~ 0 =>
  (KnownNat m, (MessageDigestSize alg `Div` 8 + m ~ BlockSize alg `Div` 8)) =>
  ((MessageDigestSize alg `Div` 8) * 8 ~ MessageDigestSize alg) =>
  Signal dom Bool ->
  Signal dom (Maybe (BitVector 8)) ->
  Signal dom (Maybe (BitVector (MessageDigestSize alg))) ->
  ( Signal dom Bool
  , Signal dom (Maybe (BitVector 8))
  , Signal dom (Maybe (BitVector (MessageDigestSize alg)))
  )
hmacController isEndS inputS digestS = mealyB step initState (isEndS, inputS, digestS)
 where
  initKey = repeat undefined
  initMsgHash = repeat undefined
  initState = ( HashKey
              , 0 :: Index (BlockSize alg + MessageDigestSize alg + 1)
              , HmacInfo @alg initKey initMsgHash)

  keySize = natToNum @(BlockSize alg `Div` 8)
  msgSize = natToNum @(MessageDigestSize alg `Div` 8)
  step (algState, n, hmacInfo) (isEndMsg, inputIn, digestIn) = (newState, (isEndPayload, hashInput, output))
   where
    newState = case (digestIn, inputIn) of
      -- If we receive a hash digest, move to the next state
      (Just digest, _)
        | algState == HashKey -> (InnerHash, 0, hmacInfo {key = unpack digest ++ repeat 0x00})
        | algState == InnerHash -> (OuterHash, 0, hmacInfo {msgHash = unpack digest})
        | algState == OuterHash -> (HashKey, 0, HmacInfo { key = initKey
                                                         , msgHash = initMsgHash })

      (_, Just input)
        | -- If the key is finished, move onto the next part
          algState == HashKey && (n+1) == keySize -> (InnerHash, 0, hmacInfo {key = hmacInfo.key <<+ input})
        | -- Otherwise, keep reading in key
          algState == HashKey -> (algState, n+1, hmacInfo {key = hmacInfo.key <<+ input})
        | -- The only other time we might receive input is in the msg part of InnerHash, so do nothing
          otherwise -> (algState, n, hmacInfo)

      (_, _)
        | isJust hashInput -> (algState, n+1, hmacInfo)
        | otherwise -> (algState, n, hmacInfo)

    hashInput = case algState of
      HashKey -> Nothing
      InnerHash
        | n < keySize -> Just (hmacInfo.key !! n `xor` innerPadByte)
        | otherwise -> inputIn
      OuterHash
        | n < keySize -> Just (hmacInfo.key !! n `xor` outerPadByte)
        | n < keySize + msgSize -> Just (hmacInfo.msgHash !! (n-keySize))
        | otherwise -> Nothing

    isEndPayload
      | algState == OuterHash && n == keySize + msgSize = True
      | otherwise = isEndMsg

    -- Send the hash digest as result iff we're on the last step of computation
    output = case algState of
      OuterHash -> digestIn
      _ -> Nothing



-- | HMAC circuit described in rfc2104 (https://www.rfc-editor.org/info/rfc2104).
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

