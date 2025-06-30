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
-- Note: `m` should only be passed as a type variable and not explicitly
--       instantiated. The type-lvel natural should always be inferred by the
--       constraint solver.
type SuitableDivisorForHMAC n alg m =
  ( -- For a given n
    KnownNat n
  , -- `n` has to be between `1` and `min (BlockSize alg, MessageDigestSize alg)`
    -- inclusive
    1 <= n, n <= BlockSize alg, n <= MessageDigestSize alg
  , -- Ensure n can evenly divide `BlockSize alg` and `MessageDigestSize alg`
    Mod (BlockSize alg) n ~ 0
  , Mod (MessageDigestSize alg) n ~ 0
  -- The below constraints are all implied by the constraints above, but our
  -- constraint solver is not strong enough to solve for them. If we improve the
  -- power of the constraint solver, the below can be removed.
  -- ---------------------------------------------------------
  -- | The below constraint logically follows from `MessageDigestSize alg `Mod` 8 ~ 0`
  , MessageDigestSize alg `Div` n * n ~ MessageDigestSize alg
  -- | The below constraint logically follows from `BlockSize alg `Mod` 8 ~ 0`
  , BlockSize alg `Div` n * n ~ BlockSize alg
  -- | The below constraint logically follows from
  --   `MessageDigestSize alg <= BlockSize alg` (which I've added to SHAFacts)
  , MessageDigestSize alg `Div` n <= BlockSize alg `Div` n
  , -- | The below constraint logically follows from
    --   `MessageDigestSize alg <= BlockSize alg`
    KnownNat m, (MessageDigestSize alg `Div` n) + m ~ BlockSize alg `Div` n
  )

-- HMAC circuit described in rfc2104 (https://www.rfc-editor.org/info/rfc2104).
-- It accepts a stream of two inputs, one is a Bool toggle if
-- the key is being passed and the other is a stream of bytes. The isKey should
-- be held high while the key is being passed, and then low once the key is finished.
-- Once isKey is put low, the circuit will ignore input for up to
-- `2*(BlockSize alg / n)+ 3` cycles, while it pads the key. Then it accepts a message.
-- The end of message is indicated by once again driving the isKey high and
-- holding it there.
--
-- Note: `hmac` requires the key to be `BlockSize alg` long. The HMAC specification
-- says if the key is shorter, it should be padded with 0s, and if the key is longer,
-- the key should be run through SHA to create a new key of size `BlockSize alg`.
-- The circuit WILL pad the key if required, but WILL NOT hash the key if the key
-- is too large. The key sender is required to handle that (if applicable).
hmac ::
  forall (alg :: SHA) dom m.
  KnownSHA alg =>
  SuitableDivisorForHMAC 8 alg m =>
  HiddenClockResetEnable dom =>
  Signal dom Bool ->
  -- ^ The "isKey" indicator.
  Signal dom (Maybe (BitVector 8)) ->
  -- ^ key + message input stream. The key comes first, then the message.
  -- The circuit needs at most `2*(BlockSize alg / n)+c` cycles
  -- to pad the key, where `n` in this case is 8 and `c` is a small constant.
  -- `c=3` should be sufficient.
  Signal dom (Maybe (BitVector (MessageDigestSize alg)))
  -- ^ Response
hmac isKey dataIn
  | SHAFacts _ <- knownSHA @alg
  = let
    hashOutput = sha @alg @_ @8 hashInputBugFix
    hashInputBugFix = hmacBugFix @alg isEndPayload hashInput
    (isEndPayload, hashInput, output) =
      hmacController @alg isEndMsg paddedData hashOutput
    (isEndMsg, paddedData) = keyPad @alg isKey dataIn
  in output


-- | Key padding for HMAC. If the key is finished but the key size has not been
-- reached, the circuit will add `0x00`s. If the key is larger than key size, the
-- circuit will leave it untouched. The circuit will also leave any non-key bytes
-- untouched.
keyPad ::
  forall (alg :: SHA) dom m.
  KnownSHA alg =>
  SuitableDivisorForHMAC 8 alg m =>
  HiddenClockResetEnable dom =>
  Signal dom Bool ->
  Signal dom (Maybe (BitVector 8)) ->
  ( Signal dom Bool
  , Signal dom (Maybe (BitVector 8))
  )
keyPad isKeyS inputS
  | SHAFacts _ <- knownSHA @alg
  = let
    step (wasKey, n) (isKey, input) = (newState, (isEndMsg, output))
     where
      output
        | not isKey && n < keySize = Just padByte
        | otherwise = input

      newState
        | -- If it's a new key, reset the padding state
          isEndMsg = (isKey, 0)
        | -- Otherwise, increment the keySize iff we pass out a byte (either
          -- from input or padding)
          isJust output && n < keySize = (isKey, n+1)
        | -- Otherwise, don't touch the state
          otherwise = (isKey, n)

      keySize = natToNum @(BlockSize alg `Div` 8)
      -- If isKey goes from low->high, we know the msg is finished
      isEndMsg = not wasKey && isKey

    outputS = mealyB step (True, 0 :: Index (BlockSize alg + 1)) (isKeyS, inputS)
  in outputS


-- This workaround is required until
-- https://github.com/QBayLogic/clash-crypto/issues/13 is fixed
hmacBugFix ::
  forall alg dom m.
  KnownSHA alg =>
  SuitableDivisorForHMAC 8 alg m =>
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


-- | Handles most of the hmac logic.
hmacController ::
  forall alg dom m.
  KnownSHA alg =>
  SuitableDivisorForHMAC 8 alg m =>
  HiddenClockResetEnable dom =>
  Signal dom Bool ->
  Signal dom (Maybe (BitVector 8)) ->
  Signal dom (Maybe (BitVector (MessageDigestSize alg))) ->
  ( Signal dom Bool
  , Signal dom (Maybe (BitVector 8))
  , Signal dom (Maybe (BitVector (MessageDigestSize alg)))
  )
hmacController isEndS inputS digestS
  | SHAFacts _ <- knownSHA @alg
  = let
    initKey = repeat undefined
    initMsgHash = repeat undefined
    initState = ( HashKey
                , 0 :: Index (BlockSize alg + MessageDigestSize alg + 1)
                , HmacInfo @alg @8 @m initKey initMsgHash)

    keySize = natToNum @(BlockSize alg `Div` 8)
    msgSize = natToNum @(MessageDigestSize alg `Div` 8)
    step (algState, n, hmacInfo) (isEndMsg, inputIn, digestIn) =
      (newState, (isEndPayload, hashInput, output))
     where
      newState = case (digestIn, inputIn) of
        -- If we receive a hash digest, move to the next state
        (Just digest, _)
          | algState == HashKey ->
              (InnerHash, 0, hmacInfo {key = unpack digest ++ repeat padByte})
          | algState == InnerHash ->
              (OuterHash, 0, hmacInfo {msgHash = unpack digest})
          | algState == OuterHash ->
              (HashKey, 0, HmacInfo {key = initKey, msgHash = initMsgHash})

        (_, Just input)
          | -- If the key is finished, move onto the next part
            algState == HashKey && (n+1) == keySize ->
              (InnerHash, 0, hmacInfo {key = hmacInfo.key <<+ input})
          | -- Otherwise, keep reading in key
            algState == HashKey ->
              (algState, n+1, hmacInfo {key = hmacInfo.key <<+ input})
          | -- The only other time we might receive input is in the msg part of
            -- InnerHash, so do nothing
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

    outputS = mealyB step initState (isEndS, inputS, digestS)
  in outputS


-- Type alias for SHA input
type ShaInput n = (BitVector n, Maybe (Index (n+1)))
data HmacAlgorithmState
  = HashKey
  | InnerHash
  | OuterHash
  deriving (Generic, Eq, NFDataX)

-- Stores the internal computed/assembled values for hmac state
data HmacInfo alg n m =
  HmacInfo
  { key :: Vec (BlockSize alg `Div` n) (BitVector n)
  , msgHash :: Vec (MessageDigestSize alg `Div` n) (BitVector n)
  } deriving (Generic)

deriving instance ( KnownNat (MessageDigestSize alg)
                  , KnownNat (BlockSize alg)
                  , SuitableDivisorForHMAC n alg m
                  ) => NFDataX (HmacInfo alg n m)
deriving instance ( KnownNat (MessageDigestSize alg)
                  , KnownNat (BlockSize alg)
                  , SuitableDivisorForHMAC n alg m
                  ) => Eq (HmacInfo alg n m)
