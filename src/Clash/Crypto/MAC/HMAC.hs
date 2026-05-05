{-|
Module      : Clash.Crypto.MAC.HMAC
Copyright   : Copyright © 2025-2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

A streaming implementation of HMAC according to
[RFC 2104](https://www.rfc-editor.org/info/rfc2104).
-}

{-# LANGUAGE ApplicativeDo #-}

module Clash.Crypto.MAC.HMAC
  ( hmac
  , hmacE
  , IPad
  , OPad
  , HmacStage(..)
  ) where

import Clash.Prelude.Safe
import Clash.Signal.Channel
import Clash.Signal.DataStream

import Data.Constraint.Nat.Extra (CancelMultiple, KeepsPositiveIfMultiple)
import Data.Functor ((<&>))
import GHC.TypeNats.Proof (Rewrite(..), using)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Hash.SHA

-- | The @ipad@ value, as defined in
-- [RFC 2104](https://www.rfc-editor.org/info/rfc2104).
type IPad = 0x36 ∷ Nat

-- | The @opad@ value, as defined in
-- [RFC 2104](https://www.rfc-editor.org/info/rfc2104).
type OPad = 0x5c ∷ Nat

-- | The stages that are traversed during every 'hmac'
-- request-response.
data HmacStage
  = -- | Calculation of the inner hash, where the input
    -- @(K XOR ipad, text)@ is forwarded to the hashing component.
    InnerHash
  | -- | Calculation of the outer hash, where first the stored
    -- @K XOR opad@ is passed to the hashing component.
    OuterKey
  | -- | Calculation of the outer hash, where the previously computed
    -- @H (K XOR ipad, text)@ is passed to the hashing component.
    OuterDigest
  deriving (Generic, NFDataX, ShowX)

-- | A streaming implementation of HMAC according to
-- [RFC 2104](https://www.rfc-editor.org/info/rfc2104).
--
-- The component reads key + message pairs from a byte-framed
-- 'DataStream', where the key comes first and the message comes
-- second. The key can be of variable size, which is attached to the
-- first frame (in bytes). After having received the key the circuit
-- will automatically zero the data of any further input frame until
-- 'BlockSize' @alg@ many bits have been received. The message always
-- starts after the first 'BlockSize' @alg@ bits have been
-- received. The component responds after the message has been
-- terminated and ignores any further input until the HMAC has been
-- calculated.
--
-- Note: [RFC 2104](https://www.rfc-editor.org/info/rfc2104) requires
-- the initial byte block, containing the key, to be exactly 'BlockSize'
-- @alg@ many bits long. If the actual key is shorter than that, then
-- it must be padded with zeros. If it is longer instead, then the key
-- should be passed through the hashing function to shorten it to at
-- most 'BlockSize' @alg@ many bits.
--
-- This implementation currently does __not__ support keys that
-- require more than 'BlockSize' @alg@ many bits.
hmac ∷
  ∀ (dom ∷ Domain). HiddenClockResetEnable dom ⇒
  ∀ (alg ∷ SHA) → KnownSHA alg ⇒
  (8 ≤ BlockSize alg, Mod (BlockSize alg) 8 ~ 0) ⇒
  -- | input stream
  DataStream dom (Index ((BlockSize alg `Div` 8) + 1)) () (BitVector 8) →
  -- | response channel
  Channel dom (Digest alg)
hmac alg input
  | SHAFacts ← knownSHA alg
  = let (result, hashInput) = hmacE alg input digest
        digest = sha alg hashInput
     in result

-- | A 'hmac' variant using shared SHA hash circuity.
hmacE ∷
  ∀ (dom ∷ Domain). HiddenClockResetEnable dom ⇒
  ∀ (alg ∷ SHA) → KnownSHA alg ⇒
  (8 ≤ BlockSize alg, Mod (BlockSize alg) 8 ~ 0) ⇒
  -- | input stream
  DataStream dom (Index ((BlockSize alg `Div` 8) + 1)) () (BitVector 8) →
  -- | hash output
  Channel dom (Digest alg) →
  -- | (response channel, hash input)
  (Channel dom (Digest alg), DataStream dom () (Index 8) (BitVector 8))
hmacE alg (mapEnd (const (0 ∷ Index 8)) → input) digest
  | SHAFacts ← knownSHA alg
  = let
      -- mark the input key frames via counting the received number of frames
      isInputKeyFrame = input.hasData .&&. count .>. 0
       where
        count = do
          frame ← input
          c ← register minBound count
          return $ case frame of
            Idle      → minBound
            Start s _ → s
            NoData    → c
            _         → satPred SatBound c

      -- mark the padded key frames via counting the received number of bytes
      isPaddedKeyFrame = input.atStartFrame .||. input.hasData .&&. count .>. 0
       where
        count = register (0 ∷ Index (BlockSize alg `Div` 8))
          $ mux input.atStartFrame (pure maxBound)
          $ apEn input.hasData (satPred SatBound)
            count

      -- zero everything behind the actual key and xor the key frames
      -- with the provided pad
      xorpad pad
        = apEn isPaddedKeyFrame (xor pad <$>)
        $ apEn (isPaddedKeyFrame .&&. not <$> isInputKeyFrame) (0x00 <$)
        $ mapStart (const ()) input

      -- the output of the hashing function
      hashInput = do
        -- immediately forward key & msg during the 'InnerHash' stage
        innerHashSel ← xorpad $ natToNum @IPad
        -- buffer @key XOR opad@ until we need it during the 'OuterKey' stage
        outerKeySel ← regEnN (SNat @(BlockSize alg `Div` 8)) Idle
          (isPaddedKeyFrame .||. atOuterKeyStage)
          (xorpad $ natToNum @OPad)
        -- memorize the digest that is responed at the end of the
        -- 'InnerDigest' stage for serializing it out during the
        -- 'OuterDigest' stage
        outerDigestSel ← serialize $ do
          curStage ← stage
          latestHash ← newsfeed digest
          return $ case curStage of
            InnerHash | Just h ← latestHash → Charge h
            OuterDigest                     → Discharge
            _                               → Hold

        curStage ← stage
        return $ case curStage of
          InnerHash   → innerHashSel
          OuterKey    → outerKeySel
          OuterDigest → case outerDigestSel of
            Start _ x → Middle x
            x         → x

      -- stage selector for passing data from the right components at
      -- the desired times
      stage = moore (~~>) fst istate digest.hasUpdates
       where
        istate = (InnerHash, minBound ∷ Index (BlockSize alg `Div` 8))

        (s, n) ~~> updated = case s of
          InnerHash   | updated   → (OuterKey   , maxBound)
          OuterKey    | n > 0     → (OuterKey   , n - 1   )
                      | otherwise → (OuterDigest, n       )
          OuterDigest | updated   → (InnerHash  , n       )
          _                       → (s          , n       )

      -- some convenience shortcuts
      atOuterKeyStage    = stage <&> \case { OuterKey    → True; _ → False }
      atOuterDigestStage = stage <&> \case { OuterDigest → True; _ → False }
    in
      (guardC atOuterDigestStage digest, hashInput)

-- | Stores the last received 'Charge' and holds it until being
-- discharged. While discharging, the stored value is streamed out in
-- network order (in chunks of the specified size). A chunk is only
-- output at the points in time where 'Discharge' is present at the
-- input. Every charged value can only be discharged once, while it
-- can be overwritten with a new 'Charge' even before the previous
-- 'Charge' has been completely streamed out.
serialize ∷
  ∀ a n dom.
  ( HiddenClockResetEnable dom
  , BitPack a, KnownNat (BitSize a), KnownNat n
  , 1 ≤ n, 1 ≤ BitSize a, BitSize a `Mod` n ~ 0
  ) ⇒
  -- | input action
  Signal dom (SerializeAction a) →
  -- | output stream
  DataStream dom () (Index n) (BitVector n)
serialize = mealy (~~>) istate
 where
  istate =
    ( repeat neval ∷ Vec (BitSize a `Div` n) (BitVector n)
    , 0 ∷ Index ((BitSize a `Div` n) + 1)
    )

  (buf, n) ~~> Discharge | n > 0
    = ((buf <<+ neval, satPred SatBound n), frame n $ bufHead buf)

  _ ~~> Charge x
    | Rewrite ← using @(CancelMultiple (BitSize a) n)
    = ((bitCoerce x, maxBound), Idle)

  (buf, n) ~~> _ =
    ((buf, n), if n > 0 then NoData else Idle)

  bufHead
    | Rewrite ← using @(KeepsPositiveIfMultiple (BitSize a) n)
    = leToPlusKN @1 @(BitSize a `Div` n) $ head @(BitSize a `Div` n - 1)

  frame n
    | n == maxBound = Start ()
    | n > 1         = Middle
    | otherwise     = End 0

  -- a value that should never be evaluated
  neval = error "Clash.Crypto.MAC.HMAC.serialize: Mealy"

data SerializeAction a = Charge a | Hold | Discharge
  deriving (Generic, NFDataX)
