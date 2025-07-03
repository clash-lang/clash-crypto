{-|
Module      : Clash.Crypto.Hash.SHA.Streaming.Padding
Copyright   : Copyright © 2024 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Streaming based padding implementation of FIPS 180-4.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}

module Clash.Crypto.Hash.SHA.Streaming.Padding
  ( ReqSizeFrames
  , atLeastOneSizeFrame
  , PaddedMsgFrame
  , pattern NoData
  , pattern Data
  , pattern EndOfMessage
  , MsgBits(..)
  , MsgPad(..)
  , padMessageStream
  ) where

import Clash.Prelude
import Clash.Sized.Internal.BitVector

import Data.Constraint (Dict(..))
import Data.Constraint.Nat.Extra (DDiv, leTrans, modBound, timesMod)
import Data.Type.Bool (If)
import Language.Haskell.Unicode (type (≤))
import Unsafe.Coerce (unsafeCoerce)

import Clash.Crypto.Hash.SHA.Specification

-- | The number of @n@-bit frames required to store the size of the
-- message.
type ReqSizeFrames alg n =
  If (n <=? SizeBits alg)
    (SizeBits alg `Div` n + If (n `Mod` SizeBits alg <=? 0) 0 1)
    1

-- | Evidence that always at least one frame is required to store the
-- message size.
--
-- prop> ∀ a b ∈ ℕ. b > 0 → a > b ? a div b + (b mod a ≡ 0 ? 0 : 1) : 1
atLeastOneSizeFrame ∷
  ∀ (a ∷ Nat) (b ∷ Nat).
  1 ≤ b ⇒
  Dict (1 ≤ If (b <=? a) (a `Div` b + If (b `Mod` a <=? 0) 0 1) 1)
atLeastOneSizeFrame =
  unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

-- | We store the message size in terms of the number of @n@-bit
-- frames + some remaining bits required to hold the whole message.
type MsgBits ∷ SHA → Nat → Type
data MsgBits alg n =
  MsgBits
    { frameCount ∷ Index ((2 ^ SizeBits alg) `DDiv` n)
      -- ^ number of full @n@-bit frames required to store the message
    , remainder ∷ Index n
      -- ^ number of remaining bits to complete the message
    }
  deriving (Generic, NFDataX)

deriving instance
  ( KnownNat n, 1 ≤ n, KnownNat ((2 ^ SizeBits alg) `DDiv` n)
  , 1 <= (2 ^ SizeBits alg) `DDiv` n
  ) ⇒
  BitPack (MsgBits alg n)

-- | All information necessary for filling the message padding in a
-- @n@-bit frame cycles. The message pad can be computed as soon as
-- the size of the message is known.
type MsgPad ∷ SHA → Nat → Type
data MsgPad alg n =
  MsgPad
    { remainingFrames ∷ Index (2 * BlockSize alg)
      -- ^ the remaining frames still to be output for completing
      -- the padded message
    , remainingSizeFrames ∷ Index (2 * BlockSize alg)
      -- ^ the remaining number of frames containing the size of
      -- the message
    , msgSize ∷ Vec (ReqSizeFrames alg n) (BitVector n)
      -- ^ the frames containing the actual size of the message
    , terminated ∷ Bool
      -- ^ indicates whether the message has already been terminated
    }
  deriving (Generic)

deriving instance
  ( KnownNat n, KnownNat (WordSize alg)
  , 1 ≤ n, 1 ≤ SizeBits alg
  ) ⇒
  NFDataX (MsgPad alg n)

deriving instance
  ( KnownNat n, KnownNat (WordSize alg), KnownNat (BlockSize alg)
  , 1 ≤ n, 1 ≤ SizeBits alg, 1 ≤ 2 * BlockSize alg
  ) ⇒
  BitPack (MsgPad alg n)

-- | Messages are streamed via using multiple message frames, where
-- the individual data frames are encoded using the 'DataFrame'
-- pattern, the end of a message is encoded using an 'EndOfMessage'
-- frame the 'NoData' pattern is used, if no frames are currenlty
-- transfered on the bus.
type PaddedMsgFrame n = Maybe (Either () (BitVector n))

-- | @Nothing@ encodes that there is no data frames being transfered.
pattern NoData ∷ PaddedMsgFrame n
pattern NoData = Nothing

-- | @Just . Right@ encodes a data frame.
pattern Data ∷ BitVector n → PaddedMsgFrame n
pattern Data f = Just (Right f)

-- | @Just (Left ())@ encodes an end-of-message frame.
pattern EndOfMessage ∷ PaddedMsgFrame n
pattern EndOfMessage = Just (Left ())

-- | Extends the input message via adding some padding to ensure that
-- the message's length is always a multiple of 'BlockSize alg'.
padMessageStream ∷
  ∀ (alg ∷ SHA) (dom ∷ Domain) (n ∷ Nat).
  (KnownSHA alg, KnownDomain dom, HiddenClockResetEnable dom, KnownNat n) ⇒
  (1 ≤ n, n ≤ BlockSize alg, BlockSize alg `Mod` n ~ 0) ⇒
  Signal dom (Maybe (BitVector n, Maybe (Index (n + 1)))) →
  -- ^ Input stream for passing messages (see 'sha' fore mode details
  -- on the data serialization).
  Signal dom (PaddedMsgFrame n)
  -- ^ Output message stream, where messages are padded according to
  -- the SHA standard. As for the input, the actual data may be
  -- non-continuous. Note that, in contrast to the input, the bitsize
  -- of the message will always be aligned with the frame size @n@.
padMessageStream
  | SHAFacts{} ← knownSHA @alg
  , Dict ← fact₁
  = mealy (~~>) $ Left $ MsgBits 0 0
 where
  (~~>) ∷
    (KnownNat ((2 ^ SizeBits alg) `DDiv` n), KnownNat (BlockSize alg)) ⇒
    Either (MsgBits alg n) (MsgPad alg n) →
    Maybe (BitVector n, Maybe (Index (n + 1))) →
    (Either (MsgBits alg n) (MsgPad alg n), PaddedMsgFrame n)

  -- no input
  state@(Left _) ~~> Nothing
    = (state, NoData)
  -- non-terminal data input
  Left (MsgBits s r) ~~> Just (d, Nothing)
    = ( Left $ MsgBits (s + 1) r
      , Data d
      )
  -- end of input / start padding
  Left msgBits ~~> Just (d, Just e)
    = initiatePaddingWith msgBits d e
  -- add padding
  Right msgPad ~~> _
    = addPaddingWith msgPad

  -------------------------------------------

  initiatePaddingWith ∷
    KnownNat ((2 ^ SizeBits alg) `DDiv` n) ⇒
    MsgBits alg n →
    BitVector n →
    Index (n + 1) →
    (Either (MsgBits alg n) (MsgPad alg n), PaddedMsgFrame n)
  initiatePaddingWith (MsgBits s _) dLast trim
    = terminate dLast trim
    $ (\mp →
         if trim == 0
         then (Right mp { terminated = False }, Data dLast)
         else addPaddingWith mp
      )
    $ createMsgPad
    $ if | trim == natToNum @n → MsgBits s 0
         | trim == 0           → MsgBits (s + 1) 0
         | otherwise           → MsgBits s
                               $ truncateB @_ @n @1
                               $ natToNum @n - trim

  terminate ∷
    BitVector n →
    Index (n + 1) →
    (Either (MsgBits alg n) (MsgPad alg n), PaddedMsgFrame n) →
    (Either (MsgBits alg n) (MsgPad alg n), PaddedMsgFrame n)

  terminate dLast trim (ePad, meVec)
    | trim == natToNum @n
    = (ePad, fmap riseMsb <$> meVec)

    | trim > 0
    , SHAFacts{} ← knownSHA @alg
    , Dict ← fact₀
    , let c = fromEnum trim; bits = ((dLast `shiftR#` c) .<<+ 1) `shiftL#` c - 1
    = (ePad, fmap (or# bits) <$> meVec)

    | otherwise
    = (ePad, meVec)

  addPaddingWith ∷
    MsgPad alg n →
    (Either (MsgBits alg n) (MsgPad alg n), PaddedMsgFrame n)
  addPaddingWith p@MsgPad{..}
    | remainingFrames > remainingSizeFrames
    , SHAFacts{} ← knownSHA @alg
    = ( Right p { remainingFrames = remainingFrames - 1
                , terminated      = True
                }
      , Data $ if terminated then 0 else 1 +>>. 0
      )

    | otherwise
    , SHAFacts{} ← knownSHA @alg
    , Dict ← fact₁
    , Dict ← atLeastOneSizeFrame @(SizeBits alg) @n
    , let d = head @(ReqSizeFrames alg n - 1) msgSize
    = ( if remainingSizeFrames > 0
        then Right p { remainingFrames     = remainingFrames - 1
                     , remainingSizeFrames = remainingSizeFrames - 1
                     , msgSize             = msgSize <<+ 0
                     , terminated          = True
                     }
        else Left (MsgBits 0 0)
      , if remainingSizeFrames == 0
        then EndOfMessage
        else Data $ if terminated then d else riseMsb d
      )

  createMsgPad ∷ MsgBits alg n → MsgPad alg n
  createMsgPad (MsgBits s r)
    | SHAFacts{} ← knownSHA @alg
    = MsgPad
        { remainingFrames =
            let
              nFits ∷ Num a ⇒ a
              nFits = natToNum @(BlockSize alg `DDiv` n)
              -- ^ number of @n@-bit frames fitting into a message
              -- block
              truncateB₀ =
                truncateB @Index
                  @(2 * BlockSize alg)
                  @((2 ^ SizeBits alg) `DDiv` n - 2 * BlockSize alg)
              -- ^ specialized 'truncateB'
              rFrames ∷ Index (2 * BlockSize alg)
              rFrames
                | Dict ← fact₀
                , Dict ← fact₁
                = nFits - truncateB₀ (mod s nFits)
              -- ^ number of @n@-bit frames that still must be padded
              -- within the current message block
              overhead
                | 1 + natToNum @(SizeBits alg) <= rFrames * natToNum @n = 0
                | otherwise = nFits
              -- ^ extend by one message block if the required padding
              -- information won't fit otherwise
            in
              rFrames + overhead

        , remainingSizeFrames =
            natToNum @(ReqSizeFrames alg n)

        , msgSize = bitCoerce $
            let
              u ∷ Unsigned (n * ReqSizeFrames alg n)
              u = unpack (extend₀ (pack₀ s)) * natToNum @n
                + unpack (extend₁ (pack r))
            in
              u
        , terminated = True
        }

  pack₀ ∷
    Index ((2 ^ SizeBits alg) `DDiv` n) →
    BitVector (CLog 2 ((2 ^ SizeBits alg) `Div` n))
  pack₀
    | SHAFacts{} ← knownSHA @alg
    , Dict ← fact₀
    , Dict ← fact₁
    , Dict ← leTrans @1 @(2 * BlockSize alg) @((2 ^ SizeBits alg) `Div` n)
    = pack

  extend₀ ∷
    BitVector (CLog 2 ((2 ^ SizeBits alg) `Div` n)) →
    BitVector (n * ReqSizeFrames alg n)
  extend₀
    | SHAFacts{} ← knownSHA @alg
    , Dict ← fact₀
    , Dict ← leTrans @1 @(2 * BlockSize alg) @((2 ^ SizeBits alg) `Div` n)
    , Dict ← lemma₀ @(SizeBits alg) @n
    = extend @BitVector
        @(CLog 2 ((2 ^ SizeBits alg) `Div` n))
        @(n * ReqSizeFrames alg n - CLog 2 ((2 ^ SizeBits alg) `Div` n))
   where
    lemma₀ ∷
      ∀ (a ∷ Nat) (b ∷ Nat).
      1 ≤ b ⇒
      Dict ( CLog 2 ((2 ^ a) `Div` b)
           ≤ b * (If (b <=? a) (a `Div` b + If (b `Mod` a <=? 0) 0 1) 1)
           )
    lemma₀ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  extend₁ ∷
    BitVector (CLog 2 n) →
    BitVector (n * ReqSizeFrames alg n)
  extend₁
    | SHAFacts{} ← knownSHA @alg
    , Dict ← atLeastOneSizeFrame @(SizeBits alg) @n
    , Dict ← lemma₀ @n @(ReqSizeFrames alg n)
    = extend @BitVector
        @(CLog 2 n)
        @(n * ReqSizeFrames alg n - CLog 2 n)
   where
    lemma₀ ∷
      ∀ (a ∷ Nat) (b ∷ Nat).
      1 ≤ b ⇒
      Dict (CLog 2 a ≤ a * b)
    lemma₀ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  fact₀ ∷ Dict (2 * BlockSize alg <= (2 ^ SizeBits alg) `Div` n)
  fact₀
    | SHAFacts{} ← knownSHA @alg
    , Dict ← modBound @(BlockSize alg) @n
    , Dict ← lemma₀ @(BlockSize alg) @n
    , Dict ← lemma₁
        @(BlockSize alg)
        @n
        @(2 ^ SizeBits alg)
        @(2 * BlockSize alg)
    = Dict
   where
    lemma₀ ∷
      ∀ (a ∷ Nat) (b ∷ Nat).
      (1 ≤ b, a `Mod` b ~ 0) ⇒
      Dict (b ≤ a)
    lemma₀ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

    lemma₁ ∷
      ∀ (a ∷ Nat) (b ∷ Nat) (c ∷ Nat) (d ∷ Nat).
      (b ≤ a, d ≤ c `Div` a) ⇒
      Dict (d ≤ c `Div` b)
    lemma₁ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  fact₁ ∷ Dict ((2 ^ SizeBits alg) `DDiv` n ~ (2 ^ SizeBits alg) `Div` n)
  fact₁
    | SHAFacts{} ← knownSHA @alg
    , Dict ← timesMod
        @(BlockSize alg)
        @((2 ^ SizeBits alg) `Div` BlockSize alg)
        @n
    , Dict ← lemma₀ @n
    = Dict
   where
    lemma₀ ∷
      ∀ (a ∷ Nat).
      1 ≤ a ⇒
      Dict (0 `Mod` a ~ 0)
    lemma₀ = unsafeCoerce (Dict ∷ Dict (0 ~ 0))

riseMsb ∷ ∀ n. (KnownNat n, 1 ≤ n) ⇒ BitVector n → BitVector n
riseMsb = (pack high ++#) . truncateB# @(n-1) @1