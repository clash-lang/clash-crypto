{-|
Module      : Clash.Crypto.Hash.SHA.Streaming.Padding
Copyright   : Copyright © 2024-2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Streaming based padding implementation of FIPS 180-4.
-}

{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}

module Clash.Crypto.Hash.SHA.Streaming.Padding
  ( padMessageStream
  , ReqSizeFrames
  , MsgBits(..)
  , MsgPad(..)
  ) where

import Clash.Prelude.Safe
import Clash.Signal.DataStream

import Data.Constraint.Nat.Extra
  ( DDiv, LeTrans, ModBound, TimesMod, DivisorIsLess, DivisorMonotoneInverse
  , ModZero, CLog2IsLessProduct, PositiveResultCond0, CLog2LECond0
  )
import Data.Kind (Type)
import Data.Type.Bool (If)
import GHC.TypeNats.Proof (Rewrite(..), using)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Hash.SHA.Specification

-- | The number of @n@-bit frames required to store the size of the
-- message.
type ReqSizeFrames alg n =
  If (n <=? SizeBits alg)
    (SizeBits alg `Div` n + If (n `Mod` SizeBits alg <=? 0) 0 1)
    1

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
  (KnownNat n, KnownNat ((2 ^ SizeBits alg) `DDiv` n)) ⇒
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
  (KnownNat n, KnownNat (WordSize alg), 1 ≤ n, 1 ≤ SizeBits alg) ⇒
  NFDataX (MsgPad alg n)

deriving instance
  ( KnownNat n, KnownNat (WordSize alg), KnownNat (BlockSize alg)
  , 1 ≤ n, 1 ≤ SizeBits alg
  ) ⇒
  BitPack (MsgPad alg n)

-- | Extends the input message via adding some padding to ensure that
-- the message's length is always a multiple of 'BlockSize alg'.
padMessageStream ∷
  ∀ (n ∷ Nat) (dom ∷ Domain).
  (KnownNat n, HiddenClockResetEnable dom, 1 ≤ n) ⇒
  ∀ (alg ∷ SHA) → KnownSHA alg ⇒
  (n ≤ BlockSize alg, BlockSize alg `Mod` n ~ 0) ⇒
  DataStream dom () (Index n) (BitVector n) →
  DataStream dom () () (BitVector n)
padMessageStream alg
  | SHAFacts ← knownSHA alg
  , Rewrite ← fact₁
  = mealy (~~>) $ Left $ MsgBits 0 0
 where
  (~~>) ∷
    (KnownNat ((2 ^ SizeBits alg) `DDiv` n), KnownNat (BlockSize alg)) ⇒
    Either (MsgBits alg n) (MsgPad alg n) →
    Frame () (Index n) (BitVector n) →
    (Either (MsgBits alg n) (MsgPad alg n), Frame () () (BitVector n))

  -- no input
  Left mbs ~~> Idle
    = (Left mbs, Idle)

  Left mbs ~~> NoData
    = (Left mbs, NoData)

  -- non-terminal frames
  Left (MsgBits s r) ~~> Start () d
    = (Left $ MsgBits (s + 1) r, Start () d)

  Left (MsgBits s r) ~~> Middle d
    = (Left $ MsgBits (s + 1) r, Middle d)

  -- end of input / start padding
  Left msgBits ~~> End e d
    = initiatePaddingWith msgBits d e

  -- add padding
  Right msgPad ~~> _
    = addPaddingWith msgPad

  -------------------------------------------

  initiatePaddingWith ∷
    KnownNat ((2 ^ SizeBits alg) `DDiv` n) ⇒
    MsgBits alg n →
    BitVector n →
    Index n →
    (Either (MsgBits alg n) (MsgPad alg n), Frame () () (BitVector n))
  initiatePaddingWith (MsgBits s _) dLast trim
    = terminate dLast trim
    $ (\mp → if trim > 0
             then addPaddingWith mp
             else (Right mp { terminated = False }, Middle dLast))
    $ createMsgPad
    $ if trim > 0
      then MsgBits s $ maxBound - (trim - 1)
      else MsgBits (s + 1) 0

  terminate ∷
    BitVector n →
    Index n →
    (Either (MsgBits alg n) (MsgPad alg n), Frame () () (BitVector n)) →
    (Either (MsgBits alg n) (MsgPad alg n), Frame () () (BitVector n))

  terminate dLast trim (ePad, meVec)
    | trim > 0
    , Rewrite ← fact₀
    , let c = fromEnum trim; bits = ((dLast `shiftR` c) .<<+ 1) `shiftL` c - 1
    = (ePad, (∨) bits <$> meVec)

    | otherwise
    = (ePad, meVec)

  addPaddingWith ∷
    MsgPad alg n →
    (Either (MsgBits alg n) (MsgPad alg n), Frame () () (BitVector n))
  addPaddingWith p@MsgPad{..}
    | remainingFrames > remainingSizeFrames
    , SHAFacts ← knownSHA alg
    = ( Right p { remainingFrames = remainingFrames - 1
                , terminated      = True
                }
      , Middle $ if terminated then 0 else 1 +>>. 0
      )

    | otherwise
    , SHAFacts ← knownSHA alg
    , Rewrite ← fact₁
    , Rewrite ← using @(PositiveResultCond0 (SizeBits alg) n)
    , let d = head @(ReqSizeFrames alg n - 1) msgSize
    = ( if remainingSizeFrames > 0
        then Right p { remainingFrames     = remainingFrames - 1
                     , remainingSizeFrames = remainingSizeFrames - 1
                     , msgSize             = msgSize <<+ 0
                     , terminated          = True
                     }
        else Left (MsgBits 0 0)
      , let dd = if terminated then d else riseMsb d in
        if | remainingSizeFrames == 0 → Idle
           | remainingSizeFrames == 1 → End () dd
           | otherwise                → Middle dd
      )

  createMsgPad ∷ MsgBits alg n → MsgPad alg n
  createMsgPad (MsgBits s r)
    | SHAFacts ← knownSHA alg
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
                | Rewrite ← fact₀
                , Rewrite ← fact₁
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
    | SHAFacts ← knownSHA alg
    , Rewrite ← fact₀
    , Rewrite ← fact₁
    , Rewrite ← using @(LeTrans 1 (2 * BlockSize alg) (2 ^ SizeBits alg `Div` n))
    = pack

  extend₀ ∷
    BitVector (CLog 2 ((2 ^ SizeBits alg) `Div` n)) →
    BitVector (n * ReqSizeFrames alg n)
  extend₀
    | SHAFacts ← knownSHA alg
    , Rewrite ← fact₀
    , Rewrite ← using
        @( LeTrans 1 (2 * BlockSize alg) ((2 ^ SizeBits alg) `Div` n)
         )
    , Rewrite ← using @(CLog2LECond0 (SizeBits alg) n)
    = extend @BitVector
        @(CLog 2 ((2 ^ SizeBits alg) `Div` n))
        @(n * ReqSizeFrames alg n - CLog 2 ((2 ^ SizeBits alg) `Div` n))

  extend₁ ∷
    BitVector (CLog 2 n) →
    BitVector (n * ReqSizeFrames alg n)
  extend₁
    | SHAFacts ← knownSHA alg
    , Rewrite ← using @(PositiveResultCond0 (SizeBits alg) n)
    , Rewrite ← using @(CLog2IsLessProduct n (ReqSizeFrames alg n))
    = extend @BitVector
        @(CLog 2 n)
        @(n * ReqSizeFrames alg n - CLog 2 n)

  fact₀ ∷ Rewrite (2 * BlockSize alg <= (2 ^ SizeBits alg) `Div` n)
  fact₀
    | SHAFacts ← knownSHA alg
    , Rewrite ← using @(ModBound (BlockSize alg) n)
    , Rewrite ← using @(DivisorIsLess (BlockSize alg) n)
    , Rewrite ← using
        @( DivisorMonotoneInverse
             (BlockSize alg)
             n
             (2 ^ SizeBits alg)
             (2 * BlockSize alg)
         )
    = Rewrite

  fact₁ ∷ Rewrite ((2 ^ SizeBits alg) `DDiv` n ~ (2 ^ SizeBits alg) `Div` n)
  fact₁
    | SHAFacts ← knownSHA alg
    , Rewrite ← using
        @(TimesMod
            (BlockSize alg)
            ((2 ^ SizeBits alg) `Div` BlockSize alg)
            n
         )
    , Rewrite ← using @(ModZero n)
    = Rewrite

riseMsb ∷ ∀ n. (KnownNat n, 1 ≤ n) ⇒ BitVector n → BitVector n
riseMsb = (pack high ++#) . checkedTruncateB @(n-1) @1
