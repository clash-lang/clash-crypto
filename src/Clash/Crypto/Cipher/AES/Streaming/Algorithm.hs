{-|
Module      : Clash.Crypto.Cipher.AES.Streaming.Algorithm
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Algorithm implementations of FIPS 197 using the enchance method.
-}

module Clash.Crypto.Cipher.AES.Streaming.Algorithm
  ( cipherStream
  , AESKeyExpansion(..)
  , invCipherStream
  , eqInvCipherStream
  , keyExpansionIECStream
  ) where

import Clash.Crypto.Cipher.AES.Specification.Types
import Clash.Crypto.Cipher.AES.Specification.Definitions
import Clash.Crypto.Cipher.AES.Specification as Spec

import Clash.Prelude
import Clash.Signal.Channel

data CipherMode (alg ∷ AES)
  = CipherStart
  | CipherRounds (Index 4) (Index (Nr alg + 1))
  | CipherLast (Index 3)
  | CipherFin
  | CipherEnd
  deriving (Generic, NFDataX, Show, Eq)

-- | Algorithm 1: @Cipher()@
--
-- /Section 5.1, streamlined version/
cipherStream ∷
  HiddenClockResetEnable dom ⇒
  ∀ (alg ∷ AES) → KnownAES alg ⇒
  Channel dom (AESBlock alg, KeySchedule alg) →
  -- ^ input + key
  Channel dom (AESBlock alg)
  -- ^ response
cipherStream alg | AESFacts ← knownAES alg = enhance put get compute
 where
  put ∷
    (AESBlock alg, KeySchedule alg) →
    ((AESBlock alg, Vec (Nr alg + 1) (AESRoundKey alg)), CipherMode alg)
  put (input, w)
    | AESFacts ← knownAES alg
    = ((input, unconcatI w), CipherStart)

  get ∷
    (AESBlock alg, KeySchedule alg) →
    ((AESBlock alg, Vec (Nr alg + 1) (AESRoundKey alg)), CipherMode alg) →
    AESBlock alg
  get _ ((output, _), _) = output

  compute ∷
    (AESBlock alg, KeySchedule alg) →
    ((AESBlock alg, Vec (Nr alg + 1) (AESRoundKey alg)), CipherMode alg) →
    CompMode
      ( (AESBlock alg, Vec (Nr alg + 1) (AESRoundKey alg))
      , CipherMode alg
      )
  compute _ ((state, w), mode0)
    | AESFacts ← knownAES alg
    = ( , mode0 /= CipherEnd)
    $ (\(s,m) → ((s, w), m))
    $ case mode0 of
        CipherEnd        → ( state, mode0 )
        CipherFin        → ( state, CipherEnd )
        CipherStart      → ( addRoundKey state $ head w
                           , CipherRounds 3 maxBound
                           )
        CipherRounds 3 1 → ( state, CipherLast 2 )
        CipherRounds 3 i → ( subBytes state, CipherRounds 2 i )
        CipherRounds 2 i → ( shiftRows state, CipherRounds 1 i )
        CipherRounds 1 i → ( mixColumns state, CipherRounds 0 i )
        CipherRounds 0 i → ( addRoundKey state $ w !! (maxBound - i + 1)
                           , CipherRounds 3 $ i - 1
                           )
        CipherLast 2     → ( subBytes state, CipherLast 1 )
        CipherLast 1     → ( shiftRows state, CipherLast 0 )
        CipherLast 0     → ( addRoundKey state $ last w, CipherFin )
        CipherRounds _ _ → ( state, CipherFin )
        CipherLast _     → ( state, CipherFin )

-- | The implementation of @KeyExpansion()@ slightly differs for each
-- AES variant, which is captured via this class.
class AESKeyExpansion (alg ∷ AES) where
  -- | Algorithm 2: @KeyExpansion()@
  --
  -- /Section 5.2, as depicted in Figure 6 & 7, streamlined version/
  keyExpansionStream ∷
    HiddenClockResetEnable dom ⇒
    ∀ x → (x ~ alg, KnownAES alg) ⇒
    Channel dom (AESKey alg) →
    -- ^ key
    Channel dom (KeySchedule alg)
    -- ^ response

data KeyMode (alg ∷ AES)
  = KeyStart
  | KeyProsXOR (Index 3) (Index (Nr alg + 1))
  | KeyProsLastW (Index 4) (Index (Nr alg + 1))
  | KeyFin
  | KeyEnd
  deriving (Generic, NFDataX, Show, Eq)

instance AESKeyExpansion AES128 where
  keyExpansionStream alg = enhance put get compute
   where
    put ∷
      ∀ alg. (KnownAES alg, alg ~ AES128) ⇒
      AESKey alg →
      ((AESKey alg, AESWord, KeySchedule alg), KeyMode alg)
    put key
      | AESFacts ← knownAES alg
      = ((key, last key, repeat (repeat 0) ++ key), KeyStart)

    get ∷
      ∀ alg. (KnownAES alg, alg ~ AES128) ⇒
      AESKey alg →
      ((AESKey alg, AESWord, KeySchedule alg), KeyMode alg)
      → KeySchedule alg
    get _ ((_, _, w), _) = w

    compute ∷
      ∀ alg. (KnownAES alg, alg ~ AES128) ⇒
      AESKey alg →
      ((AESKey alg, AESWord, KeySchedule alg), KeyMode alg) →
      CompMode ((AESKey alg, AESWord, KeySchedule alg), KeyMode alg)
    compute _ (s0@(state, lastState, w), mode0)
      | AESFacts ← knownAES alg
      = (, mode0 /= KeyEnd)
      $ case mode0 of
          KeyEnd           → ( s0, mode0 )
          KeyFin           → ( s0, KeyEnd )
          KeyStart         → ( s0, KeyProsLastW 3 maxBound )
          KeyProsLastW 3 i → ( (state, rotWord lastState, w), KeyProsLastW 2 i )
          KeyProsLastW 2 i → ( (state, subWord lastState, w), KeyProsLastW 1 i )
          KeyProsLastW 1 i → ( ( state
                               , xorWord lastState
                               $ roundConstants !! (maxBound - i)
                               , w
                               )
                             , KeyProsLastW 0 i
                             )
          KeyProsLastW 0 i → ( (postscanl xorWord lastState state, lastState, w)
                             , KeyProsXOR 0 i
                             )
          KeyProsXOR 0 0   → ( s0, KeyFin )
          KeyProsXOR 0 i   → ( (state, last state, shiftNewPart w state)
                             , KeyProsLastW 3 $ i - 1
                             )
          KeyProsLastW _ _ → ( s0, KeyFin )
          KeyProsXOR _ _   → ( s0, KeyFin )

    shiftNewPart ∷
      ∀ alg. (KnownAES alg, alg ~ AES128) ⇒
      KeySchedule alg → AESKey alg → KeySchedule alg
    shiftNewPart w = fst . shiftInAtN w

instance AESKeyExpansion AES192 where
  keyExpansionStream alg = enhance put get compute
   where
    put ∷
      ∀ alg. (KnownAES alg, alg ~ AES192) ⇒
      AESKey alg →
      ( ( AESKey alg
        , AESWord
        , Vec (Nk alg * Nr alg) AESWord
        )
      , KeyMode alg
      )
    put key
      | AESFacts ← knownAES alg
      = ((key, last key, repeat (repeat 0) ++ key), KeyStart)

    get ∷
      ∀ alg. (KnownAES alg, alg ~ AES192) ⇒
      AESKey alg →
      ( (AESKey alg, AESWord, Vec (Nk alg * Nr alg) AESWord)
      , KeyMode alg
      ) →
      KeySchedule alg
    get _ ((_, _, w), _) = takeI w

    compute ∷
      ∀ alg. (KnownAES alg, alg ~ AES192) ⇒
      AESKey alg →
      ( (AESKey alg, AESWord, Vec (Nk alg * Nr alg) AESWord)
      , KeyMode alg
      ) →
      CompMode
        ( (AESKey alg, AESWord, Vec (Nk alg * Nr alg) AESWord)
        , KeyMode alg
        )
    compute _ (s0@(state, lastState, w), mode0)
      | AESFacts ← knownAES alg
      = (, mode0 /= KeyEnd)
      $ case mode0 of
          KeyEnd           → ( s0, mode0 )
          KeyFin           → ( s0, KeyEnd )
          KeyStart         → ( s0, KeyProsLastW 3 maxBound )
          KeyProsLastW 3 i → ( (state, rotWord lastState, w), KeyProsLastW 2 i )
          KeyProsLastW 2 i → ( (state, subWord lastState, w), KeyProsLastW 1 i )
          KeyProsLastW 1 i → ( ( state
                               , xorWord lastState
                               $ roundConstants !! (maxBound - i)
                               , w
                               )
                             , KeyProsLastW 0 i
                             )
          KeyProsLastW 0 i → ( (postscanl xorWord lastState state, lastState, w)
                             , KeyProsXOR 0 i
                             )
          KeyProsXOR 0 1   → ( s0, KeyFin )
          KeyProsXOR 0 i   → ( (state, last state, shiftNewPart w state)
                             , KeyProsLastW 3 $ i - 1
                             )
          KeyProsLastW _ _ → ( s0, KeyFin )
          KeyProsXOR _ _   → ( s0, KeyFin )

    shiftNewPart ∷
      ∀ alg. (KnownAES alg, alg ~ AES192) ⇒
      Vec (Nk alg * Nr alg) AESWord →
      AESKey alg →
      Vec (Nk alg * Nr alg) AESWord
    shiftNewPart w = fst . shiftInAtN w

instance AESKeyExpansion AES256 where
  keyExpansionStream alg = enhance put get compute
   where
    put ∷
      ∀ alg. (KnownAES alg, alg ~ AES256) ⇒
      AESKey alg →
      ( (AESKey alg, AESWord, Vec (Nk alg * Nr alg) AESWord)
      , KeyMode alg
      )
    put key
      | AESFacts ← knownAES alg
      = ((key, last key, repeat (repeat 0) ++ key), KeyStart)

    get ∷
      ∀ alg. (KnownAES alg, alg ~ AES256) ⇒
      AESKey alg →
      ( (AESKey alg, AESWord, Vec (Nk alg * Nr alg) AESWord)
      , KeyMode alg
      ) →
      KeySchedule alg
    get _ ((_, _, w), _) = takeI w

    compute ∷
      ∀ alg. (KnownAES alg, alg ~ AES256) ⇒
      AESKey alg →
      ( (AESKey alg, AESWord, Vec (Nk alg * Nr alg) AESWord)
      , KeyMode alg
      ) →
      CompMode
        ( (AESKey alg, AESWord, Vec (Nk alg * Nr alg) AESWord)
        , KeyMode alg
        )
    compute _ (s0@(state, lastState, w), mode0)
      | AESFacts ← knownAES alg
      = (, mode0 /= KeyEnd)
      $ case mode0 of
          KeyEnd           → ( s0, mode0 )
          KeyFin           → ( s0, KeyEnd )
          KeyStart         → ( s0, KeyProsLastW 3 maxBound )
          KeyProsLastW 3 i → ( (state, rotWord lastState, w), KeyProsLastW 2 i)
          KeyProsLastW 2 i → ( (state, subWord lastState, w), KeyProsLastW 1 i)
          KeyProsLastW 1 i → ( ( state
                               , xorWord lastState
                               $ roundConstants !! (maxBound - i)
                               , w
                               )
                             , KeyProsLastW 0 i
                             )
          KeyProsLastW 0 i → ( (firstPart state lastState, lastState, w)
                             , KeyProsXOR 2 i
                             )
          KeyProsXOR 0 1  →  ( s0, KeyFin )
          KeyProsXOR 2 i   → ( (state, subWord $ last $ firstSplit state, w)
                             , KeyProsXOR 1 i
                             )
          KeyProsXOR 1 i   → ( (secondPart state lastState, lastState, w)
                             , KeyProsXOR 0 i
                             )
          KeyProsXOR 0 i   → ( (state, last state, shiftNewPart w state)
                             , KeyProsLastW 3 $ i - 1
                             )
          KeyProsLastW _ _ → ( s0, KeyFin )
          KeyProsXOR _ _   → ( s0, KeyFin )

    firstSplit = takeI @(Nk AES256 `Div` 2)
    secondSplit = dropI @(Nk AES256 `Div` 2)
    firstPart state lastState
      =  postscanl xorWord lastState (firstSplit state) ++ secondSplit state
    secondPart state lastState
      = firstSplit state ++ postscanl xorWord lastState (secondSplit state)

    shiftNewPart ∷
      ∀ alg. (KnownAES alg, alg ~ AES256) ⇒
      Vec (Nk alg * Nr alg) AESWord →
      AESKey alg →
      Vec (Nk alg * Nr alg) AESWord
    shiftNewPart ws = fst . shiftInAtN ws

-- | Algorithm 3: @InvCipher()@
--
-- /Section 5.3, streamlined version/
invCipherStream ∷
  HiddenClockResetEnable dom ⇒
  ∀ (alg ∷ AES) → KnownAES alg ⇒
  Channel dom (AESBlock alg, KeySchedule alg) →
  -- ^ input + key
  Channel dom (AESBlock alg)
  -- ^ response
invCipherStream alg | AESFacts ← knownAES alg  = enhance put get compute
 where
  put ∷
    (AESBlock alg, KeySchedule alg) →
    ((AESBlock alg, Vec (Nr alg + 1) (AESRoundKey alg)), CipherMode alg)
  put (input, w)
    | AESFacts ← knownAES alg
    = ((input, reverse $ unconcatI w), CipherStart)

  get ∷
    (AESBlock alg, KeySchedule alg) →
    ((AESBlock alg, Vec (Nr alg + 1) (AESRoundKey alg)), CipherMode alg) →
    AESBlock alg
  get _ ((output, _), _) = output

  compute ∷
    (AESBlock alg, KeySchedule alg) →
    ((AESBlock alg, Vec (Nr alg + 1) (AESRoundKey alg)), CipherMode alg) →
    CompMode
      ( (AESBlock alg, Vec (Nr alg + 1) (AESRoundKey alg))
      , CipherMode alg
      )
  compute _ ((state, w), mode0)
    | AESFacts ← knownAES alg
    = ( , mode0 /= CipherEnd)
    $ (\(s,m) → ((s, w), m))
    $ case mode0 of
        CipherEnd        → ( state, mode0 )
        CipherFin        → ( state, CipherEnd )
        CipherStart      → ( invAddRoundKey state $ head w
                           , CipherRounds 3 maxBound
                           )
        CipherRounds 3 1 → ( state, CipherLast 2 )
        CipherRounds 3 i → ( invShiftRows state, CipherRounds 2 i )
        CipherRounds 2 i → ( invSubBytes state, CipherRounds 1 i )
        CipherRounds 1 i → ( invAddRoundKey state $ w !! (maxBound - i + 1)
                           , CipherRounds 0 i
                           )
        CipherRounds 0 i → ( invMixColumns state, CipherRounds 3 $ i - 1 )
        CipherLast 2     → ( invShiftRows state, CipherLast 1 )
        CipherLast 1     → ( invSubBytes state,  CipherLast 0 )
        CipherLast 0     → ( invAddRoundKey state $ last w, CipherFin )
        CipherRounds _ _ → ( state, CipherFin )
        CipherLast   _   → ( state, CipherFin )

-- | Algorithm 4: @EqInvCipher()@
--
-- /Section 5.3.5, streamlined version/
eqInvCipherStream ∷
  HiddenClockResetEnable dom ⇒
  ∀ (alg ∷ AES) → KnownAES alg ⇒
  Channel dom (AESBlock alg, KeySchedule alg) →
  -- ^ input + key
  Channel dom (AESBlock alg)
  -- ^ response
eqInvCipherStream alg | AESFacts ← knownAES alg = enhance put get compute
 where
  put ∷
    (AESBlock alg, KeySchedule alg) →
    ((AESBlock alg, Vec (Nr alg + 1) (AESRoundKey alg)), CipherMode alg)
  put (input, w)
    | AESFacts ← knownAES alg
    = ((input, reverse $ unconcatI w), CipherStart)

  get ∷
    (AESBlock alg, KeySchedule alg) →
    ((AESBlock alg, Vec (Nr alg + 1) (AESRoundKey alg)), CipherMode alg) →
    AESBlock alg
  get _ ((output, _), _) = output

  compute ∷
    (AESBlock alg, KeySchedule alg) →
    ((AESBlock alg, Vec (Nr alg + 1) (AESRoundKey alg)), CipherMode alg) →
    CompMode
      ( (AESBlock alg, Vec (Nr alg + 1) (AESRoundKey alg))
      , CipherMode alg
      )
  compute _ ((state, w), mode0)
    | AESFacts ← knownAES alg
    = ( , mode0 /= CipherEnd)
    $ (\(s,m) → ((s, w), m))
    $ case mode0 of
        CipherEnd        → ( state, mode0 )
        CipherFin        → ( state, CipherEnd )
        CipherStart      → ( invAddRoundKey state $ head w
                           , CipherRounds 3 maxBound
                           )
        CipherRounds 3 1 → ( state, CipherLast 2 )
        CipherRounds 3 i → ( invSubBytes state, CipherRounds 2 i )
        CipherRounds 2 i → ( invShiftRows state, CipherRounds 1 i )
        CipherRounds 1 i → ( invMixColumns state, CipherRounds 0 i )
        CipherRounds 0 i → ( invAddRoundKey state $ w !! (maxBound - i + 1)
                           , CipherRounds 3 $ i - 1
                           )
        CipherLast 2     → ( invSubBytes state, CipherLast 1 )
        CipherLast 1     → ( invShiftRows state, CipherLast 0 )
        CipherLast 0     → ( invAddRoundKey state $ last w, CipherFin )
        CipherRounds _ _ → ( state, CipherFin )
        CipherLast _     → ( state, CipherFin )

-- | Algorithm 5: @KeyExpansionEIC()@
--
-- /Section 5.3.5, streamlined version/
keyExpansionIECStream ∷
  (HiddenClockResetEnable dom, AESKeyExpansion alg) ⇒
  ∀ x → (x ~ alg, KnownAES alg) ⇒
  Channel dom (AESKey alg) →
  -- ^ key
  Channel dom (KeySchedule alg)
  -- ^ response
keyExpansionIECStream alg
  | AESFacts ← knownAES alg
  = enhance put get compute . keyExpansionStream alg
 where
  put ∷
    KeySchedule alg →
    ( ( Vec 1 (AESRoundKey alg)
      , Vec (Nr alg - 1) (AESRoundKey alg)
      , Vec 1 (AESRoundKey alg)
      )
    , KeyMode alg
    )
  put w
    | AESFacts ← knownAES alg
    = ( ( head (unconcatI w) :> Nil
        , init $ tail $ unconcatI w
        , last (unconcatI w) :> Nil
        )
      , KeyStart
      )

  get ∷
    KnownAES alg ⇒
    KeySchedule alg →
    ( ( Vec 1 (AESRoundKey alg)
      , Vec (Nr alg - 1) (AESRoundKey alg)
      , Vec 1 (AESRoundKey alg)
      )
    , KeyMode alg
    ) →
    KeySchedule alg
  get _ ((start, middle, end), _)
    | AESFacts ← knownAES alg
    = concat $ start ++ middle ++ end

  compute ∷
    KnownAES alg ⇒
    KeySchedule alg →
    ( ( Vec 1 (AESRoundKey alg)
      , Vec (Nr alg - 1) (AESRoundKey alg)
      , Vec 1 (AESRoundKey alg)
      )
    , KeyMode alg
    ) →
    CompMode
      ( ( Vec 1 (AESRoundKey alg)
        , Vec (Nr alg - 1) (AESRoundKey alg)
        , Vec 1 (AESRoundKey alg)
        )
      , KeyMode alg
      )
  compute _ (s0@(start, middle, end), mode0)
    | AESFacts ← knownAES alg
    = (, mode0 /= KeyEnd) $ case mode0 of
    KeyEnd            → (s0, mode0 )
    KeyFin            → (s0, KeyEnd)
    KeyStart          → ((start, map invMixColumns middle, end), KeyFin)
    KeyProsLastW _ _  → (s0, KeyFin)
    KeyProsXOR   _ _  → (s0, KeyFin)
