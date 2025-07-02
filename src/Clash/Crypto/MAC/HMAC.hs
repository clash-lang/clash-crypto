{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.MAC.HMAC
  ( IPad
  , OPad
  , hmac
  ) where

import Clash.Prelude

import Data.Constraint (Dict(..))
import Data.Functor ((<&>))
import Data.Maybe (isJust, isNothing)
import Language.Haskell.Unicode (type (≤))
import Unsafe.Coerce (unsafeCoerce)

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
  = InnerHash
  -- ^ Calculation of the inner hash, where the input
  -- @(K XOR ipad, text))@ is forwarded to the hashing component.
  | OuterKey
  -- ^ Calculation of the outer hash, where first the stored
  -- @K XOR opad@ is passed to the hashing component.
  | OuterDigest
  -- ^ Calculation of the outer hash, where the previously computed
  -- @H(K XOR ipad, text)@ is passed to the hashing component.
  deriving (Generic, NFDataX)

-- | A streaming implementation of HMAC according to
-- [RFC 2104](https://www.rfc-editor.org/info/rfc2104).
--
-- The component reads from two input streams: the first one being a
-- Boolean toggle, indicating whether the key is being passed, and the
-- second one being a stream of bytes. The Boolean input needs to be
-- high until the key has been passed, and then must be lowered until
-- all the remaining bytes have been received. After having received
-- the key, which can be of variable size, the circuit will ignore any
-- further inputs until 'BlockSize' @alg@ many bits have been
-- received. The message is considered to start after the first
-- 'BlockSize' @alg@ bits have been received. The end of the message
-- is signaled via raising the "key indicator" input again. No
-- response will be produced before terminating the message. Any
-- further input is ignored until the circuit responds.
--
-- Note: [RFC 2104](https://www.rfc-editor.org/info/rfc2104) requires
-- the initial byte block containing the key to be exactly 'BlockSize'
-- @alg@ many bits long. If the actual key is shorter than that, then
-- it must be padded with zeros. If it is longer instead, then the key
-- should be passed through the hashing function to shorten it to at
-- most 'BlockSize' @alg@ many bits.
--
-- This implementation currently does __not__ support keys that
-- require more than 'BlockSize' @alg@ many bits.
hmac ∷
  ∀ (alg ∷ SHA) dom.
  ( KnownSHA alg, HiddenClockResetEnable dom
  , 8 ≤ BlockSize alg, Mod (BlockSize alg) 8 ~ 0
  ) ⇒
  Signal dom Bool →
  -- ^ the "is key" indicator
  Signal dom (Maybe (BitVector 8)) →
  -- ^ key + message input stream, where the key comes first and
  -- message afterwards
  Signal dom (Maybe (BitVector (MessageDigestSize alg)))
  -- ^ response
hmac isKey dataIn
  | SHAFacts _ ← knownSHA @alg
  = let
      -- marks the period after which the first input has been received
      operational = regMaybe False $ (True <$) <$> dataIn

      -- if isKey goes from low to high, then the end of the msg has
      -- been reached
      endOfMsg = operational .&&. isRising False isKey

      -- mark the key frame via counting the received number of bytes
      withinKeyFrame = remainingKeyFrameBytes .>. 0
       where
        remainingKeyFrameBytes
          = register (maxBound ∷ Index ((BlockSize alg `Div` 8) + 1))
          $ apWhen (isJust <$> dataIn) (satPred SatBound)
          $ mux endOfMsg (pure maxBound) remainingKeyFrameBytes

      -- zero everything behind the actual key
      padded = apWhen (withinKeyFrame .&&. (not <$> isKey)) (0x00 <$) dataIn

      -- xors the key block with the provided pad
      xorpad pad = apWhen withinKeyFrame (xor pad <$>) padded

      -- the output of the hashing function
      digest = sha @alg @_ @8 $ terminate $ do
        -- immediately forward key & msg during the 'InnerHash' stage
        innerHashSel ← xorpad $ natToNum @IPad
        -- buffer @key XOR opad@ until we need it during the 'OuterKey' stage
        outerKeySel ← bufM (SNat @(BlockSize alg `Div` 8)) (neval "bufM INIT")
          $ mux atOuterKeyStage (pure $ Just $ neval "bufM FWD")
          $ guardA withinKeyFrame $ xorpad $ natToNum @OPad
        -- use the buffered digest at the 'OuterDigest' stage
        outerDigestSel ← digestBuf

        curStage ← stage
        return $ case curStage of
          InnerHash   → innerHashSel
          OuterKey    → outerKeySel
          OuterDigest → outerDigestSel
       where
        -- memorize the digest that is responed at the end of the
        -- 'InnerDigest' stage for serializing it out during the
        -- 'OuterDigest' stage
        digestBuf
          = serializeEn (atOuterDigestStage .&&. (isNothing <$> digest))
          $ guardA atInnerHashStage digest

        endOfPayload ∷ Signal dom Bool
        endOfPayload
          = mux atInnerHashStage endOfMsg
          $ isFalling False (isJust <$> digestBuf)

        terminate x = mux endOfPayload
          (pure (Just (0, Just maxBound)))
          (fmap (, Nothing) <$> x)

      -- stage selector for passing data from the right components at
      -- the desired times
      stage = moore (~~>) fst
        (InnerHash, neval "stage Moore INIT" ∷ Index (BlockSize alg `Div` 8))
        (isJust <$> digest)
       where
        (s, n) ~~> newDigest = case s of
          InnerHash   | newDigest → (OuterKey   , maxBound                )
          OuterKey    | n > 0     → (OuterKey   , n - 1                   )
                      | otherwise → (OuterDigest, neval "stage Moore INIT")
          OuterDigest | newDigest → (InnerHash  , neval "stage Moore INIT")
          _                       → (s          , n                       )

      -- some convenience shortcuts
      atInnerHashStage   = stage <&> \case { InnerHash   → True; _ → False }
      atOuterKeyStage    = stage <&> \case { OuterKey    → True; _ → False }
      atOuterDigestStage = stage <&> \case { OuterDigest → True; _ → False }
    in
      guardA atOuterDigestStage digest
 where
  -- a value that should never be evaluated
  neval = error . ("Clash.Crypto.MAC.HMAC.hmac: " <>)

-- | Updates a value inside an 'Applicative' context if an only if a
-- Boolean condition within the same context is true.
apWhen ∷ Applicative f ⇒ f Bool → (a → a) → f a → f a
apWhen cond upd x = mux cond (upd <$> x) x

-- | Only pass the alternative, if the first input stream is high.
guardA ∷ (Alternative m, Applicative f) ⇒ f Bool → f (m b) → f (m b)
guardA b x = mux b x $ pure empty

-- | Stores the last received 'Just'-input until the first Boolean
-- input stream gets raised. The stored value then is streamed out in
-- network order in chunks of the specified size as long whenever the
-- first input is high. Further values on the second input stream are
-- ignored until all the stored input has been serialized via the
-- output.
serializeEn ∷
  ∀ a n dom.
  ( HiddenClockResetEnable dom
  , BitPack a, KnownNat (BitSize a), KnownNat n
  , 1 ≤ n, 1 ≤ BitSize a, BitSize a `Mod` n ~ 0
  ) ⇒
  Signal dom Bool →
  -- ^ serialize and output the stored value, if and only if high
  Signal dom (Maybe a) →
  -- ^ input stream
  Signal dom (Maybe (BitVector n))
  -- ^ output stream
serializeEn
  | Dict ← lemma₀ @(BitSize a) @n
  , Dict ← lemma₁ @(BitSize a) @n
  = leToPlusKN @1 @(BitSize a `Div` n)
  $ curry $ mealyB (~~>)
      ( repeat neval ∷ Vec (BitSize a `Div` n) (BitVector n)
      , 0 ∷ Index ((BitSize a `Div` n) + 1)
      )
 where
  (buf, n) ~~> (release, mInput)
    | n > 0 && release
    = ((buf <<+ neval, satPred SatBound n), Just $ head buf)

    | n == 0 && release
    , Just input ← mInput
    , let vec = bitCoerce input
    = ((vec <<+ neval, satPred SatBound maxBound), Just $ head vec)

    | n == 0
    , Just input ← mInput
    = ((bitCoerce input, maxBound), Nothing)

    | otherwise
    = ((buf, n), Nothing)

  -- a value that should never be evaluated
  neval = error "Clash.Crypto.MAC.HMAC.serializeEn: Mealy"

  lemma₀ ∷
    ∀ (x ∷ Nat) (y ∷ Nat).
    (1 ≤ x, 1 ≤ y, Mod x y ~ 0) ⇒
    Dict (1 ≤ Div x y)
  lemma₀ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  lemma₁ ∷
    ∀ (x ∷ Nat) (y ∷ Nat).
    (1 ≤ y, x `Mod` y ~ 0) ⇒
    Dict (x `Div` y * y ~ x)
  lemma₁ = unsafeCoerce (Dict ∷ Dict (0 ~ 0))

-- | A simple queuing FIFO that pushes data through on every arrival
-- of a 'Just'-input. Hence, with every new input the output at the
-- end of the queue gets released.
bufM ∷
  ∀ dom a n.
  (HiddenClockResetEnable dom, NFDataX a) ⇒
  SNat n →
  -- ^ size of FIFO / number of stored elements
  a →
  -- ^ initial content of the FIFO
  Signal dom (Maybe a) →
  -- ^ input stream
  Signal dom (Maybe a)
  -- ^ output stream
bufM n@SNat ival = mealy (~~>) $ replicate n ival
 where
  (~~>) ∷ Vec n a → Maybe a → (Vec n a, Maybe a)
  buf ~~> inp = case buf of
    Nil      → (Nil, inp)
    Cons x _ → (maybe buf (buf <<+) inp, inp >> pure x)
