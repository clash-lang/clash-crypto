{-|
Module      : Clash.Crypto.Cipher.AES.Specification.Algorithm
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Algorithmic reference implementation of FIPS 197 using a purely
functional description.
-}

{-# LANGUAGE Safe #-}
{-# LANGUAGE MagicHash #-}

module Clash.Crypto.Cipher.AES.Specification.Algorithm
  ( AESFunctions(..)
  ) where

import Clash.Prelude.Safe

import Clash.Crypto.Cipher.AES.Specification.Types
import Clash.Crypto.Cipher.AES.Specification.Definitions

-- | Purely functional implementation of the Algorithms 1 to 5 from FIPS 197.
class AESFunctions (alg ∷ AES) where
  -- | Algorithm 1: @Cipher()@
  --
  -- /Section 5.1/
  cipher ∷ ∀ x → x ~ alg ⇒ AESBlock alg → KeySchedule alg → AESBlock alg

  -- | Algorithm 2: @KeyExpansion()@
  --
  -- /Section 5.2/
  keyExpansion ∷ ∀ x → x ~ alg ⇒ AESKey alg → KeySchedule alg

  -- | Algorithm 3: @InvCipher()@
  --
  -- /Section 5.3/
  invCipher ∷ ∀ x → x ~ alg ⇒ AESBlock alg → KeySchedule alg → AESBlock alg

  -- | Algorithm 4: @EqInvCipher()@
  --
  -- /Section 5.3.5/
  eqInvCipher ∷ ∀ x → x ~ alg ⇒ AESBlock alg → KeySchedule alg → AESBlock alg

  -- | Algorithm 5: @KeyExpansionEIC()@
  --
  -- /Section 5.3.5/
  keyExpansionIEC ∷ ∀ x → x ~ alg ⇒ AESKey alg → KeySchedule alg

instance AESFunctions AES128 where
  keyExpansion _ key = concat $ scanl middelCalculation key roundConstants
   where
    middelCalculation ws i = postscanl xorWord partWord ws
     where
      partWord = xorWord (subWord $ rotWord $ last ws) i

  cipher alg = cipher# alg
  invCipher alg = invCipher# alg
  eqInvCipher alg = eqInvCipher# alg
  keyExpansionIEC alg = keyExpansionIEC# alg

instance AESFunctions AES192 where
  keyExpansion _ key =
    takeI $ concat $ scanl middelCalculation key roundConstants
   where
    middelCalculation ws i = postscanl xorWord partWord ws
     where
      partWord = xorWord (subWord $ rotWord $ last ws) i

  cipher alg = cipher# alg
  invCipher alg = invCipher# alg
  eqInvCipher alg = eqInvCipher# alg
  keyExpansionIEC alg = keyExpansionIEC# alg

instance AESFunctions AES256 where
  keyExpansion _ key =
    takeI $ concat $ scanl middelCalculation key roundConstants
   where
    middelCalculation ws i = firstPart ++ secondPart
     where
      (ws0, ws1) = splitAtI @(Nk AES256 `Div` 2) ws

      firstPart  = postscanl xorWord partWord ws0
      secondPart = postscanl xorWord (subWord $ last firstPart) ws1

      partWord = xorWord (subWord $ rotWord $ last ws) i

  cipher alg = cipher# alg
  invCipher alg = invCipher# alg
  eqInvCipher alg = eqInvCipher# alg
  keyExpansionIEC alg = keyExpansionIEC# alg

-- | Shareable parts of Algorithm 1.
cipher# ∷
  ∀ x → x ~ alg ⇒
  (KnownNat (Nr alg), 1 <= Nr alg) ⇒
  AESBlock alg → KeySchedule alg → AESBlock alg
cipher# alg input (unconcatI → ws)
  = addRoundKey (shiftRows $ subBytes rounds)
  $ last (tail ws ∷ Vec ((Nr alg - 1) + 1) (AESBlock alg))
 where
  rounds = foldl mutation (addRoundKey input $ head ws)
    (leToPlus @1 @(Nr alg) $ init $ tail ws ∷ Vec (Nr alg - 1) (AESBlock alg))
   where
    -- Algorithm 1 codeline 5-8 as a function
    mutation ∷ AESState alg → AESRoundKey alg → AESState alg
    mutation = addRoundKey . mixColumns . shiftRows . subBytes

-- | Shareable parts of Algorithm 3.
invCipher# ∷
  ∀ x → x ~ alg ⇒
  (KnownNat (Nr alg), 1 <= Nr alg) ⇒
  AESBlock alg → KeySchedule alg → AESBlock alg
invCipher# alg input (reverse . unconcatI → ws)
  = invAddRoundKey (invSubBytes $ invShiftRows rounds)
  $ last (tail ws ∷ Vec ((Nr alg - 1) + 1) (AESBlock alg))
 where
  rounds = foldl mutation (invAddRoundKey input $ head ws)
    (leToPlus @1 @(Nr alg) $ init $ tail ws ∷ Vec (Nr alg - 1) (AESBlock alg))
   where
    -- Algorithm 3 codeline 5-8 as a function
    mutation ∷ AESState alg → AESRoundKey alg → AESState alg
    mutation state =
      invMixColumns . invAddRoundKey (invSubBytes $ invShiftRows state)

-- | Shareable parts of Algorithm 4.
eqInvCipher# ∷
  ∀ x → x ~ alg ⇒
  (KnownNat (Nr alg), 1 <= Nr alg) ⇒
  AESBlock alg → KeySchedule alg → AESBlock alg
eqInvCipher# alg input (reverse . unconcatI → ws)
  = invAddRoundKey (invShiftRows $ invSubBytes rounds)
  $ last (tail ws ∷ Vec ((Nr alg - 1) + 1) (AESBlock alg))
 where
  rounds = foldl mutation (invAddRoundKey input $ head ws)
    (leToPlus @1 @(Nr alg) $ init $ tail ws ∷ Vec (Nr alg - 1) (AESBlock alg))
   where
    -- Algorithm 4 codeline 5-8 as a function
    mutation ∷ AESState alg → AESRoundKey alg → AESState alg
    mutation = invAddRoundKey . invMixColumns . invShiftRows . invSubBytes

-- | Shareable parts of Algorithm 5.
keyExpansionIEC# ∷
  ∀ x → x ~ alg ⇒
  (AESFunctions alg, KnownNat (Nr alg), 1 <= Nr alg) ⇒
  AESKey alg → KeySchedule alg
keyExpansionIEC# alg key
  = leToPlus @1 @(Nr alg)
  $ concat
  $ head ws :> (map invMixColumns intl :< last (tail ws))
 where
  ws ∷ Vec (Nr alg + 1) (AESBlock alg)
  ws = unconcatI $ keyExpansion alg key

  intl ∷ Vec (Nr alg - 1) (AESBlock alg)
  intl = init $ tail ws
