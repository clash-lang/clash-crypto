{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
module Test.Clash.Crypto.Hash.SHA
  ( tastyTests
  ) where

import Clash.Prelude


import qualified Clash.Sized.Vector as Vec
import qualified Crypto.Hash.SHA256 as CryptoHash
import qualified Data.ByteString as BS

--import qualified Data.List as List
--import Text.Printf

import Data.Constraint
import Data.Function
import Data.Proxy
import Hedgehog
import Hedgehog.Gen as Gen
import Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog
import Unsafe.Coerce (unsafeCoerce)

import Clash.Crypto.Hash.SHA

hashPure ∷ ∀ (alg ∷ SHA) (m ∷ Type → Type).
  (KnownSHA alg, Monad m) ⇒
  BS.ByteString →
  PropertyT m BS.ByteString
hashPure input | SHAFacts alg ← knownSHA @alg = do
  Just (SomeNat (_ ∷ Proxy n)) ← return $ someNatVal $ toInteger $ BS.length input

  -- TODO: figure out why all these lemma's need to be re-stated
  Dict ← return $ lemma₀ @(n * 8)
  Dict ← return $ lemma₀ @(8 * n)
  Dict ← return $ lemma₁ @(n * 8)
  Dict ← return $ lemma₁ @(8 * n)
  Dict ← return $ lemma₂ @(n * 8)
  Dict ← return $ lemma₃ @(8 * n) @(BlockSize alg)

  let
    inputAsBv8 ∷ [BitVector 8]
    inputAsBv8 = pack <$> BS.unpack input

    inputAsVBv8 ∷ Vec n (BitVector 8)
    inputAsVBv8 = Vec.unsafeFromList @n inputAsBv8

    inputAsBv ∷ Message (n * 8)
    inputAsBv = concatBitVector# inputAsVBv8

    paddedMessage = padMessage @alg @(n * 8) inputAsBv

    ℓ ∷ Integer
    ℓ = case paddedMessage of { (_ ∷ Message ℓ) → natToInteger @ℓ }

  assert $ ℓ `mod` natToInteger @(WordSize alg) == 0
  assert $ ℓ `mod` natToInteger @(BlockSize alg) == 0

  Just (SomeNat (_ ∷ Proxy ℓ)) ← return $ someNatVal ℓ

  Dict ← return $ fact₀  @(n * 8) @ℓ
  Dict ← return $ lemma₄ @(n * 8) @ℓ
  Dict ← return $ fact₁  @(n * 8) @ℓ
  Dict ← return $ lemma₅ @ℓ @(WordSize alg) @16
  Dict ← return $ lemma₆ @ℓ @(WordSize alg)
  Dict ← return $ lemma₆ @(MessageDigestSize alg) @8
  Dict ← return $ lemma₆ @ℓ @8
  Dict ← return $ lemma₇ @ℓ @(WordSize alg) @16

  let
    pmAsVWords ∷ Vec (Div ℓ (WordSize alg)) (BitVector (WordSize alg))
    pmAsVWords = unconcatBitVector# paddedMessage

    pmAsVBlocks ∷ Vec (Div ℓ (16 * WordSize alg)) (MessageBlock alg)
    pmAsVBlocks = Vec.unconcat (SNat @16) pmAsVWords

    k ∷ Integer
    k = case pmAsVBlocks of
          (_ ∷ Vec k (MessageBlock alg)) → natToInteger @k

  assert $ k * 16 * natToInteger @(WordSize alg) == ℓ

  Just (SomeNat (_ ∷ Proxy k)) ← return $ someNatVal k

  let
    resultHB ∷ HashBlock alg
    resultHB = Vec.foldl computeB (_H⁰ alg) pmAsVBlocks

    resultDigestAsBv ∷ BitVector (MessageDigestSize alg)
    resultDigestAsBv = truncateB @_ @(MessageDigestSize alg)
      @(MessageBlockWords alg * WordSize alg - MessageDigestSize alg)
      $ concatBitVector# resultHB

    resultDigestAsVBv8 ∷ Vec (Div (MessageDigestSize alg) 8) (BitVector 8)
    resultDigestAsVBv8 = unconcatBitVector# resultDigestAsBv

  {-
  footnote $ unlines $
    [ "rounds: " <> show (Vec.length (computeCycles @alg))
    ]

  footnote $ unlines $
    [ "digest:\n"
    , List.concatMap (\(i,v) → printf "%3d" (toInteger v) <> " (" <> show i <> ")\n")
    $ List.zip [0 :: Int,1..]
    $ Vec.toList
    $ resultDigestAsVBv8
    , ""
    ]

  footnote $ unlines $
    [ "final hash (" <> show (natToInteger @(BitSize (HashBlock alg))) <> " bits):\n"
    , List.concatMap (\(i,v) → printf "%08x" (toInteger v) <> " (H_" <> show i <> ")\n")
    $ List.zip [0 :: Int,1..]
    $ Vec.toList
    $ resultHB
    , ""
    ]

  footnote $ unlines $
    [ "initial hash:\n"
    , List.concatMap (\(i,v) → printf "%x" (toInteger v) <> " (H_" <> show i <> ")\n")
    $ List.zip [0 :: Int,1..]
    $ Vec.toList
    $ _H⁰ alg
    , ""
    ]

  footnote $ unlines $
    [ "blocks (" <> show k <> "):"
    ] <> fmap (("\n - " <>) . List.concatMap (\(i,v) → show v <> " (M_" <> show i <> ")\n   ") . List.zip [0 :: Int,1..] . Vec.toList) (Vec.toList pmAsVBlocks) <>
    [ ""
    ]

  footnote $ unlines
    [ "padded message (" <> show (ℓ `div` 8) <> "):\n"
    , show paddedMessage
    , ""
    ]

  footnote $ unlines
    [ "input message (" <> show (natToInteger @n) <> "):\n"
    , show inputAsBv
    , ""
    ]
  -}

  return $ BS.pack $ Vec.toList $ unpack <$> resultDigestAsVBv8
 where
  computeB ∷  HashBlock alg → MessageBlock alg → HashBlock alg
  computeB hb mb
    | SHAFacts{} ← knownSHA @alg
    = let x = snd $ Vec.foldl (&) (mb, hb) (computeCycles @alg)
       in zipWith (+) hb x

  lemma₀ ∷ ∀ (ℓ ∷ Nat). Dict
    ( 1 ≤
        RequiredBlocks alg ℓ * BlockSize alg
          - Mod ℓ (BlockSize alg)
    )
  lemma₀ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  lemma₁ ∷ ∀ (ℓ ∷ Nat). Dict
    ( Mod ℓ (BlockSize alg) ≤
        RequiredBlocks alg ℓ * BlockSize alg
    )
  lemma₁ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  lemma₂ ∷ ∀ (ℓ ∷ Nat). Dict
    ( SizeBits alg ≤
        RequiredBlocks alg ℓ * BlockSize alg
          - Mod ℓ (BlockSize alg)
          - 1
    )
  lemma₂ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  lemma₃ ∷ ∀ (a ∷ Nat) (b ∷ Nat). Dict (Mod a b ≤ b)
  lemma₃ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  fact₀ ∷ ∀ (ℓ ∷ Nat) (ℓ' ∷ Nat).
    Dict (ℓ' ~ ℓ + 1 + PaddingZeros alg ℓ + SizeBits alg)
  fact₀ = unsafeCoerce (Dict ∷ Dict (0 ~ 0))

  fact₁ ∷ ∀ (ℓ ∷ Nat) (ℓ' ∷ Nat).
    ℓ' ~ ℓ + 1 + PaddingZeros alg ℓ + SizeBits alg ⇒
    Dict (Mod ℓ' 8 ~ 0)
  fact₁ = unsafeCoerce (Dict ∷ Dict (0 ~ 0))

  lemma₄ ∷ ∀ (ℓ ∷ Nat) (ℓ' ∷ Nat).
    ℓ' ~ ℓ + 1 + PaddingZeros alg ℓ + SizeBits alg ⇒
    Dict (Mod ℓ' (16 * WordSize alg) ~ 0)
  lemma₄ = unsafeCoerce (Dict ∷ Dict (0 ~ 0))

  lemma₅ ∷ ∀ (a ∷ Nat) (b ∷ Nat) (c ∷ Nat).
    Mod a (c * b) ~ 0 ⇒
    Dict (Mod a b ~ 0)
  lemma₅ = unsafeCoerce (Dict ∷ Dict (0 ~ 0))

  lemma₆ ∷ ∀ (a ∷ Nat) (b ∷ Nat).
    Mod a b ~ 0 ⇒
    Dict (Div a b * b ~ a)
  lemma₆ = unsafeCoerce (Dict ∷ Dict (0 ~ 0))

  lemma₇ ∷ ∀ (a ∷ Nat) (b ∷ Nat) (c ∷ Nat).
    Mod a (c * b) ~ 0 ⇒
    Dict (Div a b ~ Div a (c * b) * c)
  lemma₇ = unsafeCoerce (Dict ∷ Dict (0 ~ 0))

tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.Hash.SHA"
  [ testPropertyNamed "SHA-256" "b" $ myProp
  ]

myProp ∷ Property
myProp = property $ do
  bs ← forAll $ Gen.bytes $ linear 0 1000
  let ref = BS.unpack $ CryptoHash.hash bs
  dut ← BS.unpack <$> hashPure @SHA256 bs

  ref === dut
