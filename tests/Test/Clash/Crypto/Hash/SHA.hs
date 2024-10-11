{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
module Test.Clash.Crypto.Hash.SHA where

import Clash.Prelude


import qualified Clash.Sized.Vector as Vec
import qualified Crypto.Hash.SHA256 as CryptoHash
import qualified Data.ByteString as BS

import qualified Data.List as List
import Text.Printf

import Control.Monad
import Data.Constraint
import Data.Function
import Data.Maybe
import Data.Proxy
import Hedgehog
import Hedgehog.Gen as Gen
import Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog
import Unsafe.Coerce (unsafeCoerce)

import Clash.Crypto.Hash.SHA

tastyTests ∷ TestTree
tastyTests = localOption (HedgehogTestLimit (Just 1))
  $ testGroup "Clash.Crypto.Hash.SHA"
    [ testProperty "SHA-256 (i1, pure)" $ testHashPure @SHA256 testInput1
    , testProperty "SHA-256 (i2, pure)" $ testHashPure @SHA256 testInput2
    , testProperty "SHA-256 (i3, pure)" $ testHashPure @SHA256 testInput3
    , testProperty "SHA-256 (i4, pure)" $ testHashPure @SHA256 testInput4
    , testProperty "SHA-256 (i1, stream)" $ testHashStream @SHA256 testInput1
    , testProperty "SHA-256 (i1, stream)" $ testHashStream @SHA256 testInput2
    , testProperty "SHA-256 (i1, stream)" $ testHashStream @SHA256 testInput3
    , testProperty "SHA-256 (i1, stream)" $ testHashStream @SHA256 testInput4
    ]

-- bs ← forAll $ Gen.bytes $ linear 0 1000

testInput1 ∷ BS.ByteString
testInput1 = BS.pack [ 255, 23, 42, 38, 29, 48, 244, 65, 2, 99 ]

testInput2 ∷ BS.ByteString
testInput2 = BS.pack
  [ 255, 23, 42, 38, 29, 48, 244, 65, 2, 99, 41, 31, 231, 199, 25, 32
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  , 255, 23, 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 231
  ]

testInput3 ∷ BS.ByteString
testInput3 = BS.pack
  [ 255, 23, 42, 38, 29, 48, 244, 65, 2, 99, 41, 31, 231, 199, 25, 32
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  , 255, 23, 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 231
  , 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 255, 23, 231
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  ]

testInput4 ∷ BS.ByteString
testInput4 = BS.pack
  [ 255, 23, 42, 38, 29, 48, 244, 65, 2, 99, 41, 31, 231, 199, 25, 32
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  , 255, 23, 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 231
  , 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 255, 23, 231
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  , 255, 23, 42, 38, 29, 48, 244, 65, 2, 99, 41, 31, 231, 199, 25, 32
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  , 255, 23, 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 231
  , 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 255, 23, 231
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  ]

testHashStream ∷
  ∀ (alg ∷ SHA).
  ( KnownSHA alg, 1 <= Div (BlockSize alg) 8, 8 <= BlockSize alg
  , Div (BlockSize alg) 8 <= ScheduleCount alg
  , (Div (MessageDigestSize alg) 8 * 8) ~ MessageDigestSize alg
  , Mod (BlockSize alg) 8 ~ 0
  ) ⇒
  BS.ByteString →
  Property
testHashStream bs | SHAFacts{} ← knownSHA @alg = property $ do
  let
    inputAsBv8 ∷ [BitVector 8]
    inputAsBv8 = pack <$> BS.unpack bs

    n = List.length inputAsBv8

    inputPlusCtrl ∷ [Maybe (BitVector 8, Maybe (Index 9))]
    inputPlusCtrl
      = [ Nothing, Nothing, Nothing ]
     <> ( Just . (, Nothing) <$> inputAsBv8 )
     <> [ Just (0, Just maxBound) ]
     <> List.replicate 256 Nothing

    inputAsSignal ∷ Signal System (Maybe (BitVector 8, Maybe (Index 9)))
    inputAsSignal = fromList inputPlusCtrl

    samples :: Int
    samples = 64 * (n `div` 64 + if n `mod` 64 > 0 then 3 else 2) + 4

    (output, debug, padMsg) = List.unzip3 $ sampleN samples
      $ bundle $ sha @alg inputAsSignal

    resultDigestAsVBv8 ∷ Vec (Div (MessageDigestSize alg) 8) (BitVector 8)
    resultDigestAsVBv8 = unconcatBitVector# $ List.head $ catMaybes output

    dut = Vec.toList $ unpack <$> resultDigestAsVBv8

  let
    ref = BS.unpack $ CryptoHash.hash bs

  footnote
    $ (List.concatMap (printf "|%02x" . toInteger) $ toList resultDigestAsVBv8)

  footnote $ unlines $ fmap prLine $ List.zip4 output debug padMsg $ sampleN samples inputAsSignal

--  fail ""
  ref === dut
 where
  prLine ( result
         , ( collector
           , releaseCount
           , keepStable
           , msgBlock
           , proceed
           , endOfMessage
           , hashBlock
           )
         , padMsg
         , inp
         )
    = unlines
        [ "----------------------------"
        , "I " <> showX inp
        , "P " <> showX padMsg
        , "C " <> (List.concatMap
                     (\(i,x) ->
                         printf (if i `mod` 21 == 20 then "|%02x\n  " else "|%02x")
                         $ toInteger x
                     ) $ List.zip [0 :: Int,1..] $ toList collector)
        , "R " <> showX releaseCount
        , "K " <> showX keepStable
        , "M " <> (List.concatMap (printf "|%08x" . toInteger) $ toList msgBlock)
        , "P " <> showX proceed
        , "E " <> showX endOfMessage
        , "H " <> (List.concatMap (printf "|%08x" . toInteger) $ toList hashBlock)
        , "> " <> showX result
        , "----------------------------"
        ]

testHashPure ∷
  ∀ (alg ∷ SHA).
  KnownSHA alg ⇒
  BS.ByteString →
  Property
testHashPure bs = property $ do
  let ref = BS.unpack $ CryptoHash.hash bs
  dut ← BS.unpack <$> hashPure @alg bs

  ref === dut
--  fail ""


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

  resultHB <- foldM computeB (_H⁰ alg) $ Vec.toList pmAsVBlocks

  let
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
  computeB ∷  HashBlock alg → MessageBlock alg → PropertyT m (HashBlock alg)
  computeB hb mb
    | SHAFacts{} ← knownSHA @alg
    = do
      footnote
        $ "I "<> (List.concatMap (printf "|%08x" . toInteger) $ toList $ hb)
      x <- foldM (\h f -> do
                     footnote
                       $ "C " <> (List.concatMap (printf "|%08x" . toInteger) $ toList $ f h)
                     return $ f h
                 ) hb $ Vec.toList (($ mb) <$> computeCycles @alg)

      footnote
        $ "R "<> (List.concatMap (printf "|%08x" . toInteger) $ toList $ zipWith (+) hb x)
      footnote
        $ "M "<> (List.concatMap (printf "|%08x" . toInteger) $ toList mb)
      return $ zipWith (+) hb x

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