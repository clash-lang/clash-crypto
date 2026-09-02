{-# LANGUAGE MagicHash #-}
module Simulate.Clash.Crypto.Hash.SHA3 (testyTests) where

import Clash.Prelude
import Clash.Sized.Vector hiding (fromList)

import Data.Maybe (catMaybes)
import Data.Data (Proxy)
import Data.Word (Word8)
import qualified GHC.List as List
import qualified Data.ByteString as BS
import Text.Printf (printf)
import GHC.TypeNats.Proof

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Internal.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog

import Data.Constraint.Nat.Extra
import Clash.Signal.DataStream
import Clash.Signal.Channel
import Clash.Crypto.Hash.SHA3.Types
import Clash.Crypto.Hash.SHA3.Properties
    ( KnownSHA3(..)
    , SHA3Facts(SHA3Facts)
    )
import Clash.Crypto.Hash.SHA3.Functions.Algorithm (sha3)
import qualified Clash.Crypto.Hash.SHA3.Streaming.Streaming as STR

import Test.Clash.Crypto.Hash.SHA3 (cryptoHash, CryptoHash (..))
import Simulate.Clash.Crypto.Hash.SHA (input1, input2, input3, input4)
import Clash.Crypto.Hash.SHA3.Properties (SuffixConstants(SuffixLen))

testyTests ∷ TestTree
testyTests = testGroup "Clash.Crypto.Hash.SHA3"
  [ localOption (HedgehogTestLimit $ Just 4)
      $ testGroup "Sanity Checks (unit tests)"
          [ testProperty ("SHA3-" <> algName)
              $ property
              $ forAll (Gen.element inputs)
                  >>= hashPure
          | let inputs = [input1, input2, input3, input4] ∷ [BS.ByteString]
          , (hashPure, algName) ←
              [ (testHashPure SHA3_224,        "224")
              , (testHashPure SHA3_256,        "256")
              , (testHashPure SHA3_384,        "384")
              , (testHashPure SHA3_512,        "512")
              , (testHashPure (SHAKE128 2400), "128/2400")
              , (testHashPure (SHAKE256 2400), "256/2400")
              ]
          ]
  , testGroup "Streaming"
      [ testGroup "Contiguous Input"
        [ testProperty ("SHA3-" <> algName)
          $ property
          $ do
              bs ← forAll (Gen.bytes (Range.linear 100 1000))
              hashStream $ List.map (, 0) (pack <$> BS.unpack bs)
        | (hashStream, algName) ←
            [ (testHashNCStream SHA3_224,        "224")
            , (testHashNCStream SHA3_256,        "256")
            , (testHashNCStream SHA3_384,        "384")
            , (testHashNCStream SHA3_512,        "512")
            , (testHashNCStream (SHAKE128 2400), "128/2400")
            , (testHashNCStream (SHAKE256 8000), "256/8000")
            ]
        ]
      , testGroup "Small Input"
        [ testProperty ("SHA3-" <> algName)
          $ property
          $ do
              bs ← forAll (Gen.bytes (Range.linear 1 10))
              hashStream $ List.map (, 0) (pack <$> BS.unpack bs)
        | (hashStream, algName) ←
            [ (testHashNCStream SHA3_224,        "224")
            , (testHashNCStream SHA3_256,        "256")
            , (testHashNCStream SHA3_384,        "384")
            , (testHashNCStream SHA3_512,        "512")
            , (testHashNCStream (SHAKE128 2400), "128/2400")
            , (testHashNCStream (SHAKE256 8000), "256/8000")
            ]
        ]
      , testGroup "Non Contiguous Input"
        [ testProperty ("SHA3-" <> algName)
          $ property
          $ do
              bs ← forAll (Gen.bytes (Range.linear 80 100))
              xs ← forAll
                $ Gen.list (Range.singleton $ BS.length bs)
                $ Gen.integral @_ @Int
                $ Range.linear 50 100
              hashStream $ List.zip (pack <$> BS.unpack bs) xs
        | (hashStream, algName) ←
            [ (testHashNCStream SHA3_224,        "224")
            , (testHashNCStream SHA3_256,        "256")
            , (testHashNCStream SHA3_384,        "384")
            , (testHashNCStream SHA3_512,        "512")
            , (testHashNCStream (SHAKE128 2400), "128/2400")
            , (testHashNCStream (SHAKE256 8000), "256/8000")
            ]
        ]
      ]
  ]

-- Printing util
pr :: BS.ByteString -> [Char]
pr = List.concatMap (printf "%02x " ∷ Word8 → String) . BS.unpack

-- | Purely functional hash computation according to the
-- specification.
testHashPure ∷
  ∀ (m ∷ Type → Type). Monad m ⇒
  ∀ (alg ∷ SHA3) → (KnownSHA3 alg, SuffixLen alg < 8, CryptoHash alg) ⇒
  BS.ByteString →
  PropertyT m ()
testHashPure alg bs
  | SHA3Facts ← knownSHA3 alg
  , Rewrite ← using @(CancelMultiple (MessageDigestSize alg) 8)
  = do
  Just (SomeNat (_ ∷ Proxy n)) ←
    return $ someNatVal $ toInteger $ BS.length bs
  let
    inputAsBv8 ∷ [BitVector 8]
    inputAsBv8 = pack <$> BS.unpack bs

    inputAsVBv8 ∷ Vec n (BitVector 8)
    inputAsVBv8 = unsafeFromList @n inputAsBv8

    inputAsBv ∷ BitVector (n * 8)
    inputAsBv = concatBitVector# inputAsVBv8

    resultDigestAsBv ∷ BitVector (MessageDigestSize alg)
    resultDigestAsBv
      | Rewrite ← using @(TimesMod n 8 8)
      = sha3 alg inputAsBv

    resultDigestAsVBv8 ∷ Vec (MessageDigestSize alg `Div` 8) (BitVector 8)
    resultDigestAsVBv8 = unconcatBitVector# resultDigestAsBv

    dut = BS.pack . toList $ unpack <$> resultDigestAsVBv8
    ref = cryptoHash alg bs
  pr ref === pr dut

-- | Tests on a non-contiguous data input stream.
testHashNCStream ∷
  ∀ (m ∷ Type → Type). Monad m ⇒
  ∀ (alg ∷ SHA3) → (KnownSHA3 alg, SuffixLen alg < 8, CryptoHash alg) ⇒
  [(BitVector 8, Int)] →
  -- ^ input data, where each byte in the first component is followed
  -- by the number of idle cycles stated in the second component. The
  -- list must be non-empty.
  PropertyT m ()
testHashNCStream alg xs
  | SHA3Facts ← knownSHA3 alg
  , Rewrite ← using @(CancelMultiple (MessageDigestSize alg) 8)
  = let
      addStretch f (x, j) = f x : List.replicate j Stretch
      toFrame [] = []
      toFrame [f] = [addStretch (End 0) f]
      toFrame (f1:f2:fs) = addStretch (Start ()) f1 : aux f2 fs
      aux (f,_) []  = [[End 0 f]]
      aux f (f':fs) = addStretch Middle f : aux f' fs

      contentBytesL = List.length xs
      msg = List.concat (toFrame xs)
      n = List.length msg
      rn = natToNum @(AlgRate alg)
      dn = natToNum @(MessageDigestSize alg)
      addedBits = (rn - (contentBytesL * 8 + natToNum @(SuffixLen alg) + 2)) `mod` rn
      addedFrames = addedBits `div` 8
      requiredSamples = n + addedFrames
      requiredSamplesSponge =
        24 * (dn `div` rn) + (if dn `mod` rn == 0 then 0 else 24) + 1

      input ∷ DataStream System () (Index 8) (BitVector 8)
      input = fromList i
       where
        i = [Idle, Idle, Idle] <> msg
         <> List.replicate (addedFrames + requiredSamplesSponge) Idle <> i
      totalInputSamples = (3 + requiredSamples + 1 + requiredSamplesSponge) * 2

      output ∷ [Maybe (Vec (MessageDigestSize alg `Div` 8) (BitVector 8))]
      output = sampleN totalInputSamples $ newsfeed $ STR.sha3 alg input

      resultDigestAsVBv8 ∷ Vec (MessageDigestSize alg `Div` 8) (BitVector 8)
      resultDigestAsVBv8 = case List.take 2 $ catMaybes output of
        []                    → error "No response received."
        [_]                   → error "Missing second response."
        a : b : _ | a /= b    → error "Repeated hashs differ."
                  | otherwise → a

      ref = cryptoHash alg $ BS.pack $ fmap (unpack . fst) xs
      dut = BS.pack $ toList $ unpack <$> resultDigestAsVBv8
    in
      pr ref === pr dut
