{-|
Module      : Test.Clash.Crypto.ECDSA.InverseModulo
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Cipher.AES'.
-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}

module Test.Clash.Crypto.Cipher.AES (tastyTests) where

import Clash.Sized.Vector (unsafeFromList)
import Clash.Crypto.Cipher.AES
import Clash.Prelude
-- import Data.Maybe (catMaybes, listToMaybe, fromMaybe)

-- https://hackage.haskell.org/package/clash-prelude-hedgehog
import Hedgehog
import qualified Hedgehog.Gen as Gen

import Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog
-- import qualified Data.List as List
-- import qualified Hedgehog.Range as Range
import Data.Proxy (Proxy(..))
-- Generate BitVecor and Vector
import Clash.Hedgehog.Sized.BitVector (genDefinedBitVector)
import Clash.Hedgehog.Sized.Vector
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import qualified Test.Clash.Crypto.Cipher.AES.Specifications.Definitions as Def
-- Test AES128
import Crypto.Cipher.AES as Reference (AES128, AES192, AES256) 
import Crypto.Cipher.Types
import Crypto.Error

import qualified Crypto.Random.Types as CRT

import Data.ByteArray ( ByteArray, convert )
import Data.ByteString as BA (ByteString) 
import Crypto.Cipher.AES 
import Crypto.Cipher.Types 
import Crypto.Random (getRandomBytes)
import Crypto.Error (throwCryptoError)
import Data.ByteArray (convert)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as C8
import Data.ByteString.Lazy (toStrict, fromStrict)
import Data.Word (Word8)

import qualified Clash.Crypto.Cipher.AES.Specification as Spec
tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.Cipher.AES"
  [Def.tastyTests,
  tastyTestsAESSpecification] 


tastyTestsAESSpecification ∷ TestTree
tastyTestsAESSpecification = testGroup "Clash.Crypto.Cipher.AES.Specification"
  [ localOption (HedgehogTestLimit (Just 10)) $
      testGroup "Specification Sanity Checks (unit tests)"
        [ testProperty ("AES-" <> algName) $
            property $ do
              key <- forAll (genKeyFor (Proxy @Spec.AES128))
              input <- forAll (genInputBlock)
              aesPure key input
        | (aesPure, algName) <-
            [ (testAESPure @Spec.AES128, "128")
            -- , (testAESPure @Spec.AES192, "192", Proxy @Spec.AES192, forAll (genKeyFor . Proxy Spec.AES192))
            -- , (testAESPure @Spec.AES256, "256", Proxy @Spec.AES256, forAll (genKeyFor . Proxy Spec.AES256))
            ]
        ]

  ]
genInputBlock :: Gen ByteString
genInputBlock = BS.pack <$> Gen.list (Range.singleton (snatToNum (SNat @(Spec.Nb Spec.AES128 * Spec.WordSize Spec.AES128)))) Gen.enumBounded
genKeyFor :: ∀ alg. KnownAES alg => Proxy alg -> Gen ByteString
genKeyFor alg = do
  BS.pack <$> Gen.list (Range.singleton (snatToNum (SNat @(Spec.Nk Spec.AES128 * Spec.WordSize Spec.AES128)))) Gen.enumBounded

type TestLen = 8
testOplus ∷ (Monad m) => BitVector TestLen -> BitVector TestLen -> PropertyT m ()
testOplus a b = a ⊕ b === xor a b 


-- | Not required, but most general implementation
-- A function to pad the data to be a multiple of the block size (AES block size is 16 bytes)
padData :: BA.ByteString -> BA.ByteString
padData bs = BS.take 16 (bs `BS.append` BS.replicate 16 0)  -- Simple padding to 16 bytes
-- Encrypt function using AES in ECB mode
encryptECB :: BA.ByteString -> BA.ByteString -> BA.ByteString
encryptECB key plainText = case cipherInit key of
    CryptoFailed _ -> error "Cipher initialization failed"
    CryptoPassed (cipher :: AES128) -> ecbEncrypt cipher (padData plainText)
-- Decrypt function using AES in ECB mode
decryptECB ∷ BA.ByteString -> BA.ByteString -> BA.ByteString
decryptECB key cipherText = case cipherInit key of
    CryptoFailed _ -> error "Cipher initialization failed"
    CryptoPassed (cipher ∷ AES128)-> ecbDecrypt cipher (padData cipherText)

-- Typeclass over all AES block cipher algorithms
class CryptoAES (alg ∷ Spec.AES) where
  encryptoECB :: Proxy alg -> BA.ByteString -> BA.ByteString -> BA.ByteString
  decryptoECB :: Proxy alg -> BA.ByteString -> BA.ByteString -> BA.ByteString
instance CryptoAES Spec.AES128      where 
  encryptoECB ∷ Proxy alg → BA.ByteString -> BA.ByteString -> BA.ByteString
  encryptoECB _ key plainText = case cipherInit key of
    CryptoFailed _ -> error "Cipher initialization failed"
    CryptoPassed (cipher :: AES128) -> ecbEncrypt cipher (padData plainText)
  decryptoECB ∷ Proxy alg → BA.ByteString -> BA.ByteString -> BA.ByteString
  decryptoECB _ key cipherText = case cipherInit key of
    CryptoFailed _ -> error "Cipher initialization failed"
    CryptoPassed (cipher ∷ AES128)-> ecbDecrypt cipher (padData cipherText)
instance CryptoAES Spec.AES192    where
  encryptoECB ∷ Proxy alg → BA.ByteString -> BA.ByteString -> BA.ByteString
  encryptoECB _ key plainText = case cipherInit key of
    CryptoFailed _ -> error "Cipher initialization failed"
    CryptoPassed (cipher :: AES192) -> ecbEncrypt cipher (padData plainText)
  decryptoECB ∷ Proxy alg → BA.ByteString -> BA.ByteString -> BA.ByteString
  decryptoECB _ key cipherText = case cipherInit key of
    CryptoFailed _ -> error "Cipher initialization failed"
    CryptoPassed (cipher ∷ AES192)-> ecbDecrypt cipher (padData cipherText)
instance CryptoAES Spec.AES256    where 
  encryptoECB ∷ Proxy alg → BA.ByteString -> BA.ByteString -> BA.ByteString
  encryptoECB _ key plainText = case cipherInit key of
    CryptoFailed _ -> error "Cipher initialization failed"
    CryptoPassed (cipher :: AES256) -> ecbEncrypt cipher (padData plainText)
  decryptoECB ∷ Proxy alg → BA.ByteString -> BA.ByteString -> BA.ByteString
  decryptoECB _ key cipherText = case cipherInit key of
    CryptoFailed _ -> error "Cipher initialization failed"
    CryptoPassed (cipher ∷ AES256)-> ecbDecrypt cipher (padData cipherText)

testAESPure ∷ ∀ (alg ∷ Spec.AES) m.
  (Monad m, KnownAES alg, CryptoAES alg) ⇒
  ByteString →
  -- ^ key data
    ByteString →
  -- ^ input data
  PropertyT m ()
testAESPure input key
  | AESFacts alg ← knownAES @alg
  -- , Rewrite ← using @(CancelMultiple (MessageDigestSize alg) 8)
  = do

  -- Just (SomeNat (_ ∷ Proxy n)) ←
  --   return $ someNatVal $ toInteger $ BS.length input

  let
    inputAsBv8 ∷ [BitVector 8]
    inputAsBv8 = pack <$> BS.unpack input

    inputAsVBv8 ∷ Vec (Nb alg * WordSize alg)  (BitVector 8)
    inputAsVBv8 = unsafeFromList @(Nb alg * WordSize alg) inputAsBv8

    inputAsInType ∷ InType alg
    inputAsInType = unconcatI inputAsVBv8

    keyAsBv8 ∷ [BitVector 8]
    keyAsBv8 = pack <$> BS.unpack key

    keyAsVBv8 ∷ Vec (Nk alg * WordSize alg)  (BitVector 8)
    keyAsVBv8 = unsafeFromList @(Nk alg * WordSize alg) keyAsBv8

    keyAsInType ∷ KeyType alg
    keyAsInType = unconcatI keyAsVBv8

    resultDigestAsBv ∷ OutType alg
    resultDigestAsBv = Spec.aesFunctional alg inputAsInType keyAsInType

    resultDigestAsVBv8 ∷ Vec (Nb alg * WordSize alg) (BitVector 8)
    resultDigestAsVBv8 = concat resultDigestAsBv

    dut = toList $ unpack <$> resultDigestAsVBv8
    ref = BS.unpack $ encryptoECB alg key input

  ref === dut


