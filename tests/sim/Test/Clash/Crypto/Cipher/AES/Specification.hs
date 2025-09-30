{-|
Module      : Test.Clash.Crypto.Cipher.AES.Specification
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Cipher.AES'.
-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedLists #-} -- Used to inturper a list as Byte String
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}

module Test.Clash.Crypto.Cipher.AES.Specification (tastyTests) where

import Clash.Crypto.Cipher.AES
import Clash.Prelude
import Clash.Signal.Channel
import Clash.Signal.DataStream
import Clash.Sized.Vector (unsafeFromList)

-- https://hackage.haskell.org/package/clash-prelude-hedgehog
import Hedgehog
import qualified Hedgehog.Gen as Gen

import Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog

import Data.Proxy (Proxy(..))
import Clash.Hedgehog.Sized.BitVector (genDefinedBitVector)
import Clash.Hedgehog.Sized.Vector
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import qualified Test.Clash.Crypto.Cipher.AES.Specification.Definitions as Def
import qualified Test.Clash.Crypto.Cipher.AES.Specification.Algorithm as Alg
-- Test AES128
import Test.Clash.Crypto.Cipher.AES.GoldenReference as Reference 
import Crypto.Cipher.Types
import Crypto.Error

import qualified Crypto.Random.Types as CRT

import Data.ByteString (ByteString) 
import Crypto.Cipher.AES 
import Crypto.Cipher.Types 
import Crypto.Random (getRandomBytes)
import Crypto.Error (throwCryptoError)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as C8

import qualified Clash.Crypto.Cipher.AES.Specification as Spec



tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.Cipher.AES.Specification"
  [ localOption (HedgehogTestLimit (Just 10)) $
      testGroup "Specification Sanity Checks against haskell crypton AES128"
        [ 
          testProperty "AES128" $
            property $ do
              key <- forAll $ genKeyFor @(Spec.AES128 ∷ Spec.AES)
              input <- forAll $ genInputBlock @(Spec.AES128 ∷ Spec.AES)
              testAESPure @Spec.AES128 key input,
        testProperty "AES-128, specific key" $
            property $ do
              testAESPure @Spec.AES128 in1AES128 key1AES128 
        ]
        ,
        testGroup "Specification Sanity Checks against haskell crypton AES" $
        [ testProperty ("AES-" <> algName) $
            property $ do
              key <- forAll $ genKeyFor @(Spec.AES192 ∷ Spec.AES)
              input <- forAll $ genInputBlock @(Spec.AES192 ∷ Spec.AES)
              aesPure key input
        | (aesPure, algName, proxyAlg) <-
            [ (testAESPure @Spec.AES192, "192", Proxy @Spec.AES192)
            ]
        ]
        ,
        testGroup "Specification Sanity Checks against haskell crypton AES256" $
        [ testProperty ("AES-" <> algName) $
            property $ do
              key <- forAll $ genKeyFor @(Spec.AES256 ∷ Spec.AES)
              input <- forAll $ genInputBlock @(Spec.AES256 ∷ Spec.AES)
              aesPure key input
        | (aesPure, algName) <-
            [ (testAESPure @Spec.AES256, "256")
            ]
        ]
  ]
genInputBlock ∷ ∀ (alg ∷ Spec.AES). Spec.KnownAES alg => Gen ByteString
genInputBlock 
    | AESFacts _ ← knownAES @alg =
    BS.pack <$> Gen.list (Range.singleton (snatToNum (SNat @(Spec.Nb alg * Spec.WordSize alg)))) Gen.enumBounded
genKeyFor :: ∀ (alg ∷ Spec.AES). Spec.KnownAES alg => Gen ByteString
genKeyFor   
  | AESFacts _ ← knownAES @alg = do
  BS.pack <$> Gen.list (Range.singleton (natToNum @( Spec.WordSize alg  * Spec.Nk alg ))) Gen.enumBounded

type TestLen = 8
testOplus ∷ (Monad m) => BitVector TestLen -> BitVector TestLen -> PropertyT m ()
testOplus a b = a ⊕ b === xor a b 




testAESPure ∷ ∀ (alg ∷ Spec.AES) m.
  (Monad m, KnownAES alg, CryptoAES alg) ⇒
  ByteString →
  -- ^ input data
    ByteString →
  -- ^ key data
  PropertyT m ()
testAESPure key input
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
    resultDigestAsBv = Spec.aesFunctional @alg inputAsInType keyAsInType

    resultDigestAsVBv8 ∷ Vec (Nb alg * WordSize alg) (BitVector 8)
    resultDigestAsVBv8 = concat resultDigestAsBv

    dut = toList $ unpack <$> resultDigestAsVBv8
    ref = BS.unpack $ Reference.encryptoECB alg key input
  -- inputAsInType === test_in1AES128
  -- resultDigestAsBv === test_out1AES128
  ref === dut


-- | Some example input for unit testing.
in1AES128 ∷ ByteString
in1AES128 = [0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d, 0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34]
key1AES128 ∷ ByteString
key1AES128 = [ 0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c ]
-- -- key1AES128 ∷ KeyType Spec.AES128
-- -- key1AES128 = (0x2b:> 0x7e:> 0x15:> 0x16:>Nil) :> (0x28:> 0xae:> 0xd2:> 0xa6:> Nil) :> (0xab:> 0xf7:> 0x15:> 0x88:> Nil) :> (0x09:> 0xcf:> 0x4f:> 0x3c:> Nil) :> Nil
-- key1AsBv8 ∷ [BitVector 8]
-- key1AsBv8 = pack <$> BS.unpack key1AES128

-- key1AsVBv8 ∷ Proxy Spec.AES -> Vec (Nk Spec.AES128 * WordSize Spec.AES128)  (BitVector 8)
-- key1AsVBv8 (Proxy ∷ Proxy alg Spec.AES128) = unsafeFromList @(Nk alg * WordSize alg) key1AsBv8

-- key1AsInType ∷  Proxy Spec.AES -> KeyType Spec.AES128
-- key1AsInType (Proxy ∷ Proxy alg Spec.AES128) = unconcatI (key1AsVBv8 alg)
-- w1AES128 ∷ Spec.WType Spec.AES128
-- w1AES128 =( (0x2b:>0x7e:>0x15:>0x16:>Nil)
--             :> (0x28:>0xae:>0xd2 :> 0xa6:>Nil)
--             :> (0xab:> 0:> :> :>Nil)
--             :> (:> :> :> :>Nil)
--             :>Nil
--             )
key1AES192 ∷ ByteString
key1AES192 = [ 0x8e, 0x73, 0xb0, 0xf7, 
               0xda, 0x0e, 0x64, 0x52,
               0xc8, 0x10, 0xf3, 0x2b,
               0x80, 0x90, 0x79, 0xe5,
               0x62, 0xf8, 0xea, 0xd2,
               0x52, 0x2c, 0x6b, 0x7b]
-- t = encryptoECB key1AES192 in1AES128
-- key1AES256 ∷ ByteString
-- key1AES256 = [0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe, 0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81, 0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7, 0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4]

-- attempt (Proxy ∷ alg Spec.AES128) = Alg.keyExpansion alg  key1AsInType


-- key1AES128 ∷ KeyType AES128
-- key1AES128 = (0x2b:> 0x7e:> 0x15:> 0x16:>Nil) :> (0x28:> 0xae:> 0xd2:> 0xa6:> Nil) :> (0xab:> 0xf7:> 0x15:> 0x88:> Nil) :> (0x09:> 0xcf:> 0x4f:> 0x3c:> Nil) :> Nil


-- try = keyExpansion (AES128 ∷  AES) key1AES128