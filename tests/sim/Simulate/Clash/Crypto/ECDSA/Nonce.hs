module Simulate.Clash.Crypto.ECDSA.Nonce (tastyTests) where

import Clash.Prelude

import Test.Tasty
import Test.Tasty.Hedgehog
import Hedgehog
import qualified Hedgehog.Range as Range
import qualified Hedgehog.Gen as Gen

import qualified Crypto.Hash as Spec
import qualified Crypto.PubKey.ECC.ECDSA as Spec
import qualified Crypto.PubKey.ECC.Types as Spec
import Clash.Signal.DataStream
import qualified Data.ByteString as BS
import qualified Data.List as List
import Clash.Signal.Channel
import Clash.Crypto.ECDSA.DeterministicNonce
import Clash.Crypto.MAC.HMAC
import Clash.Crypto.Hash.SHA
import Data.Maybe (catMaybes, listToMaybe, fromMaybe)
import Clash.Hedgehog.Sized.BitVector (genDefinedBitVector)
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import qualified Clash.Crypto.Calculator.Modulo as M
import Language.Haskell.Unicode (type (≤))
import Clash.Crypto.Calculator.ISA (SecP256ModPrime, SecP256OrdPrime)


-- | The prime used by the @SECP256@ curve of the FIDO protocol.

tastyTests ∷ TestTree
tastyTests = testGroup "Test.Clash.Crypto.ECDSA.Nonce" $
  [
    localOption (HedgehogShrinkLimit (Just 2))
    $ localOption (HedgehogTestLimit (Just 10))
    $ testProperty "Nonce generation" $ property $ do
      message <- forAll $ Gen.bytes (Range.linear 100 1000)
      pK      <- forAll
       $ Gen.integral (Range.linear 1 (natToNum @SecP256ModPrime - 1))
      let refDig = Spec.hash @_ @Spec.SHA256 message
          pKref  = Spec.PrivateKey (Spec.getCurveByName Spec.SEC_p256r1) pK
          ref = Spec.deterministicNonce Spec.SHA256 pKref refDig
              $ Just . fromInteger
          impl = runNonce (datastreamFromBS message) (pure $ fromInteger pK)
      ref === impl
    ,
    testProperty "Chunker (single element)" $ property $ do
      message ∷ BitVector 256 <- forAll genDefinedBitVector
      let res = runChunker MiddleChunk 1
               $ withClockResetEnable clockGen resetGen enableGen
               $ delayC $ cachedChannel @_ @System (fromList
               $ (message, Keep)
               : (message, Keep)
               : (message, Release)
               : List.repeat (message, Keep))
          vec ∷ [Frame (Index 65) () (BitVector 8)]
          vec = toList $ Middle <$> bitCoerce message
      res === vec
    ,
    testProperty "Chunker (multiple elements)" $ property $ do
      message ∷ [BitVector 256]
              <- forAll $ Gen.list (Range.linear 2 10) genDefinedBitVector
      let s     = List.unsnoc message
          (_,t) = fromMaybe (error "List is non-empty") s
          f e   = (e,Release) : List.replicate 32 (e, Keep)
          res   = runChunker MiddleChunk (List.length message)
                $ withClockResetEnable clockGen resetGen enableGen
                $ cachedChannel @_ @System
                $ fromList
                $ (undefined, Clear)
                : (undefined, Clear)
                : List.concatMap f message <> List.repeat (t, Keep)
          vec ∷ [Frame (Index 65) () (BitVector 8)]
          vec = List.concatMap
           (toList . (Middle <$>) . bitCoerce @_ @(Vec 32 (BitVector 8))) message
      res === vec
  ]

runChunker ∷ ChunkPosition → Int → Channel System (BitVector 256) →
 [Frame (Index 65) () (BitVector 8)]
runChunker typ len message
 = List.take (32 * len) $ filter (/= Idle)
 $ filter (/= NoData) $ sample @System
 $ fst $ chunkContent SHA256 message (pure typ)

runNonce ∷ DataStream System () (Index 8) (BitVector 8) →
 Signal System (BitVector 256) → M.Mod SecP256OrdPrime
runNonce message pk
 = fromMaybe (error "Should contain an element") $ listToMaybe $ catMaybes
 $ sample @System $ newsfeed $ deriveNonce SecP256OrdPrime SHA256 message pk

runHmac ∷ DataStream System (Index 65) () (BitVector 8) → BitVector 256
runHmac stream
 = fromMaybe (error "Should contain an element") $ listToMaybe $ catMaybes
 $ sample @System $ newsfeed $ hmac SHA256 stream

datastreamFromBS ∷ BS.ByteString → DataStream dom () (Index 8) (BitVector 8)
datastreamFromBS = datastreamFromBV . fmap bitCoerce . BS.unpack

datastreamFromBV ∷ [BitVector 8] → DataStream dom () (Index 8) (BitVector 8)
datastreamFromBV bvs
 = fromList $ Idle : Idle : (listFromBV () 0  bvs <> List.repeat Idle)

listFromBV ∷  a → b → [BitVector 8] → [Frame a b (BitVector 8)]
listFromBV start end bvs
 = case List.unsnoc bvs of
    Nothing          → []
    Just (ys, y)     → case List.uncons ys of
        Nothing      → [End end y]
        Just (z, zs) → [Start start z]
                    <> List.concatMap (\x → [Middle x]) zs
                    <> [End end y]
