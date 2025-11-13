{-# LANGUAGE AllowAmbiguousTypes #-}

{-|
Module      : Test.Clash.Crypto.ECDSA.Modulo
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.ECDSA.Modulo'.
-}

module Test.Clash.Crypto.ECDSA.Modulo where

import Clash.Crypto.ECDSA.Modulo (computeModuloSigned, ModSize, unMod)
import Clash.Prelude
import Clash.Signal.Channel
import Data.Maybe (fromMaybe)
import Data.Monoid (First(..))
import Data.Proxy
import Data.Type.Equality (type (:~:)(Refl))
import GHC.Stack (HasCallStack)
import GHC.TypeLits.Compare ((%<=?), type (:<=?) (..))

import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import Hedgehog ((===), property, forAll, MonadTest)
import Test.Tasty
import Test.Tasty.Hedgehog (HedgehogTestLimit(HedgehogTestLimit), testProperty)

import qualified Data.List as List
import qualified Hedgehog.Range as Range
import Clash.Hedgehog.Sized.Signed (genSigned)
import Clash.Crypto.ECDSA.Utils (signedToUnsigned)

tastyTests :: HasCallStack => TestTree
tastyTests = testGroup "Clash.Crypto.ECDSA.Modulo"
  [ localOption (HedgehogTestLimit (Just 100))
  $  testGroup "Modulo"
      [ testProperty "Equality between sequential modulo and combinatorial modulo"
        $ property $ do
          n       <- forAll $ genSigned $ Range.linear (-50_000) (50_000 :: Signed 65)
          modulus <- forAll $ genUnsigned $ Range.linear 5 500
          testMod n modulus
      ]
  ]

testOutput ::
  forall (modT :: Nat).
  (KnownNat modT, 1 <= modT, ModSize modT <= 64) =>
  Signed 65 ->
  -- ^ n
  Unsigned 64 ->
  -- ^ Modulus
  Unsigned 64
testOutput n modulus
  = fromMaybe (error "The returned list was empty")
  $ getFirst
  $ foldMap First
  $ sampleN @System (fromEnum (signedToUnsigned n `div` modulus) + 100)
  $ withClockResetEnable clockGen resetGen enableGen
  $ newsfeed
  $ fmap (resize . bitCoerce . unMod)
  $ computeModuloSigned @modT
  $ channel
  $ fmap (n, )
  $ fromList
  $ Keep : Keep : Release : List.repeat Keep

testMod :: (MonadFail m, MonadTest m) => Signed 65 -> Unsigned 64 -> m ()
testMod n modulus = do
  Just (SomeNat (_ :: Proxy modT)) <- return $ someNatVal $ toInteger modulus
  case (Proxy :: Proxy 1) %<=? (Proxy :: Proxy modT) of
    LE Refl -> case (Proxy :: Proxy (ModSize modT)) %<=? (Proxy :: Proxy 64) of
      LE Refl -> testOutput @modT n modulus === fromIntegral (n `mod` (bitCoerce $ extend modulus))
      NLE _ _ -> error "ModSize modulus should be less than or equal to 64"
    NLE _ _ -> error "The given modulus should be greater than 1"
