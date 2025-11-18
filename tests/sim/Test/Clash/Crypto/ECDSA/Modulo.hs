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

import Clash.Crypto.ECDSA.Modulo (computeModuloSigned, computeModuloUnsigned,
 ModSize, unMod, computeModuloPrime, Mod)
import Clash.Prelude hiding (Mod)
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
import Clash.Crypto.ECDSA.Utils (signedToUnsigned, unsignedToSigned)
import Clash.Crypto.ECDSA.Curves (Curve (SECP256), CurveModulo)

type Size = 512

tastyTests :: HasCallStack => TestTree
tastyTests = testGroup "Clash.Crypto.ECDSA.Modulo"
  [ localOption (HedgehogTestLimit (Just 10000))
  $  testGroup "Modulo"
      [ testProperty "Equality between sequential modulo and combinatorial modulo - Signed"
        $ property $ do
          n       <- forAll $ genSigned $ Range.linear minBound (maxBound :: Signed (Size + 1))
          modulus <- forAll $ genUnsigned $ Range.linear 1 (resize $ (maxBound :: Unsigned (Size `Div` 2)))
          testModSigned n modulus
      , testProperty "Equality between sequential modulo and combinatorial modulo - Unsigned"
        $ property $ do
          n       <- forAll $ genUnsigned $ Range.linear minBound (maxBound :: Unsigned Size)
          modulus <- forAll $ genUnsigned $ Range.linear 5 (resize $ (maxBound :: Unsigned (Size `Div` 2)))
          testModUnsigned n modulus
      , testProperty "Equality between sequential modulo and combinatorial modulo - Curve-optimized"
        $ property $ do
          n <- forAll $ genUnsigned $ Range.linear 0 (natToNum @(CurveModulo SECP256 ^ 2))
          testModOptimized @(CurveModulo SECP256) n
      ]
  ]
testModOptimized :: forall modT m. (MonadFail m, MonadTest m, KnownNat modT, 1 <= modT) => Unsigned (ModSize modT * 2) -> m ()
testModOptimized n =
 testOutput @modT n computeModuloPrime === (bitCoerce . resize $ (n `mod` (natToNum @modT) :: Unsigned (ModSize modT * 2)))

testModSigned :: (MonadFail m, MonadTest m) => Signed (Size + 1) -> Unsigned Size -> m ()
testModSigned n modulus = do
  Just (SomeNat (_ :: Proxy modT)) <- return $ someNatVal $ toInteger modulus
  case (Proxy :: Proxy 1) %<=? (Proxy :: Proxy modT) of
    LE Refl -> case (Proxy :: Proxy (ModSize modT)) %<=? (Proxy :: Proxy Size) of
      LE Refl -> testOutput @modT n computeModuloSigned
                  ===
                 (resize $ signedToUnsigned ((resize n `mod` (unsignedToSigned modulus))))
      NLE _ _ -> error $ "ModSize modulus should be less than or equal to " <> show (natToNum @Size :: Integer)
    NLE _ _ -> error "The given modulus should be greater than 1"

testModUnsigned :: (MonadFail m, MonadTest m) => Unsigned Size -> Unsigned Size -> m ()
testModUnsigned n modulus = do
  Just (SomeNat (_ :: Proxy modT)) <- return $ someNatVal $ toInteger modulus
  case (Proxy :: Proxy 1) %<=? (Proxy :: Proxy modT) of
    LE Refl -> case (Proxy :: Proxy (ModSize modT)) %<=? (Proxy :: Proxy Size) of
      LE Refl -> testOutput @modT n computeModuloUnsigned === bitCoerce (resize (n `mod` (bitCoerce $ extend modulus) :: Unsigned Size))
      NLE _ _ -> error $ "ModSize modulus should be less than or equal to " <> show (natToNum @Size :: Integer)
    NLE _ _ -> error "The given modulus should be greater than 1"

testOutput :: forall modT a. (KnownNat modT, 1 <= modT) =>
 a -> (HiddenClockResetEnable System => Channel System a -> Channel System (Mod modT)) -> Unsigned (ModSize modT)
testOutput val operation
  = fromMaybe (error "The returned list was empty")
  $ getFirst
  $ foldMap First
  $ sample @System
  $ withClockResetEnable clockGen resetGen enableGen
  $ newsfeed
  $ fmap (resize . bitCoerce . unMod)
  $ operation
  $ channel
  $ fmap (val, )
  $ fromList
  $ Keep : Keep : Release : List.repeat Keep
