{-|
Module      : Simulate.Clash.Crypto.Calculator.Karatsuba
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Simulation tests for 'Clash.Crypto.Calculator.Karatsuba'.
-}

module Simulate.Clash.Crypto.Calculator.Karatsuba where

import Clash.Prelude hiding (Mod)
import Clash.Hedgehog.Sized.Index (genIndex)

import Clash.Signal.Channel
import Hedgehog.Gen hiding (resize, maybe)
import Data.Maybe (fromMaybe)
import Data.Monoid (First(..))
import Language.Haskell.Unicode (type (≤))
import Data.Type.Equality (type (:~:)(Refl))
import GHC.TypeLits.Compare ((%<=?), type (:<=?) (..))

import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog
import Data.Proxy

import qualified Data.List as List
import qualified Hedgehog.Range as Range
import Clash.Crypto.Calculator.Modulo
import Clash.Crypto.Calculator.Karatsuba
  ( karatsuba, karatsubaSequential, karatsubaSequentialModulo )

tastyTests :: TestTree
tastyTests
  = localOption (HedgehogTestLimit (Just 500))
  $ testGroup "Clash.Crypto.Calculator.Karatsuba"
      [ testProperty "combinational" $ property $ do
          a <- forAll $ genUnsigned $ Range.linear minBound maxBound
          b <- forAll $ genUnsigned $ Range.linear minBound maxBound
          testKaratsubaEqualityWithMultiplication a b
      , testProperty "sequential" $ property $ do
          a <- forAll $ genUnsigned $ Range.linear minBound maxBound
          b <- forAll $ genUnsigned $ Range.linear minBound maxBound
          testKaratsubaSequential a b
      , testProperty "withModulo" $ property $ do
          kT <- forAll $ integral $ Range.linear 1 (shiftL 1 256)
          Just (SomeNat (_ :: Proxy k)) <- return $ someNatVal kT
          case (Proxy ∷ Proxy 1) %<=? (Proxy ∷ Proxy k) of
            NLE _ _ -> return ()
            LE Refl -> do
              a :: Mod k <- genMod
              b :: Mod k <- genMod
              testKSM (a, b) $ fromInteger
                $ (toInteger a * toInteger b) `mod` kT
      ]
 where
  genMod ∷ ∀ k m. (Monad m, KnownNat k, 1 ≤ k) ⇒ PropertyT m (Mod k)
  genMod = do
    x ← forAll $ genIndex @k $ Range.linear minBound maxBound
    return $ createMod @k x

type TestLen = 512

testKaratsubaEqualityWithMultiplication :: Monad m =>
 Unsigned TestLen -> Unsigned TestLen -> PropertyT m ()
testKaratsubaEqualityWithMultiplication a b =
  karatsuba 6 a b
  ===
  resize (resize @_ @_ @(TestLen * 2) a * resize @_ @_ @(TestLen * 2) b)

testKaratsubaSequential :: Monad m =>
 Unsigned TestLen -> Unsigned TestLen -> PropertyT m ()
testKaratsubaSequential p1 p2 = do
  actualOutput === expectedOutput
 where
  expectedOutput :: Unsigned (TestLen * 2)
  expectedOutput = resize p1 * resize p2

  actualOutput
    = fromMaybe (error "The returned list was empty")
    $ getFirst
    $ foldMap First
    $ sampleN @System 4000
    $ withClockResetEnable clockGen resetGen enableGen
    $ newsfeed
    $ karatsubaSequential 4 36
    $ channel
    $ fmap ((p1, p2), )
    $ fromList
    $ Keep : Keep : Release : List.repeat Keep

testKSM ::
  forall p m.
  (Monad m, KnownNat p, 1 <= p) =>
  (Mod p, Mod p) -> Mod p -> PropertyT m ()
testKSM i r = do
  actualOutput === r
 where
  actualOutput
    = fromMaybe (error "The returned list was empty")
    $ getFirst
    $ foldMap First
    $ sampleN @System 4000
    $ withClockResetEnable clockGen resetGen enableGen
    $ newsfeed
    $ fmap bitCoerce
    $ karatsubaSequentialModulo 4 36
    $ channel
    $ fmap ((bitCoerce i, natToNum @(p - 1) + 1), )
    $ fromList
    $ Keep : Keep : Release : List.repeat Keep
