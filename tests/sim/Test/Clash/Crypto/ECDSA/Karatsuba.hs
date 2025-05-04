{-|
Module      : Test.Clash.Crypto.ECDSA.Karatsuba
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.ECDSA.Karatsuba'.
-}

module Test.Clash.Crypto.ECDSA.Karatsuba where

import Clash.Crypto.ECDSA.Karatsuba (karatsuba, karatsubaSequentialGated)
import Clash.Prelude
import Data.Maybe (catMaybes, listToMaybe)

import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog

import qualified Data.List as List
import qualified Hedgehog.Range as Range

tastyTests :: TestTree
tastyTests = testGroup "Clash.Crypto.ECDSA.Karatsuba"
  [ localOption (HedgehogTestLimit (Just 500))
  $ testGroup "Tests for Karatsuba's algorithm"
    [
    testProperty "Karatsuba combinatorial algorithm" $ property $ do
        a <- forAll $ genUnsigned $ Range.linear minBound maxBound
        b <- forAll $ genUnsigned $ Range.linear minBound maxBound
        testKaratsubaEqualityWithMultiplication a b
    , testProperty "Karatsuba sequential algorithm" $ property $ do
        a <- forAll $ genUnsigned $ Range.linear minBound maxBound
        b <- forAll $ genUnsigned $ Range.linear minBound maxBound
        testKaratsubaSequential a b
    ]
  ]

type TestLen = 512

testKaratsubaEqualityWithMultiplication :: Monad m =>
 Unsigned TestLen -> Unsigned TestLen -> PropertyT m ()
testKaratsubaEqualityWithMultiplication a b =
  (karatsuba @6 @TestLen @TestLen SNat (resize a) (resize b))
  ===
  (resize $ resize @_ @_ @(TestLen * 2) a * resize @_ @_ @(TestLen * 2) b)

testKaratsubaSequential :: Monad m =>
 Unsigned TestLen -> Unsigned TestLen -> PropertyT m ()
testKaratsubaSequential p1 p2 = do
  actualOutput === expectedOutput
 where
  expectedOutput :: Unsigned (TestLen * 2)
  expectedOutput = resize p1 * resize p2

  testInput = List.repeat (p1, p2)
  toggleInput =
    [False, False]
      <> List.repeat True
  actualOutput =
    case listToMaybe actualOutputList of
      Just a -> a
      Nothing -> error "The returned list was empty"
  (x,y) = List.unzip testInput
  actualOutputList =
    catMaybes $
    sampleN @System 4000 $
    withClockResetEnable clockGen resetGen enableGen $
    karatsubaSequentialGated @4 @36
    (fromList toggleInput) (fromList x) (fromList y)

