module Test.Clash.Crypto.ECDSA.Karatsuba where
import Test.Tasty
import Test.Tasty.Hedgehog
import Clash.Prelude
import Hedgehog
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import qualified Hedgehog.Range as Range
import Clash.Crypto.ECDSA.Karatsuba (karatsuba, karatsubaStreamingGated)

import qualified Data.List as List
import Test.Tasty.HUnit
import Data.Maybe (catMaybes)

tastyTests :: TestTree
tastyTests = testGroup "Clash.Crypto.ECDSA.Karatsuba"
  [ localOption (HedgehogTestLimit (Just 500))
  $ testGroup "Tests for Karatsuba's algorithm"
    [ testProperty "Equality" $ property $ do
        a <- forAll $ genUnsigned $ Range.linear minBound maxBound
        b <- forAll $ genUnsigned $ Range.linear minBound maxBound
        testKaratsubaEqualityWithMultiplication a b
    ,  testCase "testKaratsubaStreaming" testKaratsubaStreaming
    ]
  ]

type TestLen = 512

testKaratsubaEqualityWithMultiplication :: Monad m => Unsigned TestLen -> Unsigned TestLen -> PropertyT m ()
testKaratsubaEqualityWithMultiplication a b =
  (karatsuba @6 @TestLen @TestLen SNat (resize a) (resize b)) === (resize $ resize @_ @_ @(TestLen * 2) a * resize @_ @_ @(TestLen * 2) b)

testKaratsubaStreaming :: Assertion
testKaratsubaStreaming = do
  assertEqual "testEquality" expectedOutput actualOutput
 where
  expectedOutput :: Unsigned 64
  expectedOutput = resize p1 * resize p2

  p1, p2 :: Unsigned 32
  p1 = 672389136
  p2 = 3498732
  testInput =
    [Nothing, Nothing]
      <> [Just (p1, p2)]
      <> List.repeat Nothing
  actualOutput =
    List.head
     $ catMaybes
     $ sampleN @System 400
     $ withClockResetEnable clockGen resetGen enableGen
     $ karatsubaStreamingGated @3 @36
     $ fromList testInput

