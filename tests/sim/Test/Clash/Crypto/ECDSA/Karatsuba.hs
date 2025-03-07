module Test.Clash.Crypto.ECDSA.Karatsuba where
import Test.Tasty
import Test.Tasty.Hedgehog
import Clash.Prelude
import Hedgehog
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import qualified Hedgehog.Range as Range
import Clash.Crypto.ECDSA.Karatsuba (karatsuba)

tastyTests :: TestTree
tastyTests = testGroup "Clash.Crypto.ECDSA.Karatsuba"
  [ localOption (HedgehogTestLimit (Just 500))
  $ testGroup "Combinatorial Karatsuba versus standard multiplication"
    [ testProperty "Equality" $ property $ do
        a <- forAll $ genUnsigned $ Range.linear minBound maxBound
        b <- forAll $ genUnsigned $ Range.linear minBound maxBound
        testKaratsubaEqualityWithMultiplication a b
    ]
  ]

type TestLen = 512

testKaratsubaEqualityWithMultiplication :: Monad m => Unsigned TestLen -> Unsigned TestLen -> PropertyT m ()
testKaratsubaEqualityWithMultiplication a b = do
  (karatsuba @6 @TestLen @6 (resize a) (resize b)) === (resize $ resize @_ @_ @(TestLen * 2) a * resize @_ @_ @(TestLen * 2) b)
