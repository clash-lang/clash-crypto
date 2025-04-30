{-# LANGUAGE AllowAmbiguousTypes #-}
module Test.Clash.Crypto.ECDSA.InverseModulo where
import Test.Tasty
import Test.Tasty.Hedgehog
import Clash.Prelude hiding (Mod)
import Hedgehog
import Hedgehog.Gen as Gen
import Hedgehog.Range as Range
import qualified Data.List as List
import Data.Maybe (catMaybes)
import Clash.Crypto.ECDSA.InverseModulo (bea)
import Clash.Crypto.ECDSA.Modulo

-- TODO: Once all PRs are merged, move this to one place.
type Q = 115792089210356248762697446949407573530086143415290314195533631308867097853951

type Modulo = Q

tastyTests :: TestTree
tastyTests = testGroup "InverseModulo"
  [ localOption (HedgehogTestLimit (Just 1000)) $ testInverse]

testInverse = testProperty "functional equality" myProp

-- Note: Modulus should always be prime for this algorithm to work.
type MyMod = Q

-- Given a modulus g, forall 0 < f < g, show `bea f` returns the inverse of f in g.
myProp :: Property
myProp = property $ do
  f <- forAll (generator (natToNum @MyMod))
  let f' = fromIntegral $ calcBea @MyMod (fromInteger f)
  (f' * f) `mod` (natToNum @MyMod) === 1
 where
  generator m = Gen.integral (Range.constantFrom (1) 1 (m-1))

  calcBea ::
    forall m.
    (KnownNat m, 1 <= m) =>
    Mod m ->
    Mod m
  calcBea input =
    List.head
     $ catMaybes
     $ sampleN @System 4000
     $ withClockResetEnable clockGen resetGen enableGen
     $ bea @m (beaInput input)

  beaInput input =
    fromList
      $ [Nothing, Nothing]
        <> [Just input]
        <> List.repeat Nothing
