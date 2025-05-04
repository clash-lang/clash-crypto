{-|
Module      : Test.Clash.Crypto.ECDSA.Modulo
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.ECDSA.InverseModulo'.
-}

module Test.Clash.Crypto.ECDSA.InverseModulo where
import Test.Tasty
import Test.Tasty.Hedgehog
import Clash.Prelude hiding (Mod)
import Hedgehog
import Hedgehog.Range as Range
import qualified Data.List as List
import Data.Maybe (catMaybes, listToMaybe, fromJust)
import Clash.Crypto.ECDSA.InverseModulo (bea)
import Clash.Crypto.ECDSA.Modulo
import Clash.Hedgehog.Sized.Index (genIndex)
import qualified Data.Modular as Modular

-- TODO: Once all PRs are merged, move this to one place.
type Q = 115792089210356248762697446949407573530086143415290314195533631308867097853951

tastyTests :: TestTree
tastyTests = testGroup "Clash.Crypto.ECDSA.InverseModulo"
  [ localOption (HedgehogTestLimit (Just 1000)) $
      testProperty "Functional equality of inverse modulo" myProp]

-- Note: Modulus should always be prime for this algorithm to work.
-- Given a modulus g, forall 0 < f < g, show `bea f` returns the inverse of f in g.
myProp :: Property
myProp = property $ do
  f <- forAll $ genIndex $ Range.constantFrom 1 1 (maxBound - 1)
  let f' = unMod $ calcBea @Q $ createMod f
  f' === fromInteger (Modular.unMod (fromJust $ Modular.inv (Modular.toMod @Q $ toInteger f)))
 where
  calcBea ::
    forall m.
    (KnownNat m, 1 <= m) =>
    Mod m ->
    Mod m
  calcBea input =
    let r = catMaybes $
            sampleN @System 10000000 $
            withClockResetEnable clockGen resetGen enableGen $
            bea @m (fromList toggleInput) (fromList $ List.repeat input)
    in case listToMaybe r of
     Just a  -> a
     Nothing -> error "The returned list was empty"

  toggleInput = [False, False] <> List.repeat True
