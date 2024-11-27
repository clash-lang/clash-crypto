import Prelude
import Test.Tasty

import qualified Test.Clash.Crypto.Hash.SHA as SHA
import qualified Test.Clash.Crypto.ECDSA.Karatsuba as Karatsuba

main ∷ IO ()
main = defaultMain $ testGroup "clash-crypto simulation tests"
  [ SHA.tastyTests
  , Karatsuba.tastyTests
  ]
