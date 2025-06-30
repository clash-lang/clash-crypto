import Prelude
import Test.Tasty

import qualified Test.Clash.Crypto.Hash.SHA as SHA
import qualified Test.Clash.Crypto.MAC.HMAC as HMAC
import qualified Test.Clash.Crypto.ECDSA.Karatsuba as Karatsuba
import qualified Test.Clash.Crypto.ECDSA.Modulo as Modulo
import qualified Test.Clash.Crypto.ECDSA.InverseModulo as InverseModulo

main ∷ IO ()
main = defaultMain $ testGroup "clash-crypto simulation tests"
  [ SHA.tastyTests
  , HMAC.tastyTests
  , InverseModulo.tastyTests
  , Karatsuba.tastyTests
  , Modulo.tastyTests
  ]
