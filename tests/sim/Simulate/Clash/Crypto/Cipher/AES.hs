{-|
Module      : Simulate.Clash.Crypto.Cipher.AES
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Cipher.AES'.
-}

module Simulate.Clash.Crypto.Cipher.AES
  ( tastyTests
  ) where

import Clash.Prelude.Safe (KnownNat)
import Test.Tasty (TestTree, testGroup)

import Clash.Crypto.Cipher.AES
import Clash.Crypto.Cipher.AES.Specification
import Test.Clash.Crypto.Cipher.AES

import qualified Simulate.Clash.Crypto.Cipher.AES.Specification
import qualified Simulate.Clash.Crypto.Cipher.AES.Specification.Definitions
import qualified Simulate.Clash.Crypto.Cipher.AES.Specification.Algorithm
import qualified Simulate.Clash.Crypto.Cipher.AES.Streaming
import qualified Simulate.Clash.Crypto.Cipher.AES.Streaming.Algorithm

tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.Cipher.AES"
  [ Simulate.Clash.Crypto.Cipher.AES.Specification.Definitions.tastyTests
  , testGroup "AES128"
    [ specificationTests AES128
    , streamingTests AES128
    ]
  , testGroup "AES192"
    [ specificationTests AES192
    , streamingTests AES192
    ]
  , testGroup "AES256"
    [ specificationTests AES256
    , streamingTests AES256
    ]
  ]

specificationTests ∷
  ∀ (alg ∷ AES) →
  ( KnownAES alg, AESKeyExpansion alg, CryptoAES alg, AESFunctions alg
  , KnownNat (Nk alg)
  ) ⇒
  TestTree
specificationTests alg = testGroup "Specification"
  [ Simulate.Clash.Crypto.Cipher.AES.Specification.Algorithm.tastyTests alg
  , Simulate.Clash.Crypto.Cipher.AES.Specification.tastyTests alg
  ]

streamingTests ∷
  ∀ (alg ∷ AES) →
  (KnownAES alg, AESKeyExpansion alg, CryptoAES alg, KnownNat (Nr alg)) ⇒
  TestTree
streamingTests alg = testGroup "Streaming"
  [ Simulate.Clash.Crypto.Cipher.AES.Streaming.Algorithm.tastyTests alg
  , Simulate.Clash.Crypto.Cipher.AES.Streaming.tastyTests alg
  ]
