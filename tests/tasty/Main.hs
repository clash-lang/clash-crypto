module Main where

import Prelude
import Test.Tasty

import qualified Test.Clash.Crypto.Hash.SHA as SHA

main ∷ IO ()
main = defaultMain $ testGroup "clash-crypto tests"
  [ SHA.tastyTests
  ]
