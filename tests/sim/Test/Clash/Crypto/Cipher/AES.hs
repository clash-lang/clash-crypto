{-|
Module      : Test.Clash.Crypto.Cipher.AES
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Cipher.AES'.
-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedLists #-} -- Used to inturper a list as Byte String
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}

module Test.Clash.Crypto.Cipher.AES (tastyTests) where


import Test.Tasty

import qualified Test.Clash.Crypto.Cipher.AES.Specification.Definitions as Def
import qualified Test.Clash.Crypto.Cipher.AES.Specification.Algorithm as Alg
import qualified Test.Clash.Crypto.Cipher.AES.Specification as Spec
import qualified Test.Clash.Crypto.Cipher.AES.Streaming.Algorithm as StreamAlg



tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.Cipher.AES"
  [Def.tastyTests, 
  Alg.tastyTests,
  Spec.tastyTests,
  StreamAlg.tastyTests] 

