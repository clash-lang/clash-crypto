{-|
Module      : Clash.Crypto.Cipher.AES.Streaming.Properties
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Some properties that can be proven to be valid from the FIPS 197
streaming.
-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Clash.Crypto.Cipher.AES.Streaming.Properties   
( AESFacts(..)
  , KnownAES(..)
  ) where
import Data.Proxy(Proxy(..))
import Clash.Crypto.Cipher.AES.Specification
import Clash.Crypto.Cipher.AES.Specification.Properties as Prop
import Clash.Crypto.Cipher.AES.Streaming.Algorithm

-- Interface liberies:
import Clash.Prelude
import Clash.Signal.Channel


import Clash.Prelude

-- | We collect all required properties via the 'AESFacts' class.
-- | In chapter 6 the constraints are defined.
data AESStreamFacts (alg ∷ AES) where
  AESStreamFacts ∷
    ( Prop.KnownAES alg,
      AESKeyExpansion alg
    ) ⇒
    Proxy alg →
    AESStreamFacts alg

-- | We utilize the type checker to provide evidence for all of the
-- required properties, which are proven automatically for each
-- instance of the class.
class    KnownAESStream alg       where knownAES ∷ AESStreamFacts alg
instance KnownAESStream AES128    where knownAES = AESStreamFacts Proxy
instance KnownAESStream AES192    where knownAES = AESStreamFacts Proxy
instance KnownAESStream AES256    where knownAES = AESStreamFacts Proxy
