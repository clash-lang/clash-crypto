module SHA.TH where

import Prelude
import Language.Haskell.TH
import Clash.Crypto.MAC.HMAC (hmac)
import Clash.Crypto.Hash.SHA (SHA(..), sha)

shaAlgorithms :: [Name]
shaAlgorithms =
  [ 'SHA1
  , 'SHA224
  , 'SHA256
  , 'SHA384
  , 'SHA512
  , 'SHA512224
  , 'SHA512256
  ]

shaEntities :: Q [(String, Exp)]
shaEntities = mapM entity shaAlgorithms
 where
  entity algorithm = do
    e <- [|sha $(pure algorithm)|]
    let name = reverse . takeWhile (/= '.') . reverse $ show algorithm
    return (name, e)

hmacEntities :: Q [(String, Type, Exp)]
hmacEntities = mapM entity shaAlgorithms
 where
  entity algorithm = do
    let t = algorithm
    e <- [|hmac $(pure t)|]
    let name = reverse . takeWhile (/= '.') . reverse $ show algorithm
    return (name, t, e)
