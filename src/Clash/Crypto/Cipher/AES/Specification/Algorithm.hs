{-|
Module      : Clash.Crypto.Cipher.AES.Specification.Algorithm
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Algorithmic reference implementation of FIPS 197 using a purely
functional description.
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

module Clash.Crypto.Cipher.AES.Specification.Algorithm where

import Clash.Prelude

import Data.Proxy (Proxy)
import Clash.Crypto.Cipher.AES.Specification.Types
import Clash.Crypto.Cipher.AES.Specification.Definitions


import GHC.TypeLits ()
-- | Implementation of 
class AESFunctions (alg ∷ AES) where
    -- Algorithm 1 of FIPS 197
    cipher ∷ Proxy alg → InType alg → WType alg → OutType alg
    -- Algorithm 2 of FIPS 197
    keyExpansion ∷ Proxy alg →  KeyType alg → WType alg
    -- Algorithm 3 of FIPS 197 
    invCipher ∷ Proxy alg → InType alg → WType alg → OutType alg 
    -- Algorithm 4 of FIPS 197
    eqInvCipher ∷ Proxy alg → InType alg → WType alg → OutType alg 
    keyExpansionIEC ∷ Proxy alg →  KeyType alg → WType alg
instance AESFunctions AES128 where

-- The keyexpansion function as written in Algorithm 2 and as illustrate in 6
--  keys 
-- k1 = wl    ==> formula(wl⊹3) ⊕ wl    ==> wl⊹4   
-- k2 = wl⊹1  ==> wl            ⊕ wl⊹1  ==> wl⊹5   
-- k3 = wl⊹2  ==> wl⊹1          ⊕ wl⊹2  ==> wl⊹6
-- k4 = wl⊹3  ==> wl⊹2          ⊕ wl⊹3  ==> wl⊹7
    keyExpansion ∷ Proxy AES128 → KeyType AES128 → WType AES128
    keyExpansion alg key = concat (scanl middelCalculation key (iterateI (+1) 0))
        where
        middelCalculation ∷ KeyType AES128 → Integer → KeyType AES128
        middelCalculation ws i = zipWith xorWord ((+>>) (partWord ws i) ws) ws
                where
                    partWord w1s index = xorWord (subWord (rotWord (last w1s)))   (_Rcon alg !! index)

    cipher ∷ Proxy AES128 → InType AES128 → WType AES128 → OutType AES128
    cipher (alg ∷ Proxy alg) input w1s = addRoundKey (shiftRows (subBytes (rounds alg input w1s))) (last (wInWords w1s))
        where 
            rounds ∷ Proxy alg → InType alg → WType alg → StateType alg                  
            rounds _ input1 ws = foldl mutation (addRoundKey input1 (head (wInWords ws))) (init (tail (wInWords ws)))
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))
            -- Algorithm 1 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state = addRoundKey (mixColumns ( shiftRows (subBytes state))) 
    invCipher ∷ Proxy AES128 → InType AES128 → WType AES128 → OutType AES128
    invCipher (alg ∷ Proxy alg) input ws = invAddRoundKey (invSubBytes (invShiftRows (rounds alg input (reverse ws)))) (last (wInWords (reverse ws)))
        where 
            rounds ∷ Proxy alg → InType alg → WType alg → StateType alg                  
            rounds _ input1 w1s = foldl mutation (invAddRoundKey input1 (head (wInWords w1s))) (init (tail (wInWords ws)))
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))
            -- Algorithm 2 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state w = invMixColumns (invAddRoundKey ( invSubBytes (invShiftRows state)) w) 

    eqInvCipher ∷ Proxy AES128 → InType AES128 → WType AES128 → OutType AES128
    eqInvCipher (alg ∷ Proxy alg) input1 ws = invAddRoundKey (invShiftRows (invSubBytes (rounds alg input1 (reverse ws)))) (last (wInWords (reverse ws)))
        where 
            rounds ∷ Proxy alg → InType alg → WType alg → StateType alg                  
            rounds _ input w1s = foldl mutation (invAddRoundKey input (head (wInWords w1s))) (init (tail (wInWords ws)))
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat :: SNat (Nb alg ))
            -- Algorithm 2 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state = invAddRoundKey (invMixColumns ( invShiftRows (invSubBytes  state)))
    keyExpansionIEC ∷ Proxy AES128 →  KeyType AES128 → WType AES128
    keyExpansionIEC (alg ∷ Proxy alg) key = concat (head (orignal alg key):>Nil ++ map invMixColumns (init (tail (orignal alg key))) ++ last (orignal alg key):>Nil)
        where
            orignal ∷ Proxy alg →  KeyType alg →  Vec (Nr alg + 1) (RoundWType alg)
            orignal alg1 w1s = wInWords (keyExpansion alg1 w1s) 
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))

instance AESFunctions AES192 where
    -- Similiar fashion as for AES128
    -- The keyexpansion function as written in Algorithm 2 and as illustrate in 7
    keyExpansion ∷ Proxy AES192 → KeyType AES192 → WType AES192
    keyExpansion alg key = takeI (keyExpansionInBlocks alg key)
        where 
            keyExpansionInBlocks ∷ Proxy AES192 → KeyType AES192 → Vec (Nk AES192 * Nr AES192) (WordType AES192)
            keyExpansionInBlocks alg1 key1 = concat (scanl (middelCalculation alg1) key1 (iterateI (+1) 1))
                where
                middelCalculation ∷ Proxy AES192 → KeyType AES192 → Integer → KeyType AES192
                middelCalculation _ ws i = zipWith xorWord ((+>>) (partWord ws i) ws) ws
                        where
                            partWord w1s index = xorWord (subWord (rotWord (last w1s)))   (_Rcon alg !! index)
    cipher ∷ Proxy AES192 → InType AES192 → WType AES192 → OutType AES192
    cipher (alg ∷ Proxy alg) input w1s = addRoundKey (shiftRows (subBytes (rounds alg input w1s))) (last (wInWords w1s))
        where 
            rounds ∷ Proxy alg → InType alg → WType alg → StateType alg                  
            rounds _ input1 ws = foldl mutation (addRoundKey input1 (head (wInWords ws))) (init (tail (wInWords ws)))
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))
            -- Algorithm 1 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state = addRoundKey (mixColumns ( shiftRows (subBytes state))) 

    invCipher ∷ Proxy AES192 → InType AES192 → WType AES192 → OutType AES192
    invCipher (alg ∷ Proxy alg) input ws = invAddRoundKey (invSubBytes (invShiftRows (rounds alg input (reverse ws)))) (last (wInWords (reverse ws)))
        where 
            rounds ∷ Proxy alg → InType alg → WType alg → StateType alg                  
            rounds _ input1 w1s = foldl mutation (invAddRoundKey input1 (head (wInWords w1s))) (init (tail (wInWords ws)))
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))
            -- Algorithm 2 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state w = invMixColumns (invAddRoundKey ( invSubBytes (invShiftRows state)) w) 

    eqInvCipher ∷ Proxy AES192 → InType AES192 → WType AES192 → OutType AES192
    eqInvCipher (alg ∷ Proxy alg) input1 ws = invAddRoundKey (invShiftRows (invSubBytes (rounds alg input1 (reverse ws)))) (last (wInWords (reverse ws)))
        where 
            rounds ∷ Proxy alg → InType alg → WType alg → StateType alg                  
            rounds _ input w1s = foldl mutation (invAddRoundKey input (head (wInWords w1s))) (init (tail (wInWords ws)))
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat :: SNat (Nb alg ))
            -- Algorithm 2 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state = invAddRoundKey (invMixColumns ( invShiftRows (invSubBytes  state)))
    keyExpansionIEC ∷ Proxy AES192 →  KeyType AES192 → WType AES192
    keyExpansionIEC (alg ∷ Proxy alg) key = concat (head (orignal alg key):>Nil ++ map invMixColumns (init (tail (orignal alg key))) ++ last (orignal alg key):>Nil)
        where
            orignal ∷ Proxy alg →  KeyType alg →  Vec (Nr alg + 1) (RoundWType alg)
            orignal alg1 w1s = wInWords (keyExpansion alg1 w1s) 
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))
instance AESFunctions AES256 where
    -- The keyexpansion function as written in Algorithm 2 and as illustrate in 8
    keyExpansion ∷ Proxy AES256 → KeyType AES256 → WType AES256
    keyExpansion alg key = takeI (keyExpansionInBlocks alg key)
        where 
            keyExpansionInBlocks ∷ Proxy AES256 → KeyType AES256 → Vec (Nk AES256 * (Nr AES256 + 3) * (Nr AES256 + 3)) (WordType AES256)
            keyExpansionInBlocks alg1 key1 = concat (scanl (middelCalculation alg1) key1 (iterateI (+1) 1))
                where
                middelCalculation ∷ Proxy AES256 → KeyType AES256 → Integer → KeyType AES256
                middelCalculation _ w1s i = firstPart w1s i ++ secondPart w1s i
                    where
                        firstPart ws i1 = zipWith xorWord ((+>>) (partWord (firstSplit ws) i1) (firstSplit ws)) (firstSplit ws)
                        firstSplit = takeI @(Nk AES256 `Div` 2)
                        secondPart ws i1 = zipWith xorWord ((+>>) (subWord (last (firstPart ws i1))) (secondSplit ws)) (secondSplit ws)
                        secondSplit = dropI @(Nk AES256 `Div` 2)
                        partWord ws index = xorWord (subWord (rotWord (last ws)))   (_Rcon alg !! index)

    cipher ∷ Proxy AES256 → InType AES256 → WType AES256 → OutType AES256
    cipher (alg ∷ Proxy alg) input w1s = addRoundKey (shiftRows (subBytes (rounds alg input w1s))) (last (wInWords w1s))
        where 
            rounds ∷ Proxy alg → InType alg → WType alg → StateType alg                  
            rounds _ input1 ws = foldl mutation (addRoundKey input1 (head (wInWords ws))) (init (tail (wInWords ws)))
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))
            -- Algorithm 1 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state = addRoundKey (mixColumns ( shiftRows (subBytes state))) 

    invCipher ∷  Proxy AES256 → InType AES256 → WType AES256 → OutType AES256
    invCipher (alg ∷ Proxy alg) input ws = invAddRoundKey (invSubBytes (invShiftRows (rounds alg input (reverse ws)))) (last (wInWords (reverse ws)))
        where 
            rounds ∷ Proxy alg → InType alg → WType alg → StateType alg                  
            rounds _ input1 w1s = foldl mutation (invAddRoundKey input1 (head (wInWords w1s))) (init (tail (wInWords ws)))
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))
            -- Algorithm 2 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state w = invMixColumns (invAddRoundKey ( invSubBytes (invShiftRows state)) w) 

    eqInvCipher ∷ Proxy AES256 → InType AES256 → WType AES256 → OutType AES256
    eqInvCipher (alg ∷ Proxy alg) input1 ws = invAddRoundKey (invShiftRows (invSubBytes (rounds alg input1 (reverse ws)))) (last (wInWords (reverse ws)))
        where 
            rounds ∷ Proxy alg → InType alg → WType alg → StateType alg                  
            rounds _ input w1s = foldl mutation (invAddRoundKey input (head (wInWords w1s))) (init (tail (wInWords ws)))
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat :: SNat (Nb alg ))
            -- Algorithm 2 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state = invAddRoundKey (invMixColumns ( invShiftRows (invSubBytes  state)))
    keyExpansionIEC ∷ Proxy AES256 →  KeyType AES256 → WType AES256
    keyExpansionIEC (alg ∷ Proxy alg) key = concat (head (orignal alg key):>Nil ++ map invMixColumns (init (tail (orignal alg key))) ++ last (orignal alg key):>Nil)
        where
            orignal ∷ Proxy alg →  KeyType alg →  Vec (Nr alg + 1) (RoundWType alg)
            orignal alg1 w1s = wInWords (keyExpansion alg1 w1s) 
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))

