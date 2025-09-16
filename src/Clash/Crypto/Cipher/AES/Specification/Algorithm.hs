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
{-# LANGUAGE AllowAmbiguousTypes #-}
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
    cipher ∷ forall nr. (Nr alg ~ nr, Nr alg + 1 ~ nr + 1) ⇒ Proxy alg → InType alg → SNat nr → WType alg → OutType alg
    -- Algorithm 2 of FIPS 197
    keyExpansion ∷ Proxy alg →  KeyType alg → WType alg
    -- Algorithm 3 of FIPS 197 
    invCipher ∷ forall nr. (Nr alg ~ nr, Nr alg + 1 ~ nr + 1) ⇒ Proxy alg → InType alg → SNat nr → WType alg → OutType alg 
    -- Algorithm 4 of FIPS 197
    eqInvCipher ∷ forall nr. (Nr alg ~ nr, Nr alg + 1 ~ nr + 1) ⇒ Proxy alg → InType alg → SNat nr → WType alg → OutType alg 
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

    cipher ∷ forall nr. (Nr AES128 ~ nr, Nr AES128 + 1 ~ nr + 1) ⇒ Proxy AES128 → InType AES128 → SNat nr → WType AES128 → OutType AES128
    cipher (alg ∷ Proxy alg) input n1r w1s = addRoundKey (shiftRows (subBytes (rounds alg input n1r w1s))) (last (select @(1) @1 @1 @nr n1r (SNat :: SNat 1)  (SNat :: SNat 1) (wInWords w1s)))
        where 
            rounds ∷ forall n1r. (Nr alg ~ n1r, Nr alg + 1 ~ n1r + 1) ⇒  Proxy alg → InType alg → SNat n1r → WType alg → StateType alg                  
            rounds _ input1 _ ws = foldl mutation (addRoundKey input1 (head (wInWords ws))) (select @n1r @1 @(n1r -2) @1 (SNat :: SNat 1) (SNat :: SNat 1) (SNat :: SNat (n1r-2)) (wInWords ws))
            --                                                                                                                                            i (f+i) size   s   n        f  f offset          s select          n number
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))
            -- Algorithm 1 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state = addRoundKey (mixColumns ( shiftRows (subBytes state))) 
    invCipher ∷ forall nr. (Nr AES128 ~ nr, Nr AES128 + 1 ~ nr + 1) ⇒ Proxy AES128 → InType AES128 → SNat nr → WType AES128 → OutType AES128
    invCipher (alg ∷ Proxy alg) input nr ws = invAddRoundKey (invSubBytes (invShiftRows (rounds alg input nr (reverse ws)))) (last (wInWords (reverse ws)))
        where 
            rounds ∷ forall n1r. (Nr alg ~ n1r, Nr alg + 1 ~ n1r + 1) ⇒  Proxy alg → InType alg → SNat n1r → WType alg → StateType alg                  
            rounds _ input1 _ w1s = foldl mutation (invAddRoundKey input1 (head (wInWords w1s))) (select @nr @1 @(nr -2) @1 (SNat :: SNat 1) (SNat :: SNat 1) (SNat :: SNat (nr-2)) (wInWords w1s))
            --                                                                                                                                            i (f+i) size   s   n        f  f offset          s select          n number
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))
            -- Algorithm 2 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state w = invMixColumns (invAddRoundKey ( invSubBytes (invShiftRows state)) w) 

    eqInvCipher ∷ forall nr. (Nr AES128 ~ nr, Nr AES128 + 1 ~ nr + 1) ⇒ Proxy AES128 → InType AES128 → SNat nr → WType AES128 → OutType AES128
    eqInvCipher (alg ∷ Proxy alg) input1 n1r ws = invAddRoundKey (invShiftRows (invSubBytes (rounds alg input1 n1r (reverse ws)))) (last (wInWords (reverse ws)))
        where 
            rounds ∷ forall n1r. (Nr alg ~ n1r, Nr alg + 1 ~ n1r + 1) ⇒  Proxy alg → InType alg → SNat n1r → WType alg → StateType alg                  
            rounds _ input _ w1s = foldl mutation (invAddRoundKey input (head (wInWords w1s))) (select @n1r @1 @(n1r -2) @1 (SNat :: SNat 1) (SNat :: SNat 1) (SNat :: SNat (n1r-2)) (wInWords w1s))
            --                                                                                                                                            i (f+i) size   s   n        f  f offset          s select          n number
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat :: SNat (Nb alg ))
            -- Algorithm 2 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state = invAddRoundKey (invMixColumns ( invShiftRows (invSubBytes  state)))
    keyExpansionIEC ∷ Proxy AES128 →  KeyType AES128 → WType AES128
    keyExpansionIEC (alg ∷ Proxy alg) key = concat (head (orignal alg key):>Nil ++ map invMixColumns (init (tail (orignal alg key))) ++ last (orignal alg key):>Nil)
        where
            orignal ∷ Proxy alg →  KeyType alg →  Vec (Nr alg + 1) (RoundWType alg)
            orignal alg1 w1s = wInWords (keyExpansionIEC alg1 w1s) 
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
    cipher ∷ forall nr. (Nr AES192 ~ nr, Nr AES192 + 1 ~ nr + 1) ⇒ Proxy AES192 → InType AES192 → SNat nr → WType AES192 → OutType AES192
    cipher (alg ∷ Proxy alg) input n1r w1s = addRoundKey (shiftRows (subBytes (rounds alg input n1r w1s))) (last (select @(1) @1 @1 @nr n1r (SNat :: SNat 1)  (SNat :: SNat 1) (wInWords w1s)))
        where 
            rounds ∷ forall n1r. (Nr alg ~ n1r, Nr alg + 1 ~ n1r + 1) ⇒  Proxy alg → InType alg → SNat n1r → WType alg → StateType alg                  
            rounds _ input1 _ ws = foldl mutation (addRoundKey input1 (head (wInWords ws))) (select @n1r @1 @(n1r -2) @1 (SNat :: SNat 1) (SNat :: SNat 1) (SNat :: SNat (n1r-2)) (wInWords ws))
            --                                                                                                                                            i (f+i) size   s   n        f  f offset          s select          n number
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))
            -- Algorithm 1 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state = addRoundKey (mixColumns ( shiftRows (subBytes state))) 

    invCipher ∷ forall nr. (Nr AES192 ~ nr, Nr AES192 + 1 ~ nr + 1) ⇒ Proxy AES192 → InType AES192 → SNat nr → WType AES192 → OutType AES192
    invCipher (alg ∷ Proxy alg) input nr ws = invAddRoundKey (invSubBytes (invShiftRows (rounds alg input nr (reverse ws)))) (last (wInWords (reverse ws)))
        where 
            rounds ∷ forall n1r. (Nr alg ~ n1r, Nr alg + 1 ~ n1r + 1) ⇒  Proxy alg → InType alg → SNat n1r → WType alg → StateType alg                  
            rounds _ input1 _ w1s = foldl mutation (invAddRoundKey input1 (head (wInWords w1s))) (select @nr @1 @(nr -2) @1 (SNat :: SNat 1) (SNat :: SNat 1) (SNat :: SNat (nr-2)) (wInWords w1s))
            --                                                                                                                                            i (f+i) size   s   n        f  f offset          s select          n number
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))
            -- Algorithm 2 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state w = invMixColumns (invAddRoundKey ( invSubBytes (invShiftRows state)) w) 

    eqInvCipher ∷ forall nr. (Nr AES192 ~ nr, Nr AES192 + 1 ~ nr + 1) ⇒ Proxy AES192 → InType AES192 → SNat nr → WType AES192 → OutType AES192
    eqInvCipher (alg ∷ Proxy alg) input1 n1r ws = invAddRoundKey (invShiftRows (invSubBytes (rounds alg input1 n1r (reverse ws)))) (last (wInWords (reverse ws)))
        where 
            rounds ∷ forall n1r. (Nr alg ~ n1r, Nr alg + 1 ~ n1r + 1) ⇒  Proxy alg → InType alg → SNat n1r → WType alg → StateType alg                  
            rounds _ input _ w1s = foldl mutation (invAddRoundKey input (head (wInWords w1s))) (select @n1r @1 @(n1r -2) @1 (SNat :: SNat 1) (SNat :: SNat 1) (SNat :: SNat (n1r-2)) (wInWords w1s))
            --                                                                                                                                            i (f+i) size   s   n        f  f offset          s select          n number
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat :: SNat (Nb alg ))
            -- Algorithm 2 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state = invAddRoundKey (invMixColumns ( invShiftRows (invSubBytes  state)))
    keyExpansionIEC ∷ Proxy AES192 →  KeyType AES192 → WType AES192
    keyExpansionIEC (alg ∷ Proxy alg) key = concat (head (orignal alg key):>Nil ++ map invMixColumns (init (tail (orignal alg key))) ++ last (orignal alg key):>Nil)
        where
            orignal ∷ Proxy alg →  KeyType alg →  Vec (Nr alg + 1) (RoundWType alg)
            orignal alg1 w1s = wInWords (keyExpansionIEC alg1 w1s) 
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

    cipher ∷ forall nr. (Nr AES256 ~ nr, Nr AES256 + 1 ~ nr + 1) ⇒ Proxy AES256 → InType AES256 → SNat nr → WType AES256 → OutType AES256
    cipher (alg ∷ Proxy alg) input n1r w1s = addRoundKey (shiftRows (subBytes (rounds alg input n1r w1s))) (last (select @(1) @1 @1 @nr n1r (SNat :: SNat 1)  (SNat :: SNat 1) (wInWords w1s)))
        where 
            rounds ∷ forall n1r. (Nr alg ~ n1r, Nr alg + 1 ~ n1r + 1) ⇒  Proxy alg → InType alg → SNat n1r → WType alg → StateType alg                  
            rounds _ input1 _ ws = foldl mutation (addRoundKey input1 (head (wInWords ws))) (select @n1r @1 @(n1r -2) @1 (SNat :: SNat 1) (SNat :: SNat 1) (SNat :: SNat (n1r-2)) (wInWords ws))
            --                                                                                                                                            i (f+i) size   s   n        f  f offset          s select          n number
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))
            -- Algorithm 1 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state = addRoundKey (mixColumns ( shiftRows (subBytes state))) 

    invCipher ∷ forall nr. (Nr AES256 ~ nr, Nr AES256 + 1 ~ nr + 1) ⇒ Proxy AES256 → InType AES256 → SNat nr → WType AES256 → OutType AES256
    invCipher (alg ∷ Proxy alg) input nr ws = invAddRoundKey (invSubBytes (invShiftRows (rounds alg input nr (reverse ws)))) (last (wInWords (reverse ws)))
        where 
            rounds ∷ forall n1r. (Nr alg ~ n1r, Nr alg + 1 ~ n1r + 1) ⇒  Proxy alg → InType alg → SNat n1r → WType alg → StateType alg                  
            rounds _ input1 _ w1s = foldl mutation (invAddRoundKey input1 (head (wInWords w1s))) (select @nr @1 @(nr -2) @1 (SNat :: SNat 1) (SNat :: SNat 1) (SNat :: SNat (nr-2)) (wInWords w1s))
            --                                                                                                                                            i (f+i) size   s   n        f  f offset          s select          n number
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))
            -- Algorithm 2 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state w = invMixColumns (invAddRoundKey ( invSubBytes (invShiftRows state)) w) 

    eqInvCipher ∷ forall n2r. (Nr AES256 ~ n2r, Nr AES256 + 1 ~ n2r + 1) ⇒ Proxy AES256 → InType AES256 → SNat n2r → WType AES256 → OutType AES256
    eqInvCipher (alg ∷ Proxy alg) input1 n1r ws = invAddRoundKey (invShiftRows (invSubBytes (rounds alg input1 n1r (reverse ws)))) (last (wInWords (reverse ws)))
        where 
            rounds ∷ forall n1r. (Nr alg ~ n1r, Nr alg + 1 ~ n1r + 1) ⇒  Proxy alg → InType alg → SNat n1r → WType alg → StateType alg                  
            rounds _ input _ w1s = foldl mutation (invAddRoundKey input (head (wInWords w1s))) (select @n1r @1 @(n1r -2) @1 (SNat :: SNat 1) (SNat :: SNat 1) (SNat :: SNat (n1r-2)) (wInWords w1s))
            --                                                                                                                                            i (f+i) size   s   n        f  f offset          s select          n number
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat :: SNat (Nb alg ))
            -- Algorithm 2 codeline 5-8 as a function
            mutation ∷ StateType alg → RoundWType alg → StateType alg
            mutation state = invAddRoundKey (invMixColumns ( invShiftRows (invSubBytes  state)))
    keyExpansionIEC ∷ Proxy AES256 →  KeyType AES256 → WType AES256
    keyExpansionIEC (alg ∷ Proxy alg) key = concat (head (orignal alg key):>Nil ++ map invMixColumns (init (tail (orignal alg key))) ++ last (orignal alg key):>Nil)
        where
            orignal ∷ Proxy alg →  KeyType alg →  Vec (Nr alg + 1) (RoundWType alg)
            orignal alg1 w1s = wInWords (keyExpansionIEC alg1 w1s) 
            wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
            wInWords = unconcat (SNat ∷ SNat (Nb alg ))
