{-|
Module      : Clash.Crypto.Blockcipher.AES.Specification
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Formalized AES specification according to
[FIPS PUB 197: Advanced Encryption Standard  (AES)](https://doi.org/10.6028/NIST.FIPS.197-upd1).

Note that this formalization adds an "@_@"-symbol to function names
that start with capital letter in the aforementioned document, to work
around the syntactic restrictions of Haskell. To keep the notation
consistent, the symbol is added to some function names starting with a
small letter as well.
-}
{-# LANGUAGE UnicodeSyntax #-}
module Clash.Crypto.Blockcipher.AES.Specification
  ( -- * INTRODUCTION and DEFINITIONS
--     SHA(..), WordSize, BlockSize, MessageDigestSize, HashValueWords
--   , ScheduleCount, SHAWord, MessageBlock, HashValue, Message
--     -- * Section 2.2.2 - Symbols and Operations
--   , (∧), (∨), (⊕), (¬), (≪), (≫), _ROTL, _ROTR, _SHR
--     -- * Section 4.1 - Functions
--   , _Ch, _Parity, _Mai, _f, SHAFunctions(..)
--     -- * Section 4.2 - Constants
--   , SHAConstants(..)
--     -- * Section 5.1 - Padding the Message
--   , SizeBits, PaddingZeros, RequiredBlocks
--     -- * Section 5.3 - Setting the Initial Hash Value
--   , SHAInitials(..)
--     -- * Section 6 - SECURE HASH ALGORITHMS
--   , SHAHashCompute(..), computeCycles, toDigest, hash
--     -- * Derivable Properties
--   , KnownSHA(..), SHAFacts(..)
--   , -- * Utility types
--     Digest
  ) where

import Clash.Crypto.Blockcipher.AES.Specification.Types
import Clash.Crypto.Blockcipher.AES.Specification.Definitions
import Clash.Crypto.Blockcipher.AES.Specification.Properties
import Clash.Crypto.Blockcipher.AES.Specification.Algorithm
