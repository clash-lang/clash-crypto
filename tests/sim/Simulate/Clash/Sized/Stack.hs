{-|
Module      : Simulate.Clash.Sized.Stack
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Simulation tests for 'Clash.Sized.Stack'.
-}

module Simulate.Clash.Sized.Stack (tastyTests) where

import Clash.Sized.Stack

import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog
import Clash.Prelude.Safe

import qualified Data.List as L
import qualified Hedgehog.Range as Range
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import Hedgehog.Gen hiding (resize, maybe)
import Clash.Hedgehog.Sized.Index (genIndex)
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Proxy (Proxy)

tastyTests ∷ TestTree
tastyTests = localOption (HedgehogTestLimit (Just 1000)) $
  testGroup "Clash.Sized.Stack"
  [ testGroup "Stack charge"
    [ -- pushing n times to a stack with charge 0 results in a stack with
      -- charge n
      testProperty "Push - empty stack" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 0
        cmdsPush ← createStack 0 stackSize
        testSize @size (Push <$> cmdsPush) $ toEnum $ L.length cmdsPush
    , -- popping m times from a stack with charge n with m ≤ n results
      -- in stack with charge (n - m)
      testProperty "Pop - non-empty stack" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 0
        cmdsPush  ← createStack 0 stackSize
        let len = L.length cmdsPush
        lenPop ← forAll $ genIndex $ Range.linear 0 (toEnum len)
        testSize @size (cmdsPush <> [Pop lenPop]) $ len - fromEnum lenPop
    , -- inspecting the stack doesn't change the charge of the stack
      testProperty "Inspect" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack 0 stackSize
        idxInspect ← forAll $ genIndex $ Range.linear 0 maxBound
        testSize @size (cmdsPush <> [Inspect idxInspect]) $ L.length cmdsPush
    , -- swapping elements on the stack doesn't change the charge of
      -- the stack
      testProperty "Swap" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack 1 stackSize
        idxSwap ← forAll $ genIndex $ Range.linear 0 maxBound
        testSize @size (cmdsPush <> [Swap idxSwap]) $ L.length cmdsPush
    , -- 'CopyUp' from an index with data doesn't change the charge of
      -- the stack
      testProperty "CopyUp - index with data" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack 0 $ stackSize - 1
        idxCopyUp ← makeUnusedIndex @size cmdsPush
        testSize (cmdsPush <> [CopyUp idxCopyUp]) $ L.length cmdsPush
    , -- 'CopyUp' with positive charge from an index with data results
      -- in a stack with charge (n + 1) unless it's full
      testProperty "CopyUp - index without data - charge < max" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 2
        cmdsPush ← createStack 1 $ stackSize - 1
        idxCopyUp ← makeUsedIndex @size cmdsPush
        testSize (cmdsPush <> [CopyUp idxCopyUp]) $ L.length cmdsPush + 1
    , -- 'CopyUp' on a full stack doesn't change the charge of the
      -- stack
      testProperty "CopyUp - full stack" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack stackSize stackSize
        let predLen = toEnum $ L.length cmdsPush - 1 ∷ Index size
        idxCopyUp ← forAll $ genIndex $ Range.linear 0 predLen
        testSize (cmdsPush <> [CopyUp idxCopyUp]) $ 1 + fromEnum predLen
    ]
  , testGroup "Single return"
    [ -- pushing to a non-full stack returns the pushed value
      testProperty "Push - non-full stack" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack 0 (stackSize - 1)
        v ← forAll $ genUnsigned $ Range.linear 0 (maxBound ∷ Unsigned 16)
        testReturned @size (cmdsPush <> [Push v]) (Just v)
    , -- pushing to a full stack returns 'Nothing'
      testProperty "Push - full stack" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 0
        cmdsPush ← createStack stackSize stackSize
        v ← forAll $ genUnsigned $ Range.linear 0 (maxBound ∷ Unsigned 16)
        testReturned @size (cmdsPush <> [Push v]) Nothing
    , -- inspecting an index with data returns the right value
      testProperty "Inspect - index with data" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack 1 stackSize
        idxInspect ← makeUsedIndex cmdsPush
        let returnVal = extractPush idxInspect (L.reverse cmdsPush)
        testReturned @size (cmdsPush <> [Inspect idxInspect]) returnVal
    , -- inspecting an index without data returns 'Nothing'
      testProperty "Inspect - index without data" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack 0 $ stackSize - 1
        idxInspect ← makeUnusedIndex @size cmdsPush
        testReturned @size (cmdsPush <> [Inspect idxInspect]) Nothing
    , -- 'CopyUp' from an index without data returns 'Nothing'
      testProperty "CopyUp - index without data" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack 0 $ stackSize - 1
        idxCpu ← makeUnusedIndex cmdsPush
        testReturned @size (cmdsPush <> [CopyUp idxCpu]) Nothing
    , -- 'CopyUp' from a full stack returns 'Nothing'
      testProperty "CopyUp - full stack" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack stackSize stackSize
        idxCpu ← forAll $ genIndex $ Range.linear minBound maxBound
        testReturned @size (cmdsPush <> [CopyUp idxCpu]) Nothing
    , -- 'CopyUp' from an index with data with a non-full stack
      -- returns the pushed element
      testProperty "CopyUp - index with data - charge < max" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 2
        cmdsPush ← createStack 1 (stackSize - 1)
        idxCpu ← makeUsedIndex cmdsPush
        let returnVal = extractPush idxCpu (L.reverse cmdsPush)
        testReturned @size (cmdsPush <> [CopyUp idxCpu]) returnVal
    , -- swapping from an index without data returns 'Nothing'
      testProperty "Swap - index without data" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack 0 (stackSize - 1)
        idxSwap ← makeUnusedIndex cmdsPush
        testReturned @size (cmdsPush <> [Swap idxSwap]) Nothing
    , -- swapping from an index with data returns the pointed value
      testProperty "Swap - index with data" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack 1 stackSize
        idxSwap ← makeUsedIndex cmdsPush
        let returnVal = extractPush idxSwap (L.reverse cmdsPush)
        testReturned @size (cmdsPush <> [Swap idxSwap]) returnVal
    , -- popping m elements from a stack with charge n (m < n) gives
      -- the value at the top
      testProperty "Pop - less than charge" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack 1 stackSize
        lenPop ← makeUsedIndex cmdsPush
        let returnVal = extractPush lenPop (L.reverse cmdsPush)
        testReturned @size (cmdsPush <> [Pop $ resize lenPop]) returnVal
    , -- popping m elements from a stack with charge n (m >= n) gives
      -- 'Nothing'
      testProperty "Pop - everything " $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 0
        cmdsPush ← createStack 0 stackSize
        let len = toEnum $ L.length cmdsPush ∷ Index (size + 1)
        lenPop ← forAll $ genIndex $ Range.linear len maxBound
        testReturned @size (cmdsPush <> [Pop lenPop]) Nothing
    ]
  , testGroup "Single return values after a Pop 1"
    [ -- pushing to a non-full stack returns the pushed value
      testProperty "Push - non-full stack" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack 1 stackSize
        v ← forAll $ genUnsigned $ Range.linear 0 (maxBound ∷ Unsigned 16)
        testReturned @size (cmdsPush <> [Pop 1, Push v]) (Just v)
    , -- inspecting an index with data returns the right value
      testProperty "Inspect - index with data" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 2
        cmdsPush ← createStack 2 stackSize
        idxInspect ← makeUsedIndex $ safeTail cmdsPush
        let returnVal = extractPush idxInspect (safeTail $ L.reverse cmdsPush)
        testReturned @size (cmdsPush <> [Pop 1, Inspect idxInspect]) returnVal
    , -- inspecting an index without data returns 'Nothing'
      testProperty "Inspect - index without data" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack 1 stackSize
        idxInspect ← makeUnusedIndex $ safeTail cmdsPush
        testReturned @size (cmdsPush <> [Pop 1, Inspect idxInspect]) Nothing
    , -- 'CopyUp' from an index without data returns 'Nothing'
      testProperty "CopyUp - index without data" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack 1 stackSize
        idxCpu ← makeUnusedIndex $ safeTail cmdsPush
        testReturned @size (cmdsPush <> [Pop 1, CopyUp idxCpu]) Nothing
    , -- 'CopyUp' from an index with data with a non-full stack
      -- returns the pushed element
      testProperty "CopyUp - index with data - charge < max" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 2
        cmdsPush ← createStack 2 stackSize
        idxCpu ← makeUsedIndex $ safeTail cmdsPush
        let returnVal = extractPush idxCpu (safeTail $ L.reverse cmdsPush)
        testReturned @size (cmdsPush <> [Pop 1, CopyUp idxCpu]) returnVal
    , -- swapping from an index without data returns 'Nothing'
      testProperty "Swap - index without data" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 1
        cmdsPush ← createStack 1 stackSize
        idxSwap ← makeUnusedIndex $ safeTail cmdsPush
        testReturned @size (cmdsPush <> [Pop 1, Swap idxSwap]) Nothing
    , -- swapping from an index with data returns the pointed value
      testProperty "Swap - index with data" $ property $ do
        (stackSize, SomeNat (_ ∷ Proxy size)) ← genStackSize 2
        cmdsPush ← createStack 2 stackSize
        idxSwap ← makeUsedIndex $ safeTail cmdsPush
        let returnVal = extractPush idxSwap (safeTail $ L.reverse cmdsPush)
        testReturned @size (cmdsPush <> [Pop 1, Swap idxSwap]) returnVal
    ]
  ]

safeTail ∷ [c] → [c]
safeTail = maybe (error "Action list shouldn't be empty") snd . L.uncons

extractPush ∷ KnownNat n ⇒ Index n → [StackAction n a] → Maybe a
extractPush idx lst = case lst L.!! fromEnum idx of
  Push i → Just i
  _      → Nothing

genStackSize ∷ Monad m ⇒ Integer → PropertyT m (Integer, SomeNat)
genStackSize m = do
  stackSize ← forAll $ integral $ Range.linear m 500
  Just someStackSize ← return $ someNatVal stackSize
  return (stackSize, someStackSize)

-- len should be less than size.
makeUnusedIndex ∷
  ∀ size t m a.
  (Foldable t, Monad m, KnownNat size) ⇒
  t a → PropertyT m (Index size)
makeUnusedIndex cmds = do
 let len = L.length cmds
 forAll $ genIndex $ Range.linear (toEnum len) maxBound

-- len should be greater than 1.
makeUsedIndex ∷
  ∀ size t m a.
  (Foldable t, Monad m, KnownNat size) ⇒
  t a → PropertyT m (Index size)
makeUsedIndex cmds = do
  let len = L.length cmds
  forAll $ genIndex $ Range.linear 0 $ toEnum $ len - 1

createStack ∷
  Monad m ⇒
  Integer →
  Integer →
  PropertyT m [StackAction n (Unsigned 16)]
createStack minSize maxSize = do
  -- Random numbers to fill the stack
  let r = genUnsigned $ Range.linear 0 (maxBound ∷ Unsigned 16)
      rPush = Range.linear (fromEnum minSize) $ fromEnum maxSize
  cmdsPush ← forAll $ list rPush r
  return $ Push <$> cmdsPush

testReturned ∷
  ∀ size a m.
  (Eq a, Show a, NFDataX a, Monad m, KnownNat size) ⇒
  [StackAction size a] →
  Maybe a →
  PropertyT m ()
testReturned cmds
  = (fst (sim cmds) ===)

testSize ∷
  ∀ size a m.
  (NFDataX a, Monad m, KnownNat size) ⇒
  [StackAction size a] →
  Int →
  PropertyT m ()
testSize cmds i
  = snd (sim cmds) === toEnum @(Index (size + 1)) i

sim ∷
  (NFDataX a, KnownNat n) ⇒
  [StackAction n a] →
  (Maybe a, Index (n + 1))
sim cmds
  = fromMaybe (error "The returned list was empty")
  $ listToMaybe
  $ L.reverse
  $ sampleN @System (L.length cmds + 3)
  $ withClockResetEnable clockGen resetGen enableGen
  $ stack
  $ fromList
  $ Pop 0 : Pop 0 : (cmds <> L.repeat (Pop 0))
