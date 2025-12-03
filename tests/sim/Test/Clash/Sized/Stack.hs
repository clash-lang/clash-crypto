module Test.Clash.Sized.Stack (tastyTests) where

import Clash.Sized.Stack

import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog
import Clash.Prelude

import qualified Data.List as L
import qualified Hedgehog.Range as Range
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import Hedgehog.Gen hiding (resize, maybe)
import Clash.Hedgehog.Sized.Index (genIndex)
import Data.Maybe (fromMaybe, listToMaybe)


type StackSize = 50

tastyTests :: TestTree
tastyTests = localOption (HedgehogTestLimit (Just 1000)) $
  testGroup "Clash.Sized.Stack"
  [ testGroup "Stack charge"
    [ testProperty "Stack push - empty stack" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize)
      testSize @StackSize (Push <$> cmdsPush) (toEnum $ L.length cmdsPush)
    ,
      testProperty "Stack pop - non-empty stack" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize)
      let len = toEnum $ L.length cmdsPush
      lenPop <- forAll $ genIndex $ Range.linear 0 len
      testSize @StackSize (cmdsPush <> [Pop lenPop]) (len - lenPop)
    ,
      testProperty "Inspect" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize)
      idxInspect <- forAll $ genIndex $ Range.linear 0 maxBound
      testSize @StackSize (cmdsPush <> [Inspect idxInspect])
                          (toEnum $ L.length cmdsPush)
    ,
      testProperty "Swap" $ property $ do
      cmdsPush <- createStack 1 (natToNum @StackSize)
      idxSwap <- forAll $ genIndex $ Range.linear 0 maxBound
      testSize @StackSize (cmdsPush <> [Swap idxSwap])
       (toEnum $ L.length cmdsPush)
    ,
      testProperty "CopyUp - unused index" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize - 1)
      idxCopyUp <- makeUnusedIndex cmdsPush
      testSize (cmdsPush <> [CopyUp idxCopyUp]) (toEnum $ L.length cmdsPush)
    ,
      testProperty "CopyUp - used index" $ property $ do
      cmdsPush <- createStack 1 (natToNum @StackSize - 1)
      idxCopyUp <- makeUsedIndex cmdsPush
      testSize (cmdsPush <> [CopyUp idxCopyUp])
               (toEnum $ L.length cmdsPush + 1)
    ,
      testProperty "CopyUp - full stack" $ property $ do
      cmdsPush <- createStack (natToNum @StackSize) (natToNum @StackSize)
      idxCopyUp <- forAll $ genIndex $
       Range.linear 0 (toEnum $ L.length cmdsPush - 1:: Index StackSize)
      testSize (cmdsPush <> [CopyUp idxCopyUp]) (toEnum $ L.length cmdsPush)
    ]
  , testGroup "Single return values"
    [
      testProperty "Push - non-full stack" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize - 1)
      v <- forAll $ genUnsigned $ Range.linear 0 (maxBound :: Unsigned 16)
      testReturned @StackSize (cmdsPush <> [Push v]) (Just v)
    ,
      testProperty "Push - full stack" $ property $ do
      cmdsPush <- createStack (natToNum @StackSize) (natToNum @StackSize)
      v <- forAll $ genUnsigned $ Range.linear 0 (maxBound :: Unsigned 16)
      testReturned @StackSize (cmdsPush <> [Push v]) Nothing
    ,
      testProperty "Inspect - used index" $ property $ do
      cmdsPush <- createStack 1 (natToNum @StackSize)
      idxInspect <- makeUsedIndex cmdsPush
      let returnVal = extractPush idxInspect (L.reverse cmdsPush)
      testReturned @StackSize (cmdsPush <> [Inspect idxInspect]) returnVal
    ,
      testProperty "Inspect - unused index" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize - 1)
      idxInspect <- makeUnusedIndex cmdsPush
      testReturned @StackSize (cmdsPush <> [Inspect idxInspect]) Nothing
    ,
      testProperty "CopyUp - unused index" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize - 1)
      idxCpu <- makeUnusedIndex cmdsPush
      testReturned @StackSize (cmdsPush <> [CopyUp idxCpu]) Nothing
    ,
      testProperty "CopyUp - full stack" $ property $ do
      cmdsPush <- createStack (natToNum @StackSize) (natToNum @StackSize)
      idxCpu <- forAll $ genIndex $ Range.linear minBound maxBound
      testReturned @StackSize (cmdsPush <> [CopyUp idxCpu]) Nothing
    ,
      testProperty "CopyUp - used index - non-full stack" $ property $ do
      cmdsPush <- createStack 1 (natToNum @StackSize - 1)
      idxCpu <- makeUsedIndex cmdsPush
      let returnVal = extractPush idxCpu (L.reverse cmdsPush)
      testReturned @StackSize (cmdsPush <> [CopyUp idxCpu]) returnVal
    ,
      testProperty "Swap - unused index" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize - 1)
      idxSwap <- makeUnusedIndex cmdsPush
      testReturned @StackSize (cmdsPush <> [Swap idxSwap]) Nothing
    ,
      testProperty "Swap - used index" $ property $ do
      cmdsPush <- createStack 1 (natToNum @StackSize)
      idxSwap <- makeUsedIndex cmdsPush
      let returnVal = extractPush idxSwap (L.reverse cmdsPush)
      testReturned @StackSize (cmdsPush <> [Swap idxSwap]) returnVal
    ,
      testProperty "Pop - used index" $ property $ do
      cmdsPush <- createStack 1 (natToNum @StackSize)
      lenPop <- makeUsedIndex cmdsPush
      let returnVal = extractPush lenPop (L.reverse cmdsPush)
      testReturned @StackSize (cmdsPush <> [Pop $ resize lenPop]) returnVal
    ,
      testProperty "Pop m - unused index" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize)
      let len = L.length cmdsPush
      lenPop <- forAll $ genIndex $
       Range.linear (toEnum len :: Index (StackSize + 1)) maxBound
      testReturned @StackSize (cmdsPush <> [Pop lenPop]) Nothing
    ]
  , testGroup "Single return values after a Pop 1"
    [
      testProperty "Push - non-full stack" $ property $ do
      cmdsPush <- createStack 1 (natToNum @StackSize - 1)
      v <- forAll $ genUnsigned $ Range.linear 0 (maxBound :: Unsigned 16)
      testReturned @StackSize (cmdsPush <> [Pop 1, Push v]) (Just v)
    ,
      testProperty "Inspect - used index" $ property $ do
      cmdsPush <- createStack 2 (natToNum @StackSize)
      idxInspect <- satPred SatBound <$> makeUsedIndex cmdsPush
      let returnVal = extractPush idxInspect (safeTail $ L.reverse cmdsPush)
      testReturned @StackSize (cmdsPush <> [Pop 1, Inspect idxInspect])
                              returnVal
    ,
      testProperty "Inspect - unused index" $ property $ do
      cmdsPush <- createStack 1 (natToNum @StackSize - 1)
      idxInspect <- makeUnusedIndex cmdsPush
      testReturned @StackSize (cmdsPush <> [Pop 1, Inspect idxInspect]) Nothing
    ,
      testProperty "CopyUp - unused index" $ property $ do
      cmdsPush <- createStack 1 (natToNum @StackSize - 1)
      idxCpu <- makeUnusedIndex cmdsPush
      testReturned @StackSize (cmdsPush <> [Pop 1, CopyUp idxCpu]) Nothing
    ,
      testProperty "CopyUp - used index - non-full stack" $ property $ do
      cmdsPush <- createStack 2 (natToNum @StackSize - 1)
      idxCpu <- satPred SatBound <$> makeUsedIndex cmdsPush
      let returnVal = extractPush idxCpu (safeTail $ L.reverse cmdsPush)
      testReturned @StackSize (cmdsPush <> [Pop 1, CopyUp idxCpu]) returnVal
    ,
      testProperty "Swap - unused index" $ property $ do
      cmdsPush <- createStack 1 (natToNum @StackSize - 1)
      idxSwap <- makeUnusedIndex cmdsPush
      testReturned @StackSize (cmdsPush <> [Pop 1, Swap idxSwap]) Nothing
    ,
      testProperty "Swap - used index" $ property $ do
      cmdsPush <- createStack 2 (natToNum @StackSize)
      idxSwap <- satPred SatBound <$> makeUsedIndex cmdsPush
      let returnVal = extractPush idxSwap (safeTail $ L.reverse cmdsPush)
      testReturned @StackSize (cmdsPush <> [Pop 1, Swap idxSwap]) returnVal
    ]
  ]

safeTail :: [c] -> [c]
safeTail = maybe (error "Action list shouldn't be empty") snd . L.uncons

extractPush :: KnownNat n => Index n -> [StackAction n a] -> Maybe a
extractPush idx lst =
 case lst L.!! fromEnum idx of
  Push i -> Just i
  _      -> Nothing

-- len should be less than StackSize.
makeUnusedIndex :: (Foldable t, Monad m) =>
 t a -> PropertyT m (Index StackSize)
makeUnusedIndex cmds = do
 let len = L.length cmds
 forAll $ genIndex $ Range.linear (toEnum len) maxBound

-- len should be greater than 1.
makeUsedIndex :: (Foldable t, Monad m) => t a -> PropertyT m (Index StackSize)
makeUsedIndex cmds = do
 let len = L.length cmds
 forAll $ genIndex $ Range.linear 0 $ toEnum $ len - 1

createStack :: Monad m =>
 Int -> Int -> PropertyT m [StackAction n (Unsigned 16)]
createStack minSize maxSize = do
 -- Random numbers to fill the stack
 let r = genUnsigned $ Range.linear 0 (maxBound :: Unsigned 16)
 let rPush = Range.linear minSize maxSize
 cmdsPush <- forAll $ list rPush r
 return $ Push <$> cmdsPush

testReturned :: forall size a m.
 (Eq a, Show a, NFDataX a, Monad m, KnownNat size) =>
 [StackAction size a] -> Maybe a -> PropertyT m ()
testReturned cmds = (fst (sim cmds) ===)

testSize :: forall size a m. (NFDataX a, Monad m, KnownNat size) =>
 [StackAction size a] -> Index (size + 1) -> PropertyT m ()
testSize cmds = (snd (sim cmds) ===)

sim :: (NFDataX a, KnownNat n) => [StackAction n a] -> (Maybe a, Index (n + 1))
sim cmds
 = fromMaybe (error "The returned list was empty")
 $ listToMaybe
 $ L.reverse
 $ sampleN @System (L.length cmds + 3)
 $ withClockResetEnable clockGen resetGen enableGen
 $ stack
 $ fromList
 $ Pop 0 : Pop 0 : (cmds <> L.repeat (Pop 0))
