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
import Data.Proxy (Proxy)

type MaximumSize = 500

tastyTests :: TestTree
tastyTests = localOption (HedgehogTestLimit (Just 1000)) $
  testGroup "Clash.Sized.Stack"
  [ testGroup "Stack charge"
    [ testProperty "Push - empty stack" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack 1 $ fromEnum stackSize
      testSize @size (Push <$> cmdsPush) (toEnum $ L.length cmdsPush)
    ,
      testProperty "Pop - non-empty stack" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 2 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack 1 $ fromEnum stackSize
      let len   =  toEnum $ L.length cmdsPush
      lenPop    <- forAll $ genIndex $ Range.linear 0 len
      testSize @size (cmdsPush <> [Pop lenPop]) (len - lenPop)
    ,
      testProperty "Inspect" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush   <- createStack 0 (fromEnum stackSize)
      idxInspect <- forAll $ genIndex $ Range.linear 0 maxBound
      testSize @size (cmdsPush <> [Inspect idxInspect])
                          (toEnum $ L.length cmdsPush)
    ,
      testProperty "Swap" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack 1 (fromEnum stackSize)
      idxSwap   <- forAll $ genIndex $ Range.linear 0 maxBound
      testSize @size (cmdsPush <> [Swap idxSwap])
       (toEnum $ L.length cmdsPush)
    ,
      testProperty "CopyUp - unused index" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack 0 $ fromEnum stackSize - 1
      idxCopyUp <- makeUnusedIndex @size cmdsPush
      testSize (cmdsPush <> [CopyUp idxCopyUp]) (toEnum $ L.length cmdsPush)
    ,
      testProperty "CopyUp - used index - non-full stack" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 2 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack 1 $ fromEnum stackSize - 1
      idxCopyUp <- makeUsedIndex @size cmdsPush
      testSize (cmdsPush <> [CopyUp idxCopyUp])
               (toEnum $ L.length cmdsPush + 1)
    ,
      testProperty "CopyUp - full stack" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack (fromEnum stackSize) (fromEnum stackSize)
      idxCopyUp <- forAll $ genIndex $
       Range.linear 0 (toEnum $ L.length cmdsPush - 1:: Index size)
      testSize (cmdsPush <> [CopyUp idxCopyUp]) (toEnum $ L.length cmdsPush)
    ]
  , testGroup "Single return values"
    [
      testProperty "Push - non-full stack" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack 0 $ fromEnum stackSize - 1
      v <- forAll $ genUnsigned $ Range.linear 0 (maxBound :: Unsigned 16)
      testReturned @size (cmdsPush <> [Push v]) (Just v)
    ,
      testProperty "Push - full stack" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 0 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack (fromEnum stackSize) $ fromEnum stackSize
      v <- forAll $ genUnsigned $ Range.linear 0 (maxBound :: Unsigned 16)
      testReturned @size (cmdsPush <> [Push v]) Nothing
    ,
      testProperty "Inspect - used index" $ property $ do
      stackSize  <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush   <- createStack 1 $ fromEnum stackSize
      idxInspect <- makeUsedIndex cmdsPush
      let returnVal = extractPush idxInspect (L.reverse cmdsPush)
      testReturned @size (cmdsPush <> [Inspect idxInspect]) returnVal
    ,
      testProperty "Inspect - unused index" $ property $ do
      stackSize  <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush   <- createStack 0 $ fromEnum stackSize - 1
      idxInspect <- makeUnusedIndex @size cmdsPush
      testReturned @size (cmdsPush <> [Inspect idxInspect]) Nothing
    ,
      testProperty "CopyUp - unused index" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack 0 $ fromEnum stackSize - 1
      idxCpu    <- makeUnusedIndex cmdsPush
      testReturned @size (cmdsPush <> [CopyUp idxCpu]) Nothing
    ,
      testProperty "CopyUp - full stack" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack (fromEnum stackSize) (fromEnum stackSize)
      idxCpu    <- forAll $ genIndex $ Range.linear minBound maxBound
      testReturned @size (cmdsPush <> [CopyUp idxCpu]) Nothing
    ,
      testProperty "CopyUp - used index - non-full stack" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 2 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack 1 $ fromEnum stackSize - 1
      idxCpu    <- makeUsedIndex cmdsPush
      let returnVal = extractPush idxCpu (L.reverse cmdsPush)
      testReturned @size (cmdsPush <> [CopyUp idxCpu]) returnVal
    ,
      testProperty "Swap - unused index" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack 0 $ fromEnum stackSize - 1
      idxSwap   <- makeUnusedIndex cmdsPush
      testReturned @size (cmdsPush <> [Swap idxSwap]) Nothing
    ,
      testProperty "Swap - used index" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack 1 (fromEnum stackSize)
      idxSwap   <- makeUsedIndex cmdsPush
      let returnVal = extractPush idxSwap (L.reverse cmdsPush)
      testReturned @size (cmdsPush <> [Swap idxSwap]) returnVal
    ,
      testProperty "Pop - used index" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 2 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack 1 $ fromEnum stackSize
      lenPop    <- makeUsedIndex cmdsPush
      let returnVal = extractPush lenPop (L.reverse cmdsPush)
      testReturned @size (cmdsPush <> [Pop $ resize lenPop]) returnVal
    ,
      testProperty "Pop m - unused index" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 0 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush  <- createStack 0 (fromEnum stackSize)
      lenPop    <- forAll $ genIndex $
       Range.linear (toEnum $ L.length cmdsPush :: Index (size + 1)) maxBound
      testReturned @size (cmdsPush <> [Pop lenPop]) Nothing
    ]
  , testGroup "Single return values after a Pop 1"
    [
      testProperty "Push - non-full stack" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush <- createStack 1 $ fromEnum stackSize
      v <- forAll $ genUnsigned $ Range.linear 0 (maxBound :: Unsigned 16)
      testReturned @size (cmdsPush <> [Pop 1, Push v]) (Just v)
    ,
      testProperty "Inspect - used index" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 2 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush <- createStack 2 (fromEnum stackSize)
      idxInspect <-makeUsedIndex $ safeTail cmdsPush
      let returnVal = extractPush idxInspect (safeTail $ L.reverse cmdsPush)
      testReturned @size (cmdsPush <> [Pop 1, Inspect idxInspect])
                              returnVal
    ,
      testProperty "Inspect - unused index" $ property $ do
      stackSize  <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush   <- createStack 1 $ fromEnum stackSize
      idxInspect <- makeUnusedIndex $ safeTail cmdsPush
      testReturned @size (cmdsPush <> [Pop 1, Inspect idxInspect]) Nothing
    ,
      testProperty "CopyUp - unused index" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush <- createStack 1 $ fromEnum stackSize
      idxCpu   <- makeUnusedIndex $ safeTail cmdsPush
      testReturned @size (cmdsPush <> [Pop 1, CopyUp idxCpu]) Nothing
    ,
      testProperty "CopyUp - used index - non-full stack" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 2 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush <- createStack 2 $ fromEnum stackSize
      idxCpu   <- makeUsedIndex $ safeTail cmdsPush
      let returnVal = extractPush idxCpu (safeTail $ L.reverse cmdsPush)
      testReturned @size (cmdsPush <> [Pop 1, CopyUp idxCpu]) returnVal
    ,
      testProperty "Swap - unused index" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 1 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush <- createStack 1 $ fromEnum stackSize
      idxSwap  <- makeUnusedIndex $ safeTail cmdsPush
      testReturned @size (cmdsPush <> [Pop 1, Swap idxSwap]) Nothing
    ,
      testProperty "Swap - used index" $ property $ do
      stackSize <- forAll $ integral $ Range.linear 2 $ natToNum @MaximumSize
      Just (SomeNat (_ :: Proxy size)) <- return $ someNatVal stackSize
      cmdsPush <- createStack 2 (fromEnum stackSize)
      idxSwap  <- makeUsedIndex $ safeTail cmdsPush
      let returnVal = extractPush idxSwap (safeTail $ L.reverse cmdsPush)
      testReturned @size (cmdsPush <> [Pop 1, Swap idxSwap]) returnVal
    ]
  ]

safeTail :: [c] -> [c]
safeTail = maybe (error "Action list shouldn't be empty") snd . L.uncons

extractPush :: KnownNat n => Index n -> [StackAction n a] -> Maybe a
extractPush idx lst =
 case lst L.!! fromEnum idx of
  Push i -> Just i
  _      -> Nothing

-- len should be less than size.
makeUnusedIndex :: forall size t m a. (Foldable t, Monad m, KnownNat size) =>
 t a -> PropertyT m (Index size)
makeUnusedIndex cmds = do
 let len = L.length cmds
 forAll $ genIndex $ Range.linear (toEnum len) maxBound

-- len should be greater than 1.
makeUsedIndex :: forall size t m a. (Foldable t, Monad m, KnownNat size) =>
 t a -> PropertyT m (Index size)
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
