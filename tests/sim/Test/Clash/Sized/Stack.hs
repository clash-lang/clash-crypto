module Test.Clash.Sized.Stack (tastyTests) where

import Clash.Sized.Stack

import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog
import Clash.Prelude

import qualified Data.List as L
import qualified Hedgehog.Range as Range
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import Hedgehog.Gen hiding (resize)
import GHC.Num (integerFromInt)
import Clash.Hedgehog.Sized.Index (genIndex)
import Data.Maybe (fromJust)


type StackSize = 5

tastyTests = testGroup "Clash.Sized.Stack"
  [ localOption (HedgehogTestLimit (Just 1000))
  $ testGroup "Tests on the charge of the stack"
    [ testProperty "Stack push n times on stack of charge 0 gives stack of charge n" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize)
      testSize @StackSize (Push <$> cmdsPush) (fromInteger $ integerFromInt $ L.length cmdsPush)
    , testProperty "Stack pop m on stack of charge n (m <= n) gives stack of charge n-m" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize)
      lenPop <- forAll $ genIndex $ Range.linear 0 (intToIndex $ L.length cmdsPush)
      testSize @StackSize (cmdsPush <> [Pop lenPop]) ((intToIndex $ L.length cmdsPush) - lenPop)
    , testProperty "Inspect on stack doesn't change the charge of the stack" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize)
      let len = L.length cmdsPush
      idxInspect <- forAll $ genIndex $ Range.linear 0 (intToIndex (if len == natToNum @StackSize then len - 1 else len) :: Index StackSize)
      testSize @StackSize (cmdsPush <> [Inspect $ resize idxInspect]) (intToIndex $ L.length cmdsPush)
    , testProperty "Swap on stack doesn't change the charge of the stack" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize)
      let len = L.length cmdsPush
      idxSwap <- forAll $ genIndex $ Range.linear 0 (intToIndex (if len == natToNum @StackSize then len - 1 else len) :: Index StackSize)
      testSize @StackSize (cmdsPush <> [Swap $ resize idxSwap]) (intToIndex $ L.length cmdsPush)
    , testProperty "CopyUp on stack on an unused index doesn't change the charge of the stack" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize - 1)
      let len = L.length cmdsPush
      idxCopyUp <- forAll $ genIndex $ Range.linear (intToIndex len :: Index StackSize) maxBound
      testSize (cmdsPush <> [CopyUp idxCopyUp]) (intToIndex $ L.length cmdsPush)
    , testProperty "CopyUp on stack of charge n (0 < n) on a used index gives stack of charge n+1 if it's not full" $ property $ do
      cmdsPush <- createStack 1 (natToNum @StackSize - 1)
      idxCopyUp <- forAll $ genIndex $ Range.linear 0 (intToIndex $ L.length cmdsPush - 1:: Index StackSize)
      testSize (cmdsPush <> [CopyUp idxCopyUp]) (intToIndex $ L.length cmdsPush + 1)
    , testProperty "CopyUp on full stack doesn't change the charge of the stack" $ property $ do
      cmdsPush <- createStack (natToNum @StackSize) (natToNum @StackSize)
      idxCopyUp <- forAll $ genIndex $ Range.linear 0 (intToIndex $ L.length cmdsPush - 1:: Index StackSize)
      testSize (cmdsPush <> [CopyUp idxCopyUp]) (intToIndex $ L.length cmdsPush)
    ]
  , localOption (HedgehogTestLimit (Just 1000))
  $ testGroup "Tests on single return values"
    [
      testProperty "Push on a non-full stack returns the pushed value" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize - 1)
      v <- forAll $ genUnsigned $ Range.linear 0 (maxBound :: Unsigned 16)
      testReturned @StackSize (cmdsPush <> [Push v]) (Just v)
      ,
      testProperty "Push on a full stack returns Nothing" $ property $ do
      cmdsPush <- createStack (natToNum @StackSize) (natToNum @StackSize)
      v <- forAll $ genUnsigned $ Range.linear 0 (maxBound :: Unsigned 16)
      testReturned @StackSize (cmdsPush <> [Push v]) Nothing
      -- ,
      -- testProperty "Inspect on a used index returns the right value" $ property $ do
      -- cmdsPush <- createStack 1 (natToNum @StackSize)
      -- let len = L.length cmdsPush
      -- idxInspect <- forAll $ genIndex $ Range.linear 0
      --  (intToIndex (if len == natToNum @StackSize then len - 2 else len - 1) :: Index StackSize)
      -- let Push returnVal = (L.reverse cmdsPush) L.!! (fromEnum idxInspect)
      -- testReturned @StackSize (cmdsPush <> [Inspect 0, Inspect idxInspect, Inspect idxInspect]) (Just returnVal)
      ,
      testProperty "Inspect on an unused index returns Nothing" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize - 1)
      idxInspect <- makeIndexUnused cmdsPush
      testReturned @StackSize (cmdsPush <> [Inspect idxInspect]) Nothing
      ,
      testProperty "CopyUp on an unused index returns Nothing" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize - 1)
      idxCpu <- makeIndexUnused cmdsPush
      testReturned @StackSize (cmdsPush <> [CopyUp idxCpu]) Nothing
      ,
      testProperty "CopyUp on an full stack returns Nothing" $ property $ do
      cmdsPush <- createStack (natToNum @StackSize) (natToNum @StackSize)
      idxCpu <- forAll $ genIndex $ Range.linear minBound maxBound
      testReturned @StackSize (cmdsPush <> [CopyUp idxCpu]) Nothing
      -- ,
      -- testProperty "CopyUp on an used index and a non-full stack returns the pushed element" $ property $ do
      -- cmdsPush <- createStack 1 (natToNum @StackSize - 1)
      -- let len = L.length cmdsPush
      -- idxCpu <- forAll $ genIndex $ Range.linear 0 (intToIndex len - 1 :: Index StackSize)
      -- let Push returnVal = (L.reverse cmdsPush) L.!! (fromEnum idxCpu)
      -- testReturned @StackSize (cmdsPush <> [CopyUp idxCpu]) (Just returnVal)
      ,
      testProperty "Swap on an unused index returns Nothing" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize - 1)
      idxSwap <- makeIndexUnused cmdsPush
      testReturned @StackSize (cmdsPush <> [Swap idxSwap]) Nothing
      -- ,
      -- testProperty "Swap on a used index returns the pointed value" $ property $ do
      -- cmdsPush <- createStack 1 (natToNum @StackSize)
      -- let len = L.length cmdsPush
      -- idxSwap <- forAll $ genIndex $ Range.linear 0 (intToIndex len - 1 :: Index StackSize)
      -- let Push returnVal = (L.reverse cmdsPush) L.!! (fromEnum idxSwap)
      -- testReturned @StackSize (cmdsPush <> [Swap idxSwap]) (Just returnVal)
      -- ,
      -- testProperty "Pop m on a stack of charge n (m < n) gives the value at the top" $ property $ do
      -- cmdsPush <- createStack 1 (natToNum @StackSize)
      -- lenPop <- makeIndexUsed cmdsPush
      -- let Push ret = (L.reverse cmdsPush) L.!! fromEnum lenPop
      -- testReturned @StackSize (cmdsPush <> [Pop $ resize lenPop]) (Just ret)
      ,
      testProperty "Pop m on a stack of charge n (m >= n) gives Nothing" $ property $ do
      cmdsPush <- createStack 0 (natToNum @StackSize - 1)
      lenPop <- makeIndexUnused cmdsPush
      testReturned @StackSize (cmdsPush <> [Pop $ resize lenPop]) Nothing
    ]
  ]

makeIndexUnused cmds = do
 let len = L.length cmds
 forAll $ genIndex $ Range.linear (intToIndex len :: Index StackSize) maxBound

makeIndexUsed cmds = do
 let len = L.length cmds
 forAll $ genIndex $ Range.linear 0
  (intToIndex (if len == natToNum @StackSize then len - 2 else len - 1) :: Index StackSize)

createStack minSize maxSize = do
 -- Random numbers to fill the stack
 let r = genUnsigned $ Range.linear 0 (maxBound :: Unsigned 16)
 let rPush = Range.linear minSize maxSize
 cmdsPush <- forAll $ list rPush r
 return $ Push <$> cmdsPush

intToIndex :: forall n. KnownNat n => Int -> Index n
intToIndex = fromInteger . integerFromInt

testReturned :: forall size a m.
 (Eq a, Show a, NFDataX a, Monad m, KnownNat size) =>
 [StackAction size a] -> Maybe a -> PropertyT m ()
testReturned cmds expectedValue =
  actualValue === expectedValue
 where
  actualValue
    = L.head
    $ L.reverse
    $ fmap fst
    $ sampleN @System (L.length cmds + 3)
    $ withClockResetEnable clockGen resetGen enableGen
    $ stack
    $ fromList
    $ Pop 0 : Pop 0 : (cmds <> L.repeat (Pop 0))

testSize :: forall size a m. (NFDataX a, Monad m, KnownNat size) =>
 [StackAction size a] -> Index (size + 1) -> PropertyT m ()
testSize cmds expectedSize =
  actualSize === expectedSize
 where
  actualSize
    = L.head
    $ L.reverse
    $ fmap snd
    $ sampleN @System (L.length cmds + 3)
    $ withClockResetEnable clockGen resetGen enableGen
    $ stack
    $ fromList
    $ Pop 0 : Pop 0 : (cmds <> L.repeat (Pop 0))
