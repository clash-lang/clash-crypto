{-# LANGUAGE AllowAmbiguousTypes #-}
module Test.Clash.Crypto.Hash.HMAC where

import Clash.Prelude
import Data.Maybe
import qualified Data.List as List

import Test.Tasty
import Test.Tasty.Hedgehog

import Clash.Crypto.Hash.HMAC
import Clash.Crypto.Hash.SHA

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Clash.Hedgehog.Sized.BitVector as Gen (genDefinedBitVector)

-- Reference implementation
import qualified Data.Digest.Pure.SHA as OfficialSHA
import qualified Data.ByteString.Lazy.UTF8 as BLU
import qualified Data.ByteString.Lazy as BL

type KeySize = 256
type HmacChunkSize = 8
type NumChunks = Div KeySize HmacChunkSize

-- Test parameters
numTestCycles, maxMsgSizeForTesting :: Int
numTestCycles = 4000
maxMsgSizeForTesting = 499

tastyTests :: TestTree
tastyTests =
  testGroup
    "HmacTests"
    [ testProperty "testHmacHedgehog" testHmacHedgehog
    ]

testHmacHedgehog :: Property
testHmacHedgehog =
  property $ do
    testKey <- forAll
      $ Gen.list (Range.constant 1 (natToNum @NumChunks)) Gen.genDefinedBitVector
    testMsg <- forAll
      $ Gen.list (Range.constant 1 maxMsgSizeForTesting) Gen.genDefinedBitVector
    let testInput = (testKey, testMsg)
    Hedgehog.assert (hmacImpl testInput == hmacRefImpl testInput)


hmacImpl :: ([BitVector 8], [BitVector 8]) -> [Integer]
hmacImpl (keyData, msgData) = myOutputClean
 where
  myOutputClean :: [Integer]
  myOutputClean = fmap fromIntegral $ catMaybes myOutput
  myOutput =
    sampleN @System numTestCycles
      $ dut
      $ fromList hmacTestInput

  dut input = output
   where
    (fifoOut, _) = unbundle $ fifo @512 input request
    (output, request) = hmacWrapper @HmacChunkSize @SHA256 $ register Nothing $ fifoOut


  hmacTestInput :: [Maybe (HmacInput HmacChunkSize)]
  hmacTestInput =
    -- Skip over reset
    List.replicate 3 Nothing
    -- Test data
    <> keyInput keyData
    <> msgInput msgData
    <> List.repeat Nothing


  keyInput :: [BitVector 8] -> [Maybe (HmacInput HmacChunkSize)]
  keyInput key = keyBody <> [keyEnd]
   where
    (dataBody, dataEnd) = fromJust (List.unsnoc key)
    (keyBody, keyEnd) = ( List.map (Just . HmacKey) dataBody
                        , Just $ HmacKeyEnd dataEnd
                        )

  msgInput :: [BitVector 8] -> [Maybe (HmacInput HmacChunkSize)]
  msgInput msg = msgBody <> [msgEnd]
   where
    (dataBody, dataEnd) = fromJust (List.unsnoc msg)
    (msgBody, msgEnd) = ( List.map (Just . HmacMsg) dataBody
                        , Just $ HmacMsgEnd dataEnd 0
                        )


hmacRefImpl :: ([BitVector 8], [BitVector 8]) -> [Integer]
hmacRefImpl (keyData, msgData) = referenceOutput
 where
  key, msg :: BLU.ByteString
  key = BL.pack $ List.map bitCoerce keyData
  msg = BL.pack $ List.map bitCoerce msgData

  referenceOutput :: [Integer]
  referenceOutput = [OfficialSHA.integerDigest $ OfficialSHA.hmacSha256 key msg]


-- Here, we just define a FIFO to use in our tests to only send in data
-- when the circuit is ready.
type RingBufferData n a = Vec n a
type RingBufferState n m a =
    ( RingBufferData n a
    -- ^ Data contained in our buffer
    , Unsigned m
    -- ^ start index
    , Unsigned m
    -- ^ end index
    )

-- | A FIFO. It accepts, stores, and outputs data (on a read request). If both Just
-- data and a readRequest=True come in on the same cycle, the fifo will immediate
-- respond to the read request and output data.
fifo ::
  forall n m dom a.
  (HiddenClockResetEnable dom) =>
  NFDataX a =>
  KnownNat n =>
  (KnownNat m, 2^m ~ n) =>
  -- ^ m is used to ensure n is a power of 2 (so we can use Unsigned wraparound)
  Signal dom (Maybe a) ->
  -- ^ Data input
  Signal dom Bool ->
  -- ^ Read request
  Signal dom (Maybe a, Bool)
  -- ^ tuple of (outputData, isFifoEmpty)
fifo input readReqS = mealy ringBufferT initState $ bundle (input, readReqS)
 where
  ringBufferData :: RingBufferData n a
  ringBufferData = repeat undefined

  initState :: RingBufferState n m a
  initState = (ringBufferData, 0, 0)

  ringBufferT ::
    RingBufferState n m a ->
    (Maybe a, Bool) ->
    (RingBufferState n m a, (Maybe a, Bool))
  ringBufferT (ringData, headI, tailI) (maybeData, readReq) =
    (newState, (output, isBufferEmpty))
     where
      output :: (Maybe a)
      output
        | not readReq = Nothing
        | isBufferEmpty = maybeData
        | otherwise = Just $ ringData !! tailI

      newState :: RingBufferState n m a
      newState = (newData, newHead, newTail)
      newData :: RingBufferData n a
      newData
        | readReq && isBufferEmpty = ringData
        | isJust maybeData && not isBufferFull =
            replace headI (fromJust maybeData) ringData
        | otherwise = ringData
      newHead :: Unsigned m
      newHead
        | readReq && isBufferEmpty = headI
        | isJust maybeData && not isBufferFull = headI + 1
        | isJust maybeData && isBufferFull = errorX "Writing while fifo full"
        | otherwise = headI
      newTail :: Unsigned m
      newTail
        | readReq && isBufferEmpty = tailI
        | not readReq = tailI
        | isBufferEmpty = tailI
        | otherwise = tailI + 1

      isBufferEmpty, isBufferFull :: Bool
      isBufferEmpty = headI == tailI
      isBufferFull = headI + 1 == tailI

