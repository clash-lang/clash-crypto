{-# OPTIONS_GHC -funfolding-creation-threshold=0 #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE RecordWildCards #-}

-- | Algorithm to sign a payload using ECDSA expressed in the instructions of
-- the calculator. In the documentation stacks are represented as an
-- unpunctuated list @x y z@, where @x@ is the top of the stack. Curve points
-- are stored as two quantities, and are written @x y@ or jointly @{r}@,
-- representing two elements on the stack. The two quantities represent the
-- affine coordinate of the point, except @0 0@, which represents the infinite
-- point, denoted O.
module Clash.Crypto.ECDSA.Algorithm where

import Data.Type.Ord (Compare)

import Clash.Crypto.Calculator.ISA
import Clash.Prelude
import Clash.Class.Counter (Counter(..))

-- | Weierstrass elliptic curve of the form @y² = x³ + Ax + B@ over a Galois
-- field of a prime order, and a base point @G@ (loosely: generator) of prime
-- order in the elliptic curve.
data Curve p a =
  Curve
  { curveFieldPrime     ∷ p
  , curveFieldMsb       ∷ a
  , curveParameterA     ∷ a
  , curveParameterB     ∷ a
  , curveBasePoint      ∷ (a, a)
  , curveBasePointOrder ∷ p
  }

type family Q  c where Q  ('Curve q _ _ _ '(_, _) _) = q
type family QL c where QL ('Curve _ l _ _ '(_, _) _) = l
type family A  c where A  ('Curve _ _ a _ '(_, _) _) = a
type family B  c where B  ('Curve _ _ _ b '(_, _) _) = b
type family GX c where GX ('Curve _ _ _ _ '(x, _) _) = x
type family GY c where GY ('Curve _ _ _ _ '(_, y) _) = y
type family N  c where N  ('Curve _ _ _ _ '(_, _) n) = n

type KnownCurve c =
  ( KnownNat (QL c)
  , KnownNat (A c)
  , KnownNat (B c)
  , KnownNat (GX c)
  , KnownNat (GY c)
  , KnownNat (Q c)
  , KnownNat (N c)
  )

type SECP256R1 ∷ Curve Nat Nat
type SECP256R1 =
  'Curve
    {- curveFieldPrime     -}
    0xffffffff_00000001_00000000_00000000_00000000_ffffffff_ffffffff_ffffffff
    {- curveFieldBitSize   -}
    0x00000000_00000000_00000000_00000000_00000000_00000000_00000000_000000ff
    {- curveParameterA     -}
    0xffffffff_00000001_00000000_00000000_00000000_ffffffff_ffffffff_fffffffc
    {- curveParameterB     -}
    0x5ac635d8_aa3a93e7_b3ebbd55_769886bc_651d06b0_cc53b0f6_3bce3c3e_27d2604b
    {- curveBasePoint      -}
 '( 0x6b17d1f2_e12c4247_f8bce6e5_63a440f2_77037d81_2deb33a0_f4a13945_d898c296
  , 0x4fe342e2_fe1a7f9b_8ee7eb4a_7c0f9e16_2bce3357_6b315ece_cbb64068_37bf51f5
  ) {- curveBasePointOrder -}
    0xffffffff_00000000_ffffffff_ffffffff_bce6faad_a7179e84_f3b9cac2_fc632551

data Routine p a (c ∷ Curve p a)
  -- | Perform the elliptic curve digital signature algorithm on a hash value
  -- @h@ given a nonce @k@ and the private key @d@. The value returned is @r s@,
  -- given by:
  -- - @r = (kG)ₓ  (mod N)@
  -- - @s = k⁻¹(h + r · d)  (mod N)@
  --
  -- __REQUIRES__ that:
  -- - @h@ is truncated to the bit length of @n@. @h@ need not be less than @n@.
  -- - @0 < k < N@. This is also satisfied by the generation algorithm for @k@
  --   in the case of deterministic ECDSA.
  --
  -- Note that @r@ or @s@ may be zero, in which case the result is considered a
  -- failure. In the case of deterministic ECDSA this means the (hash of) this
  -- message cannot be signed using @d@.
  = SignHash
  -- | Given a scalar and a curve point @{r} s@, compute the scalar multiplication
  -- @{sr}@. The result is computed by repeatedly doubling @r@, and adding the
  -- value to an accumulator when the corresponding bit in @s@ is set.
  | PointScalarMul
  | PointScalarMulStep
  -- | Given two curve points @{r₁} {r₂}@: compute their addition @{r}@.
  -- Addition is defined as the point opposing the third distinct point found
  -- when intersecting the curve with the line intersecting r₁ and r₂. The
  -- opposing point of a point is understood to be the point reflected in the
  -- x-axis, noting that the curve is symmetric in that axis, given that y only
  -- occurs squared in the formula defining the curve. In the case that either
  -- point is the infinite point, the result is the other point, making O the
  -- identity element of curve point addition. There are several special cases
  -- where no such third point can be found for two non-infinite points:
  --
  -- * When the interescting line is vertical. In this case we also return O,
  --   making the opposing point the additive inverse.
  -- * When @r₁ = r₂@ the intersecting line is that defined by the limit of r₁
  --   approaching r₂, i.e. the tangent to the curve at that point.
  -- * When one of the points is an inflection point, say r₁, we find the third
  --   point by approaching r₁ in the limit. The third point becomes arbitrarily
  --   close to r₁, making the result -r₁.
  --   TODO I don't buy that this is accurate - inflection points do not
  --   characterize points at which there is no third intersecting point.
  --
  -- The algorithm is:
  -- * Determine whether @r₁ = r₂@
  -- * Obtain the slope @s@, and store the divisor @d@ separately:
  --   * When @r₁ = r₂@, it is @(3x₁² + A) / 2y₁@.
  --   * When @r₁ ≠ r₂@, it is @(y₁ - y₂) / (x₁ - x₂)@
  -- * Obtain a value @valid@ that is the disjunction of all the cases that need
  --   to return special values; negated:
  --   * Check whether the earlier divisor is zero, i.e. the slope is vertical
  --   * Check whether @r₁ = O@
  --   * Check whether @r₂ = O@
  -- * Compute @r'@, which is given algebraically:
  --   * @x' = s · s - x₁ - x₂@
  --   * @y' = s · (x₁ - x') - y₁@
  -- * Multiply @x'@ and @y'@ by @valid@, which makes the result @O@ when
  --   @¬valid@.
  -- * Add @r₂@ to the result when @r₁ = O@
  -- * Add @r₁@ to the result when @r₂ = O@
  | PointAddMain
  | PointAddI1
  | PointAddI2
  | PointAddI3
  -- | Replace the top element with 0 if the top is 0, and 1 otherwise.
  | IsZero
  deriving (Generic, NFDataX, BitPack, Ord, Eq, Show)

type family RoutineIndex (r ∷ Routine p a c) ∷ Nat where
  RoutineIndex SignHash           = 0
  RoutineIndex PointScalarMul     = 1
  RoutineIndex PointScalarMulStep = 2
  RoutineIndex PointAddI1         = 3
  RoutineIndex PointAddI2         = 4
  RoutineIndex PointAddI3         = 5
  RoutineIndex PointAddMain       = 6
  RoutineIndex IsZero             = 7

type instance Compare (r₁ ∷ Routine p a c) (r₂ ∷ Routine p a c) =
  Compare (RoutineIndex r₁) (RoutineIndex r₂)

type Q'  = Q SECP256R1
type N'  = N SECP256R1
type QL' = QL SECP256R1
type GX' = GX SECP256R1
type GY' = GY SECP256R1
type A'  = A SECP256R1

instance KnownRoutine (IsZero ∷ Routine Nat Nat SECP256R1) where
  routine _ = IsZero
  knownRoutine = RoutineFacts
  type Instructions (IsZero ∷ Routine Nat Nat SECP256R1) =
    -- x
   '[ CUP 0
    , PUT 1
    , SUB Q'
    , PUT QL'
    , BIT Q'
    -- (msb(x-1)=1) x
    , SWP 1
    , PUT QL'
    , BIT Q'
    -- (msb(x)=1) (msb(x-1)=1)
    , PUT 1
    , SWP 1
    , SUB Q'
    , MUL Q'
    -- (msb(x)=0 ∧ msb(x-1)=1)
    -- (x=0)
    ]

instance KnownRoutine (PointAddI1 ∷ Routine Nat Nat SECP256R1) where
  routine _ = PointAddI1
  knownRoutine = RoutineFacts
  type Instructions (PointAddI1 ∷ Routine Nat Nat SECP256R1) =
   '[ CUP 3
    , CUP 2
    , SUB Q'
    , RUN 1 IsZero
    -- (y₁=y₂) {r₁} {r₂}
    , CUP 3
    , CUP 2
    , SUB Q'
    , RUN 1 IsZero
    -- (x₁=x₂) (y₁=y₂) {r₁} {r₂}
    , MUL Q'
    -- (r₁=r₂) {r₁} {r₂}
    , PUT 1
    , CUP 1
    , SUB Q'
    -- (r₁≠r₂) (r₁=r₂) {r₁} {r₂}
    , CUP 2
    , CUP 5
    , SUB Q'
    , MUL Q'
    -- (r₁≠r₂)·(x₁-x₂) (r₁=r₂) {r₁} {r₂}
    , CUP 3
    , CUP 0
    , ADD Q'
    , CUP 2
    , MUL Q'
    -- (r₁=r₂)·2y₁ (r₁≠r₂)·(x₁-x₂) (r₁=r₂) {r₁} {r₂}
    , ADD Q'
    -- d (r₁=r₂) {r₁} {r₂}
    -- d (r₁=r₂) {r₁} {r₂}
    , CUP 5
    , RUN 1 IsZero
    , CUP 5
    , RUN 1 IsZero
    , MUL Q'
    -- (r₂=O) d (r₁=r₂) {r₁} {r₂}
    ]

instance KnownRoutine (PointAddI2 ∷ Routine Nat Nat SECP256R1) where
  routine _ = PointAddI2
  knownRoutine = RoutineFacts
  type Instructions (PointAddI2 ∷ Routine Nat Nat SECP256R1) =
   '[ CUP 6
    , CUP 9
    , SUB Q'
    , PUT 1
    , CUP 6
    , SUB Q'
    , MUL Q'
    -- (r1≠r₂)·(y₁-y₂) valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 6
    , CUP 0
    , MUL Q'
    , CUP 0
    , CUP 0
    , ADD Q'
    , ADD Q'
    , PUT A'
    , ADD Q'
    , CUP 6
    , MUL Q'
    -- (r₁=r₂)·(3x₁²+A) (r₁≠r₂)·(y₁-y₂) valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , ADD Q'
    , CUP 4
    , PUT 0
    , INV Q'
    , MUL Q'
    -- s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 0
    , CUP 0
    , MUL Q'
    , CUP 7
    , SUB Q'
    , CUP 9
    , SUB Q'
    ]

instance KnownRoutine (PointAddI3 ∷ Routine Nat Nat SECP256R1) where
  routine _ = PointAddI3
  knownRoutine = RoutineFacts
  type Instructions (PointAddI3 ∷ Routine Nat Nat SECP256R1) =
    -- x s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
   '[ CUP 7
    , CUP 1
    , SUB Q'
    , CUP 2
    , MUL Q'
    , CUP 9
    , SUB Q'
    , CUP 3
    , MUL Q'
    -- y·valid x s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 9
    , CUP 6
    , MUL Q'
    , ADD Q'
    , CUP 11
    , CUP 5
    , MUL Q'
    , ADD Q'
    -- y x s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , SWP 11
    , POP 1
    -- x s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} x₁ y
    , SWP 9
    ]

instance KnownRoutine (PointAddMain ∷ Routine Nat Nat SECP256R1) where
  routine _ = PointAddMain
  knownRoutine = RoutineFacts
  type Instructions (PointAddMain ∷ Routine Nat Nat SECP256R1) =
    -- {r₁} {r₂}
    -- x₁ y₁ x₂ y₂
   '[ RUN 1 PointAddI1
    , CUP 4
    , RUN 1 IsZero
    , CUP 4
    , RUN 1 IsZero
    , MUL Q'
    -- (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , PUT 1
    , CUP 3
    , RUN 1 IsZero
    , SUB Q'
    -- (d≠0) (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , PUT 1
    , CUP 3
    , SUB Q'
    , PUT 1
    , CUP 3
    , SUB Q'
    , MUL Q'
    , MUL Q'
    -- (r₁≠O ∧ r₂≠O ∧ d≠0) (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    -- valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , RUN 1 PointAddI2
    -- (s²-x₁-x₂) s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    -- x' s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 2
    , MUL Q'
    -- x'·valid s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 7
    , CUP 5
    , MUL Q'
    , ADD Q'
    -- (x'·valid + x₁·(r₂=O)) s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 9
    , CUP 4
    , MUL Q'
    , ADD Q'
    -- (x'·valid + x₁·(r₂=O) + x₂·(r₁=O)) s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , RUN 1 PointAddI3
    , POP 9
    -- x y
    -- {r}
    ]

instance KnownRoutine (PointScalarMulStep ∷ Routine Nat Nat SECP256R1) where
  routine _ = PointScalarMulStep
  knownRoutine = RoutineFacts
  type Instructions (PointScalarMulStep ∷ Routine Nat Nat SECP256R1) =
    -- {acc} {2^bit·r} s bit
   '[ CUP 4
    , CUP 6
    , BIT Q'
    -- s[bit] {acc} {2^bit·r} s bit
    , CUP 0
    , CUP 5
    , MUL Q'
    , SWP 1
    , CUP 4
    , MUL Q'
    -- {s[bit]·2^bit·r} {acc} {2^bit·r} s bit
    , RUN 1 PointAddMain
    -- {acc'} {2^bit·r} s bit
    , CUP 3
    , CUP 3
    , CUP 1
    , CUP 1
    , RUN 1 PointAddMain
    , SWP 4
    , POP 1
    , SWP 4
    , POP 1
    -- {acc'} {2^(bit+1)·r} s bit
    , CUP 5
    , PUT 1
    , ADD Q'
    , SWP 6
    , POP 1
    -- {acc'} {2^bit'·r} s bit'
    ]

instance KnownRoutine (PointScalarMul ∷ Routine Nat Nat SECP256R1) where
  routine _ = PointScalarMul
  knownRoutine = RoutineFacts
  type Instructions (PointScalarMul ∷ Routine Nat Nat SECP256R1) =
    -- {r} s
   '[ PUT 0
    , SWP 3
    , SWP 2
    , SWP 1
    -- {r} s 0
    , PUT 0
    , PUT 0
    -- 0 {r} s 0
    -- acc {2^bit·r} s bit
    , RUN {- FIXME (1 + QL c) -} 256 PointScalarMulStep
    -- {s·r} {_} _ _
    , SWP 4
    , POP 1
    , SWP 4
    , POP 3
    -- {s·r}
    ]

instance KnownRoutine (SignHash ∷ Routine Nat Nat SECP256R1) where
  routine _ = SignHash
  knownRoutine = RoutineFacts
  type Instructions (SignHash ∷ Routine Nat Nat SECP256R1) =
    -- h k d
   '[ CUP 1
    , PUT GY'
    , PUT GX'
    , RUN 1 PointScalarMul
    -- {kG} h k d
    , PUT 0
    , ADD N'
    -- r _ h k d
    , CUP 4
    , CUP 1
    , MUL N'
    , CUP 3
    , ADD N'
    , CUP 4
    , PUT 0
    , INV N'
    , MUL N'
    -- s r _ h k d
    , SWP 5
    , POP 1
    , SWP 3
    , POP 3
    -- r s
    ]

type SignHashRIndex (r ∷ Routine Nat Nat SECP256R1) =
  RIndex (SignHash ∷ Routine Nat Nat SECP256R1) r

data EcdsaIP
  = IPSignHash           (SignHashRIndex SignHash)
  | IPPointScalarMul     (SignHashRIndex PointScalarMul)
  | IPPointScalarMulStep (SignHashRIndex PointScalarMulStep)
  | IPPointAddMain       (SignHashRIndex PointAddMain)
  | IPPointAddI1         (SignHashRIndex PointAddI1)
  | IPPointAddI2         (SignHashRIndex PointAddI2)
  | IPPointAddI3         (SignHashRIndex PointAddI3)
  | IPIsZero             (SignHashRIndex IsZero)
  | EndOfSequence
  deriving (Generic, NFDataX, Show)

instance InstructionPointer (SignHash :: Routine Nat Nat SECP256R1) EcdsaIP where
  inc _ = \case
    IPSignHash n           | (False, m) ← countSuccOverflow n → IPSignHash m
    IPPointScalarMul n     | (False, m) ← countSuccOverflow n → IPPointScalarMul m
    IPPointScalarMulStep n | (False, m) ← countSuccOverflow n → IPPointScalarMulStep m
    IPPointAddMain n       | (False, m) ← countSuccOverflow n → IPPointAddMain m
    IPPointAddI1 n         | (False, m) ← countSuccOverflow n → IPPointAddI1 m
    IPPointAddI2 n         | (False, m) ← countSuccOverflow n → IPPointAddI2 m
    IPPointAddI3 n         | (False, m) ← countSuccOverflow n → IPPointAddI3 m
    IPIsZero n             | (False, m) ← countSuccOverflow n → IPIsZero m
    _ → EndOfSequence

  start _ = \case
    SignHash
      | USucc{} ← toUNat (SNat @(InstructionCount (SignHash :: Routine Nat Nat SECP256R1)))
      → IPSignHash . RIndex 0
    PointScalarMul
      | USucc{} ← toUNat (SNat @(InstructionCount (PointScalarMul :: Routine Nat Nat SECP256R1)))
      → IPPointScalarMul . RIndex 0
    PointScalarMulStep
      | USucc{} ← toUNat (SNat @(InstructionCount (PointScalarMulStep :: Routine Nat Nat SECP256R1)))
      → IPPointScalarMulStep . RIndex 0
    PointAddMain
      | USucc{} ← toUNat (SNat @(InstructionCount (PointAddMain :: Routine Nat Nat SECP256R1)))
      → IPPointAddMain . RIndex 0
    PointAddI1
      | USucc{} ← toUNat (SNat @(InstructionCount (PointAddI1 :: Routine Nat Nat SECP256R1)))
      → IPPointAddI1 . RIndex 0
    PointAddI2
      | USucc{} ← toUNat (SNat @(InstructionCount (PointAddI2 :: Routine Nat Nat SECP256R1)))
      → IPPointAddI2 . RIndex 0
    PointAddI3
      | USucc{} ← toUNat (SNat @(InstructionCount (PointAddI3 :: Routine Nat Nat SECP256R1)))
      → IPPointAddI3 . RIndex 0
    IsZero
      | USucc{} ← toUNat (SNat @(InstructionCount (IsZero :: Routine Nat Nat SECP256R1)))
      → IPIsZero . RIndex 0

  instr @a _ = \case
    IPSignHash RIndex{..}
      | RoutineFacts ← knownRoutine @_ @(SignHash :: Routine Nat Nat SECP256R1) @a
      → pure $ instructions SignHash SignHash !! iptr
    IPPointScalarMul RIndex{..}
      | RoutineFacts ← knownRoutine @_ @(PointScalarMul :: Routine Nat Nat SECP256R1) @a
      → pure $ instructions SignHash PointScalarMul !! iptr
    IPPointScalarMulStep RIndex{..}
      | RoutineFacts ← knownRoutine @_ @(PointScalarMulStep :: Routine Nat Nat SECP256R1) @a
      → pure $ instructions SignHash PointScalarMulStep !! iptr
    IPPointAddMain RIndex{..}
      | RoutineFacts ← knownRoutine @_ @(PointAddMain :: Routine Nat Nat SECP256R1) @a
      → pure $ instructions SignHash PointAddMain !! iptr
    IPPointAddI1 RIndex{..}
      | RoutineFacts ← knownRoutine @_ @(PointAddI1 :: Routine Nat Nat SECP256R1) @a
      → pure $ instructions SignHash PointAddI1 !! iptr
    IPPointAddI2 RIndex{..}
      | RoutineFacts ← knownRoutine @_ @(PointAddI2 :: Routine Nat Nat SECP256R1) @a
      → pure $ instructions SignHash PointAddI2 !! iptr
    IPPointAddI3 RIndex{..}
      | RoutineFacts ← knownRoutine @_ @(PointAddI3 :: Routine Nat Nat SECP256R1) @a
      → pure $ instructions SignHash PointAddI3 !! iptr
    IPIsZero RIndex{..}
      | RoutineFacts ← knownRoutine @_ @(IsZero :: Routine Nat Nat SECP256R1) @a
      → pure $ instructions SignHash IsZero !! iptr
    _ → Nothing
