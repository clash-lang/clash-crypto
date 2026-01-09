{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Algorithm to sign a payload using ECDSA expressed in the instructions of
-- the calculator. In the documentation stacks are represented as an
-- unpunctuated list @x y z@, where @x@ is the top of the stack. Curve points
-- are stored as two quantities, and are written @x y@ or jointly @{r}@,
-- representing two elements on the stack. The two quantities represent the
-- affine coordinate of the point, except @0 0@, which represents the infinite
-- point, denoted O.
module Clash.Crypto.ECDSA.Algorithm where

import Prelude
import Data.Type.Ord (Compare)
import GHC.TypeNats (Nat, KnownNat)

import Clash.Crypto.Calculator.ISA

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
  ( KnownNat (Q c)
  , KnownNat (QL c)
  , KnownNat (A c)
  , KnownNat (B c)
  , KnownNat (GX c)
  , KnownNat (GY c)
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
  -- value when the corresponding bit in @s@ is set.
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
  --   making such an opposing point the additive inverse.
  -- * When @r₁ = r₂@ the intersecting line is that defined by the limit of r₁
  --   and r₂ approaching each other, i.e. the tangent to the curve at that
  --   point.
  -- * When one of the points is an inflection point, say r₁, we find the third
  --   point by approaching r₁ in the limit. The third point becomes arbitrarily
  --   close to r₁, making the result -r₁.
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
  | PointAdd
  -- | Replace the top element with 0 if the top is 0, and 1 otherwise.
  | IsZero
  deriving (Eq, Show)

type family RoutineIndex (r ∷ Routine p a c) ∷ Nat where
  RoutineIndex SignHash               = 0
  RoutineIndex PointScalarMul         = 1
  RoutineIndex PointScalarMulStep     = 2
  RoutineIndex PointAdd               = 3
  RoutineIndex IsZero              = 4

type instance Compare (r₁ ∷ Routine p a c) (r₂ ∷ Routine p a c) =
  Compare (RoutineIndex r₁) (RoutineIndex r₂)

instance KnownCurve c => KnownRoutine (IsZero ∷ Routine Nat Nat c) where
  routine _ = IsZero
  knownRoutine = RoutineFacts
  type Instructions (IsZero ∷ Routine Nat Nat c) =
    -- x
   '[ CUP 0
    , PUT 1
    , SUB (Q c)
    , PUT (QL c)
    , BIT (Q c)
    -- (msb(x-1)=1) x
    , SWP 1
    , PUT (QL c)
    , BIT (Q c)
    -- (msb(x)=1) (msb(x-1)=1)
    , PUT 1
    , SWP 1
    , SUB (Q c)
    , MUL (Q c)
    -- (msb(x)=0 ∧ msb(x-1)=1)
    -- (x=0)
    ]

instance KnownCurve c => KnownRoutine (PointAdd ∷ Routine Nat Nat c) where
  routine _ = PointAdd
  knownRoutine = RoutineFacts
  type Instructions (PointAdd ∷ Routine Nat Nat c) =
    -- {r₁} {r₂}
    -- x₁ y₁ x₂ y₂
   '[ CUP 3
    , CUP 2
    , SUB (Q c)
    , RUN 1 IsZero
    -- (y₁=y₂) {r₁} {r₂}
    , CUP 3
    , CUP 2
    , SUB (Q c)
    , RUN 1 IsZero
    -- (x₁=x₂) (y₁=y₂) {r₁} {r₂}
    , MUL (Q c)
    -- (r₁=r₂) {r₁} {r₂}
    , PUT 1
    , CUP 1
    , SUB (Q c)
    -- (r₁≠r₂) (r₁=r₂) {r₁} {r₂}
    , CUP 2
    , CUP 5
    , SUB (Q c)
    , MUL (Q c)
    -- (r₁≠r₂)·(x₁-x₂) (r₁=r₂) {r₁} {r₂}
    , CUP 3
    , CUP 0
    , ADD (Q c)
    , CUP 2
    , MUL (Q c)
    -- (r₁=r₂)·2y₁ (r₁≠r₂)·(x₁-x₂) (r₁=r₂) {r₁} {r₂}
    , ADD (Q c)
    -- d (r₁=r₂) {r₁} {r₂}
    -- d (r₁=r₂) {r₁} {r₂}
    , CUP 5
    , RUN 1 IsZero
    , CUP 5
    , RUN 1 IsZero
    , MUL (Q c)
    -- (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 4
    , RUN 1 IsZero
    , CUP 4
    , RUN 1 IsZero
    , MUL (Q c)
    -- (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , PUT 1
    , CUP 3
    , RUN 1 IsZero
    , SUB (Q c)
    -- (d≠0) (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , PUT 1
    , CUP 3
    , SUB (Q c)
    , PUT 1
    , CUP 3
    , SUB (Q c)
    , MUL (Q c)
    , MUL (Q c)
    -- (r₁≠O ∧ r₂≠O ∧ d≠0) (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    -- valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 6
    , CUP 9
    , SUB (Q c)
    , PUT 1
    , CUP 6
    , SUB (Q c)
    , MUL (Q c)
    -- (r1≠r₂)·(y₁-y₂) valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 6
    , CUP 0
    , MUL (Q c)
    , CUP 0
    , CUP 0
    , ADD (Q c)
    , ADD (Q c)
    , PUT (A c)
    , ADD (Q c)
    , CUP 6
    , MUL (Q c)
    -- (r₁=r₂)·(3x₁²+A) (r₁≠r₂)·(y₁-y₂) valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , ADD (Q c)
    , CUP 4
    , PUT 0
    , INV (Q c)
    , MUL (Q c)
    -- s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 0
    , CUP 0
    , MUL (Q c)
    , CUP 7
    , SUB (Q c)
    , CUP 9
    , SUB (Q c)
    -- (s²-x₁-x₂) s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    -- x' s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 2
    , MUL (Q c)
    -- x'·valid s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 7
    , CUP 5
    , MUL (Q c)
    , ADD (Q c)
    -- (x'·valid + x₁·(r₂=O)) s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 9
    , CUP 4
    , MUL (Q c)
    , ADD (Q c)
    -- (x'·valid + x₁·(r₂=O) + x₂·(r₁=O)) s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    -- x s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 7
    , CUP 1
    , SUB (Q c)
    , CUP 2
    , MUL (Q c)
    , CUP 9
    , SUB (Q c)
    , CUP 3
    , MUL (Q c)
    -- y·valid x s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , CUP 9
    , CUP 6
    , MUL (Q c)
    , ADD (Q c)
    , CUP 11
    , CUP 5
    , MUL (Q c)
    , ADD (Q c)
    -- y x s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} {r₂}
    , SWP 11
    , POP 1
    -- x s valid (r₁=O) (r₂=O) d (r₁=r₂) {r₁} x₁ y
    , SWP 9
    , POP 9
    -- x y
    -- {r}
    ]

instance KnownCurve c => KnownRoutine (PointScalarMulStep ∷ Routine Nat Nat c) where
  routine _ = PointScalarMulStep
  knownRoutine = RoutineFacts
  type Instructions (PointScalarMulStep ∷ Routine Nat Nat c) =
    -- {acc} {2^bit·r} s bit
   '[ CUP 4
    , CUP 6
    , BIT (Q c)
    -- s[bit] {acc} {2^bit·r} s bit
    , CUP 0
    , CUP 5
    , MUL (Q c)
    , SWP 1
    , CUP 4
    , MUL (Q c)
    -- {s[bit]·2^bit·r} {acc} {2^bit·r} s bit
    , RUN 1 PointAdd
    -- {acc'} {2^bit·r} s bit
    , CUP 3
    , CUP 3
    , CUP 1
    , CUP 1
    , RUN 1 PointAdd
    , SWP 4
    , POP 1
    , SWP 4
    , POP 1
    -- {acc'} {2^(bit+1)·r} s bit
    , CUP 5
    , PUT 1
    , ADD (Q c)
    , SWP 6
    , POP 1
    -- {acc'} {2^bit'·r} s bit'
    ]

instance KnownCurve c => KnownRoutine (PointScalarMul ∷ Routine Nat Nat c) where
  routine _ = PointScalarMul
  knownRoutine = RoutineFacts
  type Instructions (PointScalarMul ∷ Routine Nat Nat c) =
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

instance KnownCurve c ⇒ KnownRoutine (SignHash ∷ Routine Nat Nat c) where
  routine _ = SignHash
  knownRoutine = RoutineFacts
  type Instructions (SignHash ∷ Routine Nat Nat c) =
    -- h k d
   '[ CUP 1
    , PUT (GY c)
    , PUT (GX c)
    , RUN 1 PointScalarMul
    -- {kG} h k d
    , PUT 0
    , ADD (N c)
    -- r _ h k d
    , CUP 4
    , CUP 1
    , MUL (N c)
    , CUP 3
    , ADD (N c)
    , CUP 4
    , PUT 0
    , INV (N c)
    , MUL (N c)
    -- s r _ h k d
    , SWP 5
    , POP 1
    , SWP 3
    , POP 3
    -- r s
    ]
