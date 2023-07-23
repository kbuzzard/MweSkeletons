class Zero (α : Type u) where
  zero : α

instance Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1

instance Zero.ofOfNat0 {α} [OfNat α (nat_lit 0)] : Zero α where
  zero := 0

class One (α : Type u) where
  one : α

instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

instance One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

class MulZeroClass (M₀ : Type _) extends Mul M₀, Zero M₀ where
  zero_mul : ∀ a : M₀, 0 * a = 0
  mul_zero : ∀ a : M₀, a * 0 = 0

class AddSemigroup (G : Type u) extends Add G where
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

class Semigroup (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

class CommSemigroup (G : Type u) extends Semigroup G where
  mul_comm : ∀ a b : G, a * b = b * a

class AddCommSemigroup (G : Type u) extends AddSemigroup G where
  add_comm : ∀ a b : G, a + b = b + a

class SemigroupWithZero (S₀ : Type _) extends Semigroup S₀, MulZeroClass S₀

class MulOneClass (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a

class AddZeroClass (M : Type u) extends Zero M, Add M where
  zero_add : ∀ a : M, 0 + a = a
  add_zero : ∀ a : M, a + 0 = a

class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀

class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where

class Monoid (M : Type u) extends Semigroup M, MulOneClass M where

class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀

class LeftCancelSemigroup (G : Type u) extends Semigroup G where
  mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c

class LeftCancelMonoid (M : Type u) extends LeftCancelSemigroup M, Monoid M

class RightCancelSemigroup (G : Type u) extends Semigroup G where
  mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c

class RightCancelMonoid (M : Type u) extends RightCancelSemigroup M, Monoid M

class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M

class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  sub a b := a + -b
  sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by intros; rfl

class AddGroup (A : Type u) extends SubNegMonoid A where
  add_left_neg : ∀ a : A, -a + a = 0

class AddMonoidWithOne (R : Type u) extends AddMonoid R, One R where

class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M

class AddGroupWithOne (R : Type u) extends AddMonoidWithOne R, AddGroup R where

class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

class Distrib (R : Type _) extends Mul R, Add R where
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α

class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

class AddCommMonoidWithOne (R : Type _) extends AddMonoidWithOne R, AddCommMonoid R

class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α

class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α

class NonUnitalCommSemiring (α : Type u) extends NonUnitalSemiring α, CommSemigroup α

class CommSemiring (R : Type u) extends Semiring R, CommMonoid R

class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α, NonUnitalNonAssocSemiring α

class NonUnitalRing (α : Type _) extends NonUnitalNonAssocRing α, NonUnitalSemiring α

class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R



class NonUnitalCommRing (α : Type u) extends NonUnitalRing α, CommSemigroup α

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalCommRing.toNonUnitalCommSemiring [s : NonUnitalCommRing α] :
    NonUnitalCommSemiring α :=
  { s with }

class CommRing (α : Type u) extends Ring α, CommMonoid α

instance (priority := 100) CommRing.toCommSemiring [s : CommRing α] : CommSemiring α :=
  { s with }

instance (priority := 100) CommSemiring.toNonUnitalCommSemiring [CommSemiring α] :
    NonUnitalCommSemiring α :=
  { inferInstanceAs (CommMonoid α), inferInstanceAs (CommSemiring α) with }

instance (priority := 100) CommRing.toNonUnitalCommRing [s : CommRing α] : NonUnitalCommRing α :=
  { s with }

set_option pp.all true
set_option trace.Meta.synthInstance true

-- NUCS->NUS
-- CS->NUCS
-- CR->CS

-- NUR->NUS
-- NUCR->NUR
-- CR->NUCR

class StarRing' (R : Type _) [NonUnitalSemiring R]
def starGizmo [CommSemiring R] [StarRing' R] : R → R := id
theorem starGizmo_foo [CommRing R] [StarRing' R] (x : R) : starGizmo x = x := rfl

--set_option pp.all true
--set_option trace.Meta.synthInstance true
