/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
--import Mathlib.Algebra.SMulWithZero
import MweSkeletons.CommRing
set_option autoImplicit false

open Function

universe u v w

variable {α R k S M M₂ M₃ ι : Type _}

class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a • b` computes the product of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hSMul : α → β → γ

class SMul (M : Type _) (α : Type _) where
  smul : M → α → α

infixr:73 " • " => HSMul.hSMul

instance instHSMul {α β : Type _} [SMul α β] : HSMul α β β where
  hSMul := SMul.smul

class MulAction (α : Type _) (β : Type _) [Monoid α] extends SMul α β where
  /-- One is the neutral element for `•` -/
  protected one_smul : ∀ b : β, (1 : α) • b = b
  /-- Associativity of `•` and `*` -/
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b

class DistribMulAction (M A : Type _) [Monoid M] [AddMonoid A] extends MulAction M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : ∀ a : M, a • (0 : A) = 0
  /-- Scalar multiplication distributes across addition -/
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y

--@[to_additive]
instance (priority := 910) Monoid.toMulAction (M : Type _) [Monoid M] :
    MulAction M M where
  smul := (· * ·)
  one_smul := one_mul
  mul_smul := sorry

class SMulZeroClass (M A : Type _) [Zero A] extends SMul M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : ∀ a : M, a • (0 : A) = 0

/-- `SMulWithZero` is a class consisting of a Type `R` with `0 ∈ R` and a scalar multiplication
of `R` on a Type `M` with `0`, such that the equality `r • m = 0` holds if at least one among `r`
or `m` equals `0`. -/
class SMulWithZero (R M : Type _) [Zero R] [Zero M] extends SMulZeroClass R M where
  /-- Scalar multiplication by the scalar `0` is `0`. -/
  zero_smul : ∀ m : M, (0 : R) • m = 0

instance MulZeroClass.toSMulWithZero (R : Type _) [MulZeroClass R] : SMulWithZero R R where
  smul := (· * ·)
  smul_zero := mul_zero
  zero_smul := zero_mul

class MulActionWithZero (R : Type _) (M : Type _) [MonoidWithZero R] [Zero M] extends MulAction R M where
  smul_zero : ∀ r : R, r • (0 : M) = 0
  zero_smul : ∀ m : M, (0 : R) • m = 0

-- see Note [lower instance priority]
instance (priority := 100) MulActionWithZero.toSMulWithZero (R M : Type _) [MonoidWithZero R] [Zero M] 
    [m : MulActionWithZero R M] : SMulWithZero R M :=
  { m with }

/-- See also `Semiring.toModule` -/
instance MonoidWithZero.toMulActionWithZero (R : Type _) [MonoidWithZero R] : MulActionWithZero R R :=
  { MulZeroClass.toSMulWithZero R, Monoid.toMulAction R with }

class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
  DistribMulAction R M where
  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  protected zero_smul : ∀ x : M, (0 : R) • x = 0

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x y : M)

-- see Note [lower instance priority]
/-- A module over a semiring automatically inherits a `MulActionWithZero` structure. -/
instance (priority := 100) Module.toMulActionWithZero : MulActionWithZero R M :=
  { (inferInstance : MulAction R M) with
    smul_zero := sorry
    zero_smul := sorry }

end AddCommMonoid

