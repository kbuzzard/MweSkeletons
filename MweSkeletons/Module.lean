/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
--import Mathlib.Algebra.SMulWithZero
import MweSkeletons.CommRing

open Function

universe u v

variable {α R k S M M₂ M₃ ι : Type _}

class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a • b` computes the product of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hSMul : α → β → γ

class SMul (M : Type _) (α : Type _) where
  smul : M → α → α

infixr:73 " • " => HSMul.hSMul

instance instHSMul [SMul α β] : HSMul α β β where
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

class MulActionWithZero (R : Type _) (M : Type _) [MonoidWithZero R] [Zero M] extends MulAction R M where
  smul_zero : ∀ r : R, r • (0 : M) = 0
  zero_smul : ∀ m : M, (0 : R) • m = 0

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

instance (priority := 910) Semiring.toModule [Semiring R] : Module R R where
  smul_add := mul_add
  add_smul := add_mul
  zero_smul := zero_mul
  smul_zero := mul_zero

-- fields missing: 'smul', 'one_smul', 'mul_smul'