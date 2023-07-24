import MweSkeletons.Module

def Set (α : Type u) := α → Prop

namespace Set

protected def Mem (a : α) (s : Set α) : Prop :=
  s a

instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

end Set

structure AddSubsemigroup (M : Type _) [Add M] where
  /-- The carrier of an additive subsemigroup. -/
  carrier : Set M
  /-- The sum of two elements of an additive subsemigroup belongs to the subsemigroup. -/
  add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier

structure AddSubmonoid (M : Type _) [AddZeroClass M] extends AddSubsemigroup M where
  /-- An additive submonoid contains `0`. -/
  zero_mem' : (0 : M) ∈ carrier

structure SubMulAction (R : Type u) (M : Type v) [SMul R M] : Type v where
  /-- The underlying set of a `SubMulAction`. -/
  carrier : Set M
  /-- The carrier set is closed under scalar multiplication. -/
  smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier

structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] extends
  AddSubmonoid M, SubMulAction R M : Type v

@[reducible]
def Ideal (R : Type u) [Semiring R] :=
  Submodule R R

/-
failed to synthesize instance
  Module R R
-/