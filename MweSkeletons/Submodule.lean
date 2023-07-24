import MweSkeletons.Module
import MweSkeletons.Injective

def Set (α : Type u) := α → Prop

namespace Set

protected def Mem (a : α) (s : Set α) : Prop :=
  s a

instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

@[reducible] def Elem (s : Set α) : Type u := { x // x ∈ s }

instance {α : Type u} : CoeSort (Set α) (Type u) :=
  ⟨Elem⟩

end Set

class SetLike (A : Type _) (B : outParam <| Type _) where
  /-- The coercion from a term of a `SetLike` to its corresponding `Set`. -/
  protected coe : A → Set B
  /-- The coercion from a term of a `SetLike` to its corresponding `Set` is injective. -/
  protected coe_injective' : Function.Injective coe

instance {A : Type _} {B : Type _} [SetLike A B] : CoeTC A (Set B) where coe := SetLike.coe

structure AddSubsemigroup (M : Type _) [Add M] where
  /-- The carrier of an additive subsemigroup. -/
  carrier : Set M
  /-- The sum of two elements of an additive subsemigroup belongs to the subsemigroup. -/
  add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier

structure AddSubmonoid (M : Type _) [AddZeroClass M] extends AddSubsemigroup M where
  /-- An additive submonoid contains `0`. -/
  zero_mem' : (0 : M) ∈ carrier

structure AddSubgroup (G : Type _) [AddGroup G] extends AddSubmonoid G where
  /-- `G` is closed under negation -/
  neg_mem' {x} : x ∈ carrier → -x ∈ carrier

structure SubMulAction (R : Type u) (M : Type v) [SMul R M] : Type v where
  /-- The underlying set of a `SubMulAction`. -/
  carrier : Set M
  /-- The carrier set is closed under scalar multiplication. -/
  smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier

structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] extends
  AddSubmonoid M, SubMulAction R M : Type v

instance Submodule.setLike (R M : Type _) [Semiring R] [AddCommMonoid M] [Module R M] : SetLike (Submodule R M) M where
  coe s := s.carrier
  coe_injective' p q h := sorry

def Submodule.toAddSubgroup {R M : Type _} [Ring R] [AddCommGroup M] {module_M : Module R M} 
    (p : Submodule R M) : AddSubgroup M :=
  { p.toAddSubmonoid with neg_mem' := fun {_} => sorry }
