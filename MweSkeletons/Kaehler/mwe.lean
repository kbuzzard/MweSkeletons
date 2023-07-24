import Mathlib.RingTheory.TensorProduct
--import MweSkeletons.Ideal
--import MweSkeletons.Quotient

set_option autoImplicit false

namespace Module

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] {I : Ideal R} 

@[reducible]
def IsTorsionBySet (s : Set R) :=
  ∀ ⦃x : M⦄ ⦃a : s⦄, (a : R) • x = 0

variable (hM : IsTorsionBySet R M I)

variable {R M}

def IsTorsionBySet.hasSMul {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} (hM : IsTorsionBySet R M ↑I) : SMul (R ⧸ I) M where
  smul b x := Quotient.liftOn' b (· • x) sorry

def IsTorsionBySet.module : Module (R ⧸ I) M :=
  @Function.Surjective.moduleLeft _ _ _ _ _ _ _ hM.hasSMul (Ideal.Quotient.mk I) sorry sorry

instance : Module (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
  IsTorsionBySet.module (R := R) (I := I) fun x r => sorry

end Module

namespace Ideal

variable {R : Type} {S : Type} {S' : Type} [CommRing R] [CommSemiring S] [Algebra S R]

variable [CommSemiring S'] [Algebra S' R] [Algebra S S'] [IsScalarTower S S' R] 

variable (I : Ideal R)

def Cotangent : Type _ := I ⧸ (I • ⊤ : Submodule R I)

instance : AddCommGroup I.Cotangent := by delta Cotangent; infer_instance

instance cotangentModule : Module (R ⧸ I) I.Cotangent := by 
  delta Cotangent
  infer_instance

instance Cotangent.moduleOfTower : Module S I.Cotangent :=
  Submodule.Quotient.module' _

instance Cotangent.isScalarTower : IsScalarTower S S' I.Cotangent := sorry

def toCotangent : I →ₗ[R] I.Cotangent := Submodule.mkQ _

end Ideal

open scoped TensorProduct

/-- The kernel of the multiplication map `S ⊗[R] S →ₐ[R] S`. -/
abbrev KaehlerDifferential.ideal (R : Type) (S : Type) [CommRing R] [CommRing S] [Algebra R S] : Ideal (S ⊗[R] S) :=
  RingHom.ker (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S)

set_option synthInstance.maxHeartbeats 40000 in
lemma KaehlerDifferential.slow {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {M : Type} [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M] (a b : S) :
    False := by
  set_option trace.profiler true in
  set_option pp.proofs.withType false in
  have foo := LinearMap.map_smul_of_tower (Ideal.toCotangent (ideal R S)) a
  /-
  [Elab.step] [3.587504s] 
      have foo := LinearMap.map_smul_of_tower (Ideal.toCotangent (ideal R S)) a
      sorry ▶
  -/
  sorry

