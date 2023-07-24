import MweSkeletons.RingHom
import MweSkeletons.Module

class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends SMul R A,
  R →+* A where
  commutes' : ∀ r x, toRingHom r * x = x * toRingHom r
  smul_def' : ∀ r x, r • x = toRingHom r * x

--RingHom.toAlgebra

/-- Creating an algebra from a morphism to the center of a semiring. -/
def RingHom.toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R →+* S)
    (h : ∀ c x, i c * x = x * i c) : Algebra R S where
  smul c x := i c * x
  commutes' := h
  smul_def' _ _ := rfl
  toRingHom := i

/-- Creating an algebra from a morphism to a commutative semiring. -/
def RingHom.toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R →+* S) : Algebra R S :=
  i.toAlgebra' fun _ => sorry

namespace Algebra

instance id {R : Type _} [CommSemiring R] : Algebra R R :=
  (RingHom.id R).toAlgebra

end Algebra

instance (priority := 910) Semiring.toModule [Semiring R] : Module R R where
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry
  smul_zero := sorry
