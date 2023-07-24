import MweSkeletons.RingHom
import MweSkeletons.Module

class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends SMul R A,
  R →+* A where
  commutes' : ∀ r x, toRingHom r * x = x * toRingHom r
  smul_def' : ∀ r x, r • x = toRingHom r * x

namespace Algebra

instance id {R : Type _} [CommSemiring R] : Algebra R R :=
  (RingHom.id R).toAlgebra

end Algebra

instance (priority := 910) Semiring.toModule [Semiring R] : Module R R where
  smul_add := mul_add
  add_smul := add_mul
  zero_smul := zero_mul
  smul_zero := mul_zero

-- fields missing: 'smul', 'one_smul', 'mul_smul'