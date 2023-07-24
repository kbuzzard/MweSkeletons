import MweSkeletons.Submodule
import MweSkeletons.Algebra

@[reducible]
def Ideal (R : Type u) [Semiring R] :=
  Submodule R R
