import MweSkeletons.CommRing
import MweSkeletons.Module

set_option autoImplicit false

namespace Pi

universe v w

variable {I : Type v}

variable {f : I → Type w}

instance instZero [∀ i, Zero <| f i] : Zero (∀ i : I, f i) :=
  ⟨fun _ => 0⟩

variable {M}

instance instSMul [∀ i, SMul M <| f i] : SMul M (∀ i : I, f i) :=
  ⟨fun s x => fun i => s • x i⟩

universe x

variable {α : Type x}

instance smulWithZero [Zero α] [∀ i, Zero (f i)] [∀ i, SMulWithZero α (f i)] :
    SMulWithZero α (∀ i, f i) :=
  { Pi.instSMul with
    -- already this is odd:
    -- smul_zero := fun a => funext fun i => SMulZeroClass.smul_zero a -- "failed to synthesize instance `SMulZeroClass α (f i)`"
    smul_zero := fun a => funext fun i => @SMulZeroClass.smul_zero  _ (f i) _ _ a -- needs the @
    zero_smul := fun _ => funext fun _ => SMulWithZero.zero_smul _ }

instance mulAction (α) {m : Monoid α} [∀ i, MulAction α <| f i] :
    @MulAction α (∀ i : I, f i) m where
  smul := (· • ·)
  mul_smul _ _ _ := funext fun _ => MulAction.mul_smul _ _ _
  one_smul _ := funext fun _ => MulAction.one_smul _

set_option trace.Meta.synthInstance true

set_option maxHeartbeats 10000 -- consider turning trace.Meta.synthInstance to false if you
-- make this number much bigger

set_option trace.Meta.isDefEq true

end Pi
