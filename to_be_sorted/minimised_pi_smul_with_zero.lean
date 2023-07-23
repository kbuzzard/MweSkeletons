
section not_Pi

universe u

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

class Semigroup (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

class SemigroupWithZero (S₀ : Type _) extends Semigroup S₀, MulZeroClass S₀

class MulOneClass (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a

class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀

class Monoid (M : Type u) extends Semigroup M, MulOneClass M where

class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀

class SMul (M : Type _) (α : Type _) where
  smul : M → α → α

class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSMul : α → β → γ

instance instHSMul (M : Type _) (α : Type _) [SMul M α] : HSMul M α α where
  hSMul := SMul.smul

infixr:73 " • " => HSMul.hSMul

class MulAction (α : Type _) (β : Type _) [Monoid α] extends SMul α β where
  protected one_smul : ∀ b : β, (1 : α) • b = b
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b

variable (R M)

class MulActionWithZero [MonoidWithZero R] [Zero M] extends MulAction R M where
  smul_zero : ∀ r : R, r • (0 : M) = 0
  zero_smul : ∀ m : M, (0 : R) • m = 0

class SMulZeroClass (M A : Type _) [Zero A] extends SMul M A where
  smul_zero : ∀ a : M, a • (0 : A) = 0

class SMulWithZero [Zero R] [Zero M] extends SMulZeroClass R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0

instance (priority := 100) MulActionWithZero.toSMulWithZero [MonoidWithZero R] [Zero M] [m : MulActionWithZero R M] :
    SMulWithZero R M :=
  { m with }



end not_Pi

namespace Pi


variable {I : Type v}

variable {f : I → Type w}


universe v w

instance instZero [∀ i, Zero <| f i] : Zero (∀ i : I, f i) :=
  ⟨fun _ => 0⟩

variable {M}

instance instSMul [∀ i, SMul M <| f i] : SMul M (∀ i : I, f i) :=
  ⟨fun s x => fun i => s • x i⟩

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
/-



-/

set_option trace.Meta.synthInstance true

set_option maxHeartbeats 10000 -- consider turning trace.Meta.synthInstance to false if you
-- make this number much bigger

set_option trace.Meta.isDefEq true

set_option pp.universes false
--#print MulActionWithZero.{0 0} -- error
--#print MulActionWithZero

--variable (R M : Type) [Monoid R] in
--#check MulAction R M
--#print MulAction


-- why does a human have to make this instance?
instance Pi.mulActionWithZero {I : Type} {V : I → Type} (k : Type)
    [MonoidWithZero k] [∀ i, Zero (V i)]
    [∀ i, MulActionWithZero k (V i)] : MulActionWithZero k (∀ i, V i) :=
  { Pi.mulAction k, Pi.smulWithZero with } #exit
    smul_zero := Pi.smulWithZero.smul_zero
    zero_smul := Pi.smulWithZero.zero_smul }

    #print Pi.mulActionWithZero

#exit
-- also works


-- but this seems to be looping
instance mulActionWithZero' (α) [MonoidWithZero α] [∀ i, Zero (f i)]
    [∀ i, MulActionWithZero α (f i)] : MulActionWithZero α (∀ i, f i) :=
  { Pi.mulAction α, Pi.smulWithZero with }


/-
Lean claims to not be able to find `MonoidWithZero α` even though it's explicitly given as an instance.

[Meta.synthInstance] 💥 (i : I) → SMulWithZero α (f i) ▼
  [] new goal (i : I) → SMulWithZero α (f i) ▶
  [] 💥 apply MulActionWithZero.toSMulWithZero to (i : I) → SMulWithZero α (f i) ▼
    [tryResolve] 💥 SMulWithZero α (f i) ≟ SMulWithZero (?m.15131 i) (?m.15132 i) ▼
      [] ❌ Zero α ▼
        [] new goal Zero α ▶
        [] ✅ apply @MonoidWithZero.toZero to Zero α ▼
          [tryResolve] ✅ Zero α ≟ Zero α
          [] no instances for MonoidWithZero α ▶
        [] ✅ apply @AddMonoid.toZero to Zero α ▶
        [] ✅ apply @MulZeroOneClass.toZero to Zero α ▶
        [] ✅ apply @MonoidWithZero.toMulZeroOneClass to MulZeroOneClass α ▶
        [] ✅ apply @AddZeroClass.toZero to Zero α ▶
        [] ✅ apply @AddMonoid.toAddZeroClass to AddZeroClass α ▶
        [] ✅ apply @SemigroupWithZero.toZero to Zero α ▶
        [] ✅ apply @MonoidWithZero.toSemigroupWithZero to SemigroupWithZero α ▶
        [] ✅ apply @MulZeroClass.toZero to Zero α ▶
        [] ✅ apply @MulZeroOneClass.toMulZeroClass to MulZeroClass α ▶
        [] ✅ apply @SemigroupWithZero.toMulZeroClass to MulZeroClass α ▶
        [] ✅ apply @Zero.ofOfNat0 to Zero α ▶
        [] ✅ apply @Zero.toOfNat0 to OfNat α 0 ▶
      [] ✅ I → MonoidWithZero α ▶
-/
