import MweSkeletons.Ideal
set_option autoImplicit false

universe u v

class HasQuotient (A : outParam <| Type u) (B : Type v) where
  /-- auxiliary quotient function, the one used will have `A` explicit -/
  quotient' : B → Type max u v

@[reducible]
def HasQuotient.Quotient (A : outParam <| Type u) {B : Type v}
    [HasQuotient A B] (b : B) : Type max u v :=
  HasQuotient.quotient' b

protected def Quotient.liftOn' {α φ : Sort _} {s₁ : Setoid α}
(q : Quotient s₁) (f : α → φ) (h : ∀ a b, @Setoid.r α s₁ a b → f a = f b) :
    φ :=
  Quotient.liftOn q f h
  
/-- Quotient notation based on the `HasQuotient` typeclass -/
notation:35 G " ⧸ " H:34 => HasQuotient.Quotient G H

def QuotientAddGroup.leftRel {α : Type _} [AddGroup α] (s : AddSubgroup α) : Setoid α :=
-- too lazy to do opposite subgroups
{ r := fun a b => ∃ c, b = a + c -- could be a = c + b or a = b + c or...
  iseqv := sorry }

def Submodule.quotientRel {R : Type _} {M : Type _} [Ring R] [AddCommGroup M]
  [Module R M] (p : Submodule R M): Setoid M :=
  QuotientAddGroup.leftRel p.toAddSubgroup

instance Submodule.hasQuotient  {R M : Type _} [Ring R] [AddCommGroup M]
  [Module R M]: HasQuotient M (Submodule R M) :=
  ⟨fun p => Quotient (quotientRel p)⟩

@[reducible]
instance {R : Type _} [CommRing R] : HasQuotient R (Ideal R) :=
  Submodule.hasQuotient
