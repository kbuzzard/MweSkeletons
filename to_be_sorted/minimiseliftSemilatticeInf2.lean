class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := λ a b => a ≤ b ∧ ¬ b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) := by intros; rfl

class PartialOrder (α : Type u) extends Preorder α :=
(le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b)

class HasSup (α : Type u) where
  sup : α → α → α

infixl:68 " ⊔ " => HasSup.sup

class HasInf (α : Type u) where
  inf : α → α → α

infixl:69 " ⊓ " => HasInf.inf

class SemilatticeInf (α : Type u) extends HasInf α, PartialOrder α where
  protected inf_le_left : ∀ a b : α, a ⊓ b ≤ a
  protected inf_le_right : ∀ a b : α, a ⊓ b ≤ b
  protected le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c

class SemilatticeSup (α : Type u) extends HasSup α, PartialOrder α where
  protected le_sup_left : ∀ a b : α, a ≤ a ⊔ b
  protected le_sup_right : ∀ a b : α, b ≤ a ⊔ b
  protected sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c

def GaloisConnection [Preorder α] [Preorder β] (l : α → β) (u : β → α) :=
  ∀ a b, l a ≤ b ↔ a ≤ u b

structure GaloisInsertion {α β : Type _} [Preorder α] [Preorder β] (l : α → β) (u : β → α) where
  choice : ∀ x : α, u (l x) ≤ x → β
  gc : GaloisConnection l u
  le_l_u : ∀ x, x ≤ l (u x)
  choice_eq : ∀ a h, choice a h = l a

structure GaloisCoinsertion [Preorder α] [Preorder β] (l : α → β) (u : β → α) where
  choice : ∀ x : β, x ≤ l (u x) → α
  gc : GaloisConnection l u
  u_l_le : ∀ x, u (l x) ≤ x
  choice_eq : ∀ a h, choice a h = u a

structure OrderDual (α : Type _) : Type _ where
  toDual :: ofDual : α

notation:max α "ᵒᵈ" => OrderDual α

open OrderDual

instance (α : Type _) [LE α] : LE αᵒᵈ :=
  ⟨fun x y => ofDual y ≤ ofDual x⟩

instance (α : Type _) [LT α] : LT αᵒᵈ :=
  ⟨fun x y => ofDual y < ofDual x⟩

instance preorder (α : Type _) [Preorder α] : Preorder αᵒᵈ where
  le_refl := fun _ => Preorder.le_refl _
  le_trans := fun _ _ _ hab hbc => Preorder.le_trans _ _ _ hbc hab
  lt_iff_le_not_le := fun _ _ => Preorder.lt_iff_le_not_le _ _

instance partialOrder (α : Type _) [PartialOrder α] : PartialOrder αᵒᵈ :=
  { (inferInstance : Preorder αᵒᵈ) with
  le_antisymm := sorry
  --fun a b hab hba => @PartialOrder.le_antisymm α _ (ofDual a) (ofDual b) hba hab
  }

instance (α : Type _) [HasInf α] : HasSup αᵒᵈ :=
  ⟨λ a b => toDual (ofDual a ⊓ ofDual b)⟩

instance (α : Type _) [HasSup α] : HasInf αᵒᵈ :=
  ⟨λ a b => toDual (ofDual a ⊔ ofDual b)⟩

instance OrderDual.semilatticeInf (α) [SemilatticeSup α] : SemilatticeInf αᵒᵈ :=
  { (inferInstance : PartialOrder αᵒᵈ),
    (inferInstance : HasInf αᵒᵈ) with
  inf_le_left := sorry
  inf_le_right := sorry
  le_inf := fun _ _ _ hca hcb => @SemilatticeSup.sup_le α _ _ _ _ hca hcb }

instance OrderDual.semilatticeSup (α) [SemilatticeInf α] : SemilatticeSup αᵒᵈ :=
  { (inferInstance : PartialOrder αᵒᵈ),
    (inferInstance : HasSup αᵒᵈ) with
  le_sup_left := sorry
  le_sup_right := sorry
  sup_le := fun _ _ _ hca hcb => @SemilatticeInf.le_inf α _ _ _ _ hca hcb }

protected theorem GaloisConnection.dual [Preorder α] [Preorder β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) :
  GaloisConnection (OrderDual.toDual ∘ u ∘ OrderDual.ofDual)
      (OrderDual.toDual ∘ l ∘ OrderDual.ofDual) :=
  fun a b => (gc (ofDual b) (ofDual a)).symm

open OrderDual

theorem GaloisConnection.l_le [Preorder α] [Preorder β] {l : α → β} {u : β → α} {a : α} {b : β}
    (gc : GaloisConnection l u) : a ≤ u b → l a ≤ b :=
  (gc _ _).mpr

def GaloisInsertion.liftSemilatticeSup [PartialOrder β] {l : α → β} {u : β → α} [SemilatticeSup α]
  (gi : GaloisInsertion l u) : SemilatticeSup β :=
  { (inferInstance : PartialOrder β) with
    sup := fun a b => l (u a ⊔ u b)
    le_sup_left := sorry
    le_sup_right := sorry
    sup_le := sorry }


def GaloisCoinsertion.dual [Preorder α] [Preorder β] {l : α → β} {u : β → α} :
    GaloisCoinsertion l u → GaloisInsertion (toDual ∘ u ∘ ofDual) (toDual ∘ l ∘ ofDual) :=
  fun x => ⟨λ b h => toDual (x.1 (ofDual b) h), x.2.dual, λ a => x.3 _, λ bod h => sorry⟩

variable [PartialOrder α] (l : α → β) (u : β → α)

def liftSemilatticeInf [SemilatticeInf β] (gi : GaloisCoinsertion l u) : SemilatticeInf α :=
  { ‹PartialOrder α› with
    inf_le_left := sorry
    inf_le_right := sorry
    inf := fun a b => u (l a ⊓ l b)
    le_inf := fun a b c hab hbc => by
      exact (@OrderDual.semilatticeInf αᵒᵈ gi.dual.liftSemilatticeSup).le_inf
        (toDual (toDual a)) (toDual (toDual b)) (toDual (toDual c)) hab hbc
    }
