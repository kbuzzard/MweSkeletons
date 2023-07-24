import MweSkeletons.CommRing

def Function.Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

class FunLike (F : Sort _) (α : outParam (Sort _)) (β : outParam <| α → Sort _) where
  /-- The coercion from `F` to a function. -/
  coe : F → ∀ a : α, β a
  /-- The coercion to functions must be injective. -/
  coe_injective' : Function.Injective coe

section Dependent

/-! ### `FunLike F α β` where `β` depends on `a : α` -/

variable (F α : Sort _) (β : α → Sort _)

namespace FunLike

variable {F α β} [i : FunLike F α β]

instance (priority := 100) hasCoeToFun : CoeFun F fun _ ↦ ∀ a : α, β a where coe := FunLike.coe

-- #eval Lean.Elab.Command.liftTermElabM do
--   Std.Tactic.Coe.registerCoercion ``FunLike.coe
--     (some { numArgs := 5, coercee := 4, type := .coeFun })

end FunLike

end Dependent

structure ZeroHom (M : Type _) (N : Type _) [Zero M] [Zero N] where
  /-- The underlying function -/
  toFun : M → N
  /-- The proposition that the function preserves 0 -/
  map_zero' : toFun 0 = 0

class ZeroHomClass (F : Type _) (M N : outParam (Type _)) [Zero M] [Zero N]
  extends FunLike F M fun _ => N where
  /-- The proposition that the function preserves 0 -/
  map_zero : ∀ f : F, f 0 = 0

instance ZeroHom.zeroHomClass {M N : Type _} [Zero M] [Zero N] : ZeroHomClass (ZeroHom M N) M N where
  coe := ZeroHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_zero := ZeroHom.map_zero'

def ZeroHomClass.toZeroHom {M N F : Type _} [Zero M] [Zero N] [ZeroHomClass F M N] (f : F) : ZeroHom M N where
  toFun := f
  map_zero' := map_zero f

instance {M N F : Type _} [Zero M] [Zero N] [ZeroHomClass F M N] : CoeTC F (ZeroHom M N) :=
  ⟨ZeroHomClass.toZeroHom⟩

structure OneHom (M : Type _) (N : Type _) [One M] [One N] where
  /-- The underlying function -/
  toFun : M → N
  /-- The proposition that the function preserves 1 -/
  map_one' : toFun 1 = 1

class OneHomClass (F : Type _) (M N : outParam (Type _)) [One M] [One N]
  extends FunLike F M fun _ => N where
  /-- The proposition that the function preserves 1 -/
  map_one : ∀ f : F, f 1 = 1

instance OneHom.oneHomClass {M N : Type _} [One M] [One N] : OneHomClass (OneHom M N) M N where
  coe := OneHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_one := OneHom.map_one'

/-- Turn an element of a type `F` satisfying `OneHomClass F M N` into an actual
`OneHom`. This is declared as the default coercion from `F` to `OneHom M N`. -/
def OneHomClass.toOneHom {M N F : Type _} [One M] [One N] [OneHomClass F M N] (f : F) : OneHom M N where
  toFun := f
  map_one' := map_one f

/-- Any type satisfying `OneHomClass` can be cast into `OneHom` via `OneHomClass.toOneHom`. -/
instance {M N F : Type _} [One M] [One N] [OneHomClass F M N] : CoeTC F (OneHom M N) :=
  ⟨OneHomClass.toOneHom⟩

structure AddHom (M : Type _) (N : Type _) [Add M] [Add N] where
  /-- The underlying function -/
  toFun : M → N
  /-- The proposition that the function preserves addition -/
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y

class AddHomClass (F : Type _) (M N : outParam (Type _)) [Add M] [Add N]
  extends FunLike F M fun _ => N where
  /-- The proposition that the function preserves addition -/
  map_add : ∀ (f : F) (x y : M), f (x + y) = f x + f y

instance AddHom.addHomClass {M N : Type _} [Add M] [Add N] : AddHomClass (AddHom M N) M N where
  coe := AddHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_add := AddHom.map_add'

def AddHomClass.toAddHom {M N F : Type _} [Add M] [Add N] [AddHomClass F M N] (f : F) : AddHom M N where
  toFun := f
  map_add' := map_add f

instance {M N F : Type _} [Add M] [Add N] [AddHomClass F M N] : CoeTC F (AddHom M N) :=
  ⟨AddHomClass.toAddHom⟩

structure MulHom (M : Type _) (N : Type _) [Mul M] [Mul N] where
  toFun : M → N
  map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y

/-- `M →ₙ* N` denotes the type of multiplication-preserving maps from `M` to `N`. -/
infixr:25 " →ₙ* " => MulHom

class MulHomClass (F : Type _) (M N : outParam (Type _)) [Mul M] [Mul N]
  extends FunLike F M fun _ => N where
  map_mul : ∀ (f : F) (x y : M), f (x * y) = f x * f y

instance MulHom.mulHomClass {M N : Type _} [Mul M] [Mul N] : MulHomClass (M →ₙ* N) M N where
  coe := MulHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_mul := MulHom.map_mul'

def MulHomClass.toMulHom {M N F : Type _} [Mul M] [Mul N] [MulHomClass F M N] (f : F) : M →ₙ* N where
  toFun := f
  map_mul' := map_mul f

instance {M N F : Type _} [Mul M] [Mul N] [MulHomClass F M N] : CoeTC F (M →ₙ* N) :=
  ⟨MulHomClass.toMulHom⟩

structure AddMonoidHom (M : Type _) (N : Type _) [AddZeroClass M] [AddZeroClass N] extends
  ZeroHom M N, AddHom M N

infixr:25 " →+ " => AddMonoidHom

class AddMonoidHomClass (F : Type _) (M N : outParam (Type _)) [AddZeroClass M] [AddZeroClass N]
  extends AddHomClass F M N, ZeroHomClass F M N

instance AddMonoidHom.addMonoidHomClass {M : Type _} {N : Type _} [AddZeroClass M] [AddZeroClass N] : AddMonoidHomClass (M →+ N) M N where
  coe f := f.toFun
  coe_injective' f g h := sorry
  map_add := AddMonoidHom.map_add'
  map_zero f := f.toZeroHom.map_zero'

instance AddMonoidHom.coeToZeroHom [AddZeroClass M] [AddZeroClass N] :
  Coe (M →+ N) (ZeroHom M N) := ⟨AddMonoidHom.toZeroHom⟩

instance AddMonoidHom.coeToAddHom [AddZeroClass M] [AddZeroClass N] :
  Coe (M →+ N) (AddHom M N) := ⟨AddMonoidHom.toAddHom⟩

def AddMonoidHomClass.toAddMonoidHom {M N F : Type _} [AddZeroClass M] [AddZeroClass N] [AddMonoidHomClass F M N] (f : F) : M →+ N :=
  { (f : AddHom M N), (f : ZeroHom M N) with }

instance [AddZeroClass M] [AddZeroClass N] [AddMonoidHomClass F M N] : CoeTC F (M →+ N) :=
  ⟨AddMonoidHomClass.toAddMonoidHom⟩

structure MonoidHom (M : Type _) (N : Type _) [MulOneClass M] [MulOneClass N] extends
  OneHom M N, M →ₙ* N

infixr:25 " →* " => MonoidHom

class MonoidHomClass (F : Type _) (M N : outParam (Type _)) [MulOneClass M] [MulOneClass N]
  extends MulHomClass F M N, OneHomClass F M N

instance MonoidHom.monoidHomClass {M : Type _} {N : Type _} [MulOneClass M] [MulOneClass N] : MonoidHomClass (M →* N) M N where
  coe f := f.toFun
  coe_injective' f g h := sorry
  map_mul := MonoidHom.map_mul'
  map_one f := f.toOneHom.map_one'

instance MonoidHom.coeToOneHom [MulOneClass M] [MulOneClass N] :
  Coe (M →* N) (OneHom M N) := ⟨MonoidHom.toOneHom⟩

instance MonoidHom.coeToMulHom [MulOneClass M] [MulOneClass N] :
  Coe (M →* N) (M →ₙ* N) := ⟨MonoidHom.toMulHom⟩

def MonoidHomClass.toMonoidHom {M N F : Type _} [MulOneClass M] [MulOneClass N] [MonoidHomClass F M N] (f : F) : M →* N :=
  { (f : M →ₙ* N), (f : OneHom M N) with }

instance [MulOneClass M] [MulOneClass N] [MonoidHomClass F M N] : CoeTC F (M →* N) :=
  ⟨MonoidHomClass.toMonoidHom⟩

/-

## Rings 

-/

structure MonoidWithZeroHom (M : Type _) (N : Type _)
  [MulZeroOneClass M] [MulZeroOneClass N] extends ZeroHom M N, MonoidHom M N

/-- `M →*₀ N` denotes the type of zero-preserving monoid homomorphisms from `M` to `N`. -/
infixr:25 " →*₀ " => MonoidWithZeroHom
structure NonUnitalRingHom (α β : Type _) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] extends α →ₙ* β, α →+ β

class MonoidWithZeroHomClass (F : Type _) (M N : outParam (Type _)) [MulZeroOneClass M]
  [MulZeroOneClass N] extends MonoidHomClass F M N, ZeroHomClass F M N

instance MonoidWithZeroHom.monoidWithZeroHomClass {M : Type _} {N : Type _} [MulZeroOneClass M]
  [MulZeroOneClass N] : MonoidWithZeroHomClass (M →*₀ N) M N where
  coe f := f.toFun
  coe_injective' f g h := sorry
  map_mul := MonoidWithZeroHom.map_mul'
  map_one := MonoidWithZeroHom.map_one'
  map_zero f := f.map_zero'

-- def MonoidWithZeroHomClass.toMonoidWithZeroHom {M N F : Type _} [MulZeroOneClass M] [MulZeroOneClass N] 
--     [MonoidWithZeroHomClass F M N] (f : F) : M →*₀ N :=
--   { (f : M →* N), (f : ZeroHom M N) with }

-- /-- Any type satisfying `MonoidWithZeroHomClass` can be cast into `MonoidWithZeroHom` via
-- `MonoidWithZeroHomClass.toMonoidWithZeroHom`. -/
-- instance [MonoidWithZeroHomClass F M N] : CoeTC F (M →*₀ N) :=
--   ⟨MonoidWithZeroHomClass.toMonoidWithZeroHom⟩


/-- `MonoidWithZeroHom` down-cast to a `MonoidHom`, forgetting the 0-preserving property. -/
instance MonoidWithZeroHom.coeToMonoidHom [MulZeroOneClass M] [MulZeroOneClass N] :
  Coe (M →*₀ N) (M →* N) := ⟨MonoidWithZeroHom.toMonoidHom⟩

--attribute [coe] MonoidWithZeroHom.toZeroHom

/-- `MonoidWithZeroHom` down-cast to a `ZeroHom`, forgetting the monoidal property. -/
instance MonoidWithZeroHom.coeToZeroHom [MulZeroOneClass M] [MulZeroOneClass N] :
  Coe (M →*₀ N) (ZeroHom M N) := ⟨MonoidWithZeroHom.toZeroHom⟩

/-- `α →ₙ+* β` denotes the type of non-unital ring homomorphisms from `α` to `β`. -/
infixr:25 " →ₙ+* " => NonUnitalRingHom


structure RingHom (α : Type _) (β : Type _) [NonAssocSemiring α] [NonAssocSemiring β] extends
  α →* β, α →+ β, α →ₙ+* β, α →*₀ β

/-- `α →+* β` denotes the type of ring homomorphisms from `α` to `β`. -/
infixr:25 " →+* " => RingHom

class RingHomClass (F : Type _) (α β : outParam (Type _)) [NonAssocSemiring α]
  [NonAssocSemiring β] extends MonoidHomClass F α β, AddMonoidHomClass F α β,
  MonoidWithZeroHomClass F α β

def RingHomClass.toRingHom {F α β : Type _} {_ : NonAssocSemiring α}
  {_ : NonAssocSemiring β} [RingHomClass F α β] (f : F) : α →+* β :=
  { (f : α →* β), (f : α →+ β) with }

/-- Any type satisfying `RingHomClass` can be cast into `RingHom` via `RingHomClass.toRingHom`. -/
instance {F α β : Type _} {_ : NonAssocSemiring α}
  {_ : NonAssocSemiring β} [RingHomClass F α β] : CoeTC F (α →+* β) :=
  ⟨RingHomClass.toRingHom⟩

instance instRingHomClass {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} : RingHomClass (α →+* β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply FunLike.coe_injective'
    exact h
  map_add := RingHom.map_add'
  map_zero := RingHom.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

def RingHom.id (α : Type _) [NonAssocSemiring α] : α →+* α := by
  refine' { toFun := _root_.id.. } <;> intros <;> rfl