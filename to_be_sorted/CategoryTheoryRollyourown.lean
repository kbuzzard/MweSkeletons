namespace CategoryTheory

class Category (obj : Type) : Type 1 where
  Hom : obj → obj → Type
  id : ∀ X : obj, Hom X X
  comp : ∀ {X Y Z : obj}, Hom X Y → Hom Y Z → Hom X Z

infixr:10 " ⟶ " => Category.Hom

notation "𝟙" => Category.id

infixr:80 " ≫ " => Category.comp

variable {C : Type} [Category C]

structure DiagramBase (X : C) where
  Y : C
  f : Y ⟶ X

structure Relation {X : C} (Y₁ Y₂ : DiagramBase X) where
  R : C
  g₁ : R ⟶ Y₁.Y
  g₂ : R ⟶ Y₂.Y
  r : R ⟶ X

structure RelationHom {X : C} {Y₁ Y₂ : DiagramBase X}
    (R₁ R₂ : Relation Y₁ Y₂) where
  e : R₁.R ⟶ R₂.R

def RelationHom.id {X : C} {Y₁ Y₂ : DiagramBase X}
    (R : Relation Y₁ Y₂ ) : RelationHom R R where
  e := 𝟙 _

def RelationHom.comp {X : C} {Y₁ Y₂ : DiagramBase X}
    {R₁ R₂ R₃ : Relation Y₁ Y₂} (f : RelationHom R₁ R₂) (g : RelationHom R₂ R₃) :
    RelationHom R₁ R₃ where
  e := f.e ≫ g.e

instance instCategoryRelationHom {X : C} (Y₁ Y₂ : DiagramBase X) :
    Category (Relation Y₁ Y₂) where
  Hom := RelationHom
  id := RelationHom.id
  comp := RelationHom.comp

inductive Diagram (X : C) where
  | cover (Y : DiagramBase X) : Diagram X
  | relation {Y₁ Y₂ : DiagramBase X} (R : Relation Y₁ Y₂) : Diagram X

inductive DiagramHom {X : C} :
    Diagram X → Diagram X → Type _ where
  | id (x : Diagram X) : DiagramHom x x
  | rel {Y₁ Y₂ : DiagramBase X} {R₁ R₂ : Relation Y₁ Y₂} (e : R₁ ⟶ R₂) :
      DiagramHom (.relation R₁) (.relation R₂)

def DiagramHomComp {X : C} {x y z : Diagram X}
    (f : DiagramHom x y) (g : DiagramHom y z) : DiagramHom x z :=
  match f, g with
  | .id _, e => e
  | e, .id _ => e
  | .rel e₁, .rel e₂ => .rel (e₁ ≫ e₂)

instance instCategoryDiagram {X : C} : Category (Diagram X) where
  Hom := DiagramHom
  id := .id
  comp := DiagramHomComp

structure Functor (V : Type) [Category V] (W : Type) [Category W] : Type 1 where
  obj : V → W
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)
  map_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g

infixr:26 " ⥤ " => Functor

def DiagramFunctor {X : C} : Diagram X ⥤ C where
  obj | .cover Y => Y.Y
      | .relation R => R.R
  map | .id _ => 𝟙 _
      | .rel e => e.e
  map_comp := by simp
