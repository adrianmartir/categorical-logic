module



public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Monoidal.Category

@[expose] public section



namespace CategoryTheory

universe u v

/-- Think of this as the objects of a category `Assoc α` encoding
associative lists of elements of `α`. -/
@[ext]
structure AssocObj (α : Type _) where
  n : ℕ
  f : Fin n → α

def AssocF : Functor (Type u) (Type u) where
  obj := AssocObj
  map f x := ⟨x.n, f ∘ x.f⟩

namespace Assoc

@[simps]
def mul {X} (x y : AssocF.obj X) : AssocF.obj X := {
  n := x.n + y.n
  f i := Sum.elim x.f y.f (finSumFinEquiv.symm i)
}

@[simps]
def one (X) : AssocObj X := {
  n := 0
  f := Fin.elim0
}

instance instMonoid (X) : Monoid (AssocF.obj X) where
  mul := mul
  one := one X
  mul_assoc := by intros; sorry
  one_mul := sorry
  mul_one := sorry

def liftAux {X Y} (mul : Y → Y → Y) (one : Y) (f : X → Y) : AssocF.obj X → Y :=
  fun x ↦ (List.ofFn (f ∘ x.f)).foldl mul one

-- This is only unique if `Y` is actually a monoid.
/-- Lifting a morphism to a morphism of monoids through `Assoc`. This comes from the fact that
`Assoc X` is the free monoid on `X`. -/
abbrev lift {X Y} [One Y] [Mul Y] (f : X → Y) : AssocF.obj X → Y :=
  liftAux (· * ·) 1 f

@[simp]
def lift_mul {X Y} [Monoid Y] (f : X → Y) (x y) :
  lift f (x * y) = lift f x * lift f y := sorry

def reduceAux {X : Type*} (mul : X → X → X) (one : X) : AssocF.obj X → X :=
  Assoc.liftAux mul one id

def reduce {X : Type*} [One X] [Mul X] : AssocF.obj X → X :=
  Assoc.lift id

def single : NatTrans (Functor.id (Type u)) AssocF where
  app A x := ⟨1,![x]⟩
  naturality A B f := by
    ext a
    simp only [Functor.id_obj] at a
    simp [AssocF]
    funext i
    simp only [Matrix.cons_val_fin_one, Function.comp_apply]

def flatten : NatTrans (Functor.comp AssocF AssocF) AssocF where
  app A x := reduce x
  naturality A B f := by
    ext a
    simp only [Functor.comp_obj, Functor.comp_map, types_comp_apply]
    sorry

abbrev _root_.CategoryTheory.Assoc : Monad (Type u) where
  obj := AssocObj
  map := AssocF.map
  η := single
  μ := flatten
  left_unit := sorry
  right_unit := sorry
  assoc := sorry


-- This is an unbiased version of flatten, but as long as the monad laws hold it is fine.
-- def flatten {α} (a: Assoc (Assoc α)) : Assoc α := {
--   n := ∑ i: Fin a.n, (a.f i).n
--   f i := Sigma.uncurry (fun i j ↦ (a.f i).f j) (finSigmaFinEquiv.symm i)
-- }


-- abbrev flatten {X} : Assoc (Assoc X) → Assoc X :=
--   Assoc.lift id

instance instAssocFunctor : _root_.Functor Assoc.obj where
  map f a := ⟨a.n, f ∘ a.f⟩

lemma liftAux_nat {X Y Z} (mul : Z → Z → Z) (one : Z) (f : X → Y) (g : Y → Z) (x : Assoc.obj X) :
    liftAux mul one g (Assoc.map f x) = liftAux mul one (g ∘ f) x := by
  sorry

lemma reduceAux_nat {X Y Z} (mul : Z → Z → Z) (one : Z) (f : X → Y) (g : Y → Z) (x : Assoc.obj X) :
    liftAux mul one g (Assoc.map f x) = liftAux mul one (g ∘ f) x := by
  sorry

/-- `liftAux` expressed in terms of `reduceAux`. -/
lemma liftAux_eq {X Y} (mul : Y → Y → Y) (one : Y) (f : X → Y) (x : Assoc.obj X):
    liftAux mul one f x = reduceAux mul one (Assoc.map f x) := by
  sorry

open CategoryTheory MonoidalCategory

abbrev catProd {X : Type*} [Category X] [MonoidalCategory X] : Assoc.obj X → X :=
  liftAux (· ⊗ ·) (𝟙_ X) id

-- def catProd_mul {X : Type*} [Category X] [MonoidalCategory X] (x y : Assoc.obj X) :
--     catProd (x * y) ≅ catProd x ⊗ catProd y := by
--   -- simp only [catProd, reduce, lift_mul]
--   -- rfl
--   sorry

-- Pseudoalgebra laws (we don't need coherence)

def single_catProd {X : Type*} [Category X] [MonoidalCategory X] (x : X) :
    catProd (single.app X x) ≅ x := by
  sorry

end Assoc
end CategoryTheory
