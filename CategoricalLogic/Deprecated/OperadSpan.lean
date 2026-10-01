


import Mathlib
import CategoricalLogic.Deprecated.Assoc
-- import Init
-- import Mathlib.Data.Fin.VecNotation
-- import Mathlib.Algebra.BigOperators.Group.Finset.Defs
-- import Mathlib.Control.Functor
-- import Mathlib.CategoryTheory.Monoidal.Category

/-!
Coloured operads.

DEPRECATED: This is an old attempt to do operads via spans directly, without passing through double categories.
-/



universe u v

namespace CategoryTheory

open CategoryTheory MonoidalCategory

variable (T : Monad (Type u))

variable [Limits.PreservesLimitsOfShape Limits.WalkingCospan T.toFunctor]

/-- A span between two types A and B is a space Arr of arrows
together with two morphisms Arr → A and Arr → B. -/
structure Span (A B : Type*) where
  Arr : Type*
  src : Arr → A
  tgt : Arr → B

/-- A multiquiver is a type of arrows, each a source list of objects and a target object. -/
abbrev Multiquiver (obj : Type u) := Span (T.obj obj) obj

/-- The identity multiquiver that with only identity multi-edges. -/
def Multiquiver.Id (obj : Type u) : Multiquiver T obj where
  Arr := obj
  src := T.η.app obj
  tgt := id

structure Multiquiver.Mul {obj : Type u} (q : Multiquiver T obj)
    (S : T.obj obj) (T : obj) where
  arr : q.Arr
  src_f : q.src arr = S
  tgt_f : q.tgt arr = T

def uncurryPb {A B C Z : Type*} {f : A → B} {g : C → B}
    (h : (a : A) → (c : C) → (p : f a = g c) → Z) : Function.Pullback f g → Z :=
  fun t ↦ h t.fst t.snd t.2

def curryPb {A B C Z : Type*} {f : A → B} {g : C → B}
    (h : Function.Pullback f g → Z) : (a : A) → (c : C) → (p : f a = g c) → Z :=
  fun a b p ↦ h ⟨(a,b),p⟩

def pullback [Limits.PreservesLimitsOfShape Limits.WalkingCospan T.toFunctor]
    {A B C : Type u} {f : A → B} {g : C → B} :
    T.obj (Function.Pullback f g)
      ≃ Function.Pullback (T.map f) (T.map g) := sorry


-- More general version:
-- def pullback' {C} [Category C] (F : Functor C C)
--     [Limits.PreservesLimitsOfShape Limits.WalkingCospan F]
--     {A B C : Type u} {f : A → B} {g : C → B} :
--     F.obj (Function.Pullback f g)
--       ≃ Function.Pullback (F.map f) (F.map g) := by
--   sorry

variable {T}

/-- Lift a function with domain an uncurried pullback through a pullback-preserving functor. -/
def liftPb {A B C Z : Type u} {f : A → B} {g : C → B}
    (h : (a : A) → (c : C) → (p : f a = g c) → Z) :
    (a : T.obj A) → (c : T.obj C) → (p : T.map f a = T.map g c) → T.obj Z :=
  curryPb ((T.map (uncurryPb h)) ∘ (pullback T).symm)

@[simp]
lemma liftPb_fst {A B C : Type u} {f : A → B} {g : C → B}
    (x : T.obj A) (y : T.obj C) (p : T.map f x = T.map g y) :
      liftPb (fun x _ _ ↦ x) x y p = x := by
  sorry

@[simp]
lemma liftPb_snd {A B C : Type u} {f : A → B} {g : C → B}
    (x : T.obj A) (y : T.obj C) (p : T.map f x = T.map g y) :
      liftPb (fun _ y _ ↦ y) x y p = y := by
  sorry

lemma liftPb_map {A B C Z W : Type u} {f : A → B} {g : C → B}
    (h : (a : A) → (c : C) → (p : f a = g c) → Z) (k : Z → W) :
    ∀x y p, T.map k (liftPb h x y p) = liftPb (fun x y p ↦ k (h x y p)) x y p := by
  sorry

variable (T)

class Multicategory (obj: Type u) extends Multiquiver T obj where
  /-- Identity arrows. -/
  id: obj ⟶ Arr
  src_id: id ≫ src = T.η.app obj
  tgt_id: id ≫ tgt = 𝟙 obj
  /-- Arrow composition. -/
  comp: (f: T.obj Arr) → (g: Arr) → T.map tgt f = src g → Arr
  src_comp: ∀f g p, src (comp f g p) = T.μ.app _ (T.map src f)
  tgt_comp: ∀f g p, tgt (comp f g p) = tgt g
  /-- Right composition with the identity does nothing. -/
  comp_id: ∀x f (p: src f = x), comp (T.map id x) f (by
    rw [<- types_comp_apply (T.map id) (T.map tgt), <- Functor.map_comp,
        tgt_id, p, Functor.map_id, types_id_apply]) = f
  /-- Left composition with the identity does nothing. -/
  id_comp: ∀f x (p: tgt f = x), comp (T.η.app _ f) (id x) (by
      rw [<- types_comp_apply (T.η.app _) (T.map tgt), <- T.unit_naturality,
        types_comp_apply, p, <- src_id, types_comp_apply])
          = f
  -- We need to lift the domain of `comp` through `Assoc` to state associativity.
  /-- Associativity of composition. -/
  comp_assoc (f: T.obj (T.obj Arr)) (g: T.obj Arr) (h: Arr)
      (f_comp_g: T.map (T.map tgt) f = T.map src g)
      (g_comp_h: T.map tgt g = src h):
    comp (T.μ.app _ f) (comp g h g_comp_h) (by
      rw [src_comp, <- types_comp_apply (T.μ.app Arr) (T.map tgt),
        <- T.mu_naturality, types_comp_apply, f_comp_g
      ])
      = comp (liftPb comp f g f_comp_g) h
        (by simp_rw [liftPb_map, tgt_comp, <- liftPb_map, liftPb_snd, g_comp_h]
      )

open Multicategory

attribute [simp] src_id tgt_id src_comp tgt_comp Multicategory.comp_id Multicategory.id_comp

structure Multifunctor (M N : Type u) [m : Multicategory T M] [n : Multicategory T N] where
  obj : M ⟶ N
  map : m.Arr ⟶ n.Arr
  obj_src : m.src ≫ T.map obj = map ≫ n.src
  obj_tgt : m.tgt ≫ obj = map ≫ n.tgt
  map_id : ∀x, map (m.id x) = n.id (obj x)
  comp_map (f : T.obj m.Arr) (g : m.Arr) (p: _) : comp (T.map map f) (map g)
      (by simp_rw [<- types_comp_apply (T.map map) (T.map n.tgt), <- Functor.map_comp,
            <- obj_tgt, <- types_comp_apply map n.src, <- obj_src, T.map_comp,
            types_comp_apply, p])
    = map (comp f g p)

-- We would now have to define natural transformations of multifunctors and the bicategorical
-- structure on multicategories, but we leave this out since the submission would get too long.

-- structure Multicategory.NatTrans (M N : Type u) [m : Multicategory M] [n : Multicategory N]
--     (F G: Multifunctor M N) where
--   app (x : M) : Multiquiver.Mul n.toSpan (single (F.obj x)) (G.obj x)
--   naturality {x y : M} (f: Multiquiver.Mul m.toSpan (single x) y) :
--     comp (single (F.map f.arr)) (app y).arr sorry = comp ·


-- TODO: Bicategory instance for multicategory

@[ext]
structure MonoidalCategory.Multiarrow (C : Type u) [Category.{v, u} C] [MonoidalCategory C] where
  src : Assoc.obj C
  tgt : C
  arr : Assoc.catProd src ⟶ tgt

-- abbrev MonoidalCategory.Multiarrow' := Comma

def MonoidalCategory.Multiarrow.arrow {C : Type u} [Category.{v, u} C] [MonoidalCategory C]
    (f : Multiarrow C) : Arrow C := {
  left := Assoc.catProd f.src
  right := f.tgt
  hom := f.arr
}

@[simps]
def MonoidalCategory.arrowMul {C : Type u} [Category.{v, u} C] [MonoidalCategory C]
    (f g : Arrow C) : Arrow C := {
  left := f.left ⊗ g.left
  right := f.right ⊗ g.right
  hom := f.hom ⊗ₘ g.hom
}

def MonoidalCategory.arrowOne {C : Type u} [Category.{v, u} C] [MonoidalCategory C]
    (x : C) : Arrow C := {
  left := x
  right := x
  hom := 𝟙 x
}

@[simps]
def MonoidalCategory.Multiarrow.one (C : Type*) [Category C] [MonoidalCategory C]
    (x : C) : Multiarrow C := {
  src := Assoc.η.app _ x
  tgt := x
  arr := (Assoc.single_catProd x).hom ≫ 𝟙 x
}

-- def MonoidalCategory.Multiarrow.mul (C : Type*) [Category C] [MonoidalCategory C]
--     (f g : Multiarrow C) : Multiarrow C := {
--   src := f.src * g.src
--   tgt := f.tgt ⊗ g.tgt
--   arr := (catProd_mul f.src g.src).hom ≫ (f.arr ⊗ₘ g.arr)
-- }

-- def MonoidalCategory.Multiarrow.comp (C : Type*) [Category C] [MonoidalCategory C]
--     (f : Assoc (Multiarrow C)) (g : Multiarrow C) (p : (·.tgt) <$> f = g.src) : Multiarrow C :=

--   sorry

-- def MonoidalCategory.MultiarrowProdArr {C : Type*}
--     [Category C] [MonoidalCategory C] (f : Assoc (Multiarrow C)) :
--     Assoc.catProd (flatten ((·.src) <$> f)) ⟶ Assoc.catProd ((·.tgt) <$> f) := by
--   sorry

-- open Assoc in
-- def MonoidalCategory.Multiarrow.prod {C : Type u}
--     [Category C] [MonoidalCategory C] (f : T.obj (Multiarrow C)) : Multiarrow C := {
--   src := lift (·.src) f
--   tgt := catProd (Multiarrow.tgt <$> f)
--   arr := (eqToHom (by
--         simp [Functor.id_obj, liftAux_eq]
--         -- Use naturality of `reduceAux`
--         sorry)) ≫
--     (liftAux arrowMul (arrowOne (𝟙_ C)) Multiarrow.arrow f).hom ≫
--     (eqToHom (by
--       simp only [Functor.id_obj, liftAux_eq]
--       -- Naturality
--       sorry))
-- }

open MonoidalCategory

namespace Multicategory

def ofMonoidal (C : Type u) [Category.{u, u} C] [MonoidalCategory C] : Multicategory Assoc C := {
  Arr := Multiarrow.{u,u} C
  src x := x.src
  tgt x := x.tgt
  id x := Multiarrow.one C x
  src_id x := rfl
  tgt_id x := rfl
  comp f g p := ⟨joinM ((·.src) <$> f), g.tgt, by
      -- For some reason tactic-mode gives an elaboration speedup.
      exact (Multiarrow.prod f).arr ≫ eqToHom (congrArg Assoc.catProd p) ≫ g.arr
    ⟩
  src_comp := by simp only [implies_true]
  tgt_comp := by simp only [implies_true]
  comp_id x f p := by
    sorry
  id_comp := by
    sorry
  comp_assoc := by
    sorry
}


end Multicategory
end CategoryTheory
