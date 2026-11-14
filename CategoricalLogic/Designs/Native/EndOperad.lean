/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Native.Operad
public import CategoricalLogic.Designs.Native.FreeMon
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The endomorphism operad of a family of types

For `X : S → Type u`, the planar operad on the discrete category on `S` whose operations with
inputs `ss` and output `s` are the functions `Tuple X ss → X s`.

All morphisms of `Discrete S` and of `FreeMon (Discrete S)` are equalities, and the actions of
morphisms are `cast`s.
-/

@[expose] public section

namespace CategoryTheory.Native.EndOperad

universe u

open Profunctor Opposite TypeCat Limits FreeMonProf

variable {S : Type u} (X : S → Type u)

/-- Tuples of elements of `X` of the given sorts. -/
def Tuple : List (Discrete S) → Type u
  | [] => PUnit
  | s :: ss => X s.as × Tuple ss

variable {X}

/-- Split a tuple of sorts `as ++ bs`. -/
def split : ∀ {as bs : List (Discrete S)}, Tuple X (as ++ bs) → Tuple X as × Tuple X bs
  | [], _, t => (PUnit.unit, t)
  | _ :: _, _, t => ((t.1, (split t.2).1), (split t.2).2)

section Thin

variable {C : Type u} [Category.{u} C]

/-- If all morphisms of `C` are equalities, so are those of `FreeMon C`. -/
theorem eq_of_hom (h : ∀ {x y : C}, (x ⟶ y) → x = y) :
    ∀ {xs ys : List C}, FreeMon.Hom xs ys → xs = ys
  | [], [], _ => rfl
  | _ :: _, _ :: _, f => congrArg₂ List.cons (h f.1) (eq_of_hom h f.2)
  | [], _ :: _, f => PEmpty.elim f
  | _ :: _, [], f => PEmpty.elim f

/-- If `C` is thin, so is `FreeMon C`. -/
theorem hom_subsingleton (h : ∀ {x y : C} (f g : x ⟶ y), f = g) :
    ∀ {xs ys : List C} (f g : FreeMon.Hom xs ys), f = g
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, f, g => Prod.ext (h _ _) (hom_subsingleton h f.2 g.2)
  | [], _ :: _, f, _ => PEmpty.elim f
  | _ :: _, [], f, _ => PEmpty.elim f

end Thin

theorem discrete_eq {x y : Discrete S} (f : x ⟶ y) : x = y := Discrete.ext (Discrete.eq_of_hom f)

theorem discrete_thin {x y : Discrete S} (f g : x ⟶ y) : f = g := Subsingleton.elim _ _

/-- Morphisms in `FreeMon (Discrete S)` are equalities. -/
theorem eq_of_hom₁ {A B : FreeMon (Discrete S)} (f : A ⟶ B) : A = B :=
  FreeMon.ext (eq_of_hom discrete_eq (xs := A.as) (ys := B.as) f)

theorem thin₁ {A B : FreeMon (Discrete S)} (f g : A ⟶ B) : f = g :=
  hom_subsingleton discrete_thin (xs := A.as) (ys := B.as) f g

/-- Morphisms in `FreeMon (FreeMon (Discrete S))` are equalities. -/
theorem eq_of_hom₂ {A B : FreeMon (FreeMon (Discrete S))} (f : A ⟶ B) : A = B :=
  FreeMon.ext (eq_of_hom eq_of_hom₁ (xs := A.as) (ys := B.as) f)

theorem thin₂ {A B : FreeMon (FreeMon (Discrete S))} (f g : A ⟶ B) : f = g :=
  hom_subsingleton thin₁ (xs := A.as) (ys := B.as) f g

variable (X) in
/-- The operations of the endomorphism operad: `hom s ss = (Tuple X ss → X s)`. -/
def hom : Profunctor.{u} (Discrete S) (FreeMon (Discrete S)) :=
  Profunctor.ofCore
    { obj s ss := Tuple X ss.as → X s.as
      map f g := ↾fun φ t ↦
        cast (congrArg X (Discrete.eq_of_hom f))
          (φ (cast (congrArg (fun A : FreeMon (Discrete S) ↦ Tuple X A.as) (eq_of_hom₁ g)) t))
      map_id _ _ := by ext; simp
      map_comp _ _ _ _ := by ext; simp }

/-- Apply a list of operations to consecutive chunks of a tuple. -/
def applyAll : ∀ {ss : List (Discrete S)} {Ss : List (FreeMon (Discrete S))},
    Elts (hom X) ss Ss → Tuple X (Ss.flatMap FreeMon.as) → Tuple X ss
  | [], [], _, _ => PUnit.unit
  | _ :: _, _ :: _, fs, t => (fs.1 (split t).1, applyAll fs.2 (split t).2)
  | [], _ :: _, fs, _ => PEmpty.elim fs
  | _ :: _, [], fs, _ => PEmpty.elim fs

theorem prod_heq {α β β' : Type u} {a a' : α} {b : β} {b' : β'} (ha : a = a') (hb : b ≍ b') :
    (a, b) ≍ (a', b') := by
  subst ha
  obtain rfl := type_eq_of_heq hb
  obtain rfl := eq_of_heq hb
  rfl

theorem split_nil_heq : ∀ {as : List (Discrete S)} (t : Tuple X (as ++ [])),
    (split (bs := []) t).1 ≍ t
  | [], _ => HEq.rfl
  | _ :: _, t => prod_heq rfl (split_nil_heq t.2)

theorem applyAll_heq {ss ss' : List (Discrete S)} {Ss Ss' : List (FreeMon (Discrete S))}
    {fs : Elts (hom X) ss Ss} {fs' : Elts (hom X) ss' Ss'}
    {t : Tuple X (Ss.flatMap FreeMon.as)} {t' : Tuple X (Ss'.flatMap FreeMon.as)}
    (hs : ss = ss') (hS : Ss = Ss') (hf : fs ≍ fs') (ht : t ≍ t') :
    applyAll fs t ≍ applyAll fs' t' := by
  subst hs hS
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq ht
  rfl

/-- Composition of an operation with a list of operations. -/
def compFun {s : Discrete S} {ss : FreeMon (Discrete S)} {Ss : FreeMon (FreeMon (Discrete S))}
    (φ : Tuple X ss.as → X s.as) (fs : Elts (hom X) ss.as Ss.as) :
    Tuple X (Ss.as.flatMap FreeMon.as) → X s.as :=
  fun t ↦ φ (applyAll fs t)

theorem compFun_wd {s : Discrete S} {ss ss' : FreeMon (Discrete S)}
    {Ss : FreeMon (FreeMon (Discrete S))} (γ : ss ⟶ ss') (φ : Tuple X ss'.as → X s.as)
    (fs : Elts (hom X) ss.as Ss.as) :
    compFun (((hom X).obj s).map γ.op φ) fs = compFun φ (mapL (hom X) γ fs) := by
  obtain rfl := eq_of_hom₁ γ
  obtain rfl := thin₁ γ (𝟙 _)
  rw [op_id, Functor.map_id]
  exact congrArg _ (mapL_id _ fs).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The composition of the endomorphism operad. -/
def compCell : (hom X).comp (obj (hom X)) ⟶
    (hom X).whiskerLeft₂ (𝟭 _) (FreeMon.flatten (Discrete S)) where
  app s :=
    { app Ss := ↾Quot.lift (fun ⟨_, φ, fs⟩ ↦ compFun (Ss := Ss.unop) φ fs) (by
        rintro _ _ ⟨γ, φ, fs⟩
        exact compFun_wd γ φ fs)
      naturality Ss Ss' G := by
        obtain ⟨Ss⟩ := Ss
        obtain ⟨Ss'⟩ := Ss'
        obtain rfl : Ss' = Ss := eq_of_hom₂ G.unop
        obtain rfl : G = 𝟙 _ := Quiver.Hom.unop_inj (thin₂ _ _)
        simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] }
  naturality s s' f := by
    obtain rfl : s = s' := discrete_eq f
    obtain rfl : f = 𝟙 _ := discrete_thin _ _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- The identities of the endomorphism operad. -/
def idCell : (Profunctor.id : Profunctor (Discrete S) (Discrete S)) ⟶
    (hom X).whiskerLeft₂ (𝟭 _) (FreeMon.unit (Discrete S)) where
  app s :=
    { app s' := ↾fun f t ↦ cast (congrArg X (Discrete.eq_of_hom f)) t.1
      naturality s₁ s₂ g := by
        obtain ⟨s₁⟩ := s₁
        obtain ⟨s₂⟩ := s₂
        obtain rfl : s₂ = s₁ := discrete_eq g.unop
        obtain rfl : g = 𝟙 _ := Quiver.Hom.unop_inj (discrete_thin _ _)
        simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] }
  naturality s s' f := by
    obtain rfl : s = s' := discrete_eq f
    obtain rfl : f = 𝟙 _ := discrete_thin _ _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

theorem applyAll_unit_heq : ∀ {ss : List (Discrete S)}
    (t : Tuple X ((ss.map (FreeMon.unit (Discrete S)).obj).flatMap FreeMon.as)),
    applyAll (restr (hom X) (𝟭 _) (FreeMon.unit (Discrete S))
      (hmap idCell (ofHom (FreeMon.Hom.id ss)))) t ≍ t
  | [], _ => HEq.rfl
  | _ :: _, t => prod_heq rfl (applyAll_unit_heq t.2)

variable (X) in
/-- The endomorphism operad of `X`. -/
def endOperad : Operad Cat.freeMon (Cat.of (Discrete S)) where
  hom := hom X
  id := idCell
  comp := compCell
  -- TODO: the elementwise proofs (via `split_nil_heq`, `applyAll_unit_heq`) are drafted in the
  -- history of this file; the `eqToHom` component did not unify with `cast_heq`.
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end CategoryTheory.Native.EndOperad
