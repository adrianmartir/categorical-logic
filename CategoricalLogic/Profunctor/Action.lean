/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Tactic.CategoryTheory.CategoryStar

public import CategoricalLogic.Profunctor.Basic

@[expose] public section

namespace CategoryTheory

namespace Profunctor

universe w

/-! ### Acting by functors -/

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
variable {E : Type*} [Category* E] {F' : Type*} [Category* F']


/-- Compose a functor `F` on the left (contravariant) side of a profunctor `H`,
    yielding the profunctor `(X, Y) ↦ H(F(X), Y)`. -/
def actLeft (H : Profunctor.{w} C D) (F : E ⥤ D) : Profunctor.{w} C E := {
  obj X Y := H.obj (F.obj X) Y
  map f g := H.map (F.map f) g
  map_id X Y e := by grind
  map_comp f' f g g' e := by grind
}

/-- Compose a functor `F` on the right (covariant) side of a profunctor `H`,
    yielding the profunctor `(X, Y) ↦ H(X, F(Y))`. -/
def actRight (H : Profunctor.{w} C D) (F : E ⥤ C) : Profunctor.{w} E D where
  obj X Y := H.obj X (F.obj Y)
  map f g := H.map f (F.map g)
  map_id X Y e := by grind
  map_comp f' f g g' e := by grind

/-! #### Behaviour on objects -/

@[simp]
theorem actLeft_obj (H : Profunctor.{w} C D) (F : E ⥤ D) (X : E) (Y : C) :
    (H.actLeft F).obj X Y = H.obj (F.obj X) Y := rfl

@[simp]
theorem actRight_obj (H : Profunctor.{w} C D) (F : E ⥤ C) (X : D) (Y : E) :
    (H.actRight F).obj X Y = H.obj X (F.obj Y) := rfl

/-! #### Behaviour on morphisms -/

@[simp]
theorem actLeft_map (H : Profunctor.{w} C D) (F : E ⥤ D)
    {X X' : E} {Y Y' : C} (f : X' ⟶ X) (g : Y ⟶ Y') (e : H.obj (F.obj X) Y) :
    (H.actLeft F).map f g e = H.map (F.map f) g e := rfl

@[simp]
theorem actRight_map (H : Profunctor.{w} C D) (F : E ⥤ C)
    {X X' : D} {Y Y' : E} (f : X' ⟶ X) (g : Y ⟶ Y') (e : H.obj X (F.obj Y)) :
    (H.actRight F).map f g e = H.map f (F.map g) e := rfl

@[simp]
theorem actLeft_mapL (H : Profunctor.{w} C D) (F : E ⥤ D)
    {X X' : E} (f : X ⟶ X') {Y : C} (e : H.obj (F.obj X') Y) :
    (H.actLeft F).mapL f e = H.mapL (F.map f) e := rfl

@[simp]
theorem actRight_mapL (H : Profunctor.{w} C D) (F : E ⥤ C)
    {X X' : D} (f : X ⟶ X') {Y : E} (e : H.obj X' (F.obj Y)) :
    (H.actRight F).mapL f e = H.mapL f e := by
  simp only [mapL, actRight_obj, actRight_map, Functor.map_id]

@[simp]
theorem actLeft_mapR (H : Profunctor.{w} C D) (F : E ⥤ D)
    {X : E} {Y Y' : C} (g : Y ⟶ Y') (e : H.obj (F.obj X) Y) :
    (H.actLeft F).mapR g e = H.mapR g e := by
  simp only [mapR, actLeft_obj, actLeft_map, Functor.map_id]

@[simp]
theorem actRight_mapR (H : Profunctor.{w} C D) (F : E ⥤ C)
    {X : D} {Y Y' : E} (g : Y ⟶ Y') (e : H.obj X (F.obj Y)) :
    (H.actRight F).mapR g e = H.mapR (F.map g) e := rfl

/-! #### Action on natural transformations -/

/-- A natural transformation `α : h ⟶ k` between profunctors lifts along `actLeft F`
    to a natural transformation `h.actLeft F ⟶ k.actLeft F`. -/
def NatTrans.actLeft {h k : Profunctor.{w} C D} (α : NatTrans h k) (F : E ⥤ D) :
    NatTrans (h.actLeft F) (k.actLeft F) where
  app X Y e := α.app (F.obj X) Y e
  naturality f g e := α.naturality (F.map f) g e

/-- A natural transformation `α : h ⟶ k` between profunctors lifts along `actRight F`
    to a natural transformation `h.actRight F ⟶ k.actRight F`. -/
def NatTrans.actRight {h k : Profunctor.{w} C D} (α : NatTrans h k) (F : E ⥤ C) :
    NatTrans (h.actRight F) (k.actRight F) where
  app X Y e := α.app X (F.obj Y) e
  naturality f g e := α.naturality f (F.map g) e

@[simp]
theorem NatTrans.actLeft_app {h k : Profunctor.{w} C D} (α : NatTrans h k) (F : E ⥤ D)
    (X : E) (Y : C) (e : h.obj (F.obj X) Y) :
    (α.actLeft F).app X Y e = α.app (F.obj X) Y e := rfl

@[simp]
theorem NatTrans.actRight_app {h k : Profunctor.{w} C D} (α : NatTrans h k) (F : E ⥤ C)
    (X : D) (Y : E) (e : h.obj X (F.obj Y)) :
    (α.actRight F).app X Y e = α.app X (F.obj Y) e := rfl

/-! #### Functoriality of actLeft / actRight on natural transformations -/

@[simp]
theorem NatTrans.actLeft_id (h : Profunctor.{w} C D) (F : E ⥤ D) :
    (NatTrans.id h).actLeft F = NatTrans.id (h.actLeft F) := rfl

@[simp]
theorem NatTrans.actRight_id (h : Profunctor.{w} C D) (F : E ⥤ C) :
    (NatTrans.id h).actRight F = NatTrans.id (h.actRight F) := rfl

theorem NatTrans.actLeft_comp {h k R : Profunctor.{w} C D}
    (β : NatTrans k R) (α : NatTrans h k) (F : E ⥤ D) :
    (β.comp α).actLeft F = (β.actLeft F).comp (α.actLeft F) := rfl

theorem NatTrans.actRight_comp {h k R : Profunctor.{w} C D}
    (β : NatTrans k R) (α : NatTrans h k) (F : E ⥤ C) :
    (β.comp α).actRight F = (β.actRight F).comp (α.actRight F) := rfl

/-! #### Identity and associativity properties -/

/-- Acting on the left by the identity functor does nothing. -/
@[simp]
theorem actLeft_id_functor (H : Profunctor.{w} C D) :
    H.actLeft (𝟭 D) = H := by
  cases H; rfl

/-- Acting on the right by the identity functor does nothing. -/
@[simp]
theorem actRight_id_functor (H : Profunctor.{w} C D) :
    H.actRight (𝟭 C) = H := by
  cases H; rfl

/-- Acting on the left twice is the same as acting by the composition. -/
@[simp]
theorem actLeft_comp_functor (H : Profunctor.{w} C D) (F : E ⥤ D) (G : F' ⥤ E) :
    (H.actLeft F).actLeft G = H.actLeft (G ⋙ F) := by
  cases H; rfl

/-- Acting on the right twice is the same as acting by the composition. -/
@[simp]
theorem actRight_comp_functor (H : Profunctor.{w} C D) (F : E ⥤ C) (G : F' ⥤ E) :
    (H.actRight F).actRight G = H.actRight (G ⋙ F) := by
  cases H; rfl

end Profunctor

end CategoryTheory
