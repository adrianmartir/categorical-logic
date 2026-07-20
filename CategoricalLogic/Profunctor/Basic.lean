/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

import Mathlib
import CategoricalLogic.Mathlib.CategoryTheory.Profunctor.Basic
import Mathlib.CategoryTheory.Category.Cat

/-! Compatibility notation for the elementwise use of the backported profunctor API. -/

namespace CategoryTheory.Profunctor

universe w

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

/-- Evaluate a profunctor at a pair of objects, with the target object first. -/
abbrev app (H : Profunctor.{w} C D) (X : D) (Y : C) := (H.obj Y).obj (.op X)

/-- Contravariant action in the target object. -/
def mapL (H : Profunctor.{w} C D) {X X' : D} (f : X ⟶ X') {Y : C} :
    H.app X' Y → H.app X Y := (H.obj Y).map f.op

/-- Covariant action in the source object. -/
def mapR (H : Profunctor.{w} C D) {X : D} {Y Y' : C} (g : Y ⟶ Y') :
    H.app X Y → H.app X Y' := (H.map g).app (.op X)

@[simp] theorem mapL_id (H : Profunctor.{w} C D) (X : D) (Y : C)
    (e : H.app X Y) : H.mapL (𝟙 X) e = e := by simp [mapL]

@[simp] theorem mapR_id (H : Profunctor.{w} C D) (X : D) (Y : C)
    (e : H.app X Y) : H.mapR (𝟙 Y) e = e := by simp [mapR]

theorem mapL_comp (H : Profunctor.{w} C D) {X X' X'' : D}
    (f : X ⟶ X') (f' : X' ⟶ X'') {Y : C} (e : H.app X'' Y) :
    H.mapL (f ≫ f') e = H.mapL f (H.mapL f' e) := by simp [mapL]

theorem mapR_comp (H : Profunctor.{w} C D) {X : D} {Y Y' Y'' : C}
    (g : Y ⟶ Y') (g' : Y' ⟶ Y'') (e : H.app X Y) :
    H.mapR (g ≫ g') e = H.mapR g' (H.mapR g e) := by
  simpa only [mapR, NatTrans.comp_app] using
    congrArg (fun k ↦ k.app (.op X) e) (H.map_comp g g')

theorem mapL_mapR_comm (H : Profunctor.{w} C D) {X X' : D} {Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') (e : H.app X' Y) :
    H.mapL f (H.mapR g e) = H.mapR g (H.mapL f e) := by
  exact (ConcreteCategory.congr_hom ((H.map g).naturality f.op) e).symm

/-- Transport an element along an equality on the covariant side. -/
def mpRight (H : Profunctor.{w} C D) {X : D} {Y Y' : C}
    (e : H.app X Y) (h : Y = Y') : H.app X Y' := H.mapR (eqToHom h) e

/-- Transport an element along an equality on the contravariant side. -/
def mpLeft (H : Profunctor.{w} C D) {X X' : D} {Y : C}
    (h : X = X') (e : H.app X' Y) : H.app X Y := H.mapL (eqToHom h) e

/-- Restrict the contravariant side of a profunctor along a functor. -/
def actLeft {C D E : Cat} (F : E ⟶ D) (H : Profunctor.{w} C D) : Profunctor.{w} C E :=
  H.whiskerLeft₂ (𝟭 C) F.toFunctor

/-- Restrict the covariant side of a profunctor along a functor. -/
def actRight {C D E : Cat} (H : Profunctor.{w} C D) (F : E ⟶ C) : Profunctor.{w} E D :=
  H.whiskerLeft₂ F.toFunctor (𝟭 D)

@[simp] theorem actLeft_app {C D E : Cat} (F : E ⟶ D) (H : Profunctor.{w} C D)
    (X : E) (Y : C) : (H.actLeft F).app X Y = H.app (F.toFunctor.obj X) Y := rfl

@[simp] theorem actRight_app {C D E : Cat} (H : Profunctor.{w} C D) (F : E ⟶ C)
    (X : D) (Y : E) : (H.actRight F).app X Y = H.app X (F.toFunctor.obj Y) := rfl

/-- Apply a natural transformation between profunctors at a pair of objects. -/
abbrev homApp {H K : Profunctor.{w} C D} (α : H ⟶ K) (X : D) (Y : C) :
    H.app X Y → K.app X Y := (α.app Y).app (.op X)

/-- Apply a transformation whose codomain is restricted on the contravariant side. -/
abbrev homAppL {C C' D : Cat} {F : C ⟶ C'} {H : Profunctor.{w} D C}
    {K : Profunctor.{w} D C'} (α : H ⟶ K.actLeft F) (X : C) (Y : D) :
    H.app X Y → K.app (F.toFunctor.obj X) Y := (α.app Y).app (.op X)

/-- Apply a transformation whose codomain is restricted on the covariant side. -/
abbrev homAppR {C D D' : Cat} {H : Profunctor.{w} D C}
    {K : Profunctor.{w} D' C} {F : D ⟶ D'} (α : H ⟶ K.actRight F) (X : C) (Y : D) :
    H.app X Y → K.app X (F.toFunctor.obj Y) := (α.app Y).app (.op X)

end CategoryTheory.Profunctor
