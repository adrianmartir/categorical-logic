/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Profunctor.Basic

/-!
# Elementwise notation for profunctors

For a profunctor `H : Profunctor C D` (that is, `C ⥤ Dᵒᵖ ⥤ Type w`) we write `H.app X Y`
for the value `(H.obj X).obj (op Y)` at `X : C` (the covariant side) and `Y : D` (the
contravariant side), following the order of mathlib. For example, `Profunctor.id.app X Y` is
`Y ⟶ X`, and an element of `(P.comp Q).app X Z` is represented by a pair of elements of
`P.app X Y` and `Q.app Y Z`.

Operations are named after the position of the argument they act on: `mapL` is the
covariant action on the left argument `X` and `mapR` the contravariant action on the right
argument `Y`. `mpLeft` and `mpRight` transport elements along equalities of objects; the
equality is written on the side of the argument it acts on.
-/

@[expose] public section

namespace CategoryTheory.Profunctor

universe w

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

/-- Evaluate a profunctor at a pair of objects, with the covariant object first. -/
abbrev app (H : Profunctor.{w} C D) (X : C) (Y : D) := (H.obj X).obj (.op Y)

/-- Covariant action on the left argument. -/
def mapL (H : Profunctor.{w} C D) {X X' : C} (f : X ⟶ X') {Y : D} :
    H.app X Y → H.app X' Y := (H.map f).app (.op Y)

/-- Contravariant action on the right argument. -/
def mapR (H : Profunctor.{w} C D) {Y Y' : D} (g : Y ⟶ Y') {X : C} :
    H.app X Y' → H.app X Y := (H.obj X).map g.op

@[simp] theorem mapL_id (H : Profunctor.{w} C D) (X : C) (Y : D)
    (e : H.app X Y) : H.mapL (𝟙 X) e = e := by simp [mapL]

@[simp] theorem mapR_id (H : Profunctor.{w} C D) (X : C) (Y : D)
    (e : H.app X Y) : H.mapR (𝟙 Y) e = e := by simp [mapR]

theorem mapL_comp (H : Profunctor.{w} C D) {X X' X'' : C}
    (f : X ⟶ X') (f' : X' ⟶ X'') {Y : D} (e : H.app X Y) :
    H.mapL (f ≫ f') e = H.mapL f' (H.mapL f e) := by simp [mapL]

theorem mapR_comp (H : Profunctor.{w} C D) {Y Y' Y'' : D}
    (g : Y ⟶ Y') (g' : Y' ⟶ Y'') {X : C} (e : H.app X Y'') :
    H.mapR (g ≫ g') e = H.mapR g (H.mapR g' e) := by simp [mapR]

theorem mapL_mapR_comm (H : Profunctor.{w} C D) {X X' : C} {Y Y' : D}
    (f : X ⟶ X') (g : Y ⟶ Y') (e : H.app X Y') :
    H.mapL f (H.mapR g e) = H.mapR g (H.mapL f e) :=
  ConcreteCategory.congr_hom ((H.map f).naturality g.op) e

/-- Transport an element along an equality on the left (covariant) side. -/
def mpLeft (H : Profunctor.{w} C D) {X X' : C} {Y : D}
    (h : X = X') (e : H.app X Y) : H.app X' Y := H.mapL (eqToHom h) e

/-- Transport an element along an equality on the right (contravariant) side. -/
def mpRight (H : Profunctor.{w} C D) {X : C} {Y Y' : D}
    (e : H.app X Y') (h : Y = Y') : H.app X Y := H.mapR (eqToHom h) e

@[simp] theorem mpLeft_rfl (H : Profunctor.{w} C D) {X : C} {Y : D} (e : H.app X Y) :
    H.mpLeft rfl e = e := by simp [mpLeft]

@[simp] theorem mpRight_rfl (H : Profunctor.{w} C D) {X : C} {Y : D} (e : H.app X Y) :
    H.mpRight e rfl = e := by simp [mpRight]

@[simp] theorem mpLeft_mpLeft (H : Profunctor.{w} C D) {X X' X'' : C} {Y : D}
    (h : X = X') (h' : X' = X'') (e : H.app X Y) :
    H.mpLeft h' (H.mpLeft h e) = H.mpLeft (h.trans h') e := by
  subst h h'; simp

@[simp] theorem mpRight_mpRight (H : Profunctor.{w} C D) {X : C} {Y Y' Y'' : D}
    (e : H.app X Y'') (h : Y = Y') (h' : Y' = Y'') :
    H.mpRight (H.mpRight e h') h = H.mpRight e (h.trans h') := by
  subst h h'; simp

theorem mpLeft_mpRight (H : Profunctor.{w} C D) {X X' : C} {Y Y' : D}
    (h : X = X') (e : H.app X Y') (h' : Y = Y') :
    H.mpLeft h (H.mpRight e h') = H.mpRight (H.mpLeft h e) h' :=
  H.mapL_mapR_comm _ _ e

theorem mpLeft_mapR (H : Profunctor.{w} C D) {X X' : C} {Y Y' : D}
    (h : X = X') (g : Y ⟶ Y') (e : H.app X Y') :
    H.mpLeft h (H.mapR g e) = H.mapR g (H.mpLeft h e) :=
  H.mapL_mapR_comm _ g e

theorem mpRight_mapL (H : Profunctor.{w} C D) {X X' : C} {Y Y' : D}
    (f : X ⟶ X') (e : H.app X Y') (h : Y = Y') :
    H.mpRight (H.mapL f e) h = H.mapL f (H.mpRight e h) :=
  (H.mapL_mapR_comm f _ e).symm

end CategoryTheory.Profunctor
