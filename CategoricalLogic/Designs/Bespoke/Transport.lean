/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Profunctor.Square

/-!
# Transports of cells as heterogeneous equalities

Every law of `MonadProf` has the shape `s = t.cast hF hG`. These lemmas reduce such an equation
to a pointwise `HEq` between the components, which is how all laws for `Cat.freeMon` are proved.
They would belong in `CategoricalLogic.Profunctor.Basic` and `CategoricalLogic.Profunctor.Square`.
-/

@[expose] public section

namespace CategoryTheory.Profunctor

universe w w'

variable {C D : Type*} [Category* C] [Category* D]

theorem mpLeft_heq (H : Profunctor.{w} C D) {X X' : C} {Y : D} (h : X = X') (e : H.app X Y) :
    H.mpLeft h e ≍ e := by
  subst h; simp

theorem mpRight_heq (H : Profunctor.{w} C D) {X : C} {Y Y' : D} (e : H.app X Y') (h : Y = Y') :
    H.mpRight e h ≍ e := by
  subst h; simp

variable {C' D' A X Y Z X' Z' : Type*} [Category* C'] [Category* D'] [Category* A]
  [Category* X] [Category* Y] [Category* Z] [Category* X'] [Category* Z']

theorem Square.eq_cast_of_heq {P : Profunctor.{w} C D} {Q : Profunctor.{w'} C' D'}
    {F F' : C ⥤ C'} {G G' : D ⥤ D'} {s : Square P Q F' G'} {t : Square P Q F G}
    (hF : F = F') (hG : G = G') (h : ∀ {c d} (f : P.app c d), s.app f ≍ t.app f) :
    s = t.cast hF hG := by
  subst hF hG
  ext _ _ f
  simpa using eq_of_heq (h f)

theorem NullaryCell.eq_cast_of_heq {Q : Profunctor.{w} C D} {F F' : A ⥤ C} {G G' : A ⥤ D}
    {ν : NullaryCell Q F' G'} {μ : NullaryCell Q F G} (hF : F = F') (hG : G = G')
    (h : ∀ a, ν.app a ≍ μ.app a) : ν = μ.cast hF hG := by
  subst hF hG
  ext a
  simpa using eq_of_heq (h a)

theorem BinaryCell.eq_cast_of_heq {P : Profunctor.{w} X Y} {Q : Profunctor.{w} Y Z}
    {R : Profunctor.{w} X' Z'} {F F' : X ⥤ X'} {G G' : Z ⥤ Z'}
    {β : BinaryCell P Q R F' G'} {γ : BinaryCell P Q R F G} (hF : F = F') (hG : G = G')
    (h : ∀ {x y z} (f : P.app x y) (g : Q.app y z), β.app f g ≍ γ.app f g) :
    β = γ.cast hF hG := by
  subst hF hG
  ext _ _ _ f g
  simpa using eq_of_heq (h f g)

theorem Square.app_heq_of_eq_cast {P : Profunctor.{w} C D} {Q : Profunctor.{w'} C' D'}
    {F F' : C ⥤ C'} {G G' : D ⥤ D'} {s : Square P Q F' G'} {t : Square P Q F G}
    {hF : F = F'} {hG : G = G'} (h : s = t.cast hF hG) {c : C} {d : D} (f : P.app c d) :
    s.app f ≍ t.app f := by
  subst h
  exact (mpLeft_heq _ _ _).trans (mpRight_heq _ _ _)

theorem NullaryCell.app_heq_of_eq_cast {Q : Profunctor.{w} C D} {F F' : A ⥤ C} {G G' : A ⥤ D}
    {ν : NullaryCell Q F' G'} {μ : NullaryCell Q F G} {hF : F = F'} {hG : G = G'}
    (h : ν = μ.cast hF hG) (a : A) : ν.app a ≍ μ.app a := by
  subst h
  exact (mpLeft_heq _ _ _).trans (mpRight_heq _ _ _)

/-- Congruence for the components of a binary cell, along equalities of the middle and target
objects. -/
theorem BinaryCell.app_heq {P : Profunctor.{w} X Y} {Q : Profunctor.{w} Y Z}
    {R : Profunctor.{w} X' Z'} {F : X ⥤ X'} {G : Z ⥤ Z'} (β : BinaryCell P Q R F G) {x : X}
    {y y' : Y} {z z' : Z} {f : P.app x y} {f' : P.app x y'} {g : Q.app y z} {g' : Q.app y' z'}
    (hy : y = y') (hz : z = z') (hf : f ≍ f') (hg : g ≍ g') : β.app f g ≍ β.app f' g' := by
  subst hy hz
  cases hf
  cases hg
  rfl

end CategoryTheory.Profunctor
