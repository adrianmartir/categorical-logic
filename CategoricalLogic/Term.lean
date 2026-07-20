/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/



import CategoricalLogic.Operad
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Discrete.SumsProducts

/-!
We construct the free T-operad on a profunctor, using a construction through terms.
-/



namespace CategoryTheory

variable (T : Monad Cat) [MonadProf T]

open FunctorProf
universe u

def Profunctor.ofMat {X Y} (S : X → Y → Type u) :
    Profunctor (Cat.of (Discrete Y)) (Cat.of (Discrete X)) :=
  Profunctor.ofCore {
    obj y x := S x.as y.as
    map f g := fun h ↦
      (Discrete.eq_of_hom f) ▸ (Discrete.eq_of_hom g) ▸ h
    map_id _ _ := by ext; rfl
    map_comp := by
      rintro ⟨x₁⟩ ⟨x₂⟩ ⟨x₃⟩ ⟨y₁⟩ ⟨y₂⟩ ⟨y₃⟩ f f' g g'
      obtain ⟨⟨hf⟩⟩ := f
      obtain ⟨⟨hf'⟩⟩ := f'
      obtain ⟨⟨hg⟩⟩ := g
      obtain ⟨⟨hg'⟩⟩ := g'
      change x₁ = x₂ at hf
      change x₂ = x₃ at hf'
      change y₁ = y₂ at hg
      change y₂ = y₃ at hg'
      subst x₂
      subst x₃
      subst y₂
      subst y₃
      ext
      rfl }

inductive Preterm {X : Cat} (S : Profunctor X (T.obj X)) : T.obj X → X → Type u where
| base : {a : T.obj X} → {b : X} → S.app a b → Preterm S a b
| cons : {a : T.obj X} → {b : X} → {c : (T.obj (T.obj X))} → {d : T.obj X} →
  (a ⟶ (((T.μ).app X).toFunctor.obj c)) → (mapProf.obj S).app c d →
    Preterm S d b → Preterm S a b


def ring : T.obj (Cat.of (Discrete _root_.Unit)) → _root_.Unit → Type u :=
  fun _ _ ↦ PUnit


end CategoryTheory
