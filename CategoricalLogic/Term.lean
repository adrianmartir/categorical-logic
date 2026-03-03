/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

-- import Mathlib.CategoryTheory.Prof
-- import Mathlib.CategoryTheory.Category.Cat
-- import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Operad.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Discrete.SumsProducts

/-!
We construct the free T-operad on a profunctor, using a construction through terms.
-/

@[expose] public section

namespace CategoryTheory

variable (T : Monad Cat) [MonadProf T]

open FunctorProf
universe u

def Prof.ofMat {X Y} (S : X → Y → Type u) : Prof (Cat.of (Discrete X)) (Cat.of (Discrete Y)) :=
  Functor.prod (Discrete.opposite X).functor (Functor.id (Discrete Y))
  ⋙ Discrete.productEquiv.inverse
  ⋙ Discrete.functor (Function.uncurry S)

inductive Preterm {X} (S : Prof (T.obj X) X) : T.obj X → X → Type u where
| base : {a : T.obj X} → {b : X} → S.app a b → Preterm S a b
| cons : {a : T.obj X} → {b : X} → {c : (T.obj (T.obj X))} → {d : T.obj X} →
  (a ⟶ (((T.μ).app X).toFunctor.obj c)) → (mapProf.obj S).app c d →
    Preterm S d b → Preterm S a b


def ring : T.obj (Cat.of (Discrete _root_.Unit)) → _root_.Unit → Type u :=
  sorry


end CategoryTheory
