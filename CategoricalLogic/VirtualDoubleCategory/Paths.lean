/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# The paths monad on quivers

The free-category monad on quivers. Its unit is `Paths.of` and its multiplication
`pathsJoin` concatenates a path of paths.
-/

namespace CategoryTheory

universe u v

/-- Flatten a path of paths by concatenation.

Defined through `Quiver.Path.rec` so that it reduces definitionally on `nil` and
`cons`. -/
def flattenPath {Q : Type u} [Quiver.{v} Q] {x y : Paths (Paths Q)}
    (p : @Quiver.Path (Paths Q) _ x y) : @Quiver.Path Q _ x y :=
  @Quiver.Path.rec (Paths Q) _ x (fun t _ => @Quiver.Path Q _ x t)
    Quiver.Path.nil (fun {_ _} _ e ih => ih.comp e) y p

/-- The multiplication of the paths monad, as a prefunctor. -/
def pathsJoin (Q : Type u) [Quiver.{v} Q] : Paths (Paths Q) ⥤q Paths Q where
  obj x := x
  map := flattenPath

/-- Flattening paths of singleton paths is the identity. -/
theorem flattenPath_mapPath_of {Q : Type u} [Quiver.{v} Q] {x y : Q}
    (p : Quiver.Path x y) :
    flattenPath (@Prefunctor.mapPath Q _ (Paths Q) _ (Paths.of Q) x y p) = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change (flattenPath (@Prefunctor.mapPath Q _ (Paths Q) _ (Paths.of Q) _ _ p)).comp
      (Quiver.Hom.toPath e) = _
    rw [ih]
    rfl

end CategoryTheory
