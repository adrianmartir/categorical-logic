/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/
module

public import CategoricalLogic.Profunctor.Basic

/-!
# The Hom Profunctor

For any category `C`, the **hom profunctor** `Profunctor.hom C` is the profunctor that sends
a pair of objects `(d, c)` to the hom set `d ⟶ c`. It is contravariant in the first argument
and covariant in the second, acting by pre- and post-composition.

## Main definitions

* `Profunctor.hom` — the hom profunctor on a category `C`.

## Main results

* `Profunctor.hom_mapL` — left mapping is precomposition.
* `Profunctor.hom_mapR` — right mapping is postcomposition.
-/

@[expose] public section

namespace CategoryTheory.Profunctor

universe w u v

variable {C : Type u} [Category.{v} C]

/-! ### The Hom Profunctor -/

/-- The hom profunctor on a category `C`. For objects `d` and `c`, it returns the hom type
`c ⟶ d`. The mapping acts by pre-composition (contravariantly) and post-composition
(covariantly). -/
@[simps]
def hom (C : Type u) [Category.{v} C] : Profunctor.{v} C C where
  obj d c := d ⟶ c
  map f g h := f ≫ h ≫ g
  map_id _ _ e := by simp
  map_comp f' f g g' e := by simp [Category.assoc]

/-- Left mapping in the hom profunctor is precomposition. -/
@[simp]
theorem hom_mapL {X X' Y : C} (f : X' ⟶ X) (h : X ⟶ Y) :
    (hom C).mapL f h = f ≫ h := by
  simp [Profunctor.mapL, hom]

/-- Right mapping in the hom profunctor is postcomposition. -/
@[simp]
theorem hom_mapR {X Y Y' : C} (g : Y ⟶ Y') (h : X ⟶ Y) :
    (hom C).mapR g h = h ≫ g := by
  simp [Profunctor.mapR, hom]

end CategoryTheory.Profunctor
