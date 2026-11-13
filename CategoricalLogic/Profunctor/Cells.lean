/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

module

public import CategoricalLogic.Profunctor.Product

/-!
# Cells of Profunctors

This file defines cells of profunctors, generalizing binatural transformations to
arbitrary-length paths.

## Main definitions

* `Cell`: A cell from a path of profunctors to a target profunctor, defined as a map
  out of `PathProd` that preserves the wedge relation and satisfies naturality conditions.

## Design notes

A cell from a path of profunctors to a target profunctor `K` consists of:
1. A family of maps from `PathProd p c d` to `K.app c d` for all objects `c` and `d`.
2. Naturality conditions in `c` and in `d`.
3. Compatibility with the wedge relation: if two elements of `PathProd` are related by
   `WedgeRel`, they map to the same element of `K`.

-/

@[expose] public section

namespace CategoryTheory.Profunctor

universe u v

/-! ## Cell definition -/

/-- A cell from a path of profunctors to a target profunctor.

Given a path `C₀ →[H₁] C₁ → ⋯ →[Hₙ] Cₙ` of profunctors and a target profunctor
`K : Profunctor C₀ Cₙ`, a cell consists of a family of maps
  `PathProd p c d → K.app c d`
for all choices of objects `c : C₀` and `d : Cₙ`, satisfying:

* **Left naturality** (`natL`): compatibility with the covariant action on the start `c`.
* **Right naturality** (`natR`): compatibility with the contravariant action on the end `d`.
* **Wedge condition** (`wedge`): if two elements of `PathProd` are related by `WedgeRel`,
  they map to the same element of `K`.

This generalizes `BinaryCell` (the case of two profunctors, with identity boundaries) to paths
of arbitrary length. -/
structure Cell {C D : ProfQuiv.{v, u}} (p : @Quiver.Path ProfQuiv _ C D)
    (K : Profunctor.{v} C D) where
  /-- The multi-application map: takes elements from the path product and produces
      an element of the target profunctor. -/
  app : ∀ (c : C) (d : D), PathProd p c d → K.app c d
  /-- Naturality with respect to the covariant action on the start of the path. -/
  natL : ∀ {c c' : C} {d : D} (α : c ⟶ c') (args : PathProd p c d),
    app c' d (args.mapL α) = K.mapL α (app c d args)
  /-- Naturality with respect to the contravariant action on the end of the path. -/
  natR : ∀ {c : C} {d d' : D} (args : PathProd p c d') (α : d ⟶ d'),
    app c d (args.mapR α) = K.mapR α (app c d' args)
  /-- Compatibility with the wedge relation: related path products map to equal values. -/
  wedge : ∀ {c : C} {d : D} {x y : PathProd p c d},
    WedgeRel x y → app c d x = app c d y

end CategoryTheory.Profunctor