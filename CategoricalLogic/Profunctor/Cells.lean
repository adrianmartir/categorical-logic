/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/


import CategoricalLogic.Profunctor.Product

/-!
# Cells of Profunctors

This file defines cells of profunctors, generalizing binatural transformations to
arbitrary-length paths.

## Main definitions

* `Cell`: A cell from a path of profunctors to a target profunctor, defined as a map
  out of `PathProd` that preserves the wedge relation and satisfies naturality conditions.
* `Cell.ofComp`: Composition of cells via a binatural transformation.

## Design notes

A cell from a path of profunctors to a target profunctor `K` consists of:
1. A family of maps from `PathProd p d c` to `K.obj c d` for all objects `d` and `c`.
2. Left and right naturality conditions.
3. Compatibility with the wedge relation: if two elements of `PathProd` are related by
   `WedgeRel`, they map to the same element of `K`.

-/



namespace CategoryTheory.Profunctor

universe u v

/-! ## Cell definition -/

/-- A cell from a path of profunctors to a target profunctor.

Given a path `C₀ →[H₁] C₁ → ⋯ →[Hₙ] Cₙ` of profunctors and a target profunctor
`K : Profunctor Cₙ C₀`, a cell consists of a family of maps
  `PathProd p d c → K.obj c d`
for all choices of objects `d : Cₙ` and `c : C₀`, satisfying:

* **Left naturality** (`natL`): compatibility with acting on the source boundary `c`.
* **Right naturality** (`natR`): compatibility with acting on the target boundary `d`.
* **Wedge condition** (`wedge`): if two elements of `PathProd` are related by `WedgeRel`,
  they map to the same element of `K`.

This generalizes `BiNatTrans` (the case of two profunctors) to paths of
arbitrary length. -/
structure Cell {C D : ProfCat.{v, u}} (p : @Quiver.Path ProfCat _ C D)
    (K : Profunctor.{v} C D) where
  /-- The multi-application map: takes elements from the path product and produces
      an element of the target profunctor. -/
  app : ∀ (d : D) (c : C), PathProd p d c → K.app d c
  /-- Naturality with respect to acting on the source boundary. -/
  natL : ∀ {d d' : D} {c : C} (args : PathProd p d c) (α : d' ⟶ d),
    app d' c (args.mapL α) = K.mapL α (app d c args)
  /-- Naturality with respect to acting on the target boundary. -/
  natR : ∀ {d : D} {c c' : C} (args : PathProd p d c) (α : c ⟶ c'),
    app d c' (args.mapR α) = K.mapR α (app d c args)
  /-- Compatibility with the wedge relation: related path products map to equal values. -/
  wedge : ∀ {d : D} {c : C} {x y : PathProd p d c},
    WedgeRel x y → app d c x = app d c y

end CategoryTheory.Profunctor