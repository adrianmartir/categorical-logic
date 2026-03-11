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

* `Paths`: A quiver whose edges are `Quiver.Path`s, equipped with monad-like operations
  (unit and flattening) satisfying the monad laws.
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

@[expose] public section

namespace CategoryTheory.Profunctor

universe u v

/-! ## Paths as a monad on quivers -/

/-- `Paths V` is a type wrapper around `V` equipped with a quiver structure where an edge
from `a` to `b` is a `Quiver.Path a b` in the original quiver. -/
structure Paths (V : Type*) where
  /-- The underlying vertex. -/
  val : V

/-- The quiver instance on `Paths V`: edges are paths in the original quiver. -/
instance {V : Type*} [Quiver V] : Quiver (Paths V) where
  Hom a b := Quiver.Path a.val b.val

namespace Paths

variable {V : Type*} [Quiver V]

/-- The unit of the `Paths` monad: sends each edge to a singleton path. -/
def η : Prefunctor V (Paths V) where
  obj v := ⟨v⟩
  map f := .cons .nil f

/-- Flatten a path of paths into a single path by concatenation.
This is the action on morphisms of the multiplication of the `Paths` monad. -/
def flatten {a b : Paths V} :
    Quiver.Path a b → (a ⟶ b)
  | .nil => .nil
  | .cons p e => (flatten p).comp e

/-- The multiplication of the `Paths` monad as a prefunctor. -/
def μ : Prefunctor (Paths (Paths V)) (Paths V) where
  obj v := ⟨v.val.val⟩
  map := flatten

/-! ### Monad laws -/

/-- Left unit law: flattening a singleton path-of-paths recovers the original path. -/
theorem left_unit {a b : Paths V} (p : a ⟶ b) :
    flatten (.cons .nil p) = p :=
  Quiver.Path.nil_comp p

/-- Right unit law: embedding each edge as a singleton and then flattening
recovers the original path. -/
theorem right_unit {a b : V} (p : Quiver.Path a b) :
    @flatten V _ ⟨a⟩ ⟨b⟩ (@Prefunctor.mapPath V _ (Paths V) _ η a b p) = p := by
  induction p with
  | nil => rfl
  | cons p _ ih =>
    change (flatten (@Prefunctor.mapPath V _ (Paths V) _ η _ _ p)).comp _ = _
    sorry

/-- Flattening distributes over path composition. -/
theorem flatten_comp {a b c : Paths V} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    flatten (p.comp q) = (flatten p).comp (flatten q) := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    show (flatten (p.comp q)).comp e = (flatten p).comp ((flatten q).comp e)
    rw [ih, @Quiver.Path.comp_assoc V]

/-- Associativity: flattening a path of paths of paths in either order gives the same
result. -/
theorem assoc {a b : Paths (Paths V)}
    (p : @Quiver.Path (Paths (Paths V)) _ a b) :
    @flatten V _ ⟨a.val.val⟩ ⟨b.val.val⟩ (@Prefunctor.mapPath _ _ (Paths V) _ μ _ _ p) =
    @flatten V _ ⟨a.val.val⟩ ⟨b.val.val⟩ (flatten p) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    show (flatten (μ.mapPath p)).comp (flatten e) = flatten ((flatten p).comp e)
    sorry

end Paths

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
  app : ∀ (d : D) (c : C), PathProd p d c → K.obj d c
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
