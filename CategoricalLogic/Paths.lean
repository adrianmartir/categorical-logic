/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

import CategoricalLogic.QuiverSpan
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# The paths monad

`Paths` should be thought of as a monad on the virtual double category of quivers,
prefunctors and quiver spans. As in `CategoricalLogic.QuiverSpan`, this is a guiding principle
and not an instance: we never state what a monad on a virtual double category is here. Instead
each definition says in its docstring which piece of the monad structure it is.

We only build what the Kleisli virtual double category of `Paths` uses. In particular the unit
and the multiplication on spans, the comparison cells for horizontal composition, and the monad
laws on spans and cells are not here; they are what associativity and unitality of Kleisli
composition would need.

## Main definitions

* `Paths.map`, `Paths.flatten`: the functor part and the multiplication in the vertical
  direction, from mathlib's `Cat.freeMap` and `pathComposition`; the unit is mathlib's
  `Paths.of`.
* `QuiverSpan.PathSquare`, `QuiverSpan.paths`: the functor part in the horizontal direction.
* `QuiverSpan.Square.paths`, `QuiverSpan.Hom.paths`: the functor part on cells.
-/

namespace CategoryTheory

universe u v u₁ v₁ u₂ v₂ w z

/-! ### The vertical direction -/

namespace Paths

/-- `Paths` on a prefunctor: the functor part of the monad in the vertical direction.

Functoriality, `Paths.map (𝟭q Q) = 𝟭q (Paths Q)` and its analogue for composition, hold by
`Prefunctor.mapPath_id` and `Prefunctor.mapPath_comp_apply`, but neither is `rfl`. -/
def map {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R] (F : Q ⥤q R) :
    Paths Q ⥤q Paths R :=
  (Cat.freeMap F).toPrefunctor

end Paths

namespace Paths

/-- The multiplication of the monad in the vertical direction: flattening a path of paths by
concatenation. This is mathlib's `pathComposition` for the path category `Paths Q`, so on
edges it is `composePath`, which reduces definitionally on `nil` and `cons`.

The span-level multiplication, which would make Kleisli composition associative, is not
defined: Kleisli composition only uses the multiplication in this direction. -/
def flatten (Q : Type u) [Quiver.{v} Q] : Paths (Paths Q) ⥤q Paths Q :=
  (pathComposition (Paths Q)).toPrefunctor

/-- A unit law of the monad in the vertical direction: flattening the paths of one-element
paths is the identity. -/
theorem flatten_map_mapPath_of {Q : Type u} [Quiver.{v} Q] {x y : Q} (p : Quiver.Path x y) :
    (flatten Q).map ((Paths.of Q).mapPath p) = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change ((flatten Q).map ((Paths.of Q).mapPath p)).comp (Quiver.Hom.toPath e) = _
    rw [ih]
    rfl

end Paths

/-! ### The horizontal direction -/

namespace QuiverSpan

/-- A chain of squares of `A`, starting at the arrow `a`: the squares of `paths A`.

Each `cons` extends both boundary paths by one edge, so the two paths always have the same
length. Indexing the chain by its two boundary paths, rather than cutting it out of the paths
in the apex, is what makes `Paths` lift to spans at all. As for `Quiver.Path`, the start is a
parameter. -/
inductive PathSquare {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R) {x : Q} {y : R} (a : A.arr x y) :
    {x' : Q} → {y' : R} → Quiver.Path x x' → Quiver.Path y y' → A.arr x' y' →
      Type (max u₁ u₂ v₁ v₂ w z) where
  /-- The empty chain. -/
  | nil : PathSquare A a .nil .nil a
  /-- Extend a chain by one square. -/
  | cons {x' x'' : Q} {y' y'' : R} {p : Quiver.Path x x'} {q : Quiver.Path y y'}
      {e : x' ⟶ x''} {f : y' ⟶ y''} {b : A.arr x' y'} {c : A.arr x'' y''}
      (s : PathSquare A a p q b) (t : A.square e f b c) :
      PathSquare A a (p.cons e) (q.cons f) c

/-- `Paths` on a quiver span: the functor part of the monad in the horizontal direction.

The unit and multiplication on spans are not defined; see the module docstring. -/
def paths {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R) :
    QuiverSpan.{u₁, max u₁ v₁, u₂, max u₂ v₂, w, max u₁ u₂ v₁ v₂ w z}
      (Paths Q) (Paths R) where
  arr x y := A.arr x y
  square p q a b := PathSquare A a p q b

/-! ### Cells -/

namespace PathSquare

variable {Q Q' R R' : Type*} [Quiver Q] [Quiver Q'] [Quiver R] [Quiver R']

/-- Map a chain along a square, applying the prefunctors to both boundary paths. -/
def map {A : QuiverSpan Q Q'} {B : QuiverSpan R R'} {F : Q ⥤q R} {G : Q' ⥤q R'}
    (s : Square A B F G) {x x' : Q} {y y' : Q'} {a : A.arr x y}
    {p : Quiver.Path x x'} {q : Quiver.Path y y'} {b : A.arr x' y'} :
    PathSquare A a p q b →
      PathSquare B (s.map_arr a) (F.mapPath p) (G.mapPath q) (s.map_arr b)
  | .nil => .nil
  | .cons c t => .cons (map s c) (s.map_square t)

/-- Map a chain along a morphism of spans, keeping both boundary paths.

This is not a special case of `PathSquare.map`, because `(𝟭q Q).mapPath p = p` is not `rfl`. -/
def mapHom {A B : QuiverSpan Q Q'} (h : Hom A B) {x x' : Q} {y y' : Q'} {a : A.arr x y}
    {p : Quiver.Path x x'} {q : Quiver.Path y y'} {b : A.arr x' y'} :
    PathSquare A a p q b → PathSquare B (h.map_arr a) p q (h.map_arr b)
  | .nil => .nil
  | .cons c t => .cons (mapHom h c) (h.map_square t)

end PathSquare

/-- `Paths` on a square: the functor part of the monad on cells. -/
def Square.paths {Q Q' R R' : Type*} [Quiver Q] [Quiver Q'] [Quiver R] [Quiver R']
    {A : QuiverSpan Q Q'} {B : QuiverSpan R R'} {F : Q ⥤q R} {G : Q' ⥤q R'}
    (s : Square A B F G) : Square (paths A) (paths B) (Paths.map F) (Paths.map G) where
  map_arr a := s.map_arr a
  map_square c := PathSquare.map s c

/-- `Paths` on a morphism of spans: the functor part of the monad on cells, landing on
identity prefunctors on the nose. It is not a special case of `Square.paths`, because
`Paths.map (𝟭q Q) = 𝟭q (Paths Q)` is not `rfl`. -/
def Hom.paths {Q R : Type*} [Quiver Q] [Quiver R] {A B : QuiverSpan Q R} (h : Hom A B) :
    Hom (paths A) (paths B) where
  map_arr a := h.map_arr a
  map_square c := PathSquare.mapHom h c

end QuiverSpan

end CategoryTheory
