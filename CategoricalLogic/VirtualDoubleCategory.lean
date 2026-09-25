/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

import CategoricalLogic.PathsKleisli

/-!
# Virtual double categories

A virtual double category is a monoid in the Kleisli virtual double category of `Paths`, as in
*A unified framework for generalized multicategories*. Unfolded, it consists of a quiver `Q`
whose vertices are the objects and whose edges are the proarrows, a Kleisli span `hom` from `Q`
to itself carrying the arrows and the cells, and two cells into `hom`.

The dictionary, following the orientation of `CategoricalLogic.QuiverSpan`:
* `hom.arr x y`, written `y →ᵥ[hom] x`, are the arrows from `y` to `x`;
* `hom.square e p a b` are the cells with n-ary source the path `p`, unary target the proarrow
  `e`, and side arrows `a` from the start of `p` to the start of `e` and `b` from the end of `p`
  to the end of `e`. The path `p` is exactly where the n-ary source comes from.

## Main definitions

* `VirtualDoubleCategoryStruct`: the data of a virtual double category, and its elementwise
  accessors `idArr`, `compArr`, `idCell` and `subst`.
* `VirtualDoubleCategoryStruct.Functor`: the data of a functor of virtual double categories.
* `SpanQuiv.virtualDoubleCategoryStruct`: quivers, prefunctors and quiver spans.

## TODO

The axioms are not stated yet. They should be stated elementwise through the accessors. For
arrows they are the usual category axioms. For cells the boundaries agree only propositionally
(for instance `Quiver.Path.flatten_mapPath_of`), and associativity needs a chain to be split
along a concatenated path, which is not available yet.
-/

namespace CategoryTheory

universe u v u₁ v₁ u₂ v₂ w z w' z'

open QuiverSpan

/-- The data of a virtual double category whose objects and proarrows are the vertices and
edges of `Q`: a monoid in the Kleisli virtual double category of `Paths`, without its axioms.
See the module docstring for the dictionary. -/
structure VirtualDoubleCategoryStruct (Q : Type u) [Quiver.{v} Q] where
  /-- The arrows and the cells. -/
  hom : KleisliSpan.{u, v, u, v, w, z} Q Q
  /-- The unit of the monoid: identity arrows and identity cells. -/
  id : KleisliSpan.NullaryCell hom
  /-- The multiplication of the monoid: composition of arrows and substitution of cells. -/
  mul : KleisliSpan.BinaryCell hom hom hom

namespace VirtualDoubleCategoryStruct

variable {Q : Type u} [Quiver.{v} Q] (V : VirtualDoubleCategoryStruct.{u, v, w, z} Q)

/-- The identity arrow on `x`, from the unit. -/
def idArr (x : Q) : x →ᵥ[V.hom] x :=
  V.id.map_arr ⟨⟨rfl⟩⟩

/-- Composition of arrows in diagrammatic order, from the multiplication. -/
def compArr {x y z : Q} (f : x →ᵥ[V.hom] y) (g : y →ᵥ[V.hom] z) : x →ᵥ[V.hom] z :=
  V.mul.map_arr ⟨x, ⟨y, g, f⟩, ⟨⟨rfl⟩⟩⟩

/-- The identity cell on a proarrow `e`, from the unit: its source is the one-element path on
`e`, its target is `e`, and its sides are identity arrows. -/
def idCell {x x' : Q} (e : x ⟶ x') :
    V.hom.square e ((Paths.of Q).map e) (V.idArr x) (V.idArr x') :=
  V.id.map_square ⟨⟨rfl⟩⟩

/-- Substitution of cells, from the multiplication. A cell `α` with source `n` and target `e`,
together with a chain `β` of cells whose targets spell out `n`, gives a cell with target `e`
whose source is the concatenation of the sources of the cells in `β`. -/
def subst {x x' : Q} {y y' : Paths Q} {z z' : Paths (Paths Q)}
    {e : x ⟶ x'} {n : y ⟶ y'} {m : z ⟶ z'}
    {a : y →ᵥ[V.hom] x} {b : y' →ᵥ[V.hom] x'} {c : z →ᵥ[V.hom] y} {d : z' →ᵥ[V.hom] y'}
    (α : V.hom.square e n a b) (β : (paths V.hom).square n m c d) :
    V.hom.square e ((Paths.flatten Q).map m) (V.compArr c a) (V.compArr d b) :=
  V.mul.map_square ⟨m, ⟨n, α, β⟩, ⟨⟨rfl⟩⟩⟩

/-- The data of a functor of virtual double categories, without its axioms: a prefunctor on
objects and proarrows, and a Kleisli cell over it acting on arrows and cells. -/
structure Functor {R : Type u₁} [Quiver.{v₁} R] (V : VirtualDoubleCategoryStruct.{u, v, w, z} Q)
    (W : VirtualDoubleCategoryStruct.{u₁, v₁, w', z'} R) where
  /-- The action on objects and proarrows. -/
  obj : Q ⥤q R
  /-- The action on arrows and cells. -/
  map : KleisliSpan.Cell V.hom W.hom obj obj

end VirtualDoubleCategoryStruct

/-! ### Quivers, prefunctors and quiver spans -/

namespace SpanQuiv

/-- The Kleisli span of the virtual double category of quivers, prefunctors and quiver spans.
Its arrows from `r` to `q` are the prefunctors `r ⥤q q`, and its cells with source a path `p`
of spans and target a span `A` are the multisquares `MultiSquare p A`. -/
def hom : KleisliSpan SpanQuiv.{u, v} SpanQuiv.{u, v} where
  arr q r := r.α ⥤q q.α
  square A p f f' := MultiSquare p A f f'

/-- n-ary horizontal composition of cells. A chain of multisquares, whose targets spell out the
path `n` of spans and whose sources spell out the path of paths `m`, composes to one square from
the composite of the concatenation of `m` to the composite of `n`. -/
def hCompPath {q : SpanQuiv.{u, v}} {r : Paths SpanQuiv.{u, v}} {F : hom.arr q r} :
    {q' : SpanQuiv.{u, v}} → {r' : Paths SpanQuiv.{u, v}} →
    {n : Quiver.Path q q'} → {m : @Quiver.Path (Paths SpanQuiv.{u, v}) _ r r'} →
    {G : hom.arr q' r'} →
    PathSquare hom F n m G →
      Square (composePath (Quiver.Path.flatten (Q := SpanQuiv.{u, v}) m)) (composePath n) F G
  | _, _, _, _, _, .nil => Square.hId F
  | _, _, _, _, _, .cons c t =>
      Square.vComp (composePathCompInv _ _) (Square.hComp (hCompPath c) t)

/-- Composition in the virtual double category of spans: prefunctors compose on arrows, and a
chain of multisquares is substituted into a multisquare by n-ary horizontal composition
followed by vertical composition. -/
def comp : KleisliSpan.BinaryCell hom.{u, v} hom.{u, v} hom.{u, v} where
  map_arr | ⟨_, ⟨_, F, G⟩, ⟨⟨rfl⟩⟩⟩ => G ⋙q F
  map_square {_ _ _ _ _ _ a b} := fun s =>
    match a, b, s with
    | ⟨_, ⟨_, _, _⟩, ⟨⟨rfl⟩⟩⟩, ⟨_, ⟨_, _, _⟩, ⟨⟨rfl⟩⟩⟩, ⟨_, ⟨_, α, β⟩, ⟨⟨h⟩⟩⟩ =>
      h ▸ Square.vComp (hCompPath β) α

/-- Identities in the virtual double category of spans: identity prefunctors on arrows, and the
n-ary composite of a one-element path as the identity cell on a span. -/
def id : KleisliSpan.NullaryCell hom.{u, v} where
  map_arr {_ y} a :=
    match y, a with
    | _, ⟨⟨rfl⟩⟩ => 𝟭q _
  map_square {_ _ y y' A p a b} := fun s =>
    match y, y', p, a, b, s with
    | _, _, _, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩ => composePathToPath A

/-- Quivers, prefunctors and quiver spans, as the data of a virtual double category. -/
def virtualDoubleCategoryStruct : VirtualDoubleCategoryStruct SpanQuiv.{u, v} where
  hom := hom
  id := id
  mul := comp

end SpanQuiv

end CategoryTheory
