/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

import CategoricalLogic.PathsKleisli

/-!
# Virtual double categories

A virtual double category is a monoid in the Kleisli virtual double category of `Paths`, as in
*A unified framework for generalized multicategories*: a quiver `Q`, whose vertices are the
objects and whose edges are the proarrows, a Kleisli span `hom` from `Q` to itself carrying the
arrows and the cells, a unit and a multiplication, satisfying the monoid laws.

The dictionary, following the orientation of `CategoricalLogic.QuiverSpan`:
* `hom.arr x y`, written `y →ᵥ[hom] x`, are the arrows from `y` to `x`;
* `hom.square e p a b` are the cells with n-ary source the path `p`, unary target the proarrow
  `e`, and side arrows `a` from the start of `p` to the start of `e` and `b` from the end of `p`
  to the end of `e`. The path `p` is exactly where the n-ary source comes from.

## Main definitions

* `VirtualDoubleCategory`: a virtual double category, and its elementwise accessors `idArr`,
  `compArr`, `idCell` and `subst`, which are those of nullary and binary Kleisli cells.
* `VirtualDoubleCategory.Functor`: functors of virtual double categories, which are morphisms
  of monoids, with their identity and composition.
* `VirtualDoubleCategory.Transformation`: transformations, which are squares of Kleisli spans out of
  the Kleisli identity, natural with respect to the multiplications.
* `VirtualDoubleCategory.Monad`: monads on a virtual double category.
* `SpanQuiv.hom`, `SpanQuiv.id`, `SpanQuiv.comp`: the data of the virtual double category of
  quivers, prefunctors and quiver spans.

## Implementation notes

All laws are stated abstractly, as equations between morphisms and cells of Kleisli spans.
Evaluated at an element, they are the familiar elementwise laws; the ones for arrows and
`idCell_subst` are derived below. Cells whose boundaries agree only propositionally are
compared with `QuiverSpan.castSquare` and heterogeneous equality.

## TODO

* Show that quivers, prefunctors and quiver spans satisfy the monoid laws.
* Identity transformations, vertical composition and whiskering of transformations.
-/

namespace CategoryTheory

universe u v u₁ v₁ u₂ v₂ w z w₁ z₁ w₂ z₂

open QuiverSpan hiding Square
open KleisliSpan

/-- A virtual double category whose objects and proarrows are the vertices and edges of `Q`: a
monoid in the Kleisli virtual double category of `Paths`. See the module docstring for the
dictionary. -/
structure VirtualDoubleCategory (Q : Type u) [Quiver.{v} Q] where
  /-- The arrows and the cells. -/
  hom : KleisliSpan.{u, v, u, v, w, z} Q Q
  /-- The unit: identity arrows and identity cells. -/
  id : NullaryCell hom
  /-- The multiplication: composition of arrows and substitution of cells. -/
  mul : BinaryCell hom hom hom
  one_mul : (whiskerRight id hom).comp mul = KleisliSpan.leftUnitor hom
  mul_one : (whiskerLeft hom id).comp mul = KleisliSpan.rightUnitor hom
  mul_assoc :
    (associatorInv hom hom hom).comp ((whiskerRight mul hom).comp mul) =
      (whiskerLeft hom mul).comp mul

namespace VirtualDoubleCategory

variable {Q : Type u} [Quiver.{v} Q] (V : VirtualDoubleCategory.{u, v, w, z} Q)

/-- The identity arrow on `x`, from the unit. -/
abbrev idArr (x : Q) : x →ᵥ[V.hom] x :=
  V.id.arr x

/-- Composition of arrows in diagrammatic order, from the multiplication. -/
abbrev compArr {x y z : Q} (f : x →ᵥ[V.hom] y) (g : y →ᵥ[V.hom] z) : x →ᵥ[V.hom] z :=
  V.mul.arr g f

/-- The identity cell on a proarrow `e`, from the unit: its source is the one-element path on
`e`, its target is `e`, and its sides are identity arrows. -/
abbrev idCell {x x' : Q} (e : x ⟶ x') :
    V.hom.square e ((Paths.of Q).map e) (V.idArr x) (V.idArr x') :=
  V.id.square e

/-- Substitution of cells, from the multiplication. A cell `α` with source `n` and target `e`,
together with a chain `β` of cells whose targets spell out `n`, gives a cell with target `e`
whose source is the concatenation of the sources of the cells in `β`. -/
abbrev subst {x x' : Q} {y y' : Paths Q} {z z' : Paths (Paths Q)}
    {e : x ⟶ x'} {n : y ⟶ y'} {m : z ⟶ z'}
    {a : y →ᵥ[V.hom] x} {b : y' →ᵥ[V.hom] x'} {c : z →ᵥ[V.hom] y} {d : z' →ᵥ[V.hom] y'}
    (α : V.hom.square e n a b) (β : PathSquare V.hom c n m d) :
    V.hom.square e ((Paths.flatten Q).map m) (V.compArr c a) (V.compArr d b) :=
  V.mul.square α β

theorem compArr_id {x y : Q} (f : x →ᵥ[V.hom] y) : V.compArr f (V.idArr y) = f :=
  congrArg (fun h => h.map_arr ⟨_, ⟨_, ⟨⟨rfl⟩⟩, f⟩, ⟨⟨rfl⟩⟩⟩) V.one_mul

theorem id_compArr {x y : Q} (f : x →ᵥ[V.hom] y) : V.compArr (V.idArr x) f = f :=
  congrArg (fun h => h.map_arr ⟨_, ⟨_, f, ⟨⟨rfl⟩⟩⟩, ⟨⟨rfl⟩⟩⟩) V.mul_one

theorem compArr_assoc {x y z t : Q} (f : x →ᵥ[V.hom] y) (g : y →ᵥ[V.hom] z)
    (h : z →ᵥ[V.hom] t) : V.compArr (V.compArr f g) h = V.compArr f (V.compArr g h) :=
  (congrArg (fun k => k.map_arr ⟨_, ⟨_, h, ⟨_, ⟨_, g, f⟩, ⟨⟨rfl⟩⟩⟩⟩, ⟨⟨rfl⟩⟩⟩)
    V.mul_assoc).symm

/-- Substituting a cell into an identity cell gives the cell back. -/
theorem idCell_subst {x x' y y' : Q} {e : x ⟶ x'} {p : Quiver.Path y y'} {a : y →ᵥ[V.hom] x}
    {b : y' →ᵥ[V.hom] x'} (α : V.hom.square e p a b) :
    V.subst (V.idCell e) (.single α) =
      V.hom.castSquare (Paths.flatten_map_of p).symm (V.compArr_id a).symm
        (V.compArr_id b).symm α :=
  (V.hom.eq_castSquare_iff_heq _ _ _ _ _).2 <|
    (congr_arg_heq (fun h => h.map_square (a := ⟨_, ⟨_, ⟨⟨rfl⟩⟩, a⟩, ⟨⟨rfl⟩⟩⟩)
      (b := ⟨_, ⟨_, ⟨⟨rfl⟩⟩, b⟩, ⟨⟨rfl⟩⟩⟩) ⟨_, ⟨_, ⟨⟨rfl⟩⟩, .single α⟩, ⟨⟨rfl⟩⟩⟩)
      V.one_mul).trans (V.hom.castSquare_heq (Paths.flatten_map_of p).symm rfl rfl α)

/-- The identity arrows and identity cells along a prefunctor `f`, as a square of Kleisli spans
out of the Kleisli identity: the components of an identity transformation. -/
def unitCell {P : Type u₁} [Quiver.{v₁} P] (f : P ⥤q Q) :
    Square (KleisliSpan.id P) V.hom f f :=
  QuiverSpan.Square.vComp (idMap f) V.id

/-- Composition of squares of Kleisli spans out of the Kleisli identity, in diagrammatic order:
the components of a vertical composite of transformations. -/
def compCell {P : Type u₁} [Quiver.{v₁} P] {f g h : P ⥤q Q}
    (θ : Square (KleisliSpan.id P) V.hom g f) (θ' : Square (KleisliSpan.id P) V.hom h g) :
    Square (KleisliSpan.id P) V.hom h f :=
  (leftUnitorInv (KleisliSpan.id P)).vComp (QuiverSpan.Square.vComp (θ'.hComp θ) V.mul)

/-! ### Functors -/

variable {R : Type u₁} [Quiver.{v₁} R] {S : Type u₂} [Quiver.{v₂} S]

/-- A functor of virtual double categories: a morphism of monoids. It is a prefunctor on
objects and proarrows, and a square of Kleisli spans over it acting on arrows and cells, which
preserves the unit and the multiplication. -/
structure Functor (V : VirtualDoubleCategory.{u, v, w, z} Q)
    (W : VirtualDoubleCategory.{u₁, v₁, w₁, z₁} R) where
  /-- The action on objects and proarrows. -/
  obj : Q ⥤q R
  /-- The action on arrows and cells. -/
  map : Square V.hom W.hom obj obj
  map_id : V.id.vComp map = W.unitCell obj
  map_mul : V.mul.vComp map = QuiverSpan.Square.vComp (map.hComp map) W.mul

namespace Functor

/-- The identity functor. -/
protected def id (V : VirtualDoubleCategory.{u, v, w, z} Q) : Functor V V where
  obj := 𝟭q Q
  map := Square.id V.hom
  map_id := by
    refine QuiverSpan.Square.ext (fun _ => rfl) (fun {_ _ _ _ _ n _ _} u => ?_)
    exact (Square.id_map_square_heq V.hom (V.id.map_square u)).trans <|
      V.id.map_square_heq (Prefunctor.mapPath_id n).symm rfl rfl
        (id_restrict_square_heq rfl (Prefunctor.mapPath_id n).symm _ _)
  map_mul := by
    refine QuiverSpan.Square.ext (fun _ => rfl) (fun {_ _ _ _ _ e' _ _} u => ?_)
    exact (Square.id_map_square_heq V.hom (V.mul.map_square u)).trans <|
      V.mul.map_square_heq (Prefunctor.mapPath_id e').symm rfl rfl
        (Square.id_hComp_id_map_square_heq V.hom V.hom u).symm

variable {V : VirtualDoubleCategory.{u, v, w, z} Q}
  {W : VirtualDoubleCategory.{u₁, v₁, w₁, z₁} R}

/-- Composition of functors, in diagrammatic order. -/
def comp {U : VirtualDoubleCategory.{u₂, v₂, w₂, z₂} S} (F : Functor V W) (G : Functor W U) :
    Functor V U where
  obj := F.obj ⋙q G.obj
  map := F.map.vComp G.map
  map_id := by
    refine QuiverSpan.Square.ext (fun a => ?_) (fun {_ _ _ _ _ n a b} u => ?_)
    · have h₁ := congrArg (fun s => QuiverSpan.Square.map_arr s a) F.map_id
      have h₂ := congrArg (fun s => QuiverSpan.Square.map_arr s ((idMap F.obj).map_arr a))
        G.map_id
      exact (congrArg G.map.map_arr h₁).trans h₂
    · have ha := congrArg (fun s => QuiverSpan.Square.map_arr s a) F.map_id
      have hb := congrArg (fun s => QuiverSpan.Square.map_arr s b) F.map_id
      have h₁ := congr_arg_heq (fun s => QuiverSpan.Square.map_square s u) F.map_id
      have h₂ := congr_arg_heq
        (fun s => QuiverSpan.Square.map_square s ((idMap F.obj).map_square u)) G.map_id
      refine (Square.vComp_map_square_heq F.map G.map (V.id.map_square u)).trans <|
        (G.map.map_square_heq rfl ha hb h₁).trans <| h₂.trans <|
        U.id.map_square_heq (Prefunctor.mapPath_comp_apply F.obj G.obj n).symm rfl rfl ?_
      exact id_restrict_square_heq rfl (Prefunctor.mapPath_comp_apply F.obj G.obj n).symm _ _
  map_mul := by
    refine QuiverSpan.Square.ext (fun a => ?_) (fun {_ _ _ _ _ e' a b} u => ?_)
    · have h₁ := congrArg (fun s => QuiverSpan.Square.map_arr s a) F.map_mul
      have h₂ := congrArg
        (fun s => QuiverSpan.Square.map_arr s ((F.map.hComp F.map).map_arr a)) G.map_mul
      exact (congrArg G.map.map_arr h₁).trans h₂
    · have ha := congrArg (fun s => QuiverSpan.Square.map_arr s a) F.map_mul
      have hb := congrArg (fun s => QuiverSpan.Square.map_arr s b) F.map_mul
      have h₁ := congr_arg_heq (fun s => QuiverSpan.Square.map_square s u) F.map_mul
      have h₂ := congr_arg_heq
        (fun s => QuiverSpan.Square.map_square s ((F.map.hComp F.map).map_square u)) G.map_mul
      exact (Square.vComp_map_square_heq F.map G.map (V.mul.map_square u)).trans <|
        (G.map.map_square_heq rfl ha hb h₁).trans <| h₂.trans <|
        U.mul.map_square_heq (Prefunctor.mapPath_comp_apply F.obj G.obj e').symm rfl rfl
          (Square.hComp_vComp_map_square_heq F.map F.map G.map G.map u).symm

end Functor

/-! ### Transformations and monads -/

/-- A transformation between functors `F` and `G` of virtual double categories: a square of
Kleisli spans out of the Kleisli identity, whose components are an arrow from `F x` to `G x`
for every object `x` and a cell from `F e` to `G e` for every proarrow `e`. Naturality says
that substituting `F α` into the component at the target of a cell `α` is substituting the
components along the source of `α` into `G α`. -/
structure Transformation {V : VirtualDoubleCategory.{u, v, w, z} Q}
    {W : VirtualDoubleCategory.{u₁, v₁, w₁, z₁} R} (F G : Functor V W) where
  /-- The components. -/
  app : Square (KleisliSpan.id Q) W.hom G.obj F.obj
  naturality :
    (leftUnitorInv V.hom).vComp (QuiverSpan.Square.vComp (app.hComp F.map) W.mul) =
      (KleisliSpan.rightUnitorInv V.hom).vComp (QuiverSpan.Square.vComp (G.map.hComp app) W.mul)

/-- A monad on a virtual double category: an endofunctor `T` with a unit `η : 1 ⟶ T` and a
multiplication `μ : T T ⟶ T`, satisfying the unit laws `μ ∘ ηT = 1` and `μ ∘ Tη = 1` and
associativity `μ ∘ Tμ = μ ∘ μT`, as equations between the components. -/
structure Monad (V : VirtualDoubleCategory.{u, v, w, z} Q) where
  /-- The endofunctor. -/
  T : Functor V V
  /-- The unit. -/
  η : Transformation (.id V) T
  /-- The multiplication. -/
  μ : Transformation (T.comp T) T
  left_unit : V.compCell ((idMap T.obj).vComp η.app) μ.app = V.unitCell T.obj
  right_unit : V.compCell (η.app.vComp T.map) μ.app = V.unitCell T.obj
  assoc : V.compCell (μ.app.vComp T.map) μ.app = V.compCell ((idMap T.obj).vComp μ.app) μ.app

end VirtualDoubleCategory

/-! ### Quivers, prefunctors and quiver spans -/

namespace SpanQuiv

/-- The vertices of `Paths SpanQuiv` are those of `SpanQuiv`, so they are quivers too. Instance
resolution does not see through `Paths` on its own. -/
instance (C : Paths SpanQuiv.{u, v}) : Quiver.{max u v} C.α := SpanQuiv.str' C

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
      QuiverSpan.Square (composePath ((Paths.flatten SpanQuiv.{u, v}).map m)) (composePath n) F G
  | _, _, _, _, _, .nil => QuiverSpan.Square.hId F
  | _, _, _, _, _, .cons c t =>
      QuiverSpan.Square.vComp (composePathCompInv _ _) (QuiverSpan.Square.hComp (hCompPath c) t)

/-- Composition in the virtual double category of spans: prefunctors compose on arrows, and a
chain of multisquares is substituted into a multisquare by n-ary horizontal composition
followed by vertical composition. -/
def comp : KleisliSpan.BinaryCell hom.{u, v} hom.{u, v} hom.{u, v} where
  map_arr | ⟨_, ⟨_, F, G⟩, ⟨⟨rfl⟩⟩⟩ => G ⋙q F
  map_square {_ _ _ _ _ _ a b} := fun s =>
    match a, b, s with
    | ⟨_, ⟨_, _, _⟩, ⟨⟨rfl⟩⟩⟩, ⟨_, ⟨_, _, _⟩, ⟨⟨rfl⟩⟩⟩, ⟨_, ⟨_, α, β⟩, ⟨⟨h⟩⟩⟩ =>
      h ▸ QuiverSpan.Square.vComp (hCompPath β) α

/-- Identities in the virtual double category of spans: identity prefunctors on arrows, and the
n-ary composite of a one-element path as the identity cell on a span. -/
def id : KleisliSpan.NullaryCell hom.{u, v} where
  map_arr {_ y} a :=
    match y, a with
    | _, ⟨⟨rfl⟩⟩ => 𝟭q _
  map_square {_ _ y y' A p a b} := fun s =>
    match y, y', p, a, b, s with
    | _, _, _, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩ => composePathToPath A

end SpanQuiv

end CategoryTheory
