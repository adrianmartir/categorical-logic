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
* `VirtualDoubleCategory.Functor`, `VirtualDoubleCategory.Transformation`: functors of virtual
  double categories and transformations between them.
* `VirtualDoubleCategory.Monad`: monads on a virtual double category.
* `SpanQuiv.hom`, `SpanQuiv.id`, `SpanQuiv.comp`: the data of the virtual double category of
  quivers, prefunctors and quiver spans.

## Implementation notes

The laws of a virtual double category are the monoid laws, as equations between morphisms of
Kleisli spans. Elementwise they are the unit and associativity laws of composition of arrows
and of substitution of cells. The laws for arrows and `idCell_subst` are derived below, by
evaluating the monoid laws at an element.

The laws of functors, transformations and monads are stated elementwise. There the boundaries
of the two sides of a law about cells agree only propositionally, so one side is transported
with `QuiverSpan.castSquare`, and `QuiverSpan.eq_castSquare_iff_heq` turns such laws into
heterogeneous equations for proofs.

## TODO

* Show that quivers, prefunctors and quiver spans satisfy the monoid laws.
* Identity transformations, vertical composition and whiskering of transformations.
-/

namespace CategoryTheory

universe u v u₁ v₁ u₂ v₂ w z w₁ z₁ w₂ z₂

open QuiverSpan KleisliSpan

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

/-- Congruence for substitution along equal boundary paths. -/
theorem subst_heq_subst {x x' : Q} {y y' : Paths Q} {z z' : Paths (Paths Q)} {e : x ⟶ x'}
    {n n' : y ⟶ y'} {m m' : z ⟶ z'} {a : y →ᵥ[V.hom] x} {b : y' →ᵥ[V.hom] x'}
    {c : z →ᵥ[V.hom] y} {d : z' →ᵥ[V.hom] y'} (hn : n = n') (hm : m = m')
    {α : V.hom.square e n a b} {α' : V.hom.square e n' a b} {β : PathSquare V.hom c n m d}
    {β' : PathSquare V.hom c n' m' d} (hα : α ≍ α') (hβ : β ≍ β') :
    V.subst α β ≍ V.subst α' β' := by
  subst hn hm
  obtain rfl := eq_of_heq hα
  obtain rfl := eq_of_heq hβ
  rfl

/-! ### Functors -/

variable {R : Type u₁} [Quiver.{v₁} R] {S : Type u₂} [Quiver.{v₂} S]

/-- A functor of virtual double categories: a prefunctor on objects and proarrows, and a
Kleisli cell over it acting on arrows and cells, preserving identity arrows, composition of
arrows, identity cells and substitution. On the n-ary source of a cell it acts through
`Prefunctor.mapPath`. -/
structure Functor (V : VirtualDoubleCategory.{u, v, w, z} Q)
    (W : VirtualDoubleCategory.{u₁, v₁, w₁, z₁} R) where
  /-- The action on objects and proarrows. -/
  obj : Q ⥤q R
  /-- The action on arrows and cells. -/
  map : Cell V.hom W.hom obj obj
  map_idArr (x : Q) : map.map_arr (V.idArr x) = W.idArr (obj.obj x)
  map_compArr {x y z : Q} (f : x →ᵥ[V.hom] y) (g : y →ᵥ[V.hom] z) :
    map.map_arr (V.compArr f g) = W.compArr (map.map_arr f) (map.map_arr g)
  map_idCell {x x' : Q} (e : x ⟶ x') :
    map.map_square (V.idCell e) =
      W.hom.castSquare rfl (map_idArr x).symm (map_idArr x').symm (W.idCell (obj.map e))
  map_subst {x x' : Q} {y y' : Paths Q} {z z' : Paths (Paths Q)}
      {e : x ⟶ x'} {n : y ⟶ y'} {m : z ⟶ z'}
      {a : y →ᵥ[V.hom] x} {b : y' →ᵥ[V.hom] x'} {c : z →ᵥ[V.hom] y} {d : z' →ᵥ[V.hom] y'}
      (α : V.hom.square e n a b) (β : PathSquare V.hom c n m d) :
    map.map_square (V.subst α β) =
      W.hom.castSquare (Paths.flatten_naturality obj m).symm (map_compArr c a).symm
        (map_compArr d b).symm (W.subst (map.map_square α) (β.map map))

namespace Functor

variable {V : VirtualDoubleCategory.{u, v, w, z} Q}
  {W : VirtualDoubleCategory.{u₁, v₁, w₁, z₁} R} (F : Functor V W)

/-- The action of a functor on arrows. -/
abbrev mapArr {x y : Q} (a : x →ᵥ[V.hom] y) : F.obj.obj x →ᵥ[W.hom] F.obj.obj y :=
  F.map.map_arr a

/-- The action of a functor on cells. -/
abbrev mapSquare {x x' : Q} {y y' : Q} {e : x ⟶ x'} {p : Quiver.Path y y'}
    {a : y →ᵥ[V.hom] x} {b : y' →ᵥ[V.hom] x'} (α : V.hom.square e p a b) :
    W.hom.square (F.obj.map e) (F.obj.mapPath p) (F.mapArr a) (F.mapArr b) :=
  F.map.map_square α

/-- The identity functor. -/
protected def id (V : VirtualDoubleCategory.{u, v, w, z} Q) : Functor V V where
  obj := 𝟭q Q
  map := Cell.id V.hom
  map_idArr _ := rfl
  map_compArr _ _ := rfl
  map_idCell _ := rfl
  map_subst {_ _ _ _ _ _ _ n m _ _ _ _} α β :=
    (V.hom.eq_castSquare_iff_heq _ _ _ _ _).2 <| (Cell.id_map_square_heq _ _).trans <|
      V.subst_heq_subst (Prefunctor.mapPath_id n).symm (Paths.mapPath_map_id (Q := Q) m).symm
        (Cell.id_map_square_heq _ α).symm (Cell.id_map_chain_heq _ β).symm

/-- Composition of functors, in diagrammatic order. -/
def comp {U : VirtualDoubleCategory.{u₂, v₂, w₂, z₂} S} (G : Functor W U) : Functor V U where
  obj := F.obj ⋙q G.obj
  map := F.map.vComp G.map
  map_idArr x := (congrArg G.mapArr (F.map_idArr x)).trans (G.map_idArr _)
  map_compArr f g := (congrArg G.mapArr (F.map_compArr f g)).trans (G.map_compArr _ _)
  map_idCell e :=
    (U.hom.eq_castSquare_iff_heq _ _ _ _ _).2 <| (Cell.vComp_map_square_heq _ _ _).trans <|
      (heq_of_eq (congrArg (fun s => G.mapSquare s) (F.map_idCell e))).trans <|
      (G.map.map_square_castSquare_heq _ _ _ _).trans <|
      (heq_of_eq (G.map_idCell _)).trans (U.hom.castSquare_heq _ _ _ _)
  map_subst {_ _ _ _ _ _ _ n m _ _ _ _} α β :=
    (U.hom.eq_castSquare_iff_heq _ _ _ _ _).2 <| (Cell.vComp_map_square_heq _ _ _).trans <|
      (heq_of_eq (congrArg (fun s => G.mapSquare s) (F.map_subst α β))).trans <|
      (G.map.map_square_castSquare_heq _ _ _ _).trans <|
      (heq_of_eq (G.map_subst _ _)).trans <| (U.hom.castSquare_heq _ _ _ _).trans <|
      U.subst_heq_subst (Prefunctor.mapPath_comp_apply F.obj G.obj n).symm
        (Paths.mapPath_map_comp F.obj G.obj m).symm
        (Cell.vComp_map_square_heq F.map G.map α).symm
        (Cell.vComp_map_chain_heq F.map G.map β).symm

end Functor

/-! ### Transformations and monads -/

/-- A transformation between functors `F` and `G` of virtual double categories: an arrow from
`F x` to `G x` for every object `x` and a cell from `F e` to `G e` for every proarrow `e`,
natural in arrows and in cells. -/
structure Transformation {V : VirtualDoubleCategory.{u, v, w, z} Q}
    {W : VirtualDoubleCategory.{u₁, v₁, w₁, z₁} R} (F G : Functor V W) where
  /-- The component at an object. -/
  app (x : Q) : F.obj.obj x →ᵥ[W.hom] G.obj.obj x
  /-- The component at a proarrow: a cell with unary source `F e` and target `G e`. -/
  cell {x x' : Q} (e : x ⟶ x') :
    W.hom.square (G.obj.map e) ((Paths.of R).map (F.obj.map e)) (app x) (app x')
  naturality {x y : Q} (a : x →ᵥ[V.hom] y) :
    W.compArr (F.mapArr a) (app y) = W.compArr (app x) (G.mapArr a)
  /-- Naturality in cells: substituting `F α` into the component at the target of `α` is
  substituting the components along the source of `α` into `G α`. -/
  naturality_cell {x x' y y' : Q} {e : x ⟶ x'} {p : Quiver.Path y y'}
      {a : y →ᵥ[V.hom] x} {b : y' →ᵥ[V.hom] x'} (α : V.hom.square e p a b) :
    W.subst (cell e) (.single (F.mapSquare α)) =
      W.hom.castSquare
        ((Paths.flatten_map_mapPath_comp_of F.obj p).trans (Paths.flatten_map_of _).symm)
        (naturality a).symm (naturality b).symm
        (W.subst (G.mapSquare α) (.ofPath G.obj (F.obj ⋙q Paths.of R) app cell p))

/-- A monad on a virtual double category: an endofunctor `T` with a unit `η : 1 ⟶ T` and a
multiplication `μ : T T ⟶ T`, satisfying the unit laws `μ ∘ ηT = 1` and `μ ∘ Tη = 1` and
associativity `μ ∘ Tμ = μ ∘ μT`. The laws are stated componentwise, on objects and on
proarrows. -/
structure Monad (V : VirtualDoubleCategory.{u, v, w, z} Q) where
  /-- The endofunctor. -/
  T : Functor V V
  /-- The unit. -/
  η : Transformation (.id V) T
  /-- The multiplication. -/
  μ : Transformation (T.comp T) T
  left_unit (x : Q) : V.compArr (η.app (T.obj.obj x)) (μ.app x) = V.idArr (T.obj.obj x)
  right_unit (x : Q) : V.compArr (T.mapArr (η.app x)) (μ.app x) = V.idArr (T.obj.obj x)
  assoc (x : Q) :
    V.compArr (T.mapArr (μ.app x)) (μ.app x) = V.compArr (μ.app (T.obj.obj x)) (μ.app x)
  left_unit_cell {x x' : Q} (e : x ⟶ x') :
    V.subst (μ.cell e) (.single (η.cell (T.obj.map e))) =
      V.hom.castSquare rfl (left_unit x).symm (left_unit x').symm (V.idCell (T.obj.map e))
  right_unit_cell {x x' : Q} (e : x ⟶ x') :
    V.subst (μ.cell e) (.single (T.mapSquare (η.cell e))) =
      V.hom.castSquare rfl (right_unit x).symm (right_unit x').symm (V.idCell (T.obj.map e))
  assoc_cell {x x' : Q} (e : x ⟶ x') :
    V.subst (μ.cell e) (.single (T.mapSquare (μ.cell e))) =
      V.hom.castSquare rfl (assoc x).symm (assoc x').symm
        (V.subst (μ.cell e) (.single (μ.cell (T.obj.map e))))

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
      Square (composePath ((Paths.flatten SpanQuiv.{u, v}).map m)) (composePath n) F G
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

end SpanQuiv

end CategoryTheory
