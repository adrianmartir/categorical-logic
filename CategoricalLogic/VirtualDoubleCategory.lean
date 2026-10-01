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
  accessors `idArr`, `compArr`, `idCell`, `idChain`, `subst` and `substChain`. They are the
  elementwise accessors of nullary and binary Kleisli cells.
* `VirtualDoubleCategory`: a virtual double category, with its laws stated elementwise.
* `VirtualDoubleCategoryStruct.Functor`: the data of a functor of virtual double categories,
  with its identity and composition.
* `VirtualDoubleCategory.Functor`, `VirtualDoubleCategory.Transformation`: functors of virtual
  double categories and transformations between them.
* `VirtualDoubleCategory.Monad`: monads on a virtual double category.
* `SpanQuiv.virtualDoubleCategoryStruct`: quivers, prefunctors and quiver spans.

## Implementation notes

The boundaries of the two sides of a law about cells agree only propositionally, for instance
along `Paths.flatten_map_of` or along a law about arrows. Such laws transport one side with
`QuiverSpan.castSquare`, and `QuiverSpan.eq_castSquare_iff_heq` turns them into heterogeneous
equations for proofs.

## TODO

* Show that quivers, prefunctors and quiver spans satisfy the laws of a virtual double category.
* Identity transformations, vertical composition and whiskering of transformations.
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

/-- The chain of identity cells along a path of proarrows. -/
abbrev idChain {x x' : Q} (p : Quiver.Path x x') :
    PathSquare V.hom (V.idArr x) p ((Paths.of Q).mapPath p) (V.idArr x') :=
  V.id.chain p

/-- Substitution of cells, from the multiplication. A cell `α` with source `n` and target `e`,
together with a chain `β` of cells whose targets spell out `n`, gives a cell with target `e`
whose source is the concatenation of the sources of the cells in `β`. -/
abbrev subst {x x' : Q} {y y' : Paths Q} {z z' : Paths (Paths Q)}
    {e : x ⟶ x'} {n : y ⟶ y'} {m : z ⟶ z'}
    {a : y →ᵥ[V.hom] x} {b : y' →ᵥ[V.hom] x'} {c : z →ᵥ[V.hom] y} {d : z' →ᵥ[V.hom] y'}
    (α : V.hom.square e n a b) (β : PathSquare V.hom c n m d) :
    V.hom.square e ((Paths.flatten Q).map m) (V.compArr c a) (V.compArr d b) :=
  V.mul.square α β

/-- Substitution along a chain: a chain `β` of cells, and a chain of chains `γ` whose targets
spell out the sources of the cells in `β`, give the chain of the substitutions. -/
abbrev substChain {x x' : Q} {y y' : Paths Q} {z z' : Paths (Paths Q)}
    {n : Quiver.Path x x'} {m : Quiver.Path y y'} {L : Quiver.Path z z'}
    {a : y →ᵥ[V.hom] x} {b : y' →ᵥ[V.hom] x'} {c : z →ᵥ[V.hom] y} {d : z' →ᵥ[V.hom] y'}
    (β : PathSquare V.hom a n m b) (γ : PathSquare (paths V.hom) c m L d) :
    PathSquare V.hom (V.compArr c a) n ((Paths.flatten Q).mapPath L) (V.compArr d b) :=
  V.mul.chain β γ

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

end VirtualDoubleCategoryStruct

/-- A virtual double category: a monoid in the Kleisli virtual double category of `Paths`.

The laws are stated elementwise. Where the two sides of a law about cells have boundaries that
agree only propositionally, the right-hand side is transported along the laws for arrows and
the monad laws of `Paths` with `QuiverSpan.castSquare`.

Associativity of cells is stated for a chain `γ.flatten` concatenated from a chain of chains
`γ`. Every chain over a concatenated path splits like this, so this is no restriction, and it
avoids splitting chains. -/
structure VirtualDoubleCategory (Q : Type u) [Quiver.{v} Q] extends
    VirtualDoubleCategoryStruct.{u, v, w, z} Q where
  id_compArr {x y : Q} (f : x →ᵥ[hom] y) :
    toVirtualDoubleCategoryStruct.compArr (toVirtualDoubleCategoryStruct.idArr x) f = f
  compArr_id {x y : Q} (f : x →ᵥ[hom] y) :
    toVirtualDoubleCategoryStruct.compArr f (toVirtualDoubleCategoryStruct.idArr y) = f
  compArr_assoc {x y z t : Q} (f : x →ᵥ[hom] y) (g : y →ᵥ[hom] z) (h : z →ᵥ[hom] t) :
    toVirtualDoubleCategoryStruct.compArr (toVirtualDoubleCategoryStruct.compArr f g) h =
      toVirtualDoubleCategoryStruct.compArr f (toVirtualDoubleCategoryStruct.compArr g h)
  /-- Substituting a cell into an identity cell gives the cell back. -/
  idCell_subst {x x' : Q} {y y' : Paths Q} {e : x ⟶ x'} {p : y ⟶ y'}
      {a : y →ᵥ[hom] x} {b : y' →ᵥ[hom] x'} (α : hom.square e p a b) :
    toVirtualDoubleCategoryStruct.subst (toVirtualDoubleCategoryStruct.idCell e) (.single α) =
      hom.castSquare (Paths.flatten_map_of p).symm (compArr_id a).symm (compArr_id b).symm α
  /-- Substituting identity cells into a cell gives the cell back. -/
  subst_idChain {x x' : Q} {y y' : Q} {e : x ⟶ x'} {p : Quiver.Path y y'}
      {a : y →ᵥ[hom] x} {b : y' →ᵥ[hom] x'} (α : hom.square e p a b) :
    toVirtualDoubleCategoryStruct.subst α (toVirtualDoubleCategoryStruct.idChain p) =
      hom.castSquare (Paths.flatten_map_mapPath_of p).symm (id_compArr a).symm
        (id_compArr b).symm α
  /-- Substitution is associative. -/
  subst_assoc {x x' : Q} {y y' : Paths Q} {z z' : Paths (Paths Q)}
      {t t' : Paths (Paths Q)} {e : x ⟶ x'} {n : y ⟶ y'} {m : z ⟶ z'} {L : Quiver.Path t t'}
      {a : y →ᵥ[hom] x} {b : y' →ᵥ[hom] x'} {c : z →ᵥ[hom] y} {d : z' →ᵥ[hom] y'}
      {g : t →ᵥ[hom] z} {h : t' →ᵥ[hom] z'} (α : hom.square e n a b)
      (β : PathSquare hom c n m d) (γ : PathSquare (paths hom) g m L h) :
    toVirtualDoubleCategoryStruct.subst (toVirtualDoubleCategoryStruct.subst α β) γ.flatten =
      hom.castSquare (Paths.flatten_assoc (Q := Q) L).symm (compArr_assoc g c a)
        (compArr_assoc h d b)
        (toVirtualDoubleCategoryStruct.subst α (toVirtualDoubleCategoryStruct.substChain β γ))

/-! ### Functors -/

namespace VirtualDoubleCategoryStruct

variable {Q : Type u} [Quiver.{v} Q] {R : Type u₁} [Quiver.{v₁} R]
  {S : Type u₂} [Quiver.{v₂} S]

/-- The data of a functor of virtual double categories, without its axioms: a prefunctor on
objects and proarrows, and a Kleisli cell over it acting on arrows and cells. -/
structure Functor (V : VirtualDoubleCategoryStruct.{u, v, w, z} Q)
    (W : VirtualDoubleCategoryStruct.{u₁, v₁, w', z'} R) where
  /-- The action on objects and proarrows. -/
  obj : Q ⥤q R
  /-- The action on arrows and cells. -/
  map : KleisliSpan.Cell V.hom W.hom obj obj

namespace Functor

variable {V : VirtualDoubleCategoryStruct.{u, v, w, z} Q}
  {W : VirtualDoubleCategoryStruct.{u₁, v₁, w', z'} R} (F : Functor V W)

/-- The action of a functor on arrows. -/
abbrev mapArr {x y : Q} (a : x →ᵥ[V.hom] y) : F.obj.obj x →ᵥ[W.hom] F.obj.obj y :=
  F.map.map_arr a

/-- The action of a functor on cells: on the n-ary source it acts through
`Prefunctor.mapPath`. -/
abbrev mapSquare {x x' : Q} {y y' : Q} {e : x ⟶ x'} {p : Quiver.Path y y'}
    {a : y →ᵥ[V.hom] x} {b : y' →ᵥ[V.hom] x'} (α : V.hom.square e p a b) :
    W.hom.square (F.obj.map e) (F.obj.mapPath p) (F.mapArr a) (F.mapArr b) :=
  F.map.map_square α

/-- The action of a functor on chains of cells. -/
abbrev mapChain {x x' : Q} {y y' : Paths Q} {n : Quiver.Path x x'} {m : Quiver.Path y y'}
    {a : y →ᵥ[V.hom] x} {b : y' →ᵥ[V.hom] x'} (β : PathSquare V.hom a n m b) :
    PathSquare W.hom (F.mapArr a) (F.obj.mapPath n) ((Paths.map F.obj).mapPath m)
      (F.mapArr b) :=
  β.map F.map

/-- The identity functor. It transports cells along `Prefunctor.mapPath_id`. -/
@[simps obj]
protected def id (V : VirtualDoubleCategoryStruct.{u, v, w, z} Q) : Functor V V where
  obj := 𝟭q Q
  map :=
    { map_arr a := a
      map_square {_ _ _ _ _ p _ _} α := V.hom.castSquare (Prefunctor.mapPath_id p).symm rfl rfl α }

/-- Composition of functors, in diagrammatic order. It transports cells along
`Prefunctor.mapPath_comp_apply`. -/
@[simps obj]
def comp {U : VirtualDoubleCategoryStruct.{u₂, v₂, w, z} S} (G : Functor W U) :
    Functor V U where
  obj := F.obj ⋙q G.obj
  map :=
    { map_arr a := G.mapArr (F.mapArr a)
      map_square {_ _ _ _ _ p _ _} α :=
        U.hom.castSquare (Prefunctor.mapPath_comp_apply F.obj G.obj p).symm rfl rfl
          (G.mapSquare (F.mapSquare α)) }

theorem id_mapSquare_heq {x x' y y' : Q} {e : x ⟶ x'} {p : Quiver.Path y y'}
    {a : y →ᵥ[V.hom] x} {b : y' →ᵥ[V.hom] x'} (α : V.hom.square e p a b) :
    (Functor.id V).mapSquare α ≍ α :=
  V.hom.castSquare_heq (Prefunctor.mapPath_id p).symm rfl rfl α

theorem comp_mapSquare_heq {U : VirtualDoubleCategoryStruct.{u₂, v₂, w, z} S} (G : Functor W U)
    {x x' y y' : Q} {e : x ⟶ x'} {p : Quiver.Path y y'} {a : y →ᵥ[V.hom] x}
    {b : y' →ᵥ[V.hom] x'} (α : V.hom.square e p a b) :
    (F.comp G).mapSquare α ≍ G.mapSquare (F.mapSquare α) :=
  U.hom.castSquare_heq (Prefunctor.mapPath_comp_apply F.obj G.obj p).symm rfl rfl _

theorem mapSquare_castSquare_heq {x x' y y' : Q} {e : x ⟶ x'} {p₁ p₂ : Quiver.Path y y'}
    {a₁ a₂ : y →ᵥ[V.hom] x} {b₁ b₂ : y' →ᵥ[V.hom] x'} (hp : p₁ = p₂) (ha : a₁ = a₂)
    (hb : b₁ = b₂) (α : V.hom.square e p₁ a₁ b₁) :
    F.mapSquare (V.hom.castSquare hp ha hb α) ≍ F.mapSquare α := by
  subst hp ha hb
  rfl

theorem mapChain_id_heq {x x' : Q} {y y' : Paths Q} {n : Quiver.Path x x'}
    {m : Quiver.Path y y'} {a : y →ᵥ[V.hom] x} {b : y' →ᵥ[V.hom] x'}
    (β : PathSquare V.hom a n m b) : (Functor.id V).mapChain β ≍ β := by
  induction β with
  | nil => rfl
  | cons β t ih =>
    exact PathSquare.cons_heq_cons (Prefunctor.mapPath_id _) (Paths.mapPath_map_id _) rfl
      (Prefunctor.mapPath_id _) ih (id_mapSquare_heq t)

theorem mapChain_comp_heq {U : VirtualDoubleCategoryStruct.{u₂, v₂, w, z} S} (G : Functor W U)
    {x x' : Q} {y y' : Paths Q} {n : Quiver.Path x x'}
    {m : Quiver.Path y y'} {a : y →ᵥ[V.hom] x} {b : y' →ᵥ[V.hom] x'}
    (β : PathSquare V.hom a n m b) : (F.comp G).mapChain β ≍ G.mapChain (F.mapChain β) := by
  induction β with
  | nil => rfl
  | cons β t ih =>
    exact PathSquare.cons_heq_cons (Prefunctor.mapPath_comp_apply _ _ _)
      (Paths.mapPath_map_comp _ _ _) rfl (Prefunctor.mapPath_comp_apply _ _ _) ih
      (F.comp_mapSquare_heq G t)

end Functor

end VirtualDoubleCategoryStruct

namespace VirtualDoubleCategory

variable {Q : Type u} [Quiver.{v} Q] {R : Type u₁} [Quiver.{v₁} R]

/-- A functor of virtual double categories: it preserves identity arrows, composition of
arrows, identity cells and substitution. -/
structure Functor (V : VirtualDoubleCategory.{u, v, w, z} Q)
    (W : VirtualDoubleCategory.{u₁, v₁, w', z'} R) extends
    VirtualDoubleCategoryStruct.Functor V.toVirtualDoubleCategoryStruct
      W.toVirtualDoubleCategoryStruct where
  map_idArr (x : Q) : toFunctor.mapArr (V.idArr x) = W.idArr (obj.obj x)
  map_compArr {x y z : Q} (f : x →ᵥ[V.hom] y) (g : y →ᵥ[V.hom] z) :
    toFunctor.mapArr (V.compArr f g) = W.compArr (toFunctor.mapArr f) (toFunctor.mapArr g)
  map_idCell {x x' : Q} (e : x ⟶ x') :
    toFunctor.mapSquare (V.idCell e) =
      W.hom.castSquare rfl (map_idArr x).symm (map_idArr x').symm (W.idCell (obj.map e))
  map_subst {x x' : Q} {y y' : Paths Q} {z z' : Paths (Paths Q)}
      {e : x ⟶ x'} {n : y ⟶ y'} {m : z ⟶ z'}
      {a : y →ᵥ[V.hom] x} {b : y' →ᵥ[V.hom] x'} {c : z →ᵥ[V.hom] y} {d : z' →ᵥ[V.hom] y'}
      (α : V.hom.square e n a b) (β : PathSquare V.hom c n m d) :
    toFunctor.mapSquare (V.subst α β) =
      W.hom.castSquare (Paths.flatten_naturality obj m).symm (map_compArr c a).symm
        (map_compArr d b).symm (W.subst (toFunctor.mapSquare α) (toFunctor.mapChain β))

/-- A transformation between functors `F` and `G` of virtual double categories: an arrow from
`F x` to `G x` for every object `x` and a cell from `F e` to `G e` for every proarrow `e`,
natural in arrows and in cells. -/
structure Transformation {V : VirtualDoubleCategory.{u, v, w, z} Q}
    {W : VirtualDoubleCategory.{u₁, v₁, w', z'} R}
    (F G : VirtualDoubleCategoryStruct.Functor V.toVirtualDoubleCategoryStruct
      W.toVirtualDoubleCategoryStruct) where
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
  η : Transformation (.id V.toVirtualDoubleCategoryStruct) T.toFunctor
  /-- The multiplication. -/
  μ : Transformation (T.toFunctor.comp T.toFunctor) T.toFunctor
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

namespace Functor

variable {S : Type u₂} [Quiver.{v₂} S]

/-- The identity functor. -/
protected def id (V : VirtualDoubleCategory.{u, v, w, z} Q) : Functor V V where
  toFunctor := .id V.toVirtualDoubleCategoryStruct
  map_idArr _ := rfl
  map_compArr _ _ := rfl
  map_idCell _ := rfl
  map_subst {_ _ _ _ _ _ _ n m _ _ _ _} α β :=
    (V.hom.eq_castSquare_iff_heq _ _ _ _ _).2 <|
      (VirtualDoubleCategoryStruct.Functor.id_mapSquare_heq _).trans <|
      V.subst_heq_subst (Prefunctor.mapPath_id n).symm (Paths.mapPath_map_id (Q := Q) m).symm
        (VirtualDoubleCategoryStruct.Functor.id_mapSquare_heq α).symm
        (VirtualDoubleCategoryStruct.Functor.mapChain_id_heq β).symm

/-- Composition of functors, in diagrammatic order. -/
def comp {V : VirtualDoubleCategory.{u, v, w, z} Q}
    {W : VirtualDoubleCategory.{u₁, v₁, w', z'} R}
    {U : VirtualDoubleCategory.{u₂, v₂, w, z} S} (F : Functor V W) (G : Functor W U) :
    Functor V U where
  toFunctor := F.toFunctor.comp G.toFunctor
  map_idArr x := (congrArg G.mapArr (F.map_idArr x)).trans (G.map_idArr _)
  map_compArr f g := (congrArg G.mapArr (F.map_compArr f g)).trans (G.map_compArr _ _)
  map_idCell e :=
    (U.hom.eq_castSquare_iff_heq _ _ _ _ _).2 <|
      (F.toFunctor.comp_mapSquare_heq G.toFunctor _).trans <|
      (heq_of_eq (congrArg (fun s => G.mapSquare s) (F.map_idCell e))).trans <|
      (G.mapSquare_castSquare_heq _ _ _ _).trans <|
      (heq_of_eq (G.map_idCell _)).trans (U.hom.castSquare_heq _ _ _ _)
  map_subst {_ _ _ _ _ _ _ n m _ _ _ _} α β :=
    (U.hom.eq_castSquare_iff_heq _ _ _ _ _).2 <|
      (F.toFunctor.comp_mapSquare_heq G.toFunctor _).trans <|
      (heq_of_eq (congrArg (fun s => G.mapSquare s) (F.map_subst α β))).trans <|
      (G.mapSquare_castSquare_heq _ _ _ _).trans <|
      (heq_of_eq (G.map_subst _ _)).trans <| (U.hom.castSquare_heq _ _ _ _).trans <|
      U.subst_heq_subst (Prefunctor.mapPath_comp_apply F.obj G.obj n).symm
        (Paths.mapPath_map_comp F.obj G.obj m).symm
        (F.toFunctor.comp_mapSquare_heq G.toFunctor α).symm
        (F.toFunctor.mapChain_comp_heq G.toFunctor β).symm

end Functor

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

/-- Quivers, prefunctors and quiver spans, as the data of a virtual double category. -/
def virtualDoubleCategoryStruct : VirtualDoubleCategoryStruct SpanQuiv.{u, v} where
  hom := hom
  id := id
  mul := comp

end SpanQuiv

end CategoryTheory
