/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

module

public import CategoricalLogic.VirtualDoubleCategory.Paths

/-!
# The Kleisli virtual double category of `Paths`

The horizontal Kleisli virtual double category of the `Paths` monad, following *A unified
framework for generalized multicategories*: a horizontal arrow from `Q` to `R` is a quiver span
from `Q` to `Paths R`. Virtual double categories are the monoids here; they are defined in
`CategoricalLogic.VirtualDoubleCategory.Basic`.

Following the orientation of `CategoricalLogic.VirtualDoubleCategory.QuiverSpan`, the right leg `Paths R` carries the
sources: a square of a Kleisli span has a single edge as target and a path as source.

## Main definitions

* `KleisliSpan`: horizontal arrows.
* `KleisliSpan.id`, `KleisliSpan.comp`: the Kleisli identity and binary Kleisli composition.
* `KleisliSpan.Square`: squares of Kleisli spans, the cells with unary source.
* `KleisliSpan.NullaryCell`, `KleisliSpan.BinaryCell`: cells with nullary and binary source.
* `KleisliSpan.whiskerLeft`, `KleisliSpan.whiskerRight`: whiskering of morphisms of Kleisli
  spans.
* `KleisliSpan.leftUnitor`, `KleisliSpan.rightUnitor`, their inverses, and
  `KleisliSpan.associatorInv`: the coherence cells of Kleisli composition that the laws of
  virtual double categories use. Only the inverse of the associator is needed, and it only
  concatenates chains, never splits them.
* `KleisliSpan.Square.id`, `KleisliSpan.Square.vComp`, `KleisliSpan.Square.hComp`: identity,
  vertical and horizontal composition of squares of Kleisli spans, and
  `KleisliSpan.idMap`, the Kleisli identity on a prefunctor.
* `KleisliSpan.NullaryCell.arr`, `.square` and `KleisliSpan.BinaryCell.arr`, `.square`:
  nullary and binary cells elementwise, on arrows and on squares. The accessors of virtual
  double categories are these.
-/

@[expose] public section

namespace CategoryTheory

universe u v u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ w z

-- The apex universes `w` and `z` only occur together in the type; they are determined by the
-- span a `KleisliSpan` is unified with, exactly as for `QuiverSpan`.
set_option linter.checkUnivs false in
/-- A horizontal arrow from `Q` to `R` in the Kleisli virtual double category of `Paths`: a
quiver span from `Q` to `Paths R`. -/
abbrev KleisliSpan (Q : Type u₁) (R : Type u₂) [Quiver.{v₁} Q] [Quiver.{v₂} R] :=
  QuiverSpan.{u₁, v₁, u₂, max u₂ v₂, w, z} Q (Paths R)

namespace KleisliSpan

open QuiverSpan hiding Square

/-- The Kleisli identity: the horizontal identity on `Paths Q`, restricted along the unit
`Paths.of Q` of the monad on the left. -/
protected def id (Q : Type u) [Quiver.{v} Q] : KleisliSpan Q Q :=
  (QuiverSpan.id (Paths Q)).restrict (Paths.of Q) (𝟭q (Paths Q))

/-- Binary Kleisli composition: the horizontal composite of `A`, of `paths B`, and of the
horizontal identity on `Paths R` restricted along the multiplication `Paths.flatten R` of the
monad on the left. -/
protected def comp {P : Type u₁} {Q : Type u₂} {R : Type u₃}
    [Quiver.{v₁} P] [Quiver.{v₂} Q] [Quiver.{v₃} R]
    (A : KleisliSpan P Q) (B : KleisliSpan Q R) : KleisliSpan P R :=
  QuiverSpan.comp (QuiverSpan.comp A (paths B))
    ((QuiverSpan.id (Paths R)).restrict (Paths.flatten R) (𝟭q (Paths R)))

/-- Whiskering a morphism of Kleisli spans on the right of a Kleisli composite. -/
def whiskerRight {P : Type u₁} {Q : Type u₂} {R : Type u₃}
    [Quiver.{v₁} P] [Quiver.{v₂} Q] [Quiver.{v₃} R]
    {A A' : KleisliSpan P Q} (f : Hom A A') (B : KleisliSpan Q R) :
    Hom (A.comp B) (A'.comp B) :=
  QuiverSpan.Square.hComp (QuiverSpan.Square.hComp f (QuiverSpan.Square.id _))
    (QuiverSpan.Square.id _)

/-- Whiskering a morphism of Kleisli spans on the left of a Kleisli composite. -/
def whiskerLeft {P : Type u₁} {Q : Type u₂} {R : Type u₃}
    [Quiver.{v₁} P] [Quiver.{v₂} Q] [Quiver.{v₃} R]
    (A : KleisliSpan P Q) {B B' : KleisliSpan Q R} (g : Hom B B') :
    Hom (A.comp B) (A.comp B') :=
  QuiverSpan.Square.hComp (QuiverSpan.Square.hComp (QuiverSpan.Square.id A) (Hom.paths g))
    (QuiverSpan.Square.id _)

/-- The square of the left unitor, from the components of a square of the composite. -/
def leftUnitorSquare {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    {A : KleisliSpan Q R} {x x' : Q} {y y' : Paths R} {e : x ⟶ x'} {e' : y ⟶ y'}
    {a : A.arr x y} {b : A.arr x' y'} {n : Quiver.Path x x'}
    {m : Quiver.Path (V := Paths R) y y'} (hn : (Paths.of Q).map e = n)
    (c : PathSquare A a n m b) (h : (Paths.flatten R).map m = e') : A.square e e' a b :=
  match n, m, hn, c, h with
  | _, _, rfl, .cons .nil t, h =>
    A.castSquare ((Paths.flatten_map_of (Q := R) _).symm.trans h) rfl rfl t

/-- The left unitor of Kleisli composition. A square of the composite consists of the
one-element path on its target and a one-element chain, whose square is the result. -/
def leftUnitor {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : KleisliSpan Q R) : Hom ((KleisliSpan.id Q).comp A) A where
  map_arr | ⟨_, ⟨_, ⟨⟨rfl⟩⟩, a⟩, ⟨⟨rfl⟩⟩⟩ => a
  map_square {_ _ _ _ _ _ a b} := fun s =>
    match a, b, s with
    | ⟨_, ⟨_, ⟨⟨rfl⟩⟩, _⟩, ⟨⟨rfl⟩⟩⟩, ⟨_, ⟨_, ⟨⟨rfl⟩⟩, _⟩, ⟨⟨rfl⟩⟩⟩, ⟨_, ⟨_, ⟨⟨hn⟩⟩, c⟩, ⟨⟨h⟩⟩⟩ =>
      leftUnitorSquare hn c h

/-- The right unitor of Kleisli composition. A square of the composite consists of a square
and a chain of Kleisli identities, which forces its source to be the path of one-element
paths on the source of the square. -/
def rightUnitor {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : KleisliSpan Q R) : Hom (A.comp (KleisliSpan.id R)) A where
  map_arr | ⟨_, ⟨_, a, ⟨⟨rfl⟩⟩⟩, ⟨⟨rfl⟩⟩⟩ => a
  map_square {_ _ _ _ _ _ a b} := fun s =>
    match a, b, s with
    | ⟨_, ⟨_, _, ⟨⟨rfl⟩⟩⟩, ⟨⟨rfl⟩⟩⟩, ⟨_, ⟨_, _, ⟨⟨rfl⟩⟩⟩, ⟨⟨rfl⟩⟩⟩, ⟨_, ⟨n, α, c⟩, ⟨⟨h⟩⟩⟩ =>
      A.castSquare ((Paths.flatten_map_mapPath_of n).symm.trans
        ((congrArg (Paths.flatten R).map
          (eq_of_heq (PathSquare.mapPath_heq_of_restrict_id _ c))).trans h)) rfl rfl α

/-- The chain of squares of the Kleisli identity along a path. -/
def idChain {Q : Type u} [Quiver.{v} Q] {x : Q} :
    {x' : Q} → (p : Quiver.Path x x') →
      PathSquare (KleisliSpan.id Q) ⟨⟨rfl⟩⟩ p ((Paths.of Q).mapPath p) ⟨⟨rfl⟩⟩
  | _, .nil => .nil
  | _, .cons p _ => .cons (idChain p) ⟨⟨rfl⟩⟩

/-- The inverse of the left unitor of Kleisli composition. -/
def leftUnitorInv {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : KleisliSpan Q R) : Hom A ((KleisliSpan.id Q).comp A) where
  map_arr a := ⟨_, ⟨_, ⟨⟨rfl⟩⟩, a⟩, ⟨⟨rfl⟩⟩⟩
  map_square α := ⟨_, ⟨_, ⟨⟨rfl⟩⟩, .single α⟩, ⟨⟨Paths.flatten_map_of _⟩⟩⟩

/-- The inverse of the right unitor of Kleisli composition. -/
def rightUnitorInv {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : KleisliSpan Q R) : Hom A (A.comp (KleisliSpan.id R)) where
  map_arr a := ⟨_, ⟨_, a, ⟨⟨rfl⟩⟩⟩, ⟨⟨rfl⟩⟩⟩
  map_square {_ _ _ _ _ n _ _} α :=
    ⟨_, ⟨n, α, idChain n⟩, ⟨⟨Paths.flatten_map_mapPath_of n⟩⟩⟩

/-- The inverse of the associator of Kleisli composition. It unzips the chain of a square of
`A.comp (B.comp C)` into a chain of `B` and a chain of chains of `C`, and concatenates the
latter. -/
def associatorInv {P : Type u₁} {Q : Type u₂} {R : Type u₃} {S : Type u₄}
    [Quiver.{v₁} P] [Quiver.{v₂} Q] [Quiver.{v₃} R] [Quiver.{v₄} S]
    (A : KleisliSpan P Q) (B : KleisliSpan Q R) (C : KleisliSpan R S) :
    Hom (A.comp (B.comp C)) ((A.comp B).comp C) where
  map_arr
    | ⟨_, ⟨_, a, ⟨_, ⟨_, b, c⟩, ⟨⟨rfl⟩⟩⟩⟩, ⟨⟨rfl⟩⟩⟩ =>
      ⟨_, ⟨_, ⟨_, ⟨_, a, b⟩, ⟨⟨rfl⟩⟩⟩, c⟩, ⟨⟨rfl⟩⟩⟩
  map_square {_ _ _ _ _ _ a b} := fun s =>
    match a, b, s with
    | ⟨_, ⟨_, _, ⟨_, ⟨_, _, _⟩, ⟨⟨rfl⟩⟩⟩⟩, ⟨⟨rfl⟩⟩⟩,
        ⟨_, ⟨_, _, ⟨_, ⟨_, _, _⟩, ⟨⟨rfl⟩⟩⟩⟩, ⟨⟨rfl⟩⟩⟩, ⟨_, ⟨n, α, βγ⟩, ⟨⟨h⟩⟩⟩ =>
      ⟨_, ⟨_, ⟨_, ⟨n, α, (PathSquare.unzip (PathSquare.unzip βγ).2.1).2.1⟩, ⟨⟨rfl⟩⟩⟩,
        (PathSquare.unzip (PathSquare.unzip βγ).2.1).2.2.flatten⟩,
        ⟨⟨(Paths.flatten_assoc _).trans ((congrArg (Paths.flatten S).map (eq_of_heq
          (PathSquare.mapPath_heq_of_restrict_id _ (PathSquare.unzip βγ).2.2))).trans h)⟩⟩⟩

/-- A square of Kleisli spans from `A` to `B` with vertical sides `f` and `g`: a square of quiver
spans from `A` to `B` over `f` and `Paths.map g`. As a cell of the Kleisli virtual double
category it has unary source `A` and target `B`. -/
abbrev Square {Q : Type u₁} {R : Type u₂} {Q' : Type u₃} {R' : Type u₄}
    [Quiver.{v₁} Q] [Quiver.{v₂} R] [Quiver.{v₃} Q'] [Quiver.{v₄} R']
    (A : KleisliSpan Q R) (B : KleisliSpan Q' R') (f : Q ⥤q Q') (g : R ⥤q R') :=
  QuiverSpan.Square A B f (Paths.map g)

namespace Square

/-- The identity square of a Kleisli span. It transports squares along
`Prefunctor.mapPath_id`. -/
protected def id {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : KleisliSpan.{u₁, v₁, u₂, v₂, w, z} Q R) : Square A A (𝟭q Q) (𝟭q R) where
  map_arr a := a
  map_square {_ _ _ _ _ p _ _} α := A.castSquare (Prefunctor.mapPath_id p).symm rfl rfl α

/-- Vertical composition of squares of Kleisli spans. It transports squares along
`Prefunctor.mapPath_comp_apply`. -/
def vComp {Q₀ : Type u₁} {R₀ : Type u₂} {Q₁ : Type u₃} {R₁ : Type u₄} {Q₂ : Type*}
    {R₂ : Type*} [Quiver.{v₁} Q₀] [Quiver.{v₂} R₀] [Quiver.{v₃} Q₁] [Quiver.{v₄} R₁]
    [Quiver Q₂] [Quiver R₂] {A : KleisliSpan Q₀ R₀} {B : KleisliSpan Q₁ R₁}
    {C : KleisliSpan Q₂ R₂} {F : Q₀ ⥤q Q₁} {G : R₀ ⥤q R₁} {F' : Q₁ ⥤q Q₂} {G' : R₁ ⥤q R₂}
    (f : Square A B F G) (g : Square B C F' G') : Square A C (F ⋙q F') (G ⋙q G') where
  map_arr a := g.map_arr (f.map_arr a)
  map_square {_ _ _ _ _ p _ _} α :=
    C.castSquare (G.mapPath_comp_apply G' p).symm rfl rfl (g.map_square (f.map_square α))

theorem id_map_square_heq {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : KleisliSpan.{u₁, v₁, u₂, v₂, w, z} Q R) {x x' : Q} {y y' : R} {e : x ⟶ x'}
    {p : Quiver.Path y y'} {a : A.arr x y} {b : A.arr x' y'} (α : A.square e p a b) :
    (Square.id A).map_square α ≍ α :=
  A.castSquare_heq (Prefunctor.mapPath_id p).symm rfl rfl α

theorem vComp_map_square_heq {Q₀ : Type u₁} {R₀ : Type u₂} {Q₁ : Type u₃} {R₁ : Type u₄}
    {Q₂ : Type*} {R₂ : Type*} [Quiver.{v₁} Q₀] [Quiver.{v₂} R₀] [Quiver.{v₃} Q₁]
    [Quiver.{v₄} R₁] [Quiver Q₂] [Quiver R₂] {A : KleisliSpan Q₀ R₀} {B : KleisliSpan Q₁ R₁}
    {C : KleisliSpan Q₂ R₂} {F : Q₀ ⥤q Q₁} {G : R₀ ⥤q R₁} {F' : Q₁ ⥤q Q₂} {G' : R₁ ⥤q R₂}
    (f : Square A B F G) (g : Square B C F' G') {x x' : Q₀} {y y' : R₀} {e : x ⟶ x'}
    {p : Quiver.Path y y'} {a : A.arr x y} {b : A.arr x' y'} (α : A.square e p a b) :
    (f.vComp g).map_square α ≍ g.map_square (f.map_square α) :=
  C.castSquare_heq (G.mapPath_comp_apply G' p).symm rfl rfl _

theorem id_map_chain_heq {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : KleisliSpan.{u₁, v₁, u₂, v₂, w, z} Q R) {x x' : Q} {y y' : Paths R}
    {n : Quiver.Path x x'} {m : Quiver.Path y y'} {a : A.arr x y} {b : A.arr x' y'}
    (β : PathSquare A a n m b) : β.map (Square.id A) ≍ β := by
  induction β with
  | nil => rfl
  | cons β t ih =>
    exact PathSquare.cons_heq_cons (Prefunctor.mapPath_id _) (Paths.mapPath_map_id _) rfl
      (Prefunctor.mapPath_id _) ih (id_map_square_heq A t)

theorem vComp_map_chain_heq {Q₀ : Type u₁} {R₀ : Type u₂} {Q₁ : Type u₃} {R₁ : Type u₄}
    {Q₂ : Type*} {R₂ : Type*} [Quiver.{v₁} Q₀] [Quiver.{v₂} R₀] [Quiver.{v₃} Q₁]
    [Quiver.{v₄} R₁] [Quiver Q₂] [Quiver R₂] {A : KleisliSpan Q₀ R₀} {B : KleisliSpan Q₁ R₁}
    {C : KleisliSpan Q₂ R₂} {F : Q₀ ⥤q Q₁} {G : R₀ ⥤q R₁} {F' : Q₁ ⥤q Q₂} {G' : R₁ ⥤q R₂}
    (f : Square A B F G) (g : Square B C F' G') {x x' : Q₀} {y y' : Paths R₀}
    {n : Quiver.Path x x'} {m : Quiver.Path y y'} {a : A.arr x y} {b : A.arr x' y'}
    (β : PathSquare A a n m b) : β.map (f.vComp g) ≍ (β.map f).map g := by
  induction β with
  | nil => rfl
  | cons β t ih =>
    exact PathSquare.cons_heq_cons (Prefunctor.mapPath_comp_apply _ _ _)
      (Paths.mapPath_map_comp _ _ _) rfl (Prefunctor.mapPath_comp_apply _ _ _) ih
      (vComp_map_square_heq f g t)

end Square

/-- The Kleisli identity is functorial in prefunctors. -/
def idMap {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R] (f : Q ⥤q R) :
    Square (KleisliSpan.id Q) (KleisliSpan.id R) f f where
  map_arr a := ⟨⟨congrArg f.obj a.down.down⟩⟩
  map_square {_ _ y y' _ n a b} u :=
    match y, y', n, a, b, u with
    | _, _, _, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩ => ⟨⟨rfl⟩⟩

/-- Naturality of `Paths.flatten`, as a square between the restrictions of horizontal
identities that Kleisli composition uses. -/
def flattenMap {R : Type u₁} {R' : Type u₂}
    [Quiver.{v₁} R] [Quiver.{v₂} R'] (h : R ⥤q R') :
    QuiverSpan.Square ((QuiverSpan.id (Paths R)).restrict (Paths.flatten R) (𝟭q (Paths R)))
      ((QuiverSpan.id (Paths R')).restrict (Paths.flatten R') (𝟭q (Paths R')))
      (Paths.map (Paths.map h)) (Paths.map h) where
  map_arr a := ⟨⟨congrArg (Paths.map h).obj a.down.down⟩⟩
  map_square {_ _ y y' L e' a b} u :=
    match y, y', e', a, b, u with
    | _, _, _, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩ => ⟨⟨(Paths.flatten_naturality h L).symm⟩⟩

namespace Square

/-- Horizontal composition of squares of Kleisli spans. -/
def hComp {P : Type u₁} {Q : Type u₂} {R : Type u₃} {P' : Type*} {Q' : Type*} {R' : Type*}
    [Quiver.{v₁} P] [Quiver.{v₂} Q] [Quiver.{v₃} R] [Quiver P'] [Quiver Q'] [Quiver R']
    {A : KleisliSpan P Q} {A' : KleisliSpan Q R} {B : KleisliSpan P' Q'} {B' : KleisliSpan Q' R'}
    {f : P ⥤q P'} {g : Q ⥤q Q'} {h : R ⥤q R'} (φ : Square A B f g) (ψ : Square A' B' g h) :
    Square (A.comp A') (B.comp B') f h :=
  QuiverSpan.Square.hComp (QuiverSpan.Square.hComp φ (QuiverSpan.Square.paths ψ))
    (flattenMap h)

theorem id_hComp_id_map_square_heq {P : Type u₁} {Q : Type u₂} {R : Type u₃}
    [Quiver.{v₁} P] [Quiver.{v₂} Q] [Quiver.{v₃} R] (A : KleisliSpan P Q) (A' : KleisliSpan Q R)
    {x x' : P} {y y' : Paths R} {e : x ⟶ x'} {e' : y ⟶ y'} {a : (A.comp A').arr x y}
    {b : (A.comp A').arr x' y'} (u : (A.comp A').square e e' a b) :
    ((Square.id A).hComp (Square.id A')).map_square u ≍ u := by
  obtain ⟨k, ⟨n, α, β⟩, t⟩ := u
  refine comp_square_heq (a₁ := ((Square.id A).hComp (Square.id A')).map_arr a) (a₂ := a)
    (b₁ := ((Square.id A).hComp (Square.id A')).map_arr b) (b₂ := b) rfl
    (Prefunctor.mapPath_id e') rfl rfl (heq_of_eq (Paths.mapPath_map_id (Q := R) k)) ?_ ?_
  · exact comp_square_heq (a₁ := (((Square.id A).hComp (Square.id A')).map_arr a).2.1)
      (a₂ := a.2.1) (b₁ := (((Square.id A).hComp (Square.id A')).map_arr b).2.1)
      (b₂ := b.2.1) rfl (Paths.mapPath_map_id (Q := R) k) rfl rfl
      (heq_of_eq (Prefunctor.mapPath_id n)) (id_map_square_heq _ α) (id_map_chain_heq _ β)
  · exact id_restrict_square_heq (Paths.mapPath_map_id (Q := R) k)
      (Prefunctor.mapPath_id e') _ _

/-- The interchange law between horizontal and vertical composition of squares of Kleisli
spans, on squares. -/
theorem hComp_vComp_map_square_heq {P₀ : Type u₁} {Q₀ : Type u₂} {R₀ : Type u₃}
    {P₁ Q₁ R₁ : Type*} {P₂ Q₂ R₂ : Type*} [Quiver.{v₁} P₀] [Quiver.{v₂} Q₀] [Quiver.{v₃} R₀]
    [Quiver P₁]
    [Quiver Q₁] [Quiver R₁] [Quiver P₂] [Quiver Q₂] [Quiver R₂]
    {A : KleisliSpan P₀ Q₀} {A' : KleisliSpan Q₀ R₀} {B : KleisliSpan P₁ Q₁}
    {B' : KleisliSpan Q₁ R₁} {C : KleisliSpan P₂ Q₂} {C' : KleisliSpan Q₂ R₂}
    {f : P₀ ⥤q P₁} {g : Q₀ ⥤q Q₁} {h : R₀ ⥤q R₁} {f' : P₁ ⥤q P₂} {g' : Q₁ ⥤q Q₂}
    {h' : R₁ ⥤q R₂} (φ : Square A B f g) (ψ : Square A' B' g h) (φ' : Square B C f' g')
    (ψ' : Square B' C' g' h') {x x' : P₀} {y y' : Paths R₀} {e : x ⟶ x'} {e' : y ⟶ y'}
    {a : (A.comp A').arr x y} {b : (A.comp A').arr x' y'} (u : (A.comp A').square e e' a b) :
    ((φ.vComp φ').hComp (ψ.vComp ψ')).map_square u ≍
      (φ'.hComp ψ').map_square ((φ.hComp ψ).map_square u) := by
  obtain ⟨k, ⟨n, α, β⟩, t⟩ := u
  refine comp_square_heq (a₁ := ((φ.vComp φ').hComp (ψ.vComp ψ')).map_arr a)
    (a₂ := (φ'.hComp ψ').map_arr ((φ.hComp ψ).map_arr a))
    (b₁ := ((φ.vComp φ').hComp (ψ.vComp ψ')).map_arr b)
    (b₂ := (φ'.hComp ψ').map_arr ((φ.hComp ψ).map_arr b)) rfl
    (Prefunctor.mapPath_comp_apply h h' e') rfl rfl
    (heq_of_eq (Paths.mapPath_map_comp h h' k)) ?_ ?_
  · exact comp_square_heq (a₁ := (((φ.vComp φ').hComp (ψ.vComp ψ')).map_arr a).2.1)
      (a₂ := ((φ'.hComp ψ').map_arr ((φ.hComp ψ).map_arr a)).2.1)
      (b₁ := (((φ.vComp φ').hComp (ψ.vComp ψ')).map_arr b).2.1)
      (b₂ := ((φ'.hComp ψ').map_arr ((φ.hComp ψ).map_arr b)).2.1) rfl
      (Paths.mapPath_map_comp h h' k) rfl rfl
      (heq_of_eq (Prefunctor.mapPath_comp_apply g g' n))
      (vComp_map_square_heq _ _ α) (vComp_map_chain_heq _ _ β)
  · exact id_restrict_square_heq (Paths.mapPath_map_comp h h' k)
      (Prefunctor.mapPath_comp_apply h h' e') _ _

end Square

/-- A cell with nullary source, target `A` and identity vertical sides: a morphism of spans out
of the Kleisli identity.

It is a square of Kleisli spans over identity prefunctors, but it is stated as a morphism of
spans: `Square (KleisliSpan.id Q) A (𝟭q Q) (𝟭q Q)` would have `Paths.map (𝟭q Q)` as its right
side, which is not definitionally `𝟭q (Paths Q)`. As a morphism of spans it composes with the
whiskerings and coherence cells without transport. -/
abbrev NullaryCell {Q : Type u} [Quiver.{v} Q] (A : KleisliSpan Q Q) :=
  Hom (KleisliSpan.id Q) A

/-- A cell with binary source `A`, `B`, target `C` and identity vertical sides: a morphism of
spans out of the binary Kleisli composite. It is a morphism of spans rather than a square of
Kleisli spans for the same reason as `NullaryCell`. -/
abbrev BinaryCell {P : Type u₁} {Q : Type u₂} {R : Type u₃}
    [Quiver.{v₁} P] [Quiver.{v₂} Q] [Quiver.{v₃} R]
    (A : KleisliSpan P Q) (B : KleisliSpan Q R) (C : KleisliSpan P R) :=
  Hom (A.comp B) C

/-! ### Nullary and binary cells, elementwise -/

namespace NullaryCell

variable {Q : Type u} [Quiver.{v} Q] {A : KleisliSpan.{u, v, u, v, w, z} Q Q}
  (η : NullaryCell A)

/-- The arrow of `A` from `x` to `x` that a nullary cell picks out. -/
def arr (x : Q) : x →ᵥ[A] x :=
  η.map_arr ⟨⟨rfl⟩⟩

/-- The square of `A` over an edge `e` that a nullary cell picks out: its source is the
one-element path on `e`, its target is `e`, and its sides are the arrows `η.arr`. -/
def square {x x' : Q} (e : x ⟶ x') :
    A.square e ((Paths.of Q).map e) (η.arr x) (η.arr x') :=
  η.map_square ⟨⟨rfl⟩⟩

end NullaryCell

namespace BinaryCell

variable {P : Type u₁} {Q : Type u₂} {R : Type u₃}
  [Quiver.{v₁} P] [Quiver.{v₂} Q] [Quiver.{v₃} R]
  {A : KleisliSpan P Q} {B : KleisliSpan Q R} {C : KleisliSpan P R} (μ : BinaryCell A B C)

/-- A binary cell on a composable pair of arrows. -/
def arr {x : P} {y : Q} {z : R} (a : A.arr x y) (b : B.arr y z) : C.arr x z :=
  μ.map_arr ⟨z, ⟨y, a, b⟩, ⟨⟨rfl⟩⟩⟩

/-- A binary cell on a square `α` of `A` and a chain `β` of squares of `B` whose targets spell
out the source of `α`. The source of the result is the concatenation of the sources in `β`. -/
def square {x x' : P} {y y' : Q} {z z' : R} {e : x ⟶ x'} {n : Quiver.Path y y'}
    {m : Quiver.Path (V := Paths R) z z'} {a : A.arr x y} {b : A.arr x' y'}
    {c : B.arr y z} {d : B.arr y' z'} (α : A.square e n a b) (β : PathSquare B c n m d) :
    C.square e ((Paths.flatten R).map m) (μ.arr a c) (μ.arr b d) :=
  μ.map_square ⟨m, ⟨n, α, β⟩, ⟨⟨rfl⟩⟩⟩

end BinaryCell

end KleisliSpan

end CategoryTheory
