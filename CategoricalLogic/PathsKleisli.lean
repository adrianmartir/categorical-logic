/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

import CategoricalLogic.Paths

/-!
# The Kleisli virtual double category of `Paths`

The horizontal Kleisli virtual double category of the `Paths` monad, following *A unified
framework for generalized multicategories*: a horizontal arrow from `Q` to `R` is a quiver span
from `Q` to `Paths R`. Virtual double categories are the monoids here; they are defined in
`CategoricalLogic.VirtualDoubleCategory`.

Following the orientation of `CategoricalLogic.QuiverSpan`, the right leg `Paths R` carries the
sources: a square of a Kleisli span has a single edge as target and a path as source.

## Main definitions

* `KleisliSpan`: horizontal arrows.
* `KleisliSpan.id`, `KleisliSpan.comp`: the Kleisli identity and binary Kleisli composition.
* `KleisliSpan.Cell`, `KleisliSpan.NullaryCell`, `KleisliSpan.BinaryCell`: cells with unary,
  nullary and binary source.
* `KleisliSpan.NullaryCell.arr`, `.square`, `.chain` and `KleisliSpan.BinaryCell.arr`,
  `.square`, `.chain`: nullary and binary cells elementwise, on arrows, on squares and on
  chains of squares. The accessors of virtual double categories are these.
-/

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

open QuiverSpan

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

/-- Binary Kleisli composition of morphisms of Kleisli spans: Kleisli composition is
functorial in both arguments. -/
def hComp {P : Type u₁} {Q : Type u₂} {R : Type u₃}
    [Quiver.{v₁} P] [Quiver.{v₂} Q] [Quiver.{v₃} R]
    {A A' : KleisliSpan P Q} {B B' : KleisliSpan Q R} (f : Hom A A') (g : Hom B B') :
    Hom (A.comp B) (A'.comp B') :=
  Square.hComp (Square.hComp f (Hom.paths g)) (Square.id _)

/-- A Kleisli cell with unary source `A`, target `B`, and vertical sides `f` and `g`: a square
from `A` to `B` over `f` and `Paths.map g`. -/
abbrev Cell {Q : Type u₁} {R : Type u₂} {Q' : Type u₃} {R' : Type u₄}
    [Quiver.{v₁} Q] [Quiver.{v₂} R] [Quiver.{v₃} Q'] [Quiver.{v₄} R']
    (A : KleisliSpan Q R) (B : KleisliSpan Q' R') (f : Q ⥤q Q') (g : R ⥤q R') :=
  Square A B f (Paths.map g)

/-- A Kleisli cell with nullary source, target `A` and identity vertical sides: a morphism out
of the Kleisli identity. -/
abbrev NullaryCell {Q : Type u} [Quiver.{v} Q] (A : KleisliSpan Q Q) :=
  Hom (KleisliSpan.id Q) A

/-- A Kleisli cell with binary source `A`, `B`, target `C` and identity vertical sides: a
morphism out of the binary Kleisli composite. -/
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

/-- The chain of the squares `η.square` along a path. -/
def chain {x : Q} : {x' : Q} → (p : Quiver.Path x x') →
    PathSquare A (η.arr x) p ((Paths.of Q).mapPath p) (η.arr x')
  | _, .nil => .nil
  | _, .cons p e => .cons (chain p) (η.square e)

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

/-- A binary cell along a chain `β` of squares of `A` and a chain of chains `γ` of squares of
`B`, applying `μ.square` to each square of `β` and the corresponding chain of `γ`. -/
def chain {x : P} {y : Paths Q} {z : Paths R} {a : A.arr x y} {c : B.arr y z} :
    {x' : P} → {y' : Paths Q} → {z' : Paths R} → {n : Quiver.Path x x'} →
      {m : Quiver.Path y y'} → {L : Quiver.Path (V := Paths (Paths R)) z z'} →
      {b : A.arr x' y'} → {d : B.arr y' z'} →
      PathSquare A a n m b → PathSquare (paths B) c m L d →
        PathSquare C (μ.arr a c) n ((Paths.flatten R).mapPath L) (μ.arr b d)
  | _, _, _, _, _, _, _, _, .nil, .nil => .nil
  | _, _, _, _, _, _, _, _, .cons β t, .cons γ u => .cons (chain β γ) (μ.square t u)

end BinaryCell

end KleisliSpan

end CategoryTheory
