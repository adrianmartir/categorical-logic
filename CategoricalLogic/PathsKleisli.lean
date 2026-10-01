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

end KleisliSpan

end CategoryTheory
