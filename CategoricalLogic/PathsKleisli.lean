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

A Kleisli span is literally a `QuiverSpan Q (Paths R)`; there is no separate type for it. Its
operations live in the namespace `KleisliSpan` and are called by their full names: on a Kleisli
span `A`, the dot notation `A.comp` is horizontal composition of quiver spans, not Kleisli
composition.

## Main definitions

* `KleisliSpan.id`, `KleisliSpan.comp`: the Kleisli identity and binary Kleisli composition.
* `KleisliSpan.Cell`, `KleisliSpan.NullaryCell`, `KleisliSpan.BinaryCell`: cells with unary,
  nullary and binary source.
-/

namespace CategoryTheory

universe u v u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

namespace KleisliSpan

open QuiverSpan

/-- The Kleisli identity: the horizontal identity on `Paths Q`, restricted along the unit
`Paths.of Q` of the monad on the left. -/
protected def id (Q : Type u) [Quiver.{v} Q] : QuiverSpan Q (Paths Q) :=
  (QuiverSpan.id (Paths Q)).restrict (Paths.of Q) (𝟭q (Paths Q))

/-- Binary Kleisli composition: the horizontal composite of `A`, of `paths B`, and of the
horizontal identity on `Paths R` restricted along the multiplication `Paths.flatten R` of the
monad on the left. -/
protected def comp {P : Type u₁} {Q : Type u₂} {R : Type u₃}
    [Quiver.{v₁} P] [Quiver.{v₂} Q] [Quiver.{v₃} R]
    (A : QuiverSpan P (Paths Q)) (B : QuiverSpan Q (Paths R)) : QuiverSpan P (Paths R) :=
  QuiverSpan.comp (QuiverSpan.comp A (paths B))
    ((QuiverSpan.id (Paths R)).restrict (Paths.flatten R) (𝟭q (Paths R)))

/-- Binary Kleisli composition of morphisms of Kleisli spans: Kleisli composition is
functorial in both arguments. -/
def hComp {P : Type u₁} {Q : Type u₂} {R : Type u₃}
    [Quiver.{v₁} P] [Quiver.{v₂} Q] [Quiver.{v₃} R]
    {A A' : QuiverSpan P (Paths Q)} {B B' : QuiverSpan Q (Paths R)}
    (f : Hom A A') (g : Hom B B') :
    Hom (KleisliSpan.comp A B) (KleisliSpan.comp A' B') :=
  Square.hComp (Square.hComp f (Hom.paths g)) (Square.id _)

/-- A Kleisli cell with unary source `A`, target `B`, and vertical sides `f` and `g`: a square
from `A` to `B` over `f` and `Paths.map g`. -/
abbrev Cell {Q : Type u₁} {R : Type u₂} {Q' : Type u₃} {R' : Type u₄}
    [Quiver.{v₁} Q] [Quiver.{v₂} R] [Quiver.{v₃} Q'] [Quiver.{v₄} R']
    (A : QuiverSpan Q (Paths R)) (B : QuiverSpan Q' (Paths R')) (f : Q ⥤q Q') (g : R ⥤q R') :=
  Square A B f (Paths.map g)

/-- A Kleisli cell with nullary source, target `A` and identity vertical sides: a morphism out
of the Kleisli identity. -/
abbrev NullaryCell {Q : Type u} [Quiver.{v} Q] (A : QuiverSpan Q (Paths Q)) :=
  Hom (KleisliSpan.id Q) A

/-- A Kleisli cell with binary source `A`, `B`, target `C` and identity vertical sides: a
morphism out of the binary Kleisli composite. -/
abbrev BinaryCell {P : Type u₁} {Q : Type u₂} {R : Type u₃}
    [Quiver.{v₁} P] [Quiver.{v₂} Q] [Quiver.{v₃} R]
    (A : QuiverSpan P (Paths Q)) (B : QuiverSpan Q (Paths R)) (C : QuiverSpan P (Paths R)) :=
  Hom (KleisliSpan.comp A B) C

end KleisliSpan

end CategoryTheory
