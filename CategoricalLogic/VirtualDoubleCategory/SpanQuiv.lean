/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

module

public import CategoricalLogic.VirtualDoubleCategory.Basic

/-!
# The virtual double category of quiver spans

Quivers, prefunctors and quiver spans form a virtual double category. Its arrows from `r` to
`q` are the prefunctors `r ⥤q q`, composition of arrows is diagrammatic composition of
prefunctors, its cells with source a path `p` of spans and target a span `A` are the
multisquares `MultiSquare p A`, the identity cell on a span is the left unitor, and
substitution is n-ary horizontal composition (`SpanQuiv.hCompPath`) followed by vertical
composition. It lands one universe up.

## Main definitions

* `SpanQuiv.hom`, `SpanQuiv.id`, `SpanQuiv.comp`: the data.
* `SpanQuiv.virtualDoubleCategory`: the virtual double category.
-/

@[expose] public section

namespace CategoryTheory

universe u v

open QuiverSpan hiding Square
open KleisliSpan

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
