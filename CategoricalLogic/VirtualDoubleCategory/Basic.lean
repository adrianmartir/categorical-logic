/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Virtual double categories

This is an elementwise implementation of the description in *A unified framework for
generalized multicategories*: a virtual double category is a monoid among spans of quivers
for the free-category (paths) monad.

A `QuiverSpan Q R` presents a span of quivers without bundling its apex.  We define its
units, bimorphisms and their compositions, lift the paths construction to spans and span
morphisms, and define the auxiliary Kleisli construction `QuiverTSpan`.  Finally,
`VirtualDoubleCategory Q` is a monoid among these T-spans.
-/

namespace CategoryTheory

-- Indexed path constructors are substantially clearer with their indices inferred.
set_option autoImplicit true

universe u

/-- Flatten a path of paths by concatenation. -/
def flattenPath {Q : Type u} [Quiver.{u} Q] {x y : Paths (Paths Q)} :
    @Quiver.Path (Paths Q) _ x y → @Quiver.Path Q _ x y
  | .nil => .nil
  | .cons p e => (flattenPath p).comp e

/-- The multiplication of the paths monad, as a prefunctor. -/
def pathsJoin (Q : Type u) [Quiver.{u} Q] : Paths (Paths Q) ⥤q Paths Q where
  obj x := x
  map := flattenPath

/-- An elementwise span of quivers. `arr` are its apex vertices and `square` its apex edges. -/
structure QuiverSpan (Q R : Type u) [Quiver.{u} Q] [Quiver.{u} R] where
  arr (x : Q) (y : R) : Type u
  square {x x' : Q} {y y' : R} (e : x ⟶ x') (e' : y ⟶ y')
    (f : arr x y) (f' : arr x' y') : Type u

namespace QuiverSpan

variable {Q R S : Type u} [Quiver.{u} Q] [Quiver.{u} R] [Quiver.{u} S]

/-- The identity span. -/
protected def id (Q : Type u) [Quiver.{u} Q] : QuiverSpan Q Q where
  arr x y := ULift.{u, 0} (PLift (x = y))
  square e e' f f' := ULift.{u, 0} (PLift (f.down.down ▸ f'.down.down ▸ e = e'))

/-- Pull a span back along a prefunctor on its left leg. -/
def whiskerLeft {Q R S : Type u} [Quiver.{u} Q] [Quiver.{u} R] [Quiver.{u} S]
    (F : Q ⥤q S) (A : QuiverSpan S R) : QuiverSpan Q R where
  arr x y := A.arr (F.obj x) y
  square e e' a b := A.square (F.map e) e' a b

/-- Pull a span back along a prefunctor on its right leg. -/
def whiskerRight {Q R S : Type u} [Quiver.{u} Q] [Quiver.{u} R] [Quiver.{u} S]
    (F : R ⥤q S) (A : QuiverSpan Q S) : QuiverSpan Q R where
  arr x y := A.arr x (F.obj y)
  square e e' a b := A.square e (F.map e') a b

/-- Horizontal composition of spans. -/
protected def comp {Q R S : Type u} [Quiver.{u} Q] [Quiver.{u} R] [Quiver.{u} S]
    (A : QuiverSpan Q R) (B : QuiverSpan R S) : QuiverSpan Q S where
  arr x z := Σ y, A.arr x y × B.arr y z
  square e e' a b :=
    Σ m : a.1 ⟶ b.1, A.square e m a.2.1 b.2.1 × B.square m e' a.2.2 b.2.2

/-- A morphism between spans with fixed feet. -/
@[ext]
structure Hom {Q R : Type u} [Quiver.{u} Q] [Quiver.{u} R] (A B : QuiverSpan Q R) where
  map_arr {x : Q} {y : R} (a : A.arr x y) : B.arr x y
  map_square {x x' : Q} {y y' : R} {e : x ⟶ x'} {e' : y ⟶ y'}
    {a : A.arr x y} {b : A.arr x' y'} (s : A.square e e' a b) :
      B.square e e' (map_arr a) (map_arr b)

protected def Hom.id (A : QuiverSpan Q R) : Hom A A where
  map_arr a := a
  map_square s := s

def Hom.comp {A B C : QuiverSpan Q R} (f : Hom A B) (g : Hom B C) : Hom A C where
  map_arr a := g.map_arr (f.map_arr a)
  map_square s := g.map_square (f.map_square s)

/-- Horizontal composition of span morphisms. -/
def Hom.hcomp {Q R S : Type u} [Quiver.{u} Q] [Quiver.{u} R] [Quiver.{u} S]
    {A A' : QuiverSpan Q R} {B B' : QuiverSpan R S}
    (f : Hom A A') (g : Hom B B') : Hom (.comp A B) (.comp A' B') where
  map_arr a := ⟨a.1, f.map_arr a.2.1, g.map_arr a.2.2⟩
  map_square s := ⟨s.1, f.map_square s.2.1, g.map_square s.2.2⟩

def Hom.whiskerRight {Q R S : Type u} [Quiver.{u} Q] [Quiver.{u} R] [Quiver.{u} S]
    (F : R ⥤q S) {A B : QuiverSpan Q S} (f : Hom A B) :
    Hom (whiskerRight F A) (whiskerRight F B) where
  map_arr a := f.map_arr a
  map_square s := f.map_square s

/-- A unit is a morphism from the identity span. -/
abbrev Unit (A : QuiverSpan Q Q) := Hom (.id Q) A

/-- A binary bimorphism is a map out of a composite of spans. -/
abbrev Bimorphism (A : QuiverSpan Q R) (B : QuiverSpan R S) (C : QuiverSpan Q S) :=
  Hom (.comp A B) C

/-! ## Lifting paths to spans -/

/-- A path in the apex of a span, displayed together with both projected boundary paths. -/
inductive PathSquare {Q R : Type u} [Quiver.{u} Q] [Quiver.{u} R] (A : QuiverSpan Q R) :
    {x x' : Q} → {y y' : R} → Quiver.Path x x' → Quiver.Path y y' →
      A.arr x y → A.arr x' y' → Type u where
  | nil (a : A.arr x y) : PathSquare A .nil .nil a a
  | cons (s : PathSquare A p q a b) (t : A.square e f b c) :
      PathSquare A (.cons p e) (.cons q f) a c

namespace PathSquare

variable {Q R : Type u} [Quiver.{u} Q] [Quiver.{u} R]

def map {A B : QuiverSpan Q R} (F : Hom A B) {x x' : Q} {y y' : R}
    {p : Quiver.Path x x'} {q : Quiver.Path y y'} {a : A.arr x y} {b : A.arr x' y'} :
    PathSquare A p q a b → PathSquare B p q (F.map_arr a) (F.map_arr b)
  | .nil _ => .nil _
  | .cons s t => .cons (map F s) (F.map_square t)

def comp {A : QuiverSpan Q R} {x x' x'' : Q} {y y' y'' : R}
    {p : Quiver.Path x x'} {q : Quiver.Path y y'} {p' : Quiver.Path x' x''}
    {q' : Quiver.Path y' y''} {a : A.arr x y} {b : A.arr x' y'} {c : A.arr x'' y''} :
    PathSquare A p q a b → PathSquare A p' q' b c →
      PathSquare A (Quiver.Path.comp p p') (Quiver.Path.comp q q') a c
  | s, .nil _ => s
  | s, .cons t e => .cons (comp s t) e

end PathSquare

/-- Apply the paths construction to a span's apex and both legs. -/
def paths {Q R : Type u} [Quiver.{u} Q] [Quiver.{u} R] (A : QuiverSpan Q R) :
    QuiverSpan (Paths Q) (Paths R) where
  arr x y := A.arr x y
  square p q a b := PathSquare A p q a b

/-- The paths lifting acts on span maps. -/
def pathsMap {A B : QuiverSpan Q R} (F : Hom A B) :
    @Hom (Paths Q) (Paths R) _ _ (paths A) (paths B) where
  map_arr a := F.map_arr a
  map_square s := PathSquare.map F s

/-- Unit comparison for the paths lifting: an apex edge becomes a singleton apex path. -/
def pathsUnit (A : QuiverSpan Q R) :
    Hom A (whiskerRight (Paths.of R) (whiskerLeft (Paths.of Q) (paths A))) where
  map_arr a := a
  map_square s := .cons (.nil _) s

/-- Flatten a path whose individual edges are paths in the apex span. -/
def PathSquare.flatten {A : QuiverSpan Q R} {x x' : Q} {y y' : R}
    {pp : @Quiver.Path (Paths Q) _ x x'} {qq : @Quiver.Path (Paths R) _ y y'}
    {a : A.arr x y} {b : A.arr x' y'} :
    @PathSquare (Paths Q) (Paths R) _ _ (paths A) x x' y y' pp qq a b →
      PathSquare A (flattenPath pp) (flattenPath qq) a b
  | .nil _ => .nil _
  | .cons s t => PathSquare.comp (PathSquare.flatten s) t

/-- Multiplication comparison for the paths lifting. -/
def pathsMul (A : QuiverSpan Q R) :
    Hom (paths (paths A))
      (whiskerRight (pathsJoin R) (whiskerLeft (pathsJoin Q) (paths A))) where
  map_arr a := a
  map_square s := PathSquare.flatten s

end QuiverSpan

/-! ## Kleisli spans and their monoids -/

/-- A T-span from `Q` to `R` is a span from `Q` to the free category `Paths R`.

Keeping the two feet independent is important: T-spans are the horizontal arrows of the
Kleisli equipment, not merely its endomorphisms. -/
def QuiverTSpan (Q R : Type u) [Quiver.{u} Q] [Quiver.{u} R] :=
  QuiverSpan Q (Paths R)

namespace QuiverTSpan

variable {P Q R S : Type u} [Quiver.{u} P] [Quiver.{u} Q] [Quiver.{u} R]
  [Quiver.{u} S]

/-- The identity T-span. -/
def unit (Q : Type u) [Quiver.{u} Q] : QuiverTSpan Q Q where
  arr x y := ULift.{u, 0} (PLift (x = y))
  square e p a b :=
    ULift.{u, 0} (PLift (a.down.down ▸ b.down.down ▸ Quiver.Hom.toPath e = p))

/-- Kleisli composition of T-spans.

For `A : P ⟶ Paths R` and `B : R ⟶ Paths S`, first compose `A` with `paths B`.
The resulting right foot is `Paths (Paths S)`; whiskering it by the multiplication
`pathsJoin S` gives the desired T-span from `P` to `S`. -/
def comp (A : QuiverTSpan P R) (B : QuiverTSpan R S) : QuiverTSpan P S :=
  QuiverSpan.comp (QuiverSpan.comp A (QuiverSpan.paths B))
    (QuiverSpan.whiskerLeft (pathsJoin S) (QuiverSpan.id (Paths S)))

/-- A morphism of T-spans with fixed source and target. -/
def Hom (A B : QuiverTSpan Q R) := QuiverSpan.Hom A B

/-- A unit is a map from the identity T-span. -/
def Unit (A : QuiverTSpan Q Q) := Hom (unit Q) A

/-- A binary bimorphism is a map out of a Kleisli composite. -/
def Bimorphism (A : QuiverTSpan P Q) (B : QuiverTSpan Q R)
    (C : QuiverTSpan P R) := Hom (comp A B) C

/-- Composition acts on morphisms of T-spans. -/
def mapComp {A A' : QuiverTSpan P Q} {B B' : QuiverTSpan Q R}
    (f : Hom A A') (g : Hom B B') : Hom (comp A B) (comp A' B') :=
  QuiverSpan.Hom.hcomp
    (QuiverSpan.Hom.hcomp (show QuiverSpan.Hom A A' from f)
      (QuiverSpan.pathsMap (show QuiverSpan.Hom B B' from g)))
    (QuiverSpan.Hom.id (QuiverSpan.whiskerLeft (pathsJoin R) (QuiverSpan.id (Paths R))))

/-- The identity vertical arrow selected by a unit. -/
def Unit.app {A : QuiverTSpan Q Q} (i : Unit A) (x : Q) : A.arr x x :=
  i.map_arr ⟨⟨rfl⟩⟩

/-- Apply a bimorphism to two composable vertical arrows. -/
def Bimorphism.app {A : QuiverTSpan P Q} {B : QuiverTSpan Q R}
    {C : QuiverTSpan P R} (m : Bimorphism A B C)
    {x : P} {y : Q} {z : R} (f : A.arr x y) (g : B.arr y z) : C.arr x z :=
  m.map_arr ⟨z, ⟨y, f, g⟩, ⟨⟨rfl⟩⟩⟩

/-- The operation and comparison-map data of a monoid among endo-T-spans.
Coherence is deliberately kept in the separate predicate `Monoid.Coherent`. -/
structure Monoid (Q : Type u) [Quiver.{u} Q] where
  /-- Vertical arrows and cells. -/
  hom : QuiverTSpan Q Q
  /-- Identity vertical arrows and identity cells. -/
  id : Unit hom
  /-- Composition of vertical arrows and substitution of cells. -/
  mul : Bimorphism hom hom hom
  /-- The right-unit comparison for the chosen elementwise presentation. -/
  rightUnitor : Hom hom (comp hom (unit Q))
  /-- The left-unit comparison for the chosen elementwise presentation. -/
  leftUnitor : Hom hom (comp (unit Q) hom)
  /-- The associativity comparison for the chosen elementwise presentation. -/
  associator : Hom (comp (comp hom hom) hom) (comp hom (comp hom hom))

namespace Monoid

/-- Coherence laws for monoid data among T-spans.

They are equalities of span morphisms, not merely pointwise laws on vertices, so they
simultaneously state the identity and substitution axioms for cells. -/
structure Coherent (M : Monoid Q) : Prop where
  /-- Right identity, simultaneously on vertical arrows and cells. -/
  mul_id :
    QuiverSpan.Hom.comp M.rightUnitor
      (QuiverSpan.Hom.comp (mapComp (QuiverSpan.Hom.id M.hom) M.id) M.mul) =
        QuiverSpan.Hom.id M.hom
  /-- Left identity, simultaneously on vertical arrows and cells. -/
  id_mul :
    QuiverSpan.Hom.comp M.leftUnitor
      (QuiverSpan.Hom.comp (mapComp M.id (QuiverSpan.Hom.id M.hom)) M.mul) =
        QuiverSpan.Hom.id M.hom
  /-- Associativity of substitution, simultaneously on vertical arrows and cells. -/
  mul_assoc :
    QuiverSpan.Hom.comp (mapComp M.mul (QuiverSpan.Hom.id M.hom)) M.mul =
      QuiverSpan.Hom.comp M.associator
        (QuiverSpan.Hom.comp (mapComp (QuiverSpan.Hom.id M.hom) M.mul) M.mul)

end Monoid
end QuiverTSpan

/-- A virtual double category is coherent monoid data among path T-spans.  The monoid data
and its coherence laws are separate declarations, so the underlying operations can be used
without carrying proofs through every construction. -/
def VirtualDoubleCategory (Q : Type u) [Quiver.{u} Q] :=
  { M : QuiverTSpan.Monoid Q // QuiverTSpan.Monoid.Coherent M }

end CategoryTheory
