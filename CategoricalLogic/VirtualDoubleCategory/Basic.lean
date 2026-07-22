/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled

/-!
# Virtual double categories

This is an elementwise implementation of the description in *A unified framework for
generalized multicategories*: a virtual double category is a monoid among spans of quivers
for the free-category (paths) monad.
-/

namespace CategoryTheory

set_option autoImplicit true

universe u v u₁ v₁ u₂ v₂ w z w' z'

/-- Flatten a path of paths by concatenation. -/
def flattenPath {Q : Type u} [Quiver.{v} Q] {x y : Paths (Paths Q)} :
    @Quiver.Path (Paths Q) _ x y → @Quiver.Path Q _ x y
  | .nil => .nil
  | .cons p e => (flattenPath p).comp e

/-- The multiplication of the paths monad, as a prefunctor. -/
def pathsJoin (Q : Type u) [Quiver.{v} Q] : Paths (Paths Q) ⥤q Paths Q where
  obj x := x
  map := flattenPath

/-- Flattening paths of singleton paths is the identity. -/
theorem flattenPath_mapPath_of {Q : Type u} [Quiver.{v} Q] {x y : Q}
    (p : Quiver.Path x y) :
    flattenPath (@Prefunctor.mapPath Q _ (Paths Q) _ (Paths.of Q) x y p) = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change (flattenPath (@Prefunctor.mapPath Q _ (Paths Q) _ (Paths.of Q) _ _ p)).comp
      (Quiver.Hom.toPath e) = _
    rw [ih]
    rfl

/-- An elementwise span of quivers. `arr` are its apex vertices and `square` its apex edges. -/
structure QuiverSpan (Q : Type u₁) (R : Type u₂) [Quiver.{v₁} Q] [Quiver.{v₂} R] where
  arr (x : Q) (y : R) : Type w
  square {x x' : Q} {y y' : R} (e : x ⟶ x') (e' : y ⟶ y')
    (f : arr x y) (f' : arr x' y') : Type z

namespace QuiverSpan

variable {P Q R S : Type u} [Quiver.{u} P] [Quiver.{u} Q] [Quiver.{u} R] [Quiver.{u} S]

protected def id (Q : Type u) [Quiver.{v} Q] :
    QuiverSpan.{u, v, u, v, max u v, max u v} Q Q where
  arr x y := ULift.{max u v, 0} (PLift (x = y))
  square e e' f f' :=
    ULift.{max u v, 0} (PLift (f.down.down ▸ f'.down.down ▸ e = e'))

def whiskerLeft {Q : Type u₁} {R : Type u₂} {S : Type u}
    [Quiver.{v₁} Q] [Quiver.{v₂} R] [Quiver.{v} S]
    (F : Q ⥤q S) (A : QuiverSpan.{u, v, u₂, v₂, w, z} S R) :
    QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R where
  arr x y := A.arr (F.obj x) y
  square e e' a b := A.square (F.map e) e' a b

def whiskerRight {Q : Type u₁} {R : Type u₂} {S : Type u}
    [Quiver.{v₁} Q] [Quiver.{v₂} R] [Quiver.{v} S]
    (F : R ⥤q S) (A : QuiverSpan.{u₁, v₁, u, v, w, z} Q S) :
    QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R where
  arr x y := A.arr x (F.obj y)
  square e e' a b := A.square e (F.map e') a b

protected def comp {Q : Type u₁} {R : Type u₂} {S : Type u}
    [Quiver.{v₁} Q] [Quiver.{v₂} R] [Quiver.{v} S]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R)
    (B : QuiverSpan.{u₂, v₂, u, v, w', z'} R S) :
    QuiverSpan.{u₁, v₁, u, v, max u₂ w w', max v₂ z z'} Q S where
  arr x s := Σ y, A.arr x y × B.arr y s
  square e e' a b :=
    Σ m : a.1 ⟶ b.1, A.square e m a.2.1 b.2.1 × B.square m e' a.2.2 b.2.2

structure Hom {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R)
    (B : QuiverSpan.{u₁, v₁, u₂, v₂, w', z'} Q R) where
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

/-- An isomorphism of quiver spans, including mutually inverse maps on vertices and edges. -/
structure Iso (A B : QuiverSpan Q R) where
  hom : Hom A B
  inv : Hom B A
  hom_inv_arr {x : Q} {y : R} (a : A.arr x y) : inv.map_arr (hom.map_arr a) = a
  inv_hom_arr {x : Q} {y : R} (a : B.arr x y) : hom.map_arr (inv.map_arr a) = a

abbrev Unit (A : QuiverSpan Q Q) := Hom (.id Q) A
abbrev Bimorphism (A : QuiverSpan Q R) (B : QuiverSpan R S) (C : QuiverSpan Q S) :=
  Hom (.comp A B) C

inductive PathSquare {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R) :
    {x x' : Q} → {y y' : R} → Quiver.Path x x' → Quiver.Path y y' →
      A.arr x y → A.arr x' y' → Type (max u₁ u₂ v₁ v₂ w z) where
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

def paths {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R) :
    QuiverSpan.{u₁, max u₁ v₁, u₂, max u₂ v₂, w, max u₁ u₂ v₁ v₂ w z}
      (Paths Q) (Paths R) where
  arr x y := A.arr x y
  square p q a b := PathSquare A p q a b

def pathsMap {A B : QuiverSpan Q R} (F : Hom A B) :
    @Hom (Paths Q) (Paths R) _ _ (paths A) (paths B) where
  map_arr a := F.map_arr a
  map_square s := PathSquare.map F s

def pathsUnit (A : QuiverSpan Q R) :
    Hom A (whiskerRight (Paths.of R) (whiskerLeft (Paths.of Q) (paths A))) where
  map_arr a := a
  map_square s := .cons (.nil _) s

def PathSquare.flatten {A : QuiverSpan Q R} {x x' : Q} {y y' : R}
    {pp : @Quiver.Path (Paths Q) _ x x'} {qq : @Quiver.Path (Paths R) _ y y'}
    {a : A.arr x y} {b : A.arr x' y'} :
    @PathSquare (Paths Q) (Paths R) _ _ (paths A) x x' y y' pp qq a b →
      PathSquare A (flattenPath pp) (flattenPath qq) a b
  | .nil _ => .nil _
  | .cons s t => PathSquare.comp (PathSquare.flatten s) t

def pathsMul (A : QuiverSpan Q R) :
    Hom (paths (paths A))
      (whiskerRight (pathsJoin R) (whiskerLeft (pathsJoin Q) (paths A))) where
  map_arr a := a
  map_square s := PathSquare.flatten s

end QuiverSpan

/-- A T-span from `Q` to `R` is a span from `Q` to the free category `Paths R`. -/
def QuiverTSpan (Q : Type*) (R : Type*) [Quiver Q] [Quiver R] :=
  QuiverSpan Q (Paths R)

namespace QuiverTSpan

variable {P Q R S T : Type u} [Quiver.{u} P] [Quiver.{u} Q] [Quiver.{u} R]
  [Quiver.{u} S] [Quiver.{u} T]

def unit (Q : Type u) [Quiver.{u} Q] : QuiverTSpan Q Q where
  arr x y := ULift.{u, 0} (PLift (x = y))
  square e p a b :=
    ULift.{u, 0} (PLift (a.down.down ▸ b.down.down ▸ Quiver.Hom.toPath e = p))

/-- Lift an ordinary path to a path of unit squares. -/
def unitPathSquare (p : Quiver.Path x y) :
    QuiverSpan.PathSquare (unit R) p
      (@Prefunctor.mapPath R _ (Paths R) _ (Paths.of R) x y p) ⟨⟨rfl⟩⟩ ⟨⟨rfl⟩⟩ := by
  induction p with
  | nil => exact .nil _
  | cons p e ih => exact .cons ih ⟨⟨rfl⟩⟩

def comp (A : QuiverTSpan P R) (B : QuiverTSpan R S) : QuiverTSpan P S :=
  QuiverSpan.comp (QuiverSpan.comp A (QuiverSpan.paths B))
    (QuiverSpan.whiskerLeft (pathsJoin S) (QuiverSpan.id (Paths S)))

def Hom (A B : QuiverTSpan Q R) := QuiverSpan.Hom A B

/-- An isomorphism of T-spans, inherited from the explicit quiver-span notion. -/
abbrev Iso (A B : QuiverTSpan Q R) := QuiverSpan.Iso A B

def Unit (A : QuiverTSpan Q Q) := Hom (unit Q) A

def Bimorphism (A : QuiverTSpan P Q) (B : QuiverTSpan Q R)
    (C : QuiverTSpan P R) := Hom (comp A B) C

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

/-- The operation data of a monoid among endo-T-spans. -/
structure Monoid (Q : Type u) [Quiver.{u} Q] where
  hom : QuiverTSpan Q Q
  id : Unit hom
  mul : Bimorphism hom hom hom

end QuiverTSpan


/-! ### The virtual double category of quivers, prefunctors and spans -/

/-- Bundled small quivers, with independent universes for vertices and edges. -/
def QuivSpan := Bundled Quiver.{u, v}

namespace QuivSpan

instance : CoeSort QuivSpan Type* where
  coe C := C.α

instance str' (C : QuivSpan) : Quiver C := C.str

/-- Quiver spans are the vertical arrows between bundled quivers. -/
instance : Quiver QuivSpan.{u, v} where
  Hom x y := QuiverSpan x y

/-- Compose the spans along a path of bundled quivers. This is the path product
needed by the multihom span. -/
def pathComp : {q q' : QuivSpan.{u, v}} → Quiver.Path q q' → QuiverSpan q q'
  | _, _, .nil => QuiverSpan.id _
  | _, _, .cons p e => QuiverSpan.comp (pathComp p) e

/-- The multihom span: its arrows are prefunctors, and its squares are maps from
path products into the right span restricted along the two prefunctors. -/
def MultiHom : QuiverSpan (Paths QuivSpan.{u, v}) QuivSpan.{u, v} where
  arr q r := q.α ⥤q r
  square e e' f f' :=
    QuiverSpan.Hom (pathComp e)
      (QuiverSpan.whiskerRight f' (QuiverSpan.whiskerLeft f e'))


-- def MultiHom.comp : QuiverTSpan.Bimorphism MultiHom MultiHom MultiHom := sorry

-- The generalized universe levels make this application elaborate.
#check @QuiverSpan.paths (Paths QuivSpan.{u, v}) QuivSpan.{u, v} _ _ MultiHom

end QuivSpan

end CategoryTheory
