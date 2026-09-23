/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

import CategoricalLogic.VirtualDoubleCategory.Paths
import Mathlib.CategoryTheory.Category.Quiv

/-!
# Virtual double categories

This is an elementwise implementation of the description in *A unified framework for
generalized multicategories*: a virtual double category is a monoid among spans of quivers
for the free-category (paths) monad.
-/

namespace CategoryTheory

set_option autoImplicit true

universe u v u₁ v₁ u₂ v₂ w z w' z'

/-- An elementwise span of quivers. `arr` are its apex vertices and `square` its apex edges. -/
structure QuiverSpan (Q : Type u₁) (R : Type u₂) [Quiver.{v₁} Q] [Quiver.{v₂} R] where
  arr (x : Q) (y : R) : Type w
  square {x x' : Q} {y y' : R} (e : x ⟶ x') (e' : y ⟶ y')
    (f : arr x y) (f' : arr x' y') : Type z

namespace QuiverSpan

/-- Horizontal arrows in a quiver. -/
infixr:25 " →ₕ " => Quiver.Hom

/-- Vertical arrows belonging to a specified quiver span. -/
notation:25 x " →ᵥ[" A "] " y => QuiverSpan.arr A x y

variable {P Q R S : Type u} [Quiver.{u} P] [Quiver.{u} Q] [Quiver.{u} R] [Quiver.{u} S]

/- # Basic operations for quivers, prefunctors and quiver spans -/

/-- The identity quiver span. -/
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

/- Composition of quiver spans. -/
protected def comp {Q : Type u₁} {R : Type u₂} {S : Type u}
    [Quiver.{v₁} Q] [Quiver.{v₂} R] [Quiver.{v} S]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R)
    (B : QuiverSpan.{u₂, v₂, u, v, w', z'} R S) :
    QuiverSpan.{u₁, v₁, u, v, max u₂ w w', max v₂ z z'} Q S where
  arr x s := Σ y, A.arr x y × B.arr y s
  square e e' a b :=
    Σ m : a.1 ⟶ b.1, A.square e m a.2.1 b.2.1 × B.square m e' a.2.2 b.2.2

/-- Cells filling a square whose vertical boundaries are quiver spans and whose
horizontal boundaries are prefunctors.

A morphism of quiver spans is the special case where both prefunctors are identities. -/
structure Square {Q Q' R R' : Type*} [Quiver Q] [Quiver Q'] [Quiver R] [Quiver R']
    (A : QuiverSpan Q Q') (B : QuiverSpan R R') (F : Q ⥤q R) (G : Q' ⥤q R') where
  map_arr {x : Q} {y : Q'} (a : A.arr x y) : B.arr (F.obj x) (G.obj y)
  map_square {x x' : Q} {y y' : Q'} {e : x ⟶ x'} {e' : y ⟶ y'}
    {a : A.arr x y} {b : A.arr x' y'} (s : A.square e e' a b) :
      B.square (F.map e) (G.map e') (map_arr a) (map_arr b)

/-- A morphism of quiver spans: a square whose horizontal boundaries are identities. -/
abbrev Hom {Q R : Type*} [Quiver Q] [Quiver R] (A B : QuiverSpan Q R) :=
  Square A B (𝟭q Q) (𝟭q R)

namespace Square

/-- The identity square on a quiver span. -/
protected def id {Q R : Type*} [Quiver Q] [Quiver R] (A : QuiverSpan Q R) : Hom A A where
  map_arr a := a
  map_square s := s

/-- Paste squares horizontally. -/
def comp {Q Q' R R' S S' : Type*}
    [Quiver Q] [Quiver Q'] [Quiver R] [Quiver R'] [Quiver S] [Quiver S']
    {A : QuiverSpan Q Q'} {B : QuiverSpan R R'} {C : QuiverSpan S S'}
    {F : Q ⥤q R} {G : Q' ⥤q R'} {H : R ⥤q S} {K : R' ⥤q S'}
    (s : Square A B F G) (t : Square B C H K) :
    Square A C (F ⋙q H) (G ⋙q K) where
  map_arr a := t.map_arr (s.map_arr a)
  map_square a := t.map_square (s.map_square a)

/-- Take the product of vertically composable squares. -/
def prod {Q₀ Q₁ Q₂ R₀ R₁ R₂ : Type*}
    [Quiver Q₀] [Quiver Q₁] [Quiver Q₂] [Quiver R₀] [Quiver R₁] [Quiver R₂]
    {A₁ : QuiverSpan Q₀ Q₁} {A₂ : QuiverSpan Q₁ Q₂}
    {B₁ : QuiverSpan R₀ R₁} {B₂ : QuiverSpan R₁ R₂}
    {F₀ : Q₀ ⥤q R₀} {F₁ : Q₁ ⥤q R₁} {F₂ : Q₂ ⥤q R₂}
    (s : Square A₁ B₁ F₀ F₁) (t : Square A₂ B₂ F₁ F₂) :
    Square (QuiverSpan.comp A₁ A₂) (QuiverSpan.comp B₁ B₂) F₀ F₂ where
  map_arr a := ⟨F₁.obj a.1, s.map_arr a.2.1, t.map_arr a.2.2⟩
  map_square a := ⟨F₁.map a.1, s.map_square a.2.1, t.map_square a.2.2⟩

/-- Change the target span of a square.

This is `Square.comp` against a morphism of spans, but it lands in `Square A C F G` on the
nose rather than in `Square A C (F ⋙q 𝟭q) (G ⋙q 𝟭q)`, which the recursions below need. -/
def mapTarget {Q Q' R R' : Type*} [Quiver Q] [Quiver Q'] [Quiver R] [Quiver R']
    {A : QuiverSpan Q Q'} {B C : QuiverSpan R R'} {F : Q ⥤q R} {G : Q' ⥤q R'}
    (s : Square A B F G) (h : Hom B C) : Square A C F G where
  map_arr a := h.map_arr (s.map_arr a)
  map_square a := h.map_square (s.map_square a)

end Square

/-- Remove a right identity factor from a span product. -/
def rightUnitHom {Q R : Type*} [Quiver Q] [Quiver R] (A : QuiverSpan Q R) :
    Hom (QuiverSpan.comp A (QuiverSpan.id R)) A where
  map_arr | ⟨_, a, ⟨⟨rfl⟩⟩⟩ => a
  map_square {_ _ _ _ _ _ a b} := fun s =>
    match a, b, s with
    | ⟨_, _, ⟨⟨rfl⟩⟩⟩, ⟨_, _, ⟨⟨rfl⟩⟩⟩, ⟨_, t, ⟨⟨rfl⟩⟩⟩ => t

/-- Insert a right identity factor into a span product. -/
def rightUnitInvHom {Q R : Type*} [Quiver Q] [Quiver R] (A : QuiverSpan Q R) :
    Hom A (QuiverSpan.comp A (QuiverSpan.id R)) where
  map_arr a := ⟨_, a, ⟨⟨rfl⟩⟩⟩
  map_square s := ⟨_, s, ⟨⟨rfl⟩⟩⟩

/-- Reassociate three span products from left to right. -/
def assocHom {P Q R S : Type*} [Quiver P] [Quiver Q] [Quiver R] [Quiver S]
    (A : QuiverSpan P Q) (B : QuiverSpan Q R) (C : QuiverSpan R S) :
    Hom (QuiverSpan.comp (QuiverSpan.comp A B) C)
      (QuiverSpan.comp A (QuiverSpan.comp B C)) where
  map_arr a := ⟨a.2.1.1, a.2.1.2.1, a.1, a.2.1.2.2, a.2.2⟩
  map_square s := ⟨s.2.1.1, s.2.1.2.1, s.1, s.2.1.2.2, s.2.2⟩

abbrev Unit (A : QuiverSpan Q Q) := Hom (.id Q) A

/-- A map that composes pairs of vertical arrows and their filling squares. -/
abbrev BiHom (A : QuiverSpan Q R) (B : QuiverSpan R S) (C : QuiverSpan Q S) :=
  Hom (QuiverSpan.comp A B) C

/-- A string of horizontally composable squares. -/
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

/-- Apply the `Paths` monad to a quiver span. -/
def paths {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R) :
    QuiverSpan.{u₁, max u₁ v₁, u₂, max u₂ v₂, w, max u₁ u₂ v₁ v₂ w z}
      (Paths Q) (Paths R) where
  arr x y := A.arr x y
  square p q a b := PathSquare A p q a b

/-- Apply the `Paths` monad to a morphism of spans. -/
def pathsMap {A B : QuiverSpan Q R} (F : Hom A B) : Hom (paths A) (paths B) where
  map_arr a := F.map_arr a
  map_square s := PathSquare.map F s

-- -- TODO: Unused
-- def pathsUnit (A : QuiverSpan Q R) :
--     Square A (whiskerRight (Paths.of R) (whiskerLeft (Paths.of Q) (paths A)))
--       (𝟭q Q) (𝟭q R) where
--   map_arr a := a
--   map_square s := .cons (.nil _) s

-- def PathSquare.flatten {A : QuiverSpan Q R} {x x' : Q} {y y' : R}
--     {pp : @Quiver.Path (Paths Q) _ x x'} {qq : @Quiver.Path (Paths R) _ y y'}
--     {a : A.arr x y} {b : A.arr x' y'} :
--     @PathSquare (Paths Q) (Paths R) _ _ (paths A) x x' y y' pp qq a b →
--       PathSquare A (flattenPath pp) (flattenPath qq) a b
--   | .nil _ => .nil _
--   | .cons s t => PathSquare.comp (PathSquare.flatten s) t

-- -- TODO: Unused
-- def pathsMul (A : QuiverSpan Q R) :
--     Square (paths (paths A))
--       (whiskerRight (pathsJoin R) (whiskerLeft (pathsJoin Q) (paths A)))
--       (𝟭q (Paths (Paths Q))) (𝟭q (Paths (Paths R))) where
--   map_arr a := a
--   map_square s := PathSquare.flatten s

end QuiverSpan

/-! ### Quivers and spans as a quiver -/

/-- Bundled quivers, to be equipped with the quiver structure whose edges are quiver
spans. This is `CategoryTheory.Quiv` as a type synonym, so that it does not pick up the
category structure whose morphisms are prefunctors. -/
def SpanQuiv := Quiv.{u, v}

namespace SpanQuiv

instance : CoeSort SpanQuiv Type* where
  coe C := C.α

instance str' (C : SpanQuiv) : Quiver C := C.str

/-- Quiver spans are the vertical arrows between bundled quivers.

The apex universes are pinned to `max u v`, which is where `QuiverSpan.id` and
`QuiverSpan.comp`, and hence `pathProd`, already land. -/
instance : Quiver SpanQuiv.{u, v} where
  Hom x y := QuiverSpan.{v, u, v, u, max u v, max u v} x y

/-- Compose the spans along a path of quivers. This is the path product needed by the
multihom span.

It is defined through `Quiver.Path.rec` (rather than the equation compiler) so that
it reduces definitionally on `nil` and `cons`; this keeps the downstream
constructions tactic-free. -/
def pathProd {q q' : SpanQuiv.{u, v}} (p : Quiver.Path q q') : q ⟶ q' :=
  p.rec (motive := fun t _ => q ⟶ t)
    (QuiverSpan.id _) (fun _ e ih => QuiverSpan.comp ih e)

@[simp] theorem pathProd_nil {q : SpanQuiv.{u, v}} :
    pathProd (Quiver.Path.nil (a := q)) = QuiverSpan.id _ := rfl

@[simp] theorem pathProd_cons {q q' q'' : SpanQuiv.{u, v}}
    (p : Quiver.Path q q') (e : q' ⟶ q'') :
    pathProd (p.cons e) = QuiverSpan.comp (pathProd p) e := rfl

/-- The path product of a single edge is that edge, preceded by an identity span. -/
theorem pathProd_toPath {q q' : SpanQuiv.{u, v}} (e : q ⟶ q') :
    pathProd (Quiver.Hom.toPath e) = QuiverSpan.comp (QuiverSpan.id _) e := rfl

/-- The diagonal cell over an edge `e`: identity prefunctors give a square from `e` to
its own path product `pathProd (Quiver.Hom.toPath e)`. -/
def pathProdToPathSquare {q q' : SpanQuiv.{u, v}} (e : q ⟶ q') :
    QuiverSpan.Square e (pathProd (Quiver.Hom.toPath e)) (𝟭q q.α) (𝟭q q'.α) where
  map_arr a := ⟨_, ⟨⟨rfl⟩⟩, a⟩
  map_square t := ⟨_, ⟨⟨rfl⟩⟩, t⟩

/-- Reassociate the product of two paths into the product of their concatenation.

Both `pathProd` and `Quiver.Path.comp` reduce definitionally on path constructors,
so this is a plain structural recursion: the empty path uses the right unitor, and
the recursive step reassociates and re-whiskers by the new edge. -/
def pathProdComp {Q R : SpanQuiv.{u, v}} (p : Quiver.Path Q R) :
    {S : SpanQuiv.{u, v}} → (q : Quiver.Path R S) →
      QuiverSpan.Hom (QuiverSpan.comp (pathProd p) (pathProd q)) (pathProd (p.comp q))
  | _, .nil => QuiverSpan.rightUnitHom (pathProd p)
  | _, .cons q _ =>
      { map_arr := fun a =>
          ⟨a.2.2.1, (pathProdComp p q).map_arr ⟨a.1, a.2.1, a.2.2.2.1⟩, a.2.2.2.2⟩
        map_square := fun s =>
          ⟨s.2.2.1, (pathProdComp p q).map_square ⟨s.1, s.2.1, s.2.2.2.1⟩, s.2.2.2.2⟩ }

/-- Split the path product of a concatenation into the product of the two path products.

This is the direction opposite to `pathProdComp`, and it is the direction composition of
multihoms needs: there the concatenated path is the source, not the target. -/
def pathProdCompInv {Q R : SpanQuiv.{u, v}} (p : Quiver.Path Q R) :
    {S : SpanQuiv.{u, v}} → (q : Quiver.Path R S) →
      QuiverSpan.Hom (pathProd (p.comp q)) (QuiverSpan.comp (pathProd p) (pathProd q))
  | _, .nil => QuiverSpan.rightUnitInvHom (pathProd p)
  | _, .cons q e =>
      QuiverSpan.Square.mapTarget
        (QuiverSpan.Square.prod (pathProdCompInv p q) (QuiverSpan.Square.id e))
        (QuiverSpan.assocHom _ _ _)

/-- A prefunctor gives a square between identity spans. -/
def pathSquareNil {Q R : SpanQuiv.{u, v}} (F : Q.α ⥤q R.α) :
    QuiverSpan.Square (QuiverSpan.id Q.α) (QuiverSpan.id R.α) F F where
  map_arr | ⟨⟨rfl⟩⟩ => ⟨⟨rfl⟩⟩
  map_square {_ _ _ _ _ _ a b} := fun s =>
    match a, b, s with
    | ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩ => ⟨⟨rfl⟩⟩

end SpanQuiv

namespace QuiverSpan

/-- A multihom composes every vertical arrow in a path into one vertical arrow. -/
def MultiHom {q q' : SpanQuiv.{u, v}} (p : Quiver.Path q q')
    (A : QuiverSpan q q') :=
  Hom (SpanQuiv.pathProd p) A

/-- A path of multihoms: one multihom for every edge of the outer path `p`, whose sources
concatenate to the inner path `r`. -/
inductive PathMultiHom : {q q' : SpanQuiv.{u, v}} →
    Quiver.Path q q' → Quiver.Path q q' → Type (max (u + 1) (v + 1))
  | nil {q : SpanQuiv.{u, v}} : PathMultiHom (q := q) .nil .nil
  | cons {q q' q'' : SpanQuiv.{u, v}} {p r : Quiver.Path q q'} (Θ : PathMultiHom p r)
      {A : q' ⟶ q''} {s : Quiver.Path q' q''} (θ : MultiHom s A) :
      PathMultiHom (p.cons A) (r.comp s)

/-- Multiply out a path of multihoms: the product of the inner path maps to the product of
the outer one. -/
def PathMultiHom.prod {q q' : SpanQuiv.{u, v}} {p r : Quiver.Path q q'} :
    PathMultiHom p r → MultiHom r (SpanQuiv.pathProd p)
  | .nil => Square.id _
  | .cons Θ θ =>
      Square.mapTarget (SpanQuiv.pathProdCompInv _ _) (Square.prod Θ.prod θ)

/-- Substitute a multihom into each input of a multihom. -/
def MultiHom.comp {q q' : SpanQuiv.{u, v}} {p r : Quiver.Path q q'} {A : QuiverSpan q q'}
    (θ : MultiHom p A) (Θ : PathMultiHom p r) : MultiHom r A :=
  Square.mapTarget Θ.prod θ

end QuiverSpan

/- # Basic operations for quivers, prefunctors and Path-spans -/

/-- A T-span from `Q` to `R` is a span from `Q` to the free category `Paths R`. -/
def QuiverTSpan (Q : Type u₁) (R : Type u₂) [Quiver.{v₁} Q] [Quiver.{v₂} R] :=
  QuiverSpan Q (Paths R)

namespace QuiverTSpan

variable {P Q R S T : Type u} [Quiver.{u} P] [Quiver.{u} Q] [Quiver.{u} R]
  [Quiver.{u} S] [Quiver.{u} T]

def unit (Q : Type u₁) [Quiver.{v₁} Q] : QuiverTSpan Q Q where
  arr x y := ULift.{max u₁ v₁, 0} (PLift (x = y))
  square e p a b :=
    ULift.{max u₁ v₁, 0} (PLift (a.down.down ▸ b.down.down ▸ Quiver.Hom.toPath e = p))

/-- Lift an ordinary path to a path of unit squares. -/
def unitPathSquare : (p : Quiver.Path x y) →
    QuiverSpan.PathSquare (unit R) p
      (@Prefunctor.mapPath R _ (Paths R) _ (Paths.of R) x y p) ⟨⟨rfl⟩⟩ ⟨⟨rfl⟩⟩
  | .nil => .nil _
  | .cons p e => .cons (unitPathSquare p) ⟨⟨rfl⟩⟩

/-- Case analysis on the cells of the identity T-span: a cell over an edge `e` is
determined by reflexivity, so it suffices to give the diagonal cell over `e` whose
path boundary is `Quiver.Hom.toPath e`. -/
@[elab_as_elim]
def unit.squareRec {Q : Type u₁} [Quiver.{v₁} Q] {x x' : Q} {e : x ⟶ x'}
    {motive : ∀ {y y' : Paths Q} (a : (unit Q).arr x y) (b : (unit Q).arr x' y')
      {p : y ⟶ y'}, (unit Q).square e p a b → Sort*}
    (diag : motive (y := x) (y' := x') ⟨⟨rfl⟩⟩ ⟨⟨rfl⟩⟩
      (p := Quiver.Hom.toPath e) ⟨⟨rfl⟩⟩) :
    ∀ {y y' : Paths Q} (a : (unit Q).arr x y) (b : (unit Q).arr x' y')
      {p : y ⟶ y'} (s : (unit Q).square e p a b), motive a b s
  | _, _, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩, _, ⟨⟨rfl⟩⟩ => diag

def comp {P : Type u₁} {R : Type u₂} {S : Type u}
    [Quiver.{v₁} P] [Quiver.{v₂} R] [Quiver.{v} S]
    (A : QuiverTSpan P R) (B : QuiverTSpan R S) : QuiverTSpan P S :=
  QuiverSpan.comp (QuiverSpan.comp A (QuiverSpan.paths B))
    (QuiverSpan.whiskerLeft (pathsJoin S) (QuiverSpan.id (Paths S)))

/-- The prefunctor on path quivers induced by a prefunctor. -/
def pathComp {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (F : Q ⥤q R) : Paths Q ⥤q Paths R where
  obj x := F.obj x
  map p := F.mapPath p

def Unit {Q : Type u₁} [Quiver.{v₁} Q] (A : QuiverTSpan Q Q) :=
  QuiverSpan.Hom (unit Q) A

/-- A T-span bimorphism: a morphism out of the Kleisli composite. -/
abbrev BiHom {P : Type u₁} {Q : Type u₂} {R : Type u}
    [Quiver.{v₁} P] [Quiver.{v₂} Q] [Quiver.{v} R]
    (A : QuiverTSpan P Q) (B : QuiverTSpan Q R) (C : QuiverTSpan P R) :=
  QuiverSpan.Hom (comp A B) C

def mapComp {A A' : QuiverTSpan P Q} {B B' : QuiverTSpan Q R}
    (f : QuiverSpan.Hom A A') (g : QuiverSpan.Hom B B') :
    QuiverSpan.Hom (comp A B) (comp A' B') :=
  QuiverSpan.Square.prod (QuiverSpan.Square.prod f (QuiverSpan.pathsMap g))
    (QuiverSpan.Square.id (QuiverSpan.whiskerLeft (pathsJoin R) (QuiverSpan.id (Paths R))))

/-- The identity vertical arrow selected by a unit. -/
def Unit.app {A : QuiverTSpan Q Q} (i : Unit A) (x : Q) : A.arr x x :=
  i.map_arr ⟨⟨rfl⟩⟩

/-- Apply a bimorphism to two composable vertical arrows. -/
def BiHom.app {A : QuiverTSpan P Q} {B : QuiverTSpan Q R}
    {C : QuiverTSpan P R} (m : BiHom A B C)
    {x : P} {y : Q} {z : R} (f : A.arr x y) (g : B.arr y z) : C.arr x z :=
  m.map_arr ⟨_, ⟨_, f, g⟩, ⟨⟨rfl⟩⟩⟩

/-- The operation data of a monoid among endo-T-spans. -/
structure Monoid (Q : Type u) [Quiver.{u} Q] where
  hom : QuiverTSpan Q Q
  id : Unit hom
  mul : BiHom hom hom hom

end QuiverTSpan


/-! ### The virtual double category of quivers, prefunctors and spans -/

namespace SpanQuiv

/-- The T-span whose vertical arrows are prefunctors and whose cells are squares
from a span to a path-product of spans. -/
def hom : QuiverTSpan SpanQuiv.{u, v} SpanQuiv.{u, v} where
  arr q r := q.α ⥤q r.α
  square A p f f' := QuiverSpan.Square A (pathProd p) f f'

/-- A path of `hom`-squares composes to one square between path products.

Since `pathProd` and `flattenPath` reduce definitionally on path constructors, this
is a plain structural recursion on the `PathSquare`. -/
def pathSquareComp :
    {Q Q' : SpanQuiv.{u, v}} → {R R' : Paths SpanQuiv.{u, v}} →
    {p : Quiver.Path Q Q'} → {q : @Quiver.Path (Paths SpanQuiv) _ R R'} →
    {F : hom.arr Q R} → {G : hom.arr Q' R'} →
    QuiverSpan.PathSquare hom p q F G →
      QuiverSpan.Square (pathProd p) (pathProd (flattenPath q)) F G
  | _, _, _, _, _, _, _, _, .nil a => pathSquareNil a
  | _, _, _, _, _, _, _, _, .cons s' t =>
      QuiverSpan.Square.mapTarget (QuiverSpan.Square.prod (pathSquareComp s') t)
        (pathProdComp _ _)

/-- Composition of prefunctors and compatible squares. -/
def comp : QuiverTSpan.BiHom hom.{u, v} hom.{u, v} hom.{u, v} where
  map_arr | ⟨_, ⟨_, F, G⟩, ⟨⟨rfl⟩⟩⟩ => F ⋙q G
  map_square {_ _ _ _ _ _ a b} := fun s =>
    match a, b, s with
    | ⟨_, ⟨_, _, _⟩, ⟨⟨rfl⟩⟩⟩, ⟨_, ⟨_, _, _⟩, ⟨⟨rfl⟩⟩⟩, ⟨_, ⟨_, sf, sg⟩, ⟨⟨h⟩⟩⟩ =>
      h ▸ QuiverSpan.Square.comp sf (pathSquareComp sg)

/-- Identity prefunctors and their compatible squares. -/
def id : QuiverTSpan.Unit hom.{u, v} where
  map_arr a := a.down.down ▸ Prefunctor.id _
  map_square {_ _ _ _ e _ a b} := fun s =>
    QuiverTSpan.unit.squareRec (e := e) (pathProdToPathSquare e) a b s

end SpanQuiv

end CategoryTheory
