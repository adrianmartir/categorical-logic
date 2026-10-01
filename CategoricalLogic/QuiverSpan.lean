/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

import Mathlib.CategoryTheory.Category.Quiv

/-!
# Quiver spans

A quiver span from `Q` to `R` is a span of quivers `Q ← A → R`, given by its fibers: a type of
arrows over each pair of vertices, and a type of squares over each pair of edges.

## Orientation

We follow *A unified framework for generalized multicategories* (Cruttwell–Shulman): the left
leg of a span carries *targets* and the right leg carries *sources*. So `A.arr x y` is the type
of arrows from `y` to `x` (written `y →ᵥ[A] x`), and `A.square e e' f f'` is the type of squares
with source `e'`, target `e` and sides `f`, `f'`:
```
y --e'--> y'
|f        |f'
v         v
x --e-->  x'
```

## Organization

The file is organized after the double category whose objects are quivers, whose vertical
arrows are prefunctors and whose horizontal arrows are quiver spans. We do not construct an
instance of a double category: virtual double categories are defined later in terms of quiver
spans. In that double category a `Square A B F G` has source `A`, target `B`, and the
prefunctors `F`, `G` from the feet of `A` to the feet of `B`.

## Main definitions

* `QuiverSpan`, `QuiverSpan.Square`, `QuiverSpan.Hom`: spans, squares, morphisms of spans.
* `QuiverSpan.Square.vComp`, `QuiverSpan.Hom.comp`: vertical composition of squares and of
  morphisms of spans.
* `QuiverSpan.restrict`: restriction of a span along prefunctors.
* `QuiverSpan.id`, `QuiverSpan.comp`, `QuiverSpan.Square.hComp`: horizontal composition.
* `SpanQuiv.composePath`: n-ary horizontal composition along a path of spans.
* `SpanQuiv.MultiSquare`: squares with n-ary source.
-/

namespace CategoryTheory

universe u v u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ w z w' z'

/-- A span of quivers `Q ← A → R`, given by its fibers. `arr x y` is the type of arrows from
`y` to `x`, and `square e e' f f'` the type of squares with source `e'`, target `e` and sides
`f` and `f'`. -/
structure QuiverSpan (Q : Type u₁) (R : Type u₂) [Quiver.{v₁} Q] [Quiver.{v₂} R] where
  /-- The arrows from `y` to `x`: the apex vertices over `x` and `y`. -/
  arr (x : Q) (y : R) : Type w
  /-- The squares with source `e'` and target `e`: the apex edges over `e` and `e'`. -/
  square {x x' : Q} {y y' : R} (e : x ⟶ x') (e' : y ⟶ y')
    (f : arr x y) (f' : arr x' y') : Type z

namespace QuiverSpan

/-- The arrows of a span `A` from `y` to `x`. Arrows run from the right leg to the left leg. -/
notation:25 y " →ᵥ[" A "] " x => QuiverSpan.arr A x y

/-! ### Spans, squares and vertical composition -/

/-- Transport a square of `A` along equalities of its source and of its sides, keeping its
target. Laws between squares whose boundaries agree only propositionally are stated with it. -/
def castSquare {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R) {x x' : Q} {y y' : R} {e : x ⟶ x'}
    {e₁ e₂ : y ⟶ y'} {a₁ a₂ : A.arr x y} {b₁ b₂ : A.arr x' y'}
    (he : e₁ = e₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (s : A.square e e₁ a₁ b₁) :
    A.square e e₂ a₂ b₂ :=
  he ▸ ha ▸ hb ▸ s

@[simp] theorem castSquare_rfl {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R) {x x' : Q} {y y' : R} {e : x ⟶ x'}
    {e' : y ⟶ y'} {a : A.arr x y} {b : A.arr x' y'} (s : A.square e e' a b) :
    A.castSquare rfl rfl rfl s = s :=
  rfl

theorem castSquare_heq {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R) {x x' : Q} {y y' : R} {e : x ⟶ x'}
    {e₁ e₂ : y ⟶ y'} {a₁ a₂ : A.arr x y} {b₁ b₂ : A.arr x' y'}
    (he : e₁ = e₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (s : A.square e e₁ a₁ b₁) :
    A.castSquare he ha hb s ≍ s := by
  subst he ha hb
  rfl

/-- An equation with a transported square on one side is a heterogeneous equation. -/
theorem eq_castSquare_iff_heq {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R) {x x' : Q} {y y' : R} {e : x ⟶ x'}
    {e₁ e₂ : y ⟶ y'} {a₁ a₂ : A.arr x y} {b₁ b₂ : A.arr x' y'}
    (he : e₁ = e₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (s : A.square e e₁ a₁ b₁)
    (t : A.square e e₂ a₂ b₂) : t = A.castSquare he ha hb s ↔ t ≍ s := by
  subst he ha hb
  exact ⟨heq_of_eq, eq_of_heq⟩

/-- A square in the double category of quivers, prefunctors and quiver spans, with source
`A`, target `B`, and vertical sides `F` and `G`. It is a morphism of spans lying over the
prefunctors between the feet. -/
structure Square {Q Q' R R' : Type*} [Quiver Q] [Quiver Q'] [Quiver R] [Quiver R']
    (A : QuiverSpan Q Q') (B : QuiverSpan R R') (F : Q ⥤q R) (G : Q' ⥤q R') where
  /-- The action on arrows. -/
  map_arr {x : Q} {y : Q'} (a : A.arr x y) : B.arr (F.obj x) (G.obj y)
  /-- The action on squares. -/
  map_square {x x' : Q} {y y' : Q'} {e : x ⟶ x'} {e' : y ⟶ y'}
    {a : A.arr x y} {b : A.arr x' y'} (s : A.square e e' a b) :
      B.square (F.map e) (G.map e') (map_arr a) (map_arr b)

/-- A morphism of quiver spans: a square whose vertical sides are identities. -/
abbrev Hom {Q R : Type*} [Quiver Q] [Quiver R] (A B : QuiverSpan Q R) :=
  Square A B (𝟭q Q) (𝟭q R)

namespace Square

/-- The vertical identity square on a quiver span. -/
protected def id {Q R : Type*} [Quiver Q] [Quiver R] (A : QuiverSpan Q R) : Hom A A where
  map_arr a := a
  map_square s := s

/-- Vertical composition of squares, along their common span. -/
def vComp {Q Q' R R' S S' : Type*}
    [Quiver Q] [Quiver Q'] [Quiver R] [Quiver R'] [Quiver S] [Quiver S']
    {A : QuiverSpan Q Q'} {B : QuiverSpan R R'} {C : QuiverSpan S S'}
    {F : Q ⥤q R} {G : Q' ⥤q R'} {H : R ⥤q S} {K : R' ⥤q S'}
    (s : Square A B F G) (t : Square B C H K) :
    Square A C (F ⋙q H) (G ⋙q K) where
  map_arr a := t.map_arr (s.map_arr a)
  map_square s' := t.map_square (s.map_square s')

end Square

theorem Square.map_square_castSquare_heq {Q Q' R R' : Type*} [Quiver Q] [Quiver Q']
    [Quiver R] [Quiver R'] {A : QuiverSpan Q Q'} {B : QuiverSpan R R'} {F : Q ⥤q R}
    {G : Q' ⥤q R'} (s : Square A B F G) {x x' : Q} {y y' : Q'} {e : x ⟶ x'}
    {e₁ e₂ : y ⟶ y'} {a₁ a₂ : A.arr x y} {b₁ b₂ : A.arr x' y'}
    (he : e₁ = e₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (t : A.square e e₁ a₁ b₁) :
    s.map_square (A.castSquare he ha hb t) ≍ s.map_square t := by
  subst he ha hb
  rfl

/-- Composition of morphisms of spans. -/
def Hom.comp {Q R : Type*} [Quiver Q] [Quiver R] {A B C : QuiverSpan Q R} (f : Hom A B)
    (g : Hom B C) : Hom A C where
  map_arr a := g.map_arr (f.map_arr a)
  map_square s := g.map_square (f.map_square s)

/-- The restriction `A(F, G)` of a span `A` along prefunctors `F` and `G` into its feet. -/
def restrict {Q : Type u₁} {R : Type u₂} {S : Type u₃} {T : Type u₄}
    [Quiver.{v₁} Q] [Quiver.{v₂} R] [Quiver.{v₃} S] [Quiver.{v₄} T]
    (A : QuiverSpan.{u₃, v₃, u₄, v₄, w, z} S T) (F : Q ⥤q S) (G : R ⥤q T) :
    QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R where
  arr x y := A.arr (F.obj x) (G.obj y)
  square e e' a b := A.square (F.map e) (G.map e') a b

/-! ### Horizontal composition -/

/-- The horizontal identity on a quiver: its arrows and squares are equalities. -/
protected def id (Q : Type u) [Quiver.{v} Q] :
    QuiverSpan.{u, v, u, v, max u v, max u v} Q Q where
  arr x y := ULift.{max u v, 0} (PLift (x = y))
  square e e' f f' :=
    ULift.{max u v, 0} (PLift (f.down.down ▸ f'.down.down ▸ e = e'))

/-- Binary horizontal composition of quiver spans. -/
protected def comp {Q : Type u₁} {R : Type u₂} {S : Type u₃}
    [Quiver.{v₁} Q] [Quiver.{v₂} R] [Quiver.{v₃} S]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R)
    (B : QuiverSpan.{u₂, v₂, u₃, v₃, w', z'} R S) :
    QuiverSpan.{u₁, v₁, u₃, v₃, max u₂ w w', max v₂ z z'} Q S where
  arr x s := Σ y, A.arr x y × B.arr y s
  square e e' a b :=
    Σ m : a.1 ⟶ b.1, A.square e m a.2.1 b.2.1 × B.square m e' a.2.2 b.2.2

namespace Square

/-- The horizontal identity square on a prefunctor, between two horizontal identities. -/
def hId {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R] (F : Q ⥤q R) :
    Square (QuiverSpan.id Q) (QuiverSpan.id R) F F where
  map_arr | ⟨⟨rfl⟩⟩ => ⟨⟨rfl⟩⟩
  map_square {_ _ _ _ _ _ a b} := fun s =>
    match a, b, s with
    | ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩ => ⟨⟨rfl⟩⟩

/-- Binary horizontal composition of squares, along their common vertical side. -/
def hComp {Q₀ Q₁ Q₂ R₀ R₁ R₂ : Type*}
    [Quiver Q₀] [Quiver Q₁] [Quiver Q₂] [Quiver R₀] [Quiver R₁] [Quiver R₂]
    {A₁ : QuiverSpan Q₀ Q₁} {A₂ : QuiverSpan Q₁ Q₂}
    {B₁ : QuiverSpan R₀ R₁} {B₂ : QuiverSpan R₁ R₂}
    {F₀ : Q₀ ⥤q R₀} {F₁ : Q₁ ⥤q R₁} {F₂ : Q₂ ⥤q R₂}
    (s : Square A₁ B₁ F₀ F₁) (t : Square A₂ B₂ F₁ F₂) :
    Square (QuiverSpan.comp A₁ A₂) (QuiverSpan.comp B₁ B₂) F₀ F₂ where
  map_arr a := ⟨F₁.obj a.1, s.map_arr a.2.1, t.map_arr a.2.2⟩
  map_square a := ⟨F₁.map a.1, s.map_square a.2.1, t.map_square a.2.2⟩

end Square

/-- The left unitor: remove a left identity factor from a horizontal composite. -/
def leftUnitor {Q R : Type*} [Quiver Q] [Quiver R] (A : QuiverSpan Q R) :
    Hom (QuiverSpan.comp (QuiverSpan.id Q) A) A where
  map_arr | ⟨_, ⟨⟨rfl⟩⟩, a⟩ => a
  map_square {_ _ _ _ _ _ a b} := fun s =>
    match a, b, s with
    | ⟨_, ⟨⟨rfl⟩⟩, _⟩, ⟨_, ⟨⟨rfl⟩⟩, _⟩, ⟨_, ⟨⟨rfl⟩⟩, t⟩ => t

/-- The right unitor: remove a right identity factor from a horizontal composite. -/
def rightUnitor {Q R : Type*} [Quiver Q] [Quiver R] (A : QuiverSpan Q R) :
    Hom (QuiverSpan.comp A (QuiverSpan.id R)) A where
  map_arr | ⟨_, a, ⟨⟨rfl⟩⟩⟩ => a
  map_square {_ _ _ _ _ _ a b} := fun s =>
    match a, b, s with
    | ⟨_, _, ⟨⟨rfl⟩⟩⟩, ⟨_, _, ⟨⟨rfl⟩⟩⟩, ⟨_, t, ⟨⟨rfl⟩⟩⟩ => t

/-- The inverse of the right unitor: insert a right identity factor. -/
def rightUnitorInv {Q R : Type*} [Quiver Q] [Quiver R] (A : QuiverSpan Q R) :
    Hom A (QuiverSpan.comp A (QuiverSpan.id R)) where
  map_arr a := ⟨_, a, ⟨⟨rfl⟩⟩⟩
  map_square s := ⟨_, s, ⟨⟨rfl⟩⟩⟩

/-- The associator: reassociate a threefold horizontal composite from left to right. -/
def associator {P Q R S : Type*} [Quiver P] [Quiver Q] [Quiver R] [Quiver S]
    (A : QuiverSpan P Q) (B : QuiverSpan Q R) (C : QuiverSpan R S) :
    Hom (QuiverSpan.comp (QuiverSpan.comp A B) C)
      (QuiverSpan.comp A (QuiverSpan.comp B C)) where
  map_arr a := ⟨a.2.1.1, a.2.1.2.1, a.1, a.2.1.2.2, a.2.2⟩
  map_square s := ⟨s.2.1.1, s.2.1.2.1, s.1, s.2.1.2.2, s.2.2⟩

end QuiverSpan

/-! ### n-ary horizontal composition -/

/-- Bundled quivers, as the vertices of the quiver whose edges are quiver spans; n-ary
horizontal composition is then composition along a `Quiver.Path` of spans.

The edge universe is pinned to `max u v` so that it absorbs the vertex universe `v`: `Paths`
raises the edge universe of a quiver to exactly that, so only with this pinning does it act on
the quivers collected here. This is a structure of its own rather than mathlib's `Quiv`, whose
category structure has prefunctors as morphisms. -/
structure SpanQuiv where
  /-- The vertices. -/
  α : Type v
  /-- The quiver structure. -/
  str : Quiver.{max u v} α

namespace SpanQuiv

instance : CoeSort SpanQuiv.{u, v} (Type v) where
  coe C := C.α

instance str' (C : SpanQuiv.{u, v}) : Quiver.{max u v} C := C.str

/-- Quiver spans are the edges between bundled quivers. The apex universes are pinned to
`max u v`, which is where `QuiverSpan.id` and `QuiverSpan.comp` already land. -/
instance : Quiver SpanQuiv.{u, v} where
  Hom x y := QuiverSpan.{v, max u v, v, max u v, max u v, max u v} x y

/-- n-ary horizontal composition: the horizontal composite of a path of spans.

It is defined through `Quiver.Path.rec` so that it reduces definitionally on `nil` and `cons`,
which keeps the constructions below free of tactics. -/
def composePath {q q' : SpanQuiv.{u, v}} (p : Quiver.Path q q') : q ⟶ q' :=
  p.rec (motive := fun t _ => q ⟶ t)
    (QuiverSpan.id _) (fun _ e ih => QuiverSpan.comp ih e)

@[simp] theorem composePath_nil {q : SpanQuiv.{u, v}} :
    composePath (Quiver.Path.nil (a := q)) = QuiverSpan.id _ := rfl

@[simp] theorem composePath_cons {q q' q'' : SpanQuiv.{u, v}}
    (p : Quiver.Path q q') (e : q' ⟶ q'') :
    composePath (p.cons e) = QuiverSpan.comp (composePath p) e := rfl

/-- The n-ary composite of a one-element path is the span itself: the left unitor, since the
composite of `e.toPath` is `QuiverSpan.comp (QuiverSpan.id _) e` by definition. -/
def composePathToPath {q q' : SpanQuiv.{u, v}} (e : q ⟶ q') :
    QuiverSpan.Hom (composePath e.toPath) e :=
  QuiverSpan.leftUnitor e

/-- Split the composite of a concatenation into the composites of the two paths.

This is the direction that substitution of cells consumes: the concatenated path is the
source of the substituted cell. -/
def composePathCompInv {q r : SpanQuiv.{u, v}} (p : Quiver.Path q r) :
    {s : SpanQuiv.{u, v}} → (p' : Quiver.Path r s) →
      QuiverSpan.Hom (composePath (p.comp p'))
        (QuiverSpan.comp (composePath p) (composePath p'))
  | _, .nil => QuiverSpan.rightUnitorInv (composePath p)
  | _, .cons p' e =>
      QuiverSpan.Square.vComp
        (QuiverSpan.Square.hComp (composePathCompInv p p') (QuiverSpan.Square.id e))
        (QuiverSpan.associator _ _ _)

/-- A square with n-ary source: a square out of the horizontal composite of the path `p` of
spans into the span `A`, with vertical sides `F` and `G`. -/
abbrev MultiSquare {q q' r r' : SpanQuiv.{u, v}} (p : Quiver.Path q q') (A : r ⟶ r')
    (F : q.α ⥤q r.α) (G : q'.α ⥤q r'.α) :=
  QuiverSpan.Square (composePath p) A F G

end SpanQuiv

end CategoryTheory
