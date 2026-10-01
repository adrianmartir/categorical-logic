/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

import CategoricalLogic.VirtualDoubleCategory.QuiverSpan
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# The paths monad

`Paths` should be thought of as a monad on the virtual double category of quivers,
prefunctors and quiver spans. As in `CategoricalLogic.VirtualDoubleCategory.QuiverSpan`, this is a guiding principle
and not an instance: we never state what a monad on a virtual double category is here. Instead
each definition says in its docstring which piece of the monad structure it is.

We only build what the Kleisli virtual double category of `Paths` and the laws of virtual
double categories use. In particular the comparison cell for binary horizontal composition is
only here elementwise (`PathSquare.unzip`), and the monad laws on spans and cells are not here.

## Main definitions

* `Paths.map`, `Paths.flatten`: the functor part and the multiplication in the vertical
  direction, from mathlib's `Cat.freeMap` and `pathComposition`; the unit is mathlib's
  `Paths.of`.
* `Paths.flatten_map_of`, `Paths.flatten_map_mapPath_of`, `Paths.flatten_assoc`,
  `Paths.flatten_naturality`: the monad laws and naturality of the multiplication in the vertical
  direction.
* `Paths.mapPath_map_id`, `Paths.mapPath_map_comp`: functoriality of `Paths.map`, on paths of
  paths. Neither is `rfl`.
* `QuiverSpan.PathSquare`, `QuiverSpan.paths`: the functor part in the horizontal direction.
* `QuiverSpan.PathSquare.single`, `QuiverSpan.PathSquare.flatten`: the unit and the
  multiplication in the horizontal direction, elementwise.
* `QuiverSpan.PathSquare.unzip`: a chain of a binary horizontal composite, unzipped into a
  chain of each factor.
* `QuiverSpan.Square.paths`, `QuiverSpan.Hom.paths`: the functor part on cells.
-/

namespace CategoryTheory

universe u v u₁ v₁ u₂ v₂ w z

/-! ### The vertical direction -/

namespace Paths

/-- `Paths` on a prefunctor: the functor part of the monad in the vertical direction.

Functoriality, `Paths.map (𝟭q Q) = 𝟭q (Paths Q)` and its analogue for composition, hold by
`Prefunctor.mapPath_id` and `Prefunctor.mapPath_comp_apply`, but neither is `rfl`. -/
def map {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R] (F : Q ⥤q R) :
    Paths Q ⥤q Paths R :=
  (Cat.freeMap F).toPrefunctor

end Paths

namespace Paths

/-- The multiplication of the monad in the vertical direction: flattening a path of paths by
concatenation. This is mathlib's `pathComposition` for the path category `Paths Q`, so on
edges it is `composePath`, which reduces definitionally on `nil` and `cons`.

Kleisli composition only uses the multiplication in this direction; the multiplication on
spans, `QuiverSpan.PathSquare.flatten`, enters through the associativity of virtual double
categories. -/
def flatten (Q : Type u) [Quiver.{v} Q] : Paths (Paths Q) ⥤q Paths Q :=
  (pathComposition (Paths Q)).toPrefunctor

/-- A unit law of the monad in the vertical direction: flattening the paths of one-element
paths is the identity. -/
theorem flatten_map_mapPath_of {Q : Type u} [Quiver.{v} Q] {x y : Q} (p : Quiver.Path x y) :
    (flatten Q).map ((Paths.of Q).mapPath p) = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change ((flatten Q).map ((Paths.of Q).mapPath p)).comp (Quiver.Hom.toPath e) = _
    rw [ih]
    rfl

/-- The other unit law of the monad in the vertical direction: flattening a one-element path of
paths gives back its only element. -/
theorem flatten_map_of {Q : Type u} [Quiver.{v} Q] {x y : Q} (p : Quiver.Path x y) :
    (flatten Q).map ((Paths.of (Paths Q)).map p) = p :=
  Quiver.Path.nil_comp p

/-- Associativity of the monad in the vertical direction: flattening a path of paths of paths
does not depend on which level is flattened first. -/
theorem flatten_assoc {Q : Type u} [Quiver.{v} Q] {x y : Q}
    (L : Quiver.Path (V := Paths (Paths Q)) x y) :
    (flatten Q).map ((flatten (Paths Q)).map L) =
      (flatten Q).map ((Paths.map (flatten Q)).map L) := by
  induction L with
  | nil => rfl
  | cons L p ih =>
    exact (composePath_comp _ _).trans
      (congrArg (fun q : Quiver.Path _ _ => q.comp (composePath p)) ih)

/-- Naturality of the multiplication of the monad in the vertical direction. -/
theorem flatten_naturality {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (F : Q ⥤q R) {x y : Q} (m : Quiver.Path (V := Paths Q) x y) :
    (Paths.map F).map ((flatten Q).map m) =
      (flatten R).map ((Paths.map (Paths.map F)).map m) := by
  induction m with
  | nil => rfl
  | cons m p ih =>
    exact (F.mapPath_comp _ _).trans
      (congrArg (fun q : Quiver.Path _ _ => q.comp (F.mapPath p)) ih)

/-- `Paths.map` preserves identities, on paths of paths. -/
theorem mapPath_map_id {Q : Type u} [Quiver.{v} Q] {x y : Paths Q}
    (m : Quiver.Path x y) : (Paths.map (𝟭q Q)).mapPath m = m := by
  induction m with
  | nil => rfl
  | cons m p ih =>
    change ((Paths.map (𝟭q Q)).mapPath m).cons ((𝟭q Q).mapPath p) = m.cons p
    rw [ih]
    exact congrArg m.cons (Prefunctor.mapPath_id p)

/-- `Paths.map` preserves composites, on paths of paths. -/
theorem mapPath_map_comp {P : Type u} {Q : Type u₁} {R : Type u₂} [Quiver.{v} P]
    [Quiver.{v₁} Q] [Quiver.{v₂} R] (F : P ⥤q Q) (G : Q ⥤q R) {x y : Paths P}
    (m : Quiver.Path x y) :
    (Paths.map (F ⋙q G)).mapPath m = (Paths.map G).mapPath ((Paths.map F).mapPath m) := by
  induction m with
  | nil => rfl
  | cons m p ih =>
    change ((Paths.map (F ⋙q G)).mapPath m).cons ((F ⋙q G).mapPath p) =
      ((Paths.map G).mapPath ((Paths.map F).mapPath m)).cons (G.mapPath (F.mapPath p))
    rw [ih]
    exact congrArg _ (Prefunctor.mapPath_comp_apply F G p)

end Paths

/-! ### The horizontal direction -/

namespace QuiverSpan

/-- A chain of squares of `A`, starting at the arrow `a`: the squares of `paths A`.

Each `cons` extends both boundary paths by one edge, so the two paths always have the same
length. Indexing the chain by its two boundary paths, rather than cutting it out of the paths
in the apex, is what makes `Paths` lift to spans at all. As for `Quiver.Path`, the start is a
parameter. -/
inductive PathSquare {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R) {x : Q} {y : R} (a : A.arr x y) :
    {x' : Q} → {y' : R} → Quiver.Path x x' → Quiver.Path y y' → A.arr x' y' →
      Type (max u₁ u₂ v₁ v₂ w z) where
  /-- The empty chain. -/
  | nil : PathSquare A a .nil .nil a
  /-- Extend a chain by one square. -/
  | cons {x' x'' : Q} {y' y'' : R} {p : Quiver.Path x x'} {q : Quiver.Path y y'}
      {e : x' ⟶ x''} {f : y' ⟶ y''} {b : A.arr x' y'} {c : A.arr x'' y''}
      (s : PathSquare A a p q b) (t : A.square e f b c) :
      PathSquare A a (p.cons e) (q.cons f) c

/-- `Paths` on a quiver span: the functor part of the monad in the horizontal direction. -/
def paths {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
    (A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R) :
    QuiverSpan.{u₁, max u₁ v₁, u₂, max u₂ v₂, w, max u₁ u₂ v₁ v₂ w z}
      (Paths Q) (Paths R) where
  arr x y := A.arr x y
  square p q a b := PathSquare A a p q b

namespace PathSquare

variable {Q : Type u₁} {R : Type u₂} [Quiver.{v₁} Q] [Quiver.{v₂} R]
  {A : QuiverSpan.{u₁, v₁, u₂, v₂, w, z} Q R}

/-- The one-element chain on a square: the unit of the monad on spans. -/
abbrev single {x x' : Q} {y y' : R} {e : x ⟶ x'} {f : y ⟶ y'} {a : A.arr x y}
    {b : A.arr x' y'} (t : A.square e f a b) : PathSquare A a e.toPath f.toPath b :=
  .cons .nil t

/-- Concatenation of chains. -/
def comp {x x' : Q} {y y' : R} {a : A.arr x y} {p : Quiver.Path x x'} {q : Quiver.Path y y'}
    {b : A.arr x' y'} (s : PathSquare A a p q b) :
    {x'' : Q} → {y'' : R} → {p' : Quiver.Path x' x''} → {q' : Quiver.Path y' y''} →
      {c : A.arr x'' y''} → PathSquare A b p' q' c → PathSquare A a (p.comp p') (q.comp q') c
  | _, _, _, _, _, .nil => s
  | _, _, _, _, _, .cons t u => .cons (s.comp t) u

/-- Flattening a chain of chains into a chain, by concatenation: the multiplication of the
monad on spans. -/
def flatten {x : Q} {y : R} {a : A.arr x y} :
    {x' : Q} → {y' : R} → {m : Quiver.Path (V := Paths Q) x x'} →
      {L : Quiver.Path (V := Paths R) y y'} → {b : A.arr x' y'} →
      PathSquare (paths A) a m L b →
        PathSquare A a ((Paths.flatten Q).map m) ((Paths.flatten R).map L) b
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons s t => (flatten s).comp t

/-- Congruence for `cons` along equal boundary paths and edges. -/
theorem cons_heq_cons {x x' x'' : Q} {y y' y'' : R} {a : A.arr x y} {b : A.arr x' y'}
    {c : A.arr x'' y''} {e e' : x' ⟶ x''} {f f' : y' ⟶ y''} {p p' : Quiver.Path x x'}
    {q q' : Quiver.Path y y'} (hp : p = p') (hq : q = q') (he : e = e') (hf : f = f')
    {s : PathSquare A a p q b} {s' : PathSquare A a p' q' b} {t : A.square e f b c}
    {t' : A.square e' f' b c} (hs : s ≍ s') (ht : t ≍ t') :
    s.cons t ≍ s'.cons t' := by
  subst hp hq he hf
  obtain rfl := eq_of_heq hs
  obtain rfl := eq_of_heq ht
  rfl

end PathSquare

namespace PathSquare

variable {P : Type u₁} {Q : Type u₂} {R : Type u} [Quiver.{v₁} P] [Quiver.{v₂} Q] [Quiver.{v} R]

/-- A chain of squares of a binary horizontal composite unzips into a chain of each factor. -/
def unzip {A : QuiverSpan P Q} {B : QuiverSpan Q R} {x : P} {y : R}
    {a : (QuiverSpan.comp A B).arr x y} :
    {x' : P} → {y' : R} → {p : Quiver.Path x x'} → {q : Quiver.Path y y'} →
      {b : (QuiverSpan.comp A B).arr x' y'} → PathSquare (QuiverSpan.comp A B) a p q b →
      (QuiverSpan.comp (paths A) (paths B)).square p q a b
  | _, _, _, _, _, .nil => ⟨.nil, .nil, .nil⟩
  | _, _, _, _, _, .cons s t =>
      ⟨(unzip s).1.cons t.1, (unzip s).2.1.cons t.2.1, (unzip s).2.2.cons t.2.2⟩

/-- A chain of squares of the horizontal identity restricted along `F` on the left lies over
`p` and `F.mapPath p`. -/
theorem mapPath_heq_of_restrict_id (F : P ⥤q R) {x x' : P} {y y' : R}
    {a : ((QuiverSpan.id R).restrict F (𝟭q R)).arr x y} {p : Quiver.Path x x'}
    {q : Quiver.Path y y'} {b : ((QuiverSpan.id R).restrict F (𝟭q R)).arr x' y'}
    (c : PathSquare ((QuiverSpan.id R).restrict F (𝟭q R)) a p q b) : F.mapPath p ≍ q := by
  induction c with
  | nil =>
    obtain ⟨⟨h⟩⟩ := a
    cases h
    rfl
  | cons s t ih =>
    rename_i b c
    obtain ⟨⟨ha⟩⟩ := a
    cases ha
    obtain ⟨⟨hb⟩⟩ := b
    cases hb
    obtain ⟨⟨hc⟩⟩ := c
    cases hc
    obtain ⟨⟨ht⟩⟩ := t
    cases ht
    obtain rfl := eq_of_heq ih
    rfl

end PathSquare

/-! ### Cells -/

namespace PathSquare

variable {Q Q' R R' : Type*} [Quiver Q] [Quiver Q'] [Quiver R] [Quiver R']

/-- Map a chain along a square, applying the prefunctors to both boundary paths. -/
def map {A : QuiverSpan Q Q'} {B : QuiverSpan R R'} {F : Q ⥤q R} {G : Q' ⥤q R'}
    (s : Square A B F G) {x x' : Q} {y y' : Q'} {a : A.arr x y}
    {p : Quiver.Path x x'} {q : Quiver.Path y y'} {b : A.arr x' y'} :
    PathSquare A a p q b →
      PathSquare B (s.map_arr a) (F.mapPath p) (G.mapPath q) (s.map_arr b)
  | .nil => .nil
  | .cons c t => .cons (map s c) (s.map_square t)

/-- Map a chain along a morphism of spans, keeping both boundary paths.

This is not a special case of `PathSquare.map`, because `(𝟭q Q).mapPath p = p` is not `rfl`. -/
def mapHom {A B : QuiverSpan Q Q'} (h : Hom A B) {x x' : Q} {y y' : Q'} {a : A.arr x y}
    {p : Quiver.Path x x'} {q : Quiver.Path y y'} {b : A.arr x' y'} :
    PathSquare A a p q b → PathSquare B (h.map_arr a) p q (h.map_arr b)
  | .nil => .nil
  | .cons c t => .cons (mapHom h c) (h.map_square t)

end PathSquare

/-- `Paths` on a square: the functor part of the monad on cells. -/
def Square.paths {Q Q' R R' : Type*} [Quiver Q] [Quiver Q'] [Quiver R] [Quiver R']
    {A : QuiverSpan Q Q'} {B : QuiverSpan R R'} {F : Q ⥤q R} {G : Q' ⥤q R'}
    (s : Square A B F G) : Square (paths A) (paths B) (Paths.map F) (Paths.map G) where
  map_arr a := s.map_arr a
  map_square c := PathSquare.map s c

/-- `Paths` on a morphism of spans: the functor part of the monad on cells, landing on
identity prefunctors on the nose. It is not a special case of `Square.paths`, because
`Paths.map (𝟭q Q) = 𝟭q (Paths Q)` is not `rfl`. -/
def Hom.paths {Q R : Type*} [Quiver Q] [Quiver R] {A B : QuiverSpan Q R} (h : Hom A B) :
    Hom (paths A) (paths B) where
  map_arr a := h.map_arr a
  map_square c := PathSquare.mapHom h c

end QuiverSpan

end CategoryTheory
