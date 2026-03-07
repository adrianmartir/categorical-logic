/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/
module

public import CategoricalLogic.Prof
public import Mathlib.Combinatorics.Quiver.Path

public import CategoricalLogic.Profunctor.Basic
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Cells of Profunctors

This file defines cells of profunctors, generalizing binatural transformations to
arbitrary-length paths.

## Main definitions

* `Paths`: A quiver whose edges are `Quiver.Path`s, equipped with monad-like operations
  (unit and flattening) satisfying the monad laws.
* `ProfCat`: A wrapper around `Cat` equipped with a quiver structure where an edge from `C`
  to `D` is a profunctor `Prof C D`.
* `PathProd`: The product of profunctor values along a path of profunctors.
* `Cell`: A cell from a path of profunctors to a target profunctor, satisfying naturality
  and wedge conditions. This generalizes `BiNatTrans` from `Operad.lean` to paths of
  arbitrary length.
* `Cell.ofComp`: Composition of cells via a binatural transformation.

## Design notes

The base case of `PathProd` for the empty path `.nil` uses `ULift (c ⟶ d)`. This ensures
that a cell from the empty path to `K` is equivalent to a dinatural element (unit) of `K`,
and a cell from a singleton path `[H]` to `K` is equivalent to a natural transformation from
`H` to `K`.

The wedge conditions are defined recursively via `AllWedge`, which checks the compatibility
condition at each internal vertex where two consecutive profunctors in the path meet.
-/

@[expose] public section

namespace CategoryTheory

universe u v

/-! ## Paths as a monad on quivers -/

/-- `Paths V` is a type wrapper around `V` equipped with a quiver structure where an edge
from `a` to `b` is a `Quiver.Path a b` in the original quiver. -/
structure Paths (V : Type*) where
  /-- The underlying vertex. -/
  val : V

/-- The quiver instance on `Paths V`: edges are paths in the original quiver. -/
instance {V : Type*} [Quiver V] : Quiver (Paths V) where
  Hom a b := Quiver.Path a.val b.val

namespace Paths

variable {V : Type*} [Quiver V]

/-- The unit of the `Paths` monad: sends each edge to a singleton path. -/
def η : Prefunctor V (Paths V) where
  obj v := ⟨v⟩
  map f := .cons .nil f

/-- Flatten a path of paths into a single path by concatenation.
This is the action on morphisms of the multiplication of the `Paths` monad. -/
def flatten {a b : Paths V} :
    Quiver.Path a b → (a ⟶ b)
  | .nil => .nil
  | .cons p e => (flatten p).comp e

/-- The multiplication of the `Paths` monad as a prefunctor. -/
def μ : Prefunctor (Paths (Paths V)) (Paths V) where
  obj v := ⟨v.val.val⟩
  map := flatten

/-! ### Monad laws -/

/-- Left unit law: flattening a singleton path-of-paths recovers the original path. -/
theorem left_unit {a b : Paths V} (p : a ⟶ b) :
    flatten (.cons .nil p) = p :=
  Quiver.Path.nil_comp p

/-- Right unit law: embedding each edge as a singleton and then flattening
recovers the original path. -/
theorem right_unit {a b : V} (p : Quiver.Path a b) :
    @flatten V _ ⟨a⟩ ⟨b⟩ (@Prefunctor.mapPath V _ (Paths V) _ η a b p) = p := by
  induction p with
  | nil => rfl
  | cons p _ ih =>
    change (flatten (@Prefunctor.mapPath V _ (Paths V) _ η _ _ p)).comp _ = _
    sorry
    -- rw [ih]; rfl

/-- Flattening distributes over path composition. -/
theorem flatten_comp {a b c : Paths V} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    flatten (p.comp q) = (flatten p).comp (flatten q) := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    show (flatten (p.comp q)).comp e = (flatten p).comp ((flatten q).comp e)
    rw [ih, @Quiver.Path.comp_assoc V]

/-- Associativity: flattening a path of paths of paths in either order gives the same
result. -/
theorem assoc {a b : Paths (Paths V)}
    (p : @Quiver.Path (Paths (Paths V)) _ a b) :
    @flatten V _ ⟨a.val.val⟩ ⟨b.val.val⟩ (@Prefunctor.mapPath _ _ (Paths V) _ μ _ _ p) =
    @flatten V _ ⟨a.val.val⟩ ⟨b.val.val⟩ (flatten p) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    show (flatten (μ.mapPath p)).comp (flatten e) = flatten ((flatten p).comp e)
    sorry
    -- rw [ih, flatten_comp]

end Paths

/-! ## The profunctor quiver -/

/-- `ProfCat` is a wrapper around `Cat` equipped with a quiver structure where
an edge from `C` to `D` is a profunctor `Prof C D`.

While `Cat` uses functors as morphisms (and has a `Category` instance), `ProfCat`
uses profunctors as edges (and only has a `Quiver` instance). -/
structure ProfCat.{v', u'} where
  /-- The underlying category. -/
  toCat : Cat.{v', u'}

instance : CoeSort ProfCat.{v, u} (Type u) where
  coe C := C.toCat.α

-- instance (C : ProfCat.{v, u}) : Category.{v} (C : Type u) :=
  -- C.toCat.str

/-- The quiver structure on `ProfCat`: an edge from `C` to `D` is a profunctor. -/
instance : Quiver ProfCat.{v, u} where
  Hom C D := Prof C.toCat D.toCat

/-! ## Path products -/

/-- The product of profunctor values along a path of profunctors.

For the empty path (`.nil : Path C C`), `PathProd .nil c d = ULift (c ⟶ d)`, recording
a morphism from `c` to `d` in the category `C`.

For a path `.cons p H` ending with profunctor `H : Prof E D`, `PathProd (.cons p H) c d`
is the Σ-type `Σ (e : E), PathProd p c e × H.app e d`, quantifying over the intermediate
object `e` where the sub-path `p` meets `H`. -/
def PathProd {C D : ProfCat.{v, u}} :
    Quiver.Path C D → C → D → Type (max u v)
  | .nil, c, d => ULift.{u} (c ⟶ d)
  | @Quiver.Path.cons _ _ _ E _ p H, c, d => Σ (e : E), PathProd p c e × H.app e d

-- NOTE: The arguments are swapped here!

namespace PathProd

/-- Left action on `PathProd`: precomposes a morphism on the left boundary.
This acts on the base morphism in the `.nil` case, or recursively on the
leftmost component. -/
def mapL {C D : ProfCat.{v, u}} {c c' : C} {d : D} (α : c' ⟶ c)
    {p : Quiver.Path C D} (args : PathProd p c d) : PathProd p c' d :=
  match p, d, args with
  | .nil, _, ⟨f⟩ => ⟨α ≫ f⟩
  | Quiver.Path.cons _ _, _, args =>
    let ⟨e, inner, h⟩ := args; ⟨e, mapL α inner, h⟩

/-- Right action on `PathProd`: postcomposes a morphism on the right boundary,
acting on the rightmost profunctor via `Prof.mapR` in the `.cons` case. -/
def mapR {C D : ProfCat.{v, u}} {c : C} {d d' : D}
    {p : Quiver.Path C D} (args : PathProd p c d)
    (α : d ⟶ d') : PathProd p c d' :=
  match D, p, d, d', args, α with
  | _, .nil, _, _, ⟨f⟩, α => ⟨f ≫ α⟩
  | _, @Quiver.Path.cons _ _ _ _ _ _ H, _, _, args, α =>
    let ⟨e, inner, h⟩ := args; ⟨e, inner, H.mapR h α⟩

/-- Concatenation of path products: given path products for composable paths `p` and `q`,
produce a path product for the composition `p.comp q`. -/
def comp {C E D : ProfCat.{v, u}} {c : C} {e : E} {d : D}
    {p : Quiver.Path C E} {q : Quiver.Path E D}
    (args_p : PathProd p c e) (args_q : PathProd q e d) : PathProd (p.comp q) c d :=
  match D, q, d, args_q with
  | _, .nil, _, ⟨f⟩ => args_p.mapR f
  | _, Quiver.Path.cons _ _, _, args_q =>
    let ⟨f, inner_q, h⟩ := args_q; ⟨f, PathProd.comp args_p inner_q, h⟩

-- NOTE: You really want an n-ary composition operation here

end PathProd

/-! ## Wedge conditions -/

/-- All internal wedge conditions for a cell with path `p`, at a fixed right boundary `d`.

For the empty path, there are no wedge conditions.
For `.cons p H`, the conditions are:
1. **Junction wedge**: for any morphism `α : e ⟶ e'` at the vertex shared between `p`
   and `H`, sliding `α` from the right boundary of `p` to the left boundary of `H` does
   not change the cell's value.
2. **Internal wedges**: all wedge conditions within the sub-path `p`, for each fixed choice
   of intermediate object `e` and element `h : H.app e d`. -/
def AllWedge {C D : ProfCat.{v, u}} :
    (p : Quiver.Path C D) → (d : D) → {R : C → Sort*} →
    (app : ∀ (c : C), PathProd p c d → R c) → Prop
  | .nil, _, _, _ => True
  | @Quiver.Path.cons _ _ _ E _ p H, d, _, app =>
    (∀ (c : _) (e e' : E) (α : e ⟶ e') (args : PathProd p c e) (h : H.app e' d),
      app c ⟨e', args.mapR α, h⟩ = app c ⟨e, args, H.mapL α h⟩)
    ∧
    (∀ (e : E) (h : H.app e d),
      AllWedge p e (fun c args => app c ⟨e, args, h⟩))

-- NOTE: We parameterize over `app` here, to get the data that will later be part of `Cell`.


/-! ## Cell definition -/

/-- A cell from a path of profunctors to a target profunctor.

Given a path `C₀ →[H₁] C₁ → ⋯ →[Hₙ] Cₙ` of profunctors and a target profunctor
`K : Prof C₀ Cₙ`, a cell consists of a family of maps
  `H₁(c₀,c₁) × ⋯ × Hₙ(cₙ₋₁,cₙ) → K(c₀,cₙ)`
for all choices of objects `c₀, …, cₙ`, satisfying:

* **Left naturality** (`natL`): compatibility with acting on the left boundary `c₀`.
* **Right naturality** (`natR`): compatibility with acting on the right boundary `cₙ`.
* **Wedge conditions** (`wedge`): for each internal vertex `cᵢ` shared by `Hᵢ` and `Hᵢ₊₁`,
  sliding a morphism `α : cᵢ ⟶ cᵢ'` between the right action of `Hᵢ` and the left action
  of `Hᵢ₊₁` does not change the result.

This generalizes `BiNatTrans` (the case of two profunctors) to arbitrary-length paths. -/
structure Cell {C D : ProfCat.{v, u}} (p : @Quiver.Path ProfCat _ C D)
    (K : Prof C.toCat D.toCat) where
  /-- The multi-application map: takes elements from each profunctor in the path
      and produces an element of the target profunctor. -/
  app : ∀ (c : C) (d : D), PathProd p c d → K.app c d
  /-- Naturality with respect to acting on the left boundary. -/
  natL : ∀ {c c' : C} {d : D} (α : c' ⟶ c) (args : PathProd p c d),
    app c' d (args.mapL α) = K.mapL α (app c d args)
  /-- Naturality with respect to acting on the right boundary. -/
  natR : ∀ {c : C} {d d' : D} (args : PathProd p c d) (α : d ⟶ d'),
    app c d' (args.mapR α) = K.mapR (app c d args) α
  /-- All internal wedge conditions. -/
  wedge : ∀ (d : D), AllWedge p d (fun c args => app c d args)

/-! ## Splitting and composition of cells -/

/-- Split a path product for a composed path into path products for the two parts.
Given `PathProd (p.comp q) c d`, produce an intermediate object `e : E` together
with `PathProd p c e` and `PathProd q e d`. -/
def PathProd.split {C E D : ProfCat.{v, u}} {c : C} {d : D}
    {p : @Quiver.Path ProfCat _ C E} {q : @Quiver.Path ProfCat _ E D}
    (args : PathProd (p.comp q) c d) : (e : E) × PathProd p c e × PathProd q e d :=
  match D, q, d, args with
  | _, .nil, d, args => ⟨d, args, ⟨𝟙 d⟩⟩
  | _, Quiver.Path.cons _ _, _, args =>
    let ⟨f, inner, h⟩ := args
    let ⟨e, p_part, q_part⟩ := PathProd.split inner
    ⟨e, p_part, ⟨f, q_part, h⟩⟩

/-- Composition of cells: given a binatural transformation `bi` from `(J, K)` to `L`,
a cell `φ` from path `p` to `J`, and a cell `ψ` from path `q` to `K`, produce a cell
from the concatenated path `p ++ q` to `L`.

This is the fundamental composition operation for cells of profunctors. -/
noncomputable def Cell.ofComp {C E D : ProfCat.{v, u}}
    {p : @Quiver.Path ProfCat _ C E} {q : @Quiver.Path ProfCat _ E D}
    {J : Prof C.toCat E.toCat} {K : Prof E.toCat D.toCat} {L : Prof C.toCat D.toCat}
    (bi : Cell (.cons (.cons .nil J) K) L)
    (φ : Cell p J) (ψ : Cell q K) : Cell (p.comp q) L where
  app c d args :=
    bi.app c d ⟨args.split.1, ⟨c, ⟨𝟙 c⟩, φ.app c args.split.1 args.split.2.1⟩, ψ.app args.split.1 d args.split.2.2⟩
  natL := sorry
  natR := sorry
  wedge := sorry

end CategoryTheory
