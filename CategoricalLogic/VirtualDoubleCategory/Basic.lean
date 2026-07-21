import Mathlib

namespace CategoryTheory

-- Think of the edges in Q and R as proarrows.
-- `arr` gives the type of arrows between two vertices.
-- `square` gives the type of cells filling a square of arrows and proarrows

structure QuiverSpan (Q R : Type*) [Quiver Q] [Quiver R] where
  /-- `arr` gives the type of arrows between two vertices. -/
  arr (x : Q) (y : R) : Type*
  /-- `square` gives the type of cells filling a square of arrows and proarrows. -/
  square {x x' : Q} {y y' : R} (e : x ⟶ x') (e' : y ⟶ y') (f : arr x y) (f' : arr x' y')
    : Type*

namespace QuiverSpan

protected def id (Q : Type*) [Quiver Q] : QuiverSpan Q Q where
  arr x y := PLift (x = y)
  square e e' f f' := match f.down, f'.down with
    | Eq.refl _, Eq.refl _ => PLift (e = e')

protected def comp {Q R S : Type*} [Quiver Q] [Quiver R] [Quiver S] (F : QuiverSpan Q R) (G : QuiverSpan R S) : QuiverSpan Q S where
  arr x y := Σ (w : R), F.arr x w × G.arr w y
  square := fun e e' ⟨w,f,g⟩ ⟨w',f',g'⟩ => Σ (z : w ⟶ w'), F.square e z f f' × G.square z e' g g'

structure Hom {Q R : Type*} [Quiver Q] [Quiver R] (S T : QuiverSpan Q R) where
  map_arr {x : Q} {y : R} (a : S.arr x y) : T.arr x y
  map_square {x x' : Q} {y y' : R} {e : x ⟶ x'} {e' : y ⟶ y'}
    {f : S.arr x y} {f' : S.arr x' y'} (square : S.square e e' f f') :
      T.square e e' (map_arr f) (map_arr f')

end QuiverSpan

/-! ## The Paths monad

TODO: This is work in progress, finish this using the api in `Mathlib.CategoryTheory.PathCategory.Basic` as much as possible.
-/

namespace Paths

variable {V : Type*} [Quiver V]

/-- The unit of the `Paths` monad: sends each edge to a singleton path. -/
def η : Prefunctor V (Paths V) where
  obj v := v
  map f := .cons .nil f

/-- Flatten a path of paths into a single path by concatenation.
This is the action on morphisms of the multiplication of the `Paths` monad. -/
def flatten {a b : Paths V} :
    Quiver.Path a b → (a ⟶ b)
  | .nil => .nil
  | .cons p e => (flatten p).comp e

/-- The multiplication of the `Paths` monad as a prefunctor. -/
def μ : Prefunctor (Paths (Paths V)) (Paths V) where
  obj v := v
  -- map remains to be specified
  map p := @flatten V _ _ _ p

/-! ### Monad laws -/

/-- Left unit law: flattening a singleton path-of-paths recovers the original path. -/
theorem left_unit {a b : Paths V} (p : a ⟶ b) :
    flatten (.cons .nil p) = p :=
  Quiver.Path.nil_comp p

/-- Right unit law: embedding each edge as a singleton and then flattening
recovers the original path. -/
theorem right_unit {a b : V} (p : Quiver.Path a b) :
    @flatten V _ a b (@Prefunctor.mapPath V _ (Paths V) _ η a b p) = p := by
  induction p with
  | nil => rfl
  | cons p _ ih =>
    change (flatten (@Prefunctor.mapPath V _ (Paths V) _ η _ _ p)).comp _ = _
    exact congrArg (fun q ↦ Quiver.Path.comp q (η.map _)) ih

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
    @flatten V _ a b (@Prefunctor.mapPath _ _ (Paths V) _ μ _ _ p) =
    @flatten V _ a b (flatten p) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, flatten]
    exact (congrArg (fun q ↦ Quiver.Path.comp q (μ.map e)) ih).trans
      (flatten_comp (flatten p) e).symm

/-! ### Path functor on spans -/

open Quiver

variable {S T : Type*} [Quiver S] [Quiver T]

structure ProArr (s : QuiverSpan S T)  where
  src : S
  tgt : T
  arr : s.arr src tgt

instance (s : QuiverSpan S T) : Quiver (ProArr s) where
  Hom a a' := Σ (f : a.src ⟶ a'.src) (g : a.tgt ⟶ a'.tgt), s.square f g a.arr a'.arr

-- Okay, just do this on the blueprint and then extend using AI
-- def mapQuiverSpan (s : QuiverSpan S T) :
--     QuiverSpan (Paths S) (Paths T) where
--   arr x y := s.arr x y
--   square f g a b := { p : Quiver.Path (ProArr.mk _ _ a) (ProArr.mk _ _ b) | True }

end Paths

-- def QuivSpan := Bundled Quiver

-- instance : CoeSort QuivSpan (Type*) where coe := Bundled.α

-- instance str' (C : QuivSpan) : Quiver C :=
--   C.str

-- A bicategory instance remains to be specified
  -- Hom Q R := QuiverSpan Q R
  -- id Q := QuiverSpan.id Q
  -- comp F G := QuiverSpan.comp F G


-- `comp.map_arr` composes a pair of arrows
-- `comp.map_square` (vertically) composes a pair of cells

/-
The following two sketches were incomplete: their law fields were unstated placeholders whose
universe levels cannot be inferred. They are retained here as design notes until the laws are given
actual propositions.

structure DoubleCategory (Q : Type*) [Quiver Q] where
  squares : QuiverSpan Q Q
  id : QuiverSpan.Hom (QuiverSpan.id Q) squares
  comp : QuiverSpan.Hom (QuiverSpan.comp squares squares) squares
  id_comp : <left unit law>
  comp_id : <right unit law>
  comp_assoc : <associativity law>

structure VirtualDoubleCategory (Q : Quiv) where
  squares : QuiverSpan Q (Paths Q)
-/
