/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Native.EndOperad

/-!
# Computing in the endomorphism operad of `ℕ`

With one sort and `X = ℕ`, we compose addition with (addition, identity) and evaluate.
-/

@[expose] public section

namespace CategoryTheory.Native.EndOperad.Example

open Opposite Limits FreeMonProf

/-- The family with one sort, interpreted as `ℕ`. -/
abbrev N : Unit → Type := fun _ ↦ ℕ

/-- The unique sort. -/
def star : Discrete Unit := ⟨()⟩

/-- The operad. -/
abbrev E : Operad Cat.freeMon (Cat.of (Discrete Unit)) := endOperad N

/-- Addition, a binary operation. -/
def add : ((hom N).obj star).obj (op (FreeMon.mk [star, star])) := fun t ↦ t.1 + t.2.1

/-- The identity operation, obtained from the operad's identity cell. -/
def one : ((hom N).obj star).obj (op (FreeMon.mk [star])) :=
  (E.id.app star).app (op star) (𝟙 star)

/-- The arity of the composite `add ∘ (add, one)`. -/
abbrev arity : FreeMon (FreeMon (Discrete Unit)) := FreeMon.mk [FreeMon.mk [star, star], FreeMon.mk [star]]

/-- `add ∘ (add, one)`, computed by the operad's composition cell. -/
def addAddOne : Tuple N [star, star, star] → ℕ :=
  (E.comp.app star).app (op arity)
    (Quot.mk (Types.coendRel ((hom N).compDiagram (obj (hom N)) star arity))
      ⟨FreeMon.mk [star, star], (add, (add, (one, PUnit.unit)))⟩)

example : addAddOne (1, 2, 3, PUnit.unit) = 6 := rfl

example : addAddOne (1, 2, 3, PUnit.unit) = 6 := by decide

-- `#eval addAddOne (1, 2, 3, PUnit.unit)` is refused: first because the instance's law fields
-- contain `sorry`; with `#eval!` because no native code for `endOperad` is available from an
-- imported module of this package ("Could not find native implementation").

end CategoryTheory.Native.EndOperad.Example
