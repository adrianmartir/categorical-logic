/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Kleisli.FreeMon

/-!
# The Kleisli unitors of `FreeMon`, on representatives

What the left and right unitor of the Kleisli composition do to a representative of the coend,
for the planar monad `FreeMon`. They show the residue left in the unfolded monoid laws: a
transport along `[w] ++ [] = w`, resp. along `flatten (map unit bs) = bs`.
-/

@[expose] public section

namespace CategoryTheory

universe u

open Profunctor Opposite KleisliProf FreeMon

variable {X Y : Cat.{u, u}} (P : Profunctor.{u} X (FreeMon Y))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The left unitor on a representative: an identity `f₁` composed with the single operation
`t₁` is `t₁` (moved along `f₁`), up to the transport along `w ++ [] = w`. -/
theorem kleftUnitor_mk {a b : X} {w z : FreeMon Y} (f₁ : b ⟶ a) (t₁ : P.app b w)
    (h : z ⟶ (flatten Y).obj (mk [w])) :
    ((kleftUnitor (T := Cat.freeMon) P).app a).app (op z)
      (Quot.mk _ ⟨mk [w], Quot.mk _ ⟨mk [b], cons f₁ nil, (t₁, PUnit.unit)⟩, h⟩) =
      P.mapR (h ≫ eqToHom (FreeMon.ext (List.append_nil w.as))) (P.mapL f₁ t₁) := by
  change P.mapR (h ≫ _ ≫ _) (P.mapL f₁ t₁) = _
  congr 2
  first
    | (simp only [show cons (𝟙 w) nil = 𝟙 (FreeMon.mk [w]) from rfl, Functor.map_id,
        Category.id_comp]; done)
    | sorry

end CategoryTheory
