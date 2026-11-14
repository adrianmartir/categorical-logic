/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Operad
public import CategoricalLogic.Designs.Bespoke.Transport

/-!
# The category of `T`-operads

For any monad of profunctors `T`, operads (bundled with their category of objects) and their
morphisms form a category. The laws hold up to the transports in `Operad.Hom.id` and
`Operad.Hom.comp`, and are proved through `HEq`.
-/

@[expose] public section

namespace CategoryTheory

universe w v u

open Profunctor FunctorProf MonadProf

/-- Close a goal `x ≍ y` where `x` and `y` are the same term up to transports `mpLeft`,
`mpRight` wrapped around it. -/
macro "strip_mp" : tactic => `(tactic| (
  repeat (first | refine (mpLeft_heq _ _ _).trans ?_ | refine (mpRight_heq _ _ _).trans ?_)
  refine HEq.symm ?_
  repeat (first | refine (mpLeft_heq _ _ _).trans ?_ | refine (mpRight_heq _ _ _).trans ?_)
  exact HEq.rfl))

variable {T : Monad Cat.{v, u}} [MonadProf.{u, v, w} T]

namespace Operad.Hom

variable {X Y : Cat.{v, u}} {M : Operad T X} {N : Operad T Y}

theorem ext {φ ψ : Hom M N} (h : φ.functor = ψ.functor)
    (h' : ∀ {a b} (f : M.hom.app a b), φ.map.app f ≍ ψ.map.app f) : φ = ψ := by
  obtain ⟨F, s, _, _⟩ := φ
  obtain ⟨F', s', _, _⟩ := ψ
  subst h
  obtain rfl : s = s' := Square.ext fun f => eq_of_heq (h' f)
  rfl

end Operad.Hom

variable (T) in
/-- `T`-operads, bundled with their category of objects. -/
structure OperadCat where
  /-- The category of objects. -/
  obj : Cat.{v, u}
  /-- The operad. -/
  operad : Operad T obj

namespace OperadCat

instance : Category (OperadCat.{w, v, u} T) where
  Hom M N := Operad.Hom M.operad N.operad
  id M := Operad.Hom.id M.operad
  comp φ ψ := φ.comp ψ
  id_comp φ := Operad.Hom.ext (Category.id_comp _) fun f => by
    simp only [Operad.Hom.comp, Operad.Hom.id, Square.cast_app, Square.vComp_app, Square.id_app,
      Square.app_mpLeft, Square.app_mpRight]
    strip_mp
  comp_id φ := Operad.Hom.ext (Category.comp_id _) fun f => by
    simp only [Operad.Hom.comp, Operad.Hom.id, Square.cast_app, Square.vComp_app, Square.id_app]
    strip_mp
  assoc φ ψ χ := Operad.Hom.ext (Category.assoc _ _ _) fun f => by
    simp only [Operad.Hom.comp, Square.cast_app, Square.vComp_app, Square.app_mpLeft,
      Square.app_mpRight]
    strip_mp

end OperadCat

end CategoryTheory
