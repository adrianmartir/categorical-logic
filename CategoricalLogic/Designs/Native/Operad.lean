/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Native.Monad

/-!
# Operads, natively

A `T`-operad on `X` is a profunctor `hom : X ⇸ T X` with an identity cell
`id : Profunctor.id ⟶ hom(𝟭, η)` and a composition cell `comp : hom ⊙ T hom ⟶ hom(𝟭, μ)`,
both morphisms of mathlib's profunctor categories, satisfying the unit and associativity laws as
equations of morphisms (pastings).
-/

@[expose] public section

namespace CategoryTheory.Native

universe u

open Profunctor ProfMonad

variable (T : Monad Cat.{u, u}) [ProfMonad T]

/-- A `T`-operad on `X` (a `T`-monoid in the sense of Cruttwell–Shulman): `hom.obj a` evaluated
at `b` are the operations with output `a : X` and arity `b : T X`. -/
structure Operad (X : Cat.{u, u}) where
  /-- The operations. -/
  hom : Profunctor.{u} X (T.obj X)
  /-- The identities: a nullary cell `id ⟶ hom(𝟭, η)`. -/
  id : Profunctor.id ⟶ hom.whiskerLeft₂ (𝟭 X) (T.η.app X).toFunctor
  /-- The composition: a binary cell `hom ⊙ T hom ⟶ hom(𝟭, μ)`. -/
  comp : hom.comp (mapProf.obj hom) ⟶ hom.whiskerLeft₂ (𝟭 X) (T.μ.app X).toFunctor
  /-- Left unit law: `id ⊙ hom ⟶ hom(𝟭, η) ⊙ (T hom)(η, η) ⟶ hom(𝟭, η ⋙ μ) = hom` is the left
  unitor. -/
  id_comp : hComp id (η.app hom) ≫ (restrict (𝟭 X) (T.η.app (T.obj X)).toFunctor).map comp ≫
      eqToHom (hom.whiskerLeft₂_congr rfl (left_unit_toFunctor T X)) = (leftUnitor hom).hom
  /-- Right unit law: `hom ⊙ id ⟶ hom ⊙ (T hom)(𝟭, T η) ⟶ hom(𝟭, T η ⋙ μ) = hom` is the right
  unitor. -/
  comp_id : hComp (𝟙 _ : hom ⟶ hom.whiskerLeft₂ (𝟭 X) (𝟭 (T.obj X)))
        (mapNullary (F := 𝟙 X) (G := T.η.app X) id ≫
          eqToHom ((mapProf.obj hom).whiskerLeft₂_congr (map_id_toFunctor T X) rfl)) ≫
      (restrict (𝟭 X) (T.map (T.η.app X)).toFunctor).map comp ≫
        eqToHom (hom.whiskerLeft₂_congr rfl (right_unit_toFunctor T X)) = (rightUnitor hom).hom
  /-- Associativity. -/
  assoc : Profunctor.whiskerRight (mapProf.obj (mapProf.obj hom)) comp ≫
        hComp (K := (T.μ.app X).toFunctor) (𝟙 _) (μ.app hom) ≫
          (restrict (𝟭 X) (T.μ.app (T.obj X)).toFunctor).map comp ≫
            eqToHom (hom.whiskerLeft₂_congr rfl (assoc_toFunctor T X).symm) =
      (associator hom (mapProf.obj hom) (mapProf.obj (mapProf.obj hom))).hom ≫
        hComp (P' := hom) (F := 𝟭 X) (K := 𝟭 (T.obj X)) (𝟙 hom)
          (mapBinary (F := 𝟙 X) (G := T.μ.app X) comp ≫
            eqToHom ((mapProf.obj hom).whiskerLeft₂_congr (map_id_toFunctor T X) rfl)) ≫
          (restrict (𝟭 X) (T.map (T.μ.app X)).toFunctor).map comp

namespace Operad

variable {T} {X Y Z : Cat.{u, u}}

/-- A morphism of `T`-operads: a functor `f` on objects and a cell `hom ⟶ hom(f, T f)`
preserving identities and composition. -/
structure Hom (M : Operad T X) (N : Operad T Y) where
  /-- The action on objects. -/
  functor : X ⟶ Y
  /-- The action on operations. -/
  map : M.hom ⟶ N.hom.whiskerLeft₂ functor.toFunctor (T.map functor).toFunctor
  /-- Identities are preserved. -/
  map_id : M.id ≫ (restrict (𝟭 X) (T.η.app X).toFunctor).map map =
    idRestrict functor.toFunctor ≫ (restrict functor.toFunctor functor.toFunctor).map N.id ≫
      eqToHom (N.hom.whiskerLeft₂_congr rfl (η_naturality_toFunctor T functor))
  /-- Composition is preserved. -/
  map_comp : M.comp ≫ (restrict (𝟭 X) (T.μ.app X).toFunctor).map map =
    hComp map (mapCell map) ≫
      (restrict functor.toFunctor (T.map (T.map functor)).toFunctor).map N.comp ≫
        eqToHom (N.hom.whiskerLeft₂_congr rfl (μ_naturality_toFunctor T functor))

end Operad

end CategoryTheory.Native
