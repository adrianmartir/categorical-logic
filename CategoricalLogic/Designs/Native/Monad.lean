/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import CategoricalLogic.Designs.Native.Basic

/-!
# Monads acting on profunctors, natively

A monad `T` on `Cat` *acts on profunctors* if it comes with

* a functor `mapProf : Profunctor C D ⥤ Profunctor (T C) (T D)` (so `T` acts on cells with
  identity vertical boundary, functorially, for free);
* a comparison `mapRestrict F G : T(P(F, G)) ⟶ (T P)(T F, T G)`, natural in `P` (stated as a
  natural transformation between functors of profunctor categories);
* a laxator `mapComp P Q : T P ⊙ T Q ⟶ T (P ⊙ Q)` and a unit comparison
  `mapId : id ⟶ T id`;
* the unit and multiplication as natural transformations
  `η : 𝟭 ⟶ mapProf ⋙ restrict η η` and `μ : mapProf ⋙ mapProf ⟶ mapProf ⋙ restrict μ μ`;

subject to coherence laws. The action on a general cell is derived: a unary cell
`s : P ⟶ Q(F, G)` is sent to `mapProf.map s ≫ mapRestrict F G` (`mapCell`), a binary cell
`β : P ⊙ Q ⟶ R(F, G)` to `mapComp P Q ≫ mapCell β` and a nullary cell
`ν : id ⟶ Q(F, G)` to `mapId ≫ mapCell ν`.

Propositional equalities of functors (`T.map (F ≫ G) = T.map F ⋙ T.map G`, the monad laws)
appear as `eqToHom` between restricted profunctors.
-/

@[expose] public section

namespace CategoryTheory.Native

universe u

open Profunctor

/-! ### The monad laws as equalities of functors -/

section toFunctor

variable (T : Monad Cat.{u, u})

theorem map_id_toFunctor (C : Cat.{u, u}) : (T.map (𝟙 C)).toFunctor = 𝟭 (T.obj C) :=
  congrArg Cat.Hom.toFunctor (T.map_id C)

theorem map_comp_toFunctor {C D E : Cat.{u, u}} (F : C ⟶ D) (G : D ⟶ E) :
    (T.map (F ≫ G)).toFunctor = (T.map F).toFunctor ⋙ (T.map G).toFunctor :=
  congrArg Cat.Hom.toFunctor (T.map_comp F G)

theorem η_naturality_toFunctor {C D : Cat.{u, u}} (F : C ⟶ D) :
    F.toFunctor ⋙ (T.η.app D).toFunctor = (T.η.app C).toFunctor ⋙ (T.map F).toFunctor :=
  congrArg Cat.Hom.toFunctor (T.η.naturality F)

theorem μ_naturality_toFunctor {C D : Cat.{u, u}} (F : C ⟶ D) :
    (T.map (T.map F)).toFunctor ⋙ (T.μ.app D).toFunctor =
      (T.μ.app C).toFunctor ⋙ (T.map F).toFunctor :=
  congrArg Cat.Hom.toFunctor (T.μ.naturality F)

theorem left_unit_toFunctor (C : Cat.{u, u}) :
    (T.η.app (T.obj C)).toFunctor ⋙ (T.μ.app C).toFunctor = 𝟭 (T.obj C) :=
  congrArg Cat.Hom.toFunctor (T.left_unit C)

theorem right_unit_toFunctor (C : Cat.{u, u}) :
    (T.map (T.η.app C)).toFunctor ⋙ (T.μ.app C).toFunctor = 𝟭 (T.obj C) :=
  congrArg Cat.Hom.toFunctor (T.right_unit C)

theorem assoc_toFunctor (C : Cat.{u, u}) :
    (T.map (T.μ.app C)).toFunctor ⋙ (T.μ.app C).toFunctor =
      (T.μ.app (T.obj C)).toFunctor ⋙ (T.μ.app C).toFunctor :=
  congrArg Cat.Hom.toFunctor (T.assoc C)

end toFunctor

/-! ### Monads acting on profunctors -/

/-- A monad `T` on `Cat` acting on profunctors: a functor between categories of profunctors,
lax with respect to restriction, composition and identities, with unit and multiplication
natural transformations. This is a monad on the virtual equipment of categories, functors and
profunctors, truncated at cells of arity `≤ 2`, presented through mathlib's categories of
profunctors. -/
class ProfMonad (T : Monad Cat.{u, u}) where
  /-- The action on profunctors and on cells with identity boundary. -/
  mapProf {C D : Cat.{u, u}} : Profunctor.{u} C D ⥤ Profunctor.{u} (T.obj C) (T.obj D)
  /-- The comparison `T(P(F, G)) ⟶ (T P)(T F, T G)`. -/
  mapRestrict {A B C D : Cat.{u, u}} (F : A ⟶ C) (G : B ⟶ D) :
    restrict F.toFunctor G.toFunctor ⋙ mapProf ⟶
      mapProf ⋙ restrict (T.map F).toFunctor (T.map G).toFunctor
  /-- The laxator `T P ⊙ T Q ⟶ T (P ⊙ Q)`. -/
  mapComp {C D E : Cat.{u, u}} (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) :
    (mapProf.obj P).comp (mapProf.obj Q) ⟶ mapProf.obj (P.comp Q)
  /-- The unit comparison `id ⟶ T id`. -/
  mapId (C : Cat.{u, u}) : (Profunctor.id : Profunctor.{u} (T.obj C) (T.obj C)) ⟶
    mapProf.obj (Profunctor.id : Profunctor.{u} C C)
  /-- The unit, with component `P ⟶ (T P)(η, η)` at `P`. -/
  η {C D : Cat.{u, u}} :
    𝟭 (Profunctor.{u} C D) ⟶ mapProf ⋙ restrict (T.η.app C).toFunctor (T.η.app D).toFunctor
  /-- The multiplication, with component `T T P ⟶ (T P)(μ, μ)` at `P`. -/
  μ {C D : Cat.{u, u}} :
    mapProf ⋙ mapProf ⟶ mapProf ⋙ restrict (T.μ.app C).toFunctor (T.μ.app D).toFunctor
  /-- `mapRestrict` along identities is the identity. -/
  mapRestrict_id (C D : Cat.{u, u}) (P : Profunctor.{u} C D) :
    (mapRestrict (𝟙 C) (𝟙 D)).app P =
      eqToHom ((mapProf.obj P).whiskerLeft₂_congr (map_id_toFunctor T C).symm
        (map_id_toFunctor T D).symm)
  /-- `mapRestrict` along composites is the composite of `mapRestrict`s. -/
  mapRestrict_comp {A' B' A B C D : Cat.{u, u}} (F' : A' ⟶ A) (G' : B' ⟶ B) (F : A ⟶ C)
    (G : B ⟶ D) (P : Profunctor.{u} C D) :
    (mapRestrict (F' ≫ F) (G' ≫ G)).app P =
      (mapRestrict F' G').app (P.whiskerLeft₂ F.toFunctor G.toFunctor) ≫
        (restrict (T.map F').toFunctor (T.map G').toFunctor).map ((mapRestrict F G).app P) ≫
          eqToHom ((mapProf.obj P).whiskerLeft₂_congr (map_comp_toFunctor T F' F).symm
            (map_comp_toFunctor T G' G).symm)
  /-- Naturality of the laxator in the right argument. -/
  mapComp_whiskerLeft {C D E : Cat.{u, u}} (P : Profunctor.{u} C D) {Q Q' : Profunctor.{u} D E}
    (g : Q ⟶ Q') :
    (mapProf.obj P).whiskerLeft (mapProf.map g) ≫ mapComp P Q' =
      mapComp P Q ≫ mapProf.map (P.whiskerLeft g)
  /-- Naturality of the laxator in the left argument. -/
  mapComp_whiskerRight {C D E : Cat.{u, u}} {P P' : Profunctor.{u} C D} (f : P ⟶ P')
    (Q : Profunctor.{u} D E) :
    Profunctor.whiskerRight (mapProf.obj Q) (mapProf.map f) ≫ mapComp P' Q =
      mapComp P Q ≫ mapProf.map (Profunctor.whiskerRight Q f)
  /-- The laxator is compatible with restriction. -/
  mapComp_compRestrict {A B E' C D E : Cat.{u, u}} (P : Profunctor.{u} C D)
    (Q : Profunctor.{u} D E) (F : A ⟶ C) (K : B ⟶ D) (G : E' ⟶ E) :
    mapComp (P.whiskerLeft₂ F.toFunctor K.toFunctor) (Q.whiskerLeft₂ K.toFunctor G.toFunctor) ≫
        mapProf.map (compRestrict P Q F.toFunctor K.toFunctor G.toFunctor) ≫
          (mapRestrict F G).app (P.comp Q) =
      hComp ((mapRestrict F K).app P) ((mapRestrict K G).app Q) ≫
        (restrict (T.map F).toFunctor (T.map G).toFunctor).map (mapComp P Q)
  /-- The laxator is associative. -/
  mapComp_assoc {C D E E' : Cat.{u, u}} (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E)
    (R : Profunctor.{u} E E') :
    Profunctor.whiskerRight (mapProf.obj R) (mapComp P Q) ≫ mapComp (P.comp Q) R ≫
        mapProf.map (associator P Q R).hom =
      (associator (mapProf.obj P) (mapProf.obj Q) (mapProf.obj R)).hom ≫
        (mapProf.obj P).whiskerLeft (mapComp Q R) ≫ mapComp P (Q.comp R)
  /-- The laxator is left unital. -/
  mapComp_leftUnitor {C D : Cat.{u, u}} (P : Profunctor.{u} C D) :
    Profunctor.whiskerRight (mapProf.obj P) (mapId C) ≫ mapComp Profunctor.id P ≫
        mapProf.map (leftUnitor P).hom = (leftUnitor (mapProf.obj P)).hom
  /-- The laxator is right unital. -/
  mapComp_rightUnitor {C D : Cat.{u, u}} (P : Profunctor.{u} C D) :
    (mapProf.obj P).whiskerLeft (mapId D) ≫ mapComp P Profunctor.id ≫
        mapProf.map (rightUnitor P).hom = (rightUnitor (mapProf.obj P)).hom
  /-- The unit comparison is compatible with reindexing along functors. -/
  mapId_idRestrict {A C : Cat.{u, u}} (K : A ⟶ C) :
    mapId A ≫ mapProf.map (idRestrict K.toFunctor) ≫ (mapRestrict K K).app Profunctor.id =
      idRestrict (T.map K).toFunctor ≫
        (restrict (T.map K).toFunctor (T.map K).toFunctor).map (mapId C)
  /-- The unit is compatible with restriction. -/
  η_restrict {A B C D : Cat.{u, u}} (F : A ⟶ C) (G : B ⟶ D) (P : Profunctor.{u} C D) :
    η.app (P.whiskerLeft₂ F.toFunctor G.toFunctor) ≫
        (restrict (T.η.app A).toFunctor (T.η.app B).toFunctor).map ((mapRestrict F G).app P) ≫
          eqToHom ((mapProf.obj P).whiskerLeft₂_congr (η_naturality_toFunctor T F).symm
            (η_naturality_toFunctor T G).symm) =
      (restrict F.toFunctor G.toFunctor).map (η.app P)
  /-- The unit is compatible with composition. -/
  η_comp {C D E : Cat.{u, u}} (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) :
    hComp (η.app P) (η.app Q) ≫
        (restrict (T.η.app C).toFunctor (T.η.app E).toFunctor).map (mapComp P Q) =
      η.app (P.comp Q)
  /-- The unit is compatible with identities. -/
  η_id (C : Cat.{u, u}) :
    idRestrict (T.η.app C).toFunctor ≫
        (restrict (T.η.app C).toFunctor (T.η.app C).toFunctor).map (mapId C) =
      η.app Profunctor.id
  /-- The multiplication is compatible with restriction. -/
  μ_restrict {A B C D : Cat.{u, u}} (F : A ⟶ C) (G : B ⟶ D) (P : Profunctor.{u} C D) :
    μ.app (P.whiskerLeft₂ F.toFunctor G.toFunctor) ≫
        (restrict (T.μ.app A).toFunctor (T.μ.app B).toFunctor).map ((mapRestrict F G).app P) ≫
          eqToHom ((mapProf.obj P).whiskerLeft₂_congr (μ_naturality_toFunctor T F)
            (μ_naturality_toFunctor T G)).symm =
      mapProf.map ((mapRestrict F G).app P) ≫
        (mapRestrict (T.map F) (T.map G)).app (mapProf.obj P) ≫
          (restrict (T.map (T.map F)).toFunctor (T.map (T.map G)).toFunctor).map (μ.app P)
  /-- The multiplication is compatible with composition. -/
  μ_comp {C D E : Cat.{u, u}} (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) :
    hComp (μ.app P) (μ.app Q) ≫
        (restrict (T.μ.app C).toFunctor (T.μ.app E).toFunctor).map (mapComp P Q) =
      mapComp (mapProf.obj P) (mapProf.obj Q) ≫ mapProf.map (mapComp P Q) ≫ μ.app (P.comp Q)
  /-- The multiplication is compatible with identities. -/
  μ_id (C : Cat.{u, u}) :
    idRestrict (T.μ.app C).toFunctor ≫
        (restrict (T.μ.app C).toFunctor (T.μ.app C).toFunctor).map (mapId C) =
      mapId (T.obj C) ≫ mapProf.map (mapId C) ≫ μ.app Profunctor.id
  /-- The left unit law. -/
  left_unit {C D : Cat.{u, u}} (P : Profunctor.{u} C D) :
    η.app (mapProf.obj P) ≫
        (restrict (T.η.app (T.obj C)).toFunctor (T.η.app (T.obj D)).toFunctor).map (μ.app P) ≫
          eqToHom ((mapProf.obj P).whiskerLeft₂_congr (left_unit_toFunctor T C)
            (left_unit_toFunctor T D)) = 𝟙 _
  /-- The right unit law. -/
  right_unit {C D : Cat.{u, u}} (P : Profunctor.{u} C D) :
    mapProf.map (η.app P) ≫ (mapRestrict (T.η.app C) (T.η.app D)).app (mapProf.obj P) ≫
        (restrict (T.map (T.η.app C)).toFunctor (T.map (T.η.app D)).toFunctor).map (μ.app P) ≫
          eqToHom ((mapProf.obj P).whiskerLeft₂_congr (right_unit_toFunctor T C)
            (right_unit_toFunctor T D)) = 𝟙 _
  /-- The associativity law. -/
  assoc {C D : Cat.{u, u}} (P : Profunctor.{u} C D) :
    μ.app (mapProf.obj P) ≫
        (restrict (T.μ.app (T.obj C)).toFunctor (T.μ.app (T.obj D)).toFunctor).map (μ.app P) ≫
          eqToHom ((mapProf.obj P).whiskerLeft₂_congr (assoc_toFunctor T C)
            (assoc_toFunctor T D)).symm =
      mapProf.map (μ.app P) ≫ (mapRestrict (T.μ.app C) (T.μ.app D)).app (mapProf.obj P) ≫
        (restrict (T.map (T.μ.app C)).toFunctor (T.map (T.μ.app D)).toFunctor).map (μ.app P)

namespace ProfMonad

variable {T : Monad Cat.{u, u}} [ProfMonad T]

/-- The action of `T` on a unary cell `s : P ⟶ Q(F, G)`. -/
def mapCell {A B C D : Cat.{u, u}} {P : Profunctor.{u} A B} {Q : Profunctor.{u} C D}
    {F : A ⟶ C} {G : B ⟶ D} (s : P ⟶ Q.whiskerLeft₂ F.toFunctor G.toFunctor) :
    mapProf.obj P ⟶ (mapProf.obj Q).whiskerLeft₂ (T.map F).toFunctor (T.map G).toFunctor :=
  mapProf.map s ≫ (mapRestrict F G).app Q

/-- The action of `T` on a nullary cell `ν : id ⟶ Q(F, G)`. -/
def mapNullary {A C D : Cat.{u, u}} {Q : Profunctor.{u} C D} {F : A ⟶ C} {G : A ⟶ D}
    (ν : Profunctor.id ⟶ Q.whiskerLeft₂ F.toFunctor G.toFunctor) :
    Profunctor.id ⟶ (mapProf.obj Q).whiskerLeft₂ (T.map F).toFunctor (T.map G).toFunctor :=
  mapId A ≫ mapCell ν

/-- The action of `T` on a binary cell `β : P ⊙ Q ⟶ R(F, G)`. -/
def mapBinary {X Y Z X' Z' : Cat.{u, u}} {P : Profunctor.{u} X Y} {Q : Profunctor.{u} Y Z}
    {R : Profunctor.{u} X' Z'} {F : X ⟶ X'} {G : Z ⟶ Z'}
    (β : P.comp Q ⟶ R.whiskerLeft₂ F.toFunctor G.toFunctor) :
    (mapProf.obj P).comp (mapProf.obj Q) ⟶
      (mapProf.obj R).whiskerLeft₂ (T.map F).toFunctor (T.map G).toFunctor :=
  mapComp P Q ≫ mapCell β

end ProfMonad

end CategoryTheory.Native
