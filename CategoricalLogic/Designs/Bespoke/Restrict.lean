/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Operad
public import CategoricalLogic.Designs.Bespoke.Transport

/-!
# Restriction of an operad along a functor

For a `T`-operad `M` on `X` and a functor `K : Y ⟶ X`, the restricted operad `M.restrict K` on
`Y` has operations `M.hom.app (K a) (T K b)`. This is the first construction, for a general
`T`, that consumes the naturality laws `ηCell_square`, `mapNullary_vComp`, `mapNullary_comap`,
`mapBinary_vComp`, `mapBinary_precomp` and `μCell_square` of `MonadProf`: they are what moves
the restriction square `whiskerSquare` through `T`.
-/

@[expose] public section

namespace CategoryTheory

universe w v u

open Profunctor FunctorProf MonadProf

namespace Profunctor

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

/-- The tautological square out of a restricted profunctor. -/
def whiskerSquare (P : Profunctor.{w} C D) (F : A ⥤ C) (G : B ⥤ D) :
    Square (P.whiskerLeft₂ F G) P F G where
  app f := f
  natL _ _ := rfl
  natR _ _ := rfl

/-- A nullary cell into `P` with boundary `F₀ ⋙ F, G₀ ⋙ G` is a nullary cell into the
restriction `P.whiskerLeft₂ F G`. -/
def NullaryCell.lift {A' : Type*} [Category* A'] {P : Profunctor.{w} C D} {F₀ : A' ⥤ A}
    {F : A ⥤ C} {G₀ : A' ⥤ B} {G : B ⥤ D} (ν : NullaryCell P (F₀ ⋙ F) (G₀ ⋙ G)) :
    NullaryCell (P.whiskerLeft₂ F G) F₀ G₀ where
  app a := ν.app a
  naturality α := ν.naturality α

/-- A binary cell into `R` with boundary `F₀ ⋙ F, G₀ ⋙ G` is a binary cell into the
restriction `R.whiskerLeft₂ F G`. -/
def BinaryCell.lift {X Y Z X' Z' : Type*} [Category* X] [Category* Y] [Category* Z]
    [Category* X'] [Category* Z'] {P : Profunctor.{w} X Y} {Q : Profunctor.{w} Y Z}
    {R : Profunctor.{w} C D} {F₀ : X ⥤ X'} {F : X' ⥤ C} {G₀ : Z ⥤ Z'} {G : Z' ⥤ D}
    (β : BinaryCell P Q R (F₀ ⋙ F) (G₀ ⋙ G)) : BinaryCell P Q (R.whiskerLeft₂ F G) F₀ G₀ where
  app f g := β.app f g
  wedge f α g := β.wedge f α g
  natL α f g := β.natL α f g
  natR f g α := β.natR f g α

end Profunctor

variable {T : Monad Cat.{v, u}} [MonadProf.{u, v, w} T] {X Y : Cat.{v, u}}

namespace FunctorProf

theorem mapNullary_cast_heq {A C D : Cat.{v, u}} {Q : Profunctor.{w} C D} {F F' : A ⟶ C}
    {G G' : A ⟶ D} (hF : F.toFunctor = F'.toFunctor) (hG : G.toFunctor = G'.toFunctor)
    (ν : NullaryCell Q F.toFunctor G.toFunctor) (a : T.obj A) :
    (mapNullary (T := T.toFunctor) F' G' (ν.cast hF hG)).app a ≍ (mapNullary F G ν).app a := by
  obtain rfl := Cat.Hom.ext hF
  obtain rfl := Cat.Hom.ext hG
  simp

end FunctorProf

namespace Operad

variable (M : Operad T X) (K : Y ⟶ X)

/-- The identities of the restricted operad. -/
def restrictId : NullaryCell (M.hom.whiskerLeft₂ K.toFunctor (T.map K).toFunctor) (𝟭 Y)
    (T.η.app Y).toFunctor :=
  NullaryCell.lift (F₀ := 𝟭 Y) (F := K.toFunctor) (G₀ := (T.η.app Y).toFunctor)
    (G := (T.map K).toFunctor) ((M.id.comap K.toFunctor).cast rfl (T.η_naturality_toFunctor K))

/-- The composition of the restricted operad. -/
def restrictComp : BinaryCell (M.hom.whiskerLeft₂ K.toFunctor (T.map K).toFunctor)
    (mapProf (M.hom.whiskerLeft₂ K.toFunctor (T.map K).toFunctor))
    (M.hom.whiskerLeft₂ K.toFunctor (T.map K).toFunctor) (𝟭 Y) (T.μ.app Y).toFunctor :=
  BinaryCell.lift (F₀ := 𝟭 Y) (F := K.toFunctor) (G₀ := (T.μ.app Y).toFunctor)
    (G := (T.map K).toFunctor)
    ((M.comp.precomp (whiskerSquare M.hom K.toFunctor (T.map K).toFunctor)
      (mapSquare K (T.map K) (whiskerSquare M.hom K.toFunctor (T.map K).toFunctor))).cast rfl
      (T.μ_naturality_toFunctor K))

/-- `T` applied to the naturality square of `η` at `K`, on objects. -/
theorem map_η_naturality_obj (b : T.obj Y) :
    (T.map (T.map K)).toFunctor.obj ((T.map (T.η.app Y)).toFunctor.obj b) =
      (T.map (T.η.app X)).toFunctor.obj ((T.map K).toFunctor.obj b) :=
  (Functor.congr_obj (T.map_comp_toFunctor _ _) b).symm.trans
    ((congrArg (fun F => (T.map F).toFunctor.obj b) (T.η.naturality K)).symm.trans
      (Functor.congr_obj (T.map_comp_toFunctor _ _) b))

/-- The restriction of an operad along a functor. -/
def restrict : Operad T Y where
  hom := M.hom.whiskerLeft₂ K.toFunctor (T.map K).toFunctor
  id := M.restrictId K
  comp := M.restrictComp K
  comp_id {a b} f := by
    apply eq_of_heq
    have h1 := Square.app_heq_of_eq_cast
      (ηCell_square (T := T) (whiskerSquare M.hom K.toFunctor (T.map K).toFunctor)) f
    refine (mpLeft_heq _ _ _).trans ((mpRight_heq _ _ _).trans ?_)
    refine (BinaryCell.app_heq M.comp ?_ ?_ ((mpLeft_heq _ _ _).trans (mpRight_heq _ _ _))
      h1.symm).trans ((heq_of_eq (M.comp_id f)).trans
        ((mpRight_heq _ _ _).trans (mpRight_heq _ _ _).symm))
    · exact (Functor.congr_obj (T.η_naturality_toFunctor K) a).symm
    · exact (Functor.congr_obj (T.η_naturality_toFunctor (T.map K)) b).symm
  id_comp {a b} f := by
    apply eq_of_heq
    let wsq := whiskerSquare M.hom K.toFunctor (T.map K).toFunctor
    have e1 : (mapSquare K (T.map K) wsq).app ((mapNullaryId (M.restrictId K)).app b) ≍
        (mapSquare K (T.map K) wsq).app
          ((mapNullary (T := T.toFunctor) (𝟙 Y) (T.η.app Y) (M.restrictId K)).app b) := by
      simp only [mapNullaryId, NullaryCell.cast_app, Square.app_mpLeft, Square.app_mpRight]
      exact (mpLeft_heq _ _ _).trans (mpRight_heq _ _ _)
    have e2 := (NullaryCell.app_heq_of_eq_cast (mapNullary_vComp (T := T.toFunctor) (F := 𝟙 Y)
      (G := T.η.app Y) (F' := K) (G' := T.map K) (M.restrictId K) wsq) b).symm
    have e3 : (M.restrictId K).vComp wsq =
        (M.id.comap K.toFunctor).cast rfl (T.η_naturality_toFunctor K) :=
      NullaryCell.ext fun _ => rfl
    have e4 := mapNullary_cast_heq (T := T) (F := K ≫ 𝟙 X) (G := K ≫ T.η.app X) (F' := 𝟙 Y ≫ K)
      (G' := T.η.app Y ≫ T.map K) rfl (T.η_naturality_toFunctor K) (M.id.comap K.toFunctor) b
    rw [← e3] at e4
    have e5 := NullaryCell.app_heq_of_eq_cast
      (mapNullary_comap (T := T.toFunctor) (F := 𝟙 X) (G := T.η.app X) K M.id) b
    have e6 : (mapNullaryId M.id).app ((T.map K).toFunctor.obj b) ≍
        (mapNullary (T := T.toFunctor) (𝟙 X) (T.η.app X) M.id).app ((T.map K).toFunctor.obj b) :=
      (mpLeft_heq _ _ _).trans (mpRight_heq _ _ _)
    refine (mpLeft_heq _ _ _).trans ((mpRight_heq _ _ _).trans ?_)
    exact (BinaryCell.app_heq M.comp rfl (map_η_naturality_obj K b) HEq.rfl
      (e1.trans (e2.trans (e4.trans (e5.trans e6.symm))))).trans
      ((heq_of_eq (M.id_comp f)).trans ((mpRight_heq _ _ _).trans (mpRight_heq _ _ _).symm))
  comp_assoc h g f := by
    sorry

end Operad

end CategoryTheory
