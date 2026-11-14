/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import Mathlib.CategoryTheory.Profunctor.Bicategory

/-!
# Restriction of profunctors, natively

The "Native" design has no cell structures: a cell with unary source `P`, target `Q` and
vertical boundary `F, G` is a morphism `P ⟶ Q.whiskerLeft₂ F G` in the functor category
`Profunctor C D`, a binary cell is a morphism `P.comp Q ⟶ R.whiskerLeft₂ F G` and a nullary
cell is a morphism `Profunctor.id ⟶ Q.whiskerLeft₂ F G`.

This file provides the only structure on top of mathlib that this needs:

* `Profunctor.restrict F G`: restriction `P ↦ P.whiskerLeft₂ F G`, as a functor between
  profunctor categories (so that it acts on morphisms, i.e. on cells).
* `Profunctor.compRestrict`: the canonical comparison
  `(P.whiskerLeft₂ F K).comp (Q.whiskerLeft₂ K G) ⟶ (P.comp Q).whiskerLeft₂ F G`, which is how
  two cells with a common middle boundary `K` are placed side by side.
* `Profunctor.idRestrict K`: the canonical comparison `Profunctor.id ⟶ Profunctor.id.whiskerLeft₂
  K K` (the action of `K` on morphisms), how a nullary cell is reindexed along `K`.

Restriction along identities and along composites is definitional:
`P.whiskerLeft₂ (𝟭 _) (𝟭 _) = P` and
`(P.whiskerLeft₂ F G).whiskerLeft₂ F' G' = P.whiskerLeft₂ (F' ⋙ F) (G' ⋙ G)` hold by `rfl`.
-/

@[expose] public section

namespace CategoryTheory.Profunctor

universe w u

open Opposite Limits TypeCat

section Restrict

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

/-- Restriction of profunctors along a pair of functors, as a functor between the categories of
profunctors: it sends `P` to `P.whiskerLeft₂ F G`. -/
abbrev restrict (F : A ⥤ C) (G : B ⥤ D) : Profunctor.{w} C D ⥤ Profunctor.{w} A B :=
  ((Functor.whiskeringLeft₂ _).obj F).obj G.op

@[simp] theorem restrict_obj (F : A ⥤ C) (G : B ⥤ D) (P : Profunctor.{w} C D) :
    (restrict F G).obj P = P.whiskerLeft₂ F G := rfl

theorem whiskerLeft₂_id (P : Profunctor.{w} C D) : P.whiskerLeft₂ (𝟭 C) (𝟭 D) = P := rfl

theorem whiskerLeft₂_whiskerLeft₂ {A' B' : Type*} [Category* A'] [Category* B']
    (P : Profunctor.{w} C D) (F : A ⥤ C) (G : B ⥤ D) (F' : A' ⥤ A) (G' : B' ⥤ B) :
    (P.whiskerLeft₂ F G).whiskerLeft₂ F' G' = P.whiskerLeft₂ (F' ⋙ F) (G' ⋙ G) := rfl

/-- Restriction along equal functors gives equal profunctors; use it with `eqToHom`. -/
theorem whiskerLeft₂_congr (P : Profunctor.{w} C D) {F F' : A ⥤ C} {G G' : B ⥤ D}
    (hF : F = F') (hG : G = G') : P.whiskerLeft₂ F G = P.whiskerLeft₂ F' G' :=
  congrArg₂ P.whiskerLeft₂ hF hG

/-- `eqToHom` between profunctors acts on elements by `cast`. -/
theorem eqToHom_app_app {P Q : Profunctor.{w} C D} (h : P = Q) (c : C) (d : Dᵒᵖ)
    (x : (P.obj c).obj d) :
    ((eqToHom h).app c).app d x =
      cast (congrArg (fun P : Profunctor.{w} C D ↦ (P.obj c).obj d) h) x := by
  subst h
  rfl

/-- `eqToHom` between profunctors acts on elements by a transport. -/
theorem eqToHom_app_app_heq {P Q : Profunctor.{w} C D} (h : P = Q) (c : C) (d : Dᵒᵖ)
    (x : (P.obj c).obj d) : ((eqToHom h).app c).app d x ≍ x := by
  subst h
  rfl

/-- Restriction along identities is the identity functor (definitionally). -/
theorem restrict_id : restrict.{w} (𝟭 C) (𝟭 D) = 𝟭 _ := rfl

/-- Restriction along composites is iterated restriction (definitionally). -/
theorem restrict_comp {A' B' : Type*} [Category* A'] [Category* B']
    (F : A ⥤ C) (G : B ⥤ D) (F' : A' ⥤ A) (G' : B' ⥤ B) :
    restrict.{w} (F' ⋙ F) (G' ⋙ G) = restrict F G ⋙ restrict F' G' := rfl

end Restrict

section CompRestrict

variable {A B C D E E' : Type u} [Category.{u} A] [Category.{u} B] [Category.{u} C]
  [Category.{u} D] [Category.{u} E] [Category.{u} E']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Two restrictions with a common middle functor `K` compose to the restriction of the
composite: `(P(F, K)) ⊙ (Q(K, G)) ⟶ (P ⊙ Q)(F, G)`. On representatives it is the identity, and
it reindexes the middle object along `K`. -/
def compRestrict (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) (F : A ⥤ C) (K : B ⥤ D)
    (G : E' ⥤ E) :
    (P.whiskerLeft₂ F K).comp (Q.whiskerLeft₂ K G) ⟶ (P.comp Q).whiskerLeft₂ F G where
  app a :=
    { app e := ↾Quot.lift (fun ⟨b, p, q⟩ ↦ Quot.mk _ ⟨K.obj b, p, q⟩) (by
        rintro _ _ ⟨f, p, q⟩
        apply Quot.sound
        rw [Types.coendRel_iff]
        exact ⟨K.map f, (p, q), rfl, rfl⟩)
      naturality _ _ g := by
        ext ⟨_, _, _⟩
        simp [Types.chosenCoend_def, chosenCoend.map_apply] }
  naturality _ _ f := by
    ext _ ⟨_, _, _⟩
    simp [Types.chosenCoend_def, chosenCoend.map_apply]

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Types.chosenCoend_def in
@[simp]
theorem compRestrict_mk (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) (F : A ⥤ C)
    (K : B ⥤ D) (G : E' ⥤ E) (a : A) (e : E'ᵒᵖ) (b : B)
    (p : (P.obj (F.obj a)).obj (op (K.obj b))) (q : (Q.obj (K.obj b)).obj (op (G.obj e.unop))) :
    dsimp% ((compRestrict P Q F K G).app a).app e (Quot.mk _ ⟨b, p, q⟩) =
      Quot.mk _ ⟨K.obj b, p, q⟩ :=
  rfl

variable {A₀ B₀ E₀ : Type u} [Category.{u} A₀] [Category.{u} B₀] [Category.{u} E₀]

/-- Horizontal composition of two cells `α : P ⇒ P'(F, K)` and `β : Q ⇒ Q'(K, G)` sharing the
middle boundary `K`: the cell `P ⊙ Q ⇒ (P' ⊙ Q')(F, G)`. This is a derived operation (mathlib's
whiskerings followed by `compRestrict`), not a new structure. -/
def hComp {P : Profunctor.{u} A₀ B₀} {Q : Profunctor.{u} B₀ E₀} {P' : Profunctor.{u} C D}
    {Q' : Profunctor.{u} D E} {F : A₀ ⥤ C} {K : B₀ ⥤ D} {G : E₀ ⥤ E}
    (α : P ⟶ P'.whiskerLeft₂ F K) (β : Q ⟶ Q'.whiskerLeft₂ K G) :
    P.comp Q ⟶ (P'.comp Q').whiskerLeft₂ F G :=
  Profunctor.whiskerRight Q α ≫ (P'.whiskerLeft₂ F K).whiskerLeft β ≫ compRestrict P' Q' F K G

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Types.chosenCoend_def in
@[simp]
theorem hComp_mk {P : Profunctor.{u} A₀ B₀} {Q : Profunctor.{u} B₀ E₀} {P' : Profunctor.{u} C D}
    {Q' : Profunctor.{u} D E} {F : A₀ ⥤ C} {K : B₀ ⥤ D} {G : E₀ ⥤ E}
    (α : P ⟶ P'.whiskerLeft₂ F K) (β : Q ⟶ Q'.whiskerLeft₂ K G) (a : A₀) (e : E₀ᵒᵖ) (b : B₀)
    (p : (P.obj a).obj (op b)) (q : (Q.obj b).obj e) :
    dsimp% ((hComp α β).app a).app e (Quot.mk _ ⟨b, p, q⟩) =
      Quot.mk _ ⟨K.obj b, (α.app a).app (op b) p, (β.app b).app e q⟩ :=
  rfl

/-- The covariant action of a composite on a representative. -/
theorem comp_mapL_mk (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) {c c' : C} (f : c ⟶ c')
    (e : Eᵒᵖ) (d : D) (x : (P.obj c).obj (op d)) (y : (Q.obj d).obj e) :
    ((P.comp Q).map f).app e (Quot.mk (Types.coendRel (P.compDiagram Q c e.unop)) ⟨d, x, y⟩) =
      Quot.mk (Types.coendRel (P.compDiagram Q c' e.unop)) ⟨d, (P.map f).app _ x, y⟩ :=
  congrArg (fun z ↦ Quot.mk (Types.coendRel (P.compDiagram Q c' e.unop))
    ⟨d, ((P.map f).app _ x, z)⟩) (by simp)

/-- The contravariant action of a composite on a representative. -/
theorem comp_mapR_mk (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) (c : C) {e e' : Eᵒᵖ}
    (g : e ⟶ e') (d : D) (x : (P.obj c).obj (op d)) (y : (Q.obj d).obj e) :
    ((P.comp Q).obj c).map g (Quot.mk (Types.coendRel (P.compDiagram Q c e.unop)) ⟨d, x, y⟩) =
      Quot.mk (Types.coendRel (P.compDiagram Q c e'.unop)) ⟨d, x, (Q.obj d).map g y⟩ :=
  congrArg (fun z ↦ Quot.mk (Types.coendRel (P.compDiagram Q c e'.unop))
    ⟨d, (z, (Q.obj d).map g y)⟩) (by simp)

theorem compRestrict_id (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) :
    compRestrict P Q (𝟭 C) (𝟭 D) (𝟭 E) = 𝟙 _ := by
  ext _ _ ⟨_, _, _⟩
  rfl

theorem hComp_eqToHom (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) {F₀ F : A ⥤ C}
    {K₀ K : B ⥤ D} {G₀ G : E' ⥤ E} (hF : F₀ = F) (hK : K₀ = K) (hG : G₀ = G) :
    hComp (eqToHom (P.whiskerLeft₂_congr hF hK)) (eqToHom (Q.whiskerLeft₂_congr hK hG)) =
      compRestrict P Q F₀ K₀ G₀ ≫ eqToHom ((P.comp Q).whiskerLeft₂_congr hF hG) := by
  subst hF hK hG
  simp [hComp]

end CompRestrict

section Congr

variable {A B C D : Type u} [Category.{u} A] [Category.{u} B] [Category.{u} C] [Category.{u} D]

theorem eqToHom_restrict_map {P Q : Profunctor.{u} C D} (f : P ⟶ Q) {F F' : A ⥤ C}
    {G G' : B ⥤ D} (hF : F = F') (hG : G = G') :
    eqToHom (P.whiskerLeft₂_congr hF hG) ≫ (restrict F' G').map f =
      (restrict F G).map f ≫ eqToHom (Q.whiskerLeft₂_congr hF hG) := by
  subst hF hG
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end Congr

section IdRestrict

variable {A C : Type u} [Category.{u} A] [Category.{u} C]

/-- The action of a functor on morphisms, as a nullary cell `Profunctor.id ⟶ id(K, K)`. -/
def idRestrict (K : A ⥤ C) :
    (Profunctor.id : Profunctor A A) ⟶ Profunctor.id.whiskerLeft₂ K K where
  app a :=
    { app b := ↾fun f ↦ K.map f
      naturality _ _ f := by ext; exact K.map_comp _ _ }
  naturality _ _ f := by ext; exact K.map_comp _ _

theorem idRestrict_id : idRestrict (𝟭 A) = 𝟙 _ := by
  ext
  rfl

theorem idRestrict_comp {E : Type u} [Category.{u} E] (F : A ⥤ C) (G : C ⥤ E) :
    idRestrict (F ⋙ G) = idRestrict F ≫ (restrict F F).map (idRestrict G) := by
  ext
  rfl

end IdRestrict

end CategoryTheory.Profunctor
