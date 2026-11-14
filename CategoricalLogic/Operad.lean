/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.LaxMonad

/-!
# Generalized operads for a lax monad on profunctors

A `T`-operad (a `T`-monoid of Cruttwell–Shulman, i.e. a monad in the horizontal Kleisli
bicategory of `T`) on a small category `X` is a profunctor `hom : X ⇸ T X` with an identity
`Square Profunctor.id hom 𝟭 η` and a composition `Square (hom.comp (T hom)) hom 𝟭 μ`, both
squares out of mathlib's composites. The laws are stated elementwise, on representatives
`compMk g f` of the composite.

## Main definitions

* `Operad M X`, with the derived `Operad.unit a` (the identity operation on `a`) and
  `Operad.mul g f` (the composite of `g` with the family `f`).
* `Operad.Hom`, `Operad.Hom.id`, `Operad.Hom.comp`, and the category of `T`-operads.
-/

@[expose] public section

namespace CategoryTheory.Lax

universe u

open Profunctor

variable {T : Type u → Type u} [CatFamily T] (M : LaxMonad T)

/-- A `T`-operad on `X`: operations `hom.app a b` with output `a : X` and arity `b : T X`,
identities and a composition. -/
structure Operad (X : Type u) [SmallCategory X] where
  /-- The operations. -/
  hom : Profunctor.{u} X (T X)
  /-- The identities, as a nullary cell. -/
  ident : Square Profunctor.id hom (𝟭 X) (M.η X)
  /-- The composition, as a square out of the composite `hom ⊙ T hom`. -/
  comp : Square (hom.comp (M.mapProf hom)) hom (𝟭 X) (M.μ X)
  /-- The identity, composed with an operation `f` seen as a family through `η`, is `f`. -/
  ident_comp {a : X} {b : T X} (f : hom.app a b) :
    comp.app (compMk (ident.app (𝟙 a)) ((M.ηCell hom).app f)) =
      hom.mpRight f (Functor.congr_obj (M.left_unit X) b)
  /-- An operation `f` composed with the family of identities is `f`. -/
  comp_ident {a : X} {b : T X} (f : hom.app a b) :
    comp.app (compMk f ((M.mapProf hom).mpLeft (Functor.congr_obj (M.map_id X) b)
        ((M.mapSquare ident).app ((M.unit X).app (𝟙 b))))) =
      hom.mpRight f (Functor.congr_obj (M.right_unit X) b)
  /-- Composition is associative. -/
  comp_assoc {a : X} {b : T X} {c : T (T X)} {d : T (T (T X))} (h : hom.app a b)
      (g : (M.mapProf hom).app b c) (f : (M.mapProf (M.mapProf hom)).app c d) :
    comp.app (compMk (comp.app (compMk h g)) ((M.μCell hom).app f)) =
      hom.mpRight (comp.app (compMk h ((M.mapProf hom).mpLeft
          (Functor.congr_obj (M.map_id X) b)
          ((M.mapSquare comp).app ((M.lax hom (M.mapProf hom)).app (compMk g f))))))
        (Functor.congr_obj (M.assoc X) d).symm

namespace Operad

variable {M} {X Y Z : Type u} [SmallCategory X] [SmallCategory Y] [SmallCategory Z]

/-- The composite of an operation `g` with a family `f` of operations. -/
abbrev mul (O : Operad M X) {a : X} {b : T X} {c : T (T X)} (g : O.hom.app a b)
    (f : (M.mapProf O.hom).app b c) : O.hom.app a ((M.μ X).obj c) :=
  O.comp.app (compMk g f)

/-- The identity operation on `a`. -/
abbrev unit (O : Operad M X) (a : X) : O.hom.app a ((M.η X).obj a) := O.ident.app (𝟙 a)

/-- A morphism of `T`-operads: a functor together with a square between the profunctors of
operations, preserving identities and composition. -/
structure Hom (A : Operad M X) (B : Operad M Y) where
  /-- The action on objects. -/
  functor : X ⥤ Y
  /-- The action on operations. -/
  map : Square A.hom B.hom functor (M.map functor)
  map_unit (a : X) :
    map.app (A.unit a) =
      B.hom.mpRight (B.unit (functor.obj a)) (Functor.congr_obj (M.η_naturality functor) a).symm
  map_mul {a : X} {b : T X} {c : T (T X)} (g : A.hom.app a b) (f : (M.mapProf A.hom).app b c) :
    map.app (A.mul g f) =
      B.hom.mpRight (B.mul (map.app g) ((M.mapSquare map).app f))
        (Functor.congr_obj (M.μ_naturality functor) c).symm

namespace Hom

/-- The identity morphism of operads. -/
def id (A : Operad M X) : Hom A A where
  functor := 𝟭 X
  map := (Square.id A.hom).cast rfl (M.map_id X).symm
  map_unit a := eq_of_heq ((Square.cast_app_heq _ _ _ _).trans (mpRight_heq _ _ _).symm)
  map_mul g f := by
    refine eq_of_heq ((Square.cast_app_heq _ _ _ _).trans (HEq.symm ((mpRight_heq _ _ _).trans ?_)))
    refine Square.app_compMk_congr A.comp (Functor.congr_obj (M.map_id X) _)
      (Functor.congr_obj ((congrArg M.map (M.map_id X)).trans (M.map_id (T X))) _)
      (Square.cast_app_heq _ _ _ _) ?_
    exact (M.mapSquare_cast_app_heq _ _ _ f).trans (M.mapSquare_id_app_heq _ f)

theorem id_map_app_heq (A : Operad M X) {a : X} {b : T X} (f : A.hom.app a b) :
    (Hom.id A).map.app f ≍ f :=
  Square.cast_app_heq (Square.id A.hom) rfl (M.map_id X).symm f

variable {A : Operad M X} {B : Operad M Y} {C : Operad M Z}

/-- The composition of morphisms of operads. -/
def comp (φ : Hom A B) (ψ : Hom B C) : Hom A C where
  functor := φ.functor ⋙ ψ.functor
  map := (φ.map.vComp ψ.map).cast rfl (M.map_comp φ.functor ψ.functor).symm
  map_unit a := by
    refine eq_of_heq ((Square.cast_app_heq _ _ _ _).trans ?_)
    refine HEq.trans ?_ (mpRight_heq _ _ _).symm
    rw [Square.vComp_app, φ.map_unit]
    refine (Square.app_congr_heq ψ.map (Functor.congr_obj (M.η_naturality φ.functor) a).symm
      (mpRight_heq _ _ _)).trans ?_
    rw [ψ.map_unit]
    exact mpRight_heq _ _ _
  map_mul g f := by
    have hL : (φ.map.vComp ψ.map).app (A.mul g f) ≍
        C.mul (ψ.map.app (φ.map.app g)) ((M.mapSquare ψ.map).app ((M.mapSquare φ.map).app f)) := by
      rw [Square.vComp_app, φ.map_mul]
      refine (Square.app_congr_heq ψ.map (Functor.congr_obj (M.μ_naturality φ.functor) _).symm
        (mpRight_heq _ _ _)).trans ?_
      rw [ψ.map_mul]
      exact mpRight_heq _ _ _
    refine eq_of_heq ((Square.cast_app_heq _ _ _ _).trans
      (hL.trans (HEq.symm ((mpRight_heq _ _ _).trans ?_))))
    refine Square.app_compMk_congr C.comp (Functor.congr_obj (M.map_comp _ _) _)
      (Functor.congr_obj ((congrArg M.map (M.map_comp φ.functor ψ.functor)).trans
        (M.map_comp _ _)) _) (Square.cast_app_heq _ _ _ _) ?_
    exact (M.mapSquare_cast_app_heq _ _ _ f).trans (M.mapSquare_vComp_app_heq _ _ f)

theorem comp_map_app_heq (φ : Hom A B) (ψ : Hom B C) {a : X} {b : T X} (f : A.hom.app a b) :
    (φ.comp ψ).map.app f ≍ ψ.map.app (φ.map.app f) :=
  Square.cast_app_heq (φ.map.vComp ψ.map) rfl (M.map_comp φ.functor ψ.functor).symm f

theorem ext {φ ψ : Hom A B} (h : φ.functor = ψ.functor)
    (h' : ∀ {a : X} {b : T X} (f : A.hom.app a b), φ.map.app f ≍ ψ.map.app f) : φ = ψ := by
  obtain ⟨F, s, _, _⟩ := φ
  obtain ⟨G, t, _, _⟩ := ψ
  subst h
  have : s = t := Square.ext fun f => eq_of_heq (h' f)
  subst this
  rfl

end Hom

end Operad

/-- The category of `T`-operads, over varying small categories of objects. -/
structure OperadCat where
  /-- The category of objects. -/
  X : Type u
  [cat : SmallCategory X]
  /-- The operad. -/
  O : Operad M X

attribute [instance] OperadCat.cat

variable {M}

instance : Category (OperadCat M) where
  Hom A B := Operad.Hom A.O B.O
  id A := Operad.Hom.id A.O
  comp φ ψ := Operad.Hom.comp φ ψ
  id_comp {A _} φ := Operad.Hom.ext rfl fun f =>
    (Operad.Hom.comp_map_app_heq _ φ f).trans
      (Square.app_congr_heq φ.map (Functor.congr_obj (M.map_id A.X) _)
        (Operad.Hom.id_map_app_heq A.O f))
  comp_id φ := Operad.Hom.ext rfl fun f =>
    (Operad.Hom.comp_map_app_heq φ _ f).trans (Operad.Hom.id_map_app_heq _ _)
  assoc φ ψ χ := Operad.Hom.ext rfl fun f =>
    ((Operad.Hom.comp_map_app_heq _ χ f).trans
      (Square.app_congr_heq χ.map (Functor.congr_obj (M.map_comp φ.functor ψ.functor) _)
        (Operad.Hom.comp_map_app_heq φ ψ f))).trans
      ((Operad.Hom.comp_map_app_heq φ _ f).trans (Operad.Hom.comp_map_app_heq ψ χ _)).symm

end CategoryTheory.Lax
