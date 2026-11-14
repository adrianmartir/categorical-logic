/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import CategoricalLogic.Designs.Kleisli.Cells

/-!
# Operads as monoids in a Kleisli category of profunctors

For a monad `T` on `Cat` acting on profunctors, a *Kleisli profunctor* `X ⇸ Y` is a profunctor
`P : Profunctor X (T Y)`. They compose by

  `P ⊙ₖ Q := (P.comp (T Q)).comp μ_*`

where `μ_* = (μ Y).toProfunctor` is the companion of the multiplication (composing with it is
pushing forward along `μ`), with identity `η_* = (η X).toProfunctor`. A `T`-operad on `X` is a
monoid for this composition on the Kleisli profunctors `X ⇸ X`: a profunctor `hom : X ⇸ T X`,
a unit `η_* ⟶ hom`, a multiplication `hom ⊙ₖ hom ⟶ hom`, and the three monoid laws, stated with
explicit (forward) unitor and associator morphisms.

## The structure on `T`

The Kleisli composition only needs the action of `T` on profunctors and their morphisms
(`KleisliProf.mapProf`, a functor). The unitors and the associator need, in addition, one
direction of each structure 2-cell of a pseudomonad on the bicategory of profunctors whose
underlying monad on `Cat` is `T` (Fiore–Gambino–Hyland–Winskel):

* `mapComp`: the laxator `T P ⊙ T Q ⟶ T (P ⊙ Q)` (associator);
* `mapCompanion`: `T` commutes with companions, `T (F_*) ≅ (T F)_*` (both unitors use one
  direction, the associator the other);
* `ηComm`: the (inverse of the) pseudonaturality of `η`, `η_* ⊙ T P ⟶ P ⊙ η_*` (left unitor),
  where `η_* ⊙ T P` is written as the restriction `T P (η -, -)` (co-Yoneda);
* `μComm`: the (inverse of the) pseudonaturality of `μ`, `μ_* ⊙ T P ⟶ T T P ⊙ μ_*`
  (associator), with `μ_* ⊙ T P` written as `T P (μ -, -)`.

No law about these cells is needed to *state* the operad axioms; the coherence laws of a
pseudomonad are only needed to prove that `⊙ₖ` is a (bi)category, which is not done here.

## Main definitions

* `KleisliProf T`: the structure on `T`.
* `KleisliProf.kcomp`, `KleisliProf.kid`, `kwhiskerLeft`, `kwhiskerRight`, `kleftUnitor`,
  `krightUnitor`, `kassoc`.
* `KOperad T X`: monoids on `X`.
* `KOperad.Hom`: identity-on-objects morphisms of operads, with identities and composition.
-/

@[expose] public section

namespace CategoryTheory

universe u

open Profunctor Opposite

/-- The structure on a monad `T` on `Cat` needed to define its Kleisli composition of
profunctors, together with its unitors and associator. These are the components of a
pseudomonad on profunctors extending `T`, each taken in the one direction that is used. -/
class KleisliProf (T : Monad Cat.{u, u}) where
  /-- The action on profunctors and their morphisms. -/
  mapProf {C D : Cat.{u, u}} : Profunctor.{u} C D ⥤ Profunctor.{u} (T.obj C) (T.obj D)
  /-- The laxator. -/
  mapComp {C D E : Cat.{u, u}} (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) :
    (mapProf.obj P).comp (mapProf.obj Q) ⟶ mapProf.obj (P.comp Q)
  /-- `T` commutes with companions of functors. -/
  mapCompanion {C D : Cat.{u, u}} (F : C ⟶ D) :
    mapProf.obj F.toFunctor.toProfunctor ≅ (T.map F).toFunctor.toProfunctor
  /-- The pseudonaturality of `η`, in the direction used by the left unitor. -/
  ηComm {C D : Cat.{u, u}} (P : Profunctor.{u} C D) :
    (mapProf.obj P).whiskerLeft₂ (T.η.app C).toFunctor (𝟭 _) ⟶
      P.comp (T.η.app D).toFunctor.toProfunctor
  /-- The pseudonaturality of `μ`, in the direction used by the associator. -/
  μComm {C D : Cat.{u, u}} (P : Profunctor.{u} C D) :
    (mapProf.obj P).whiskerLeft₂ (T.μ.app C).toFunctor (𝟭 _) ⟶
      (mapProf.obj (mapProf.obj P)).comp (T.μ.app D).toFunctor.toProfunctor

namespace KleisliProf

variable {T : Monad Cat.{u, u}} [KleisliProf.{u} T] {W X Y Z : Cat.{u, u}}

/-- The companion of the unit, the identity Kleisli profunctor. -/
abbrev ηP (T : Monad Cat.{u, u}) (X : Cat.{u, u}) : Profunctor.{u} X (T.obj X) :=
  (T.η.app X).toFunctor.toProfunctor

/-- The companion of the multiplication. -/
abbrev μP (T : Monad Cat.{u, u}) (X : Cat.{u, u}) : Profunctor.{u} (T.obj (T.obj X)) (T.obj X) :=
  (T.μ.app X).toFunctor.toProfunctor

/-- The identity Kleisli profunctor. -/
abbrev kid (T : Monad Cat.{u, u}) (X : Cat.{u, u}) : Profunctor.{u} X (T.obj X) := ηP T X

/-- Kleisli composition of profunctors. -/
abbrev kcomp (P : Profunctor.{u} X (T.obj Y)) (Q : Profunctor.{u} Y (T.obj Z)) :
    Profunctor.{u} X (T.obj Z) :=
  (P.comp (mapProf.obj Q)).comp (μP T Z)

@[inherit_doc] scoped infixr:80 " ⊙ₖ " => kcomp

/-- Left whiskering for the Kleisli composition. -/
def kwhiskerLeft (P : Profunctor.{u} X (T.obj Y)) {Q Q' : Profunctor.{u} Y (T.obj Z)}
    (g : Q ⟶ Q') : P ⊙ₖ Q ⟶ P ⊙ₖ Q' :=
  Profunctor.whiskerRight (μP T Z) (P.whiskerLeft (mapProf.map g))

/-- Right whiskering for the Kleisli composition. -/
def kwhiskerRight {P P' : Profunctor.{u} X (T.obj Y)} (f : P ⟶ P')
    (Q : Profunctor.{u} Y (T.obj Z)) : P ⊙ₖ Q ⟶ P' ⊙ₖ Q :=
  Profunctor.whiskerRight (μP T Z) (Profunctor.whiskerRight (mapProf.obj Q) f)

/-- The left unit law of `T`, as a transformation of functors. -/
def leftUnitHom (Y : Cat.{u, u}) :
    (T.η.app (T.obj Y)).toFunctor ⋙ (T.μ.app Y).toFunctor ⟶ 𝟭 _ :=
  eqToHom (congrArg Cat.Hom.toFunctor (T.left_unit Y))

/-- The right unit law of `T`, as a transformation of functors. -/
def rightUnitHom (Y : Cat.{u, u}) :
    (T.map (T.η.app Y)).toFunctor ⋙ (T.μ.app Y).toFunctor ⟶ 𝟭 _ :=
  eqToHom (congrArg Cat.Hom.toFunctor (T.right_unit Y))

/-- The associativity law of `T`, as a transformation of functors. -/
def assocHom (Z : Cat.{u, u}) :
    (T.μ.app (T.obj Z)).toFunctor ⋙ (T.μ.app Z).toFunctor ⟶
      (T.map (T.μ.app Z)).toFunctor ⋙ (T.μ.app Z).toFunctor :=
  eqToHom (congrArg Cat.Hom.toFunctor (T.assoc Z)).symm

/-- The left unitor of the Kleisli composition (forward direction). -/
def kleftUnitor (P : Profunctor.{u} X (T.obj Y)) : kid T X ⊙ₖ P ⟶ P :=
  Profunctor.whiskerRight (μP T Y) (companionRestrict (T.η.app X).toFunctor (mapProf.obj P) ≫
      ηComm P) ≫
    (associator P (ηP T (T.obj Y)) (μP T Y)).hom ≫
    P.whiskerLeft (companionCounit (leftUnitHom Y)) ≫
    P.rightUnitor.hom

/-- The right unitor of the Kleisli composition (forward direction). -/
def krightUnitor (P : Profunctor.{u} X (T.obj Y)) : P ⊙ₖ kid T Y ⟶ P :=
  Profunctor.whiskerRight (μP T Y) (P.whiskerLeft (mapCompanion (T.η.app Y)).hom) ≫
    (associator P (T.map (T.η.app Y)).toFunctor.toProfunctor (μP T Y)).hom ≫
    P.whiskerLeft (companionCounit (rightUnitHom Y)) ≫
    P.rightUnitor.hom

/-- The comparison `μ_* ⊙ μ_* ⟶ T(μ_*) ⊙ μ_*` used by the associator: both sides are companions
of the two sides of the associativity law of `T`. -/
def μμ (Z : Cat.{u, u}) :
    (μP T (T.obj Z)).comp (μP T Z) ⟶ (mapProf.obj (μP T Z)).comp (μP T Z) :=
  companionComp (𝟙 ((T.μ.app (T.obj Z)).toFunctor ⋙ (T.μ.app Z).toFunctor)) ≫
    companionDecomp (assocHom Z) ≫
    Profunctor.whiskerRight (μP T Z) (mapCompanion (T.μ.app Z)).inv

/-- The associator of the Kleisli composition (forward direction). -/
def kassoc (P : Profunctor.{u} W (T.obj X)) (Q : Profunctor.{u} X (T.obj Y))
    (R : Profunctor.{u} Y (T.obj Z)) : (P ⊙ₖ Q) ⊙ₖ R ⟶ P ⊙ₖ (Q ⊙ₖ R) :=
  let A := P.comp (mapProf.obj Q)
  let TTR := mapProf.obj (mapProf.obj R)
  let TμZ := mapProf.obj (μP T Z)
  Profunctor.whiskerRight (μP T Z) (associator A (μP T Y) (mapProf.obj R)).hom ≫
    Profunctor.whiskerRight (μP T Z)
      (A.whiskerLeft (companionRestrict (T.μ.app Y).toFunctor (mapProf.obj R) ≫ μComm R)) ≫
    (associator A (TTR.comp (μP T (T.obj Z))) (μP T Z)).hom ≫
    A.whiskerLeft (associator TTR (μP T (T.obj Z)) (μP T Z)).hom ≫
    A.whiskerLeft (TTR.whiskerLeft (μμ Z)) ≫
    A.whiskerLeft (associator TTR TμZ (μP T Z)).inv ≫
    A.whiskerLeft (Profunctor.whiskerRight (μP T Z) (mapComp (mapProf.obj R) (μP T Z))) ≫
    (associator A (mapProf.obj ((mapProf.obj R).comp (μP T Z))) (μP T Z)).inv ≫
    Profunctor.whiskerRight (μP T Z)
      (associator P (mapProf.obj Q) (mapProf.obj ((mapProf.obj R).comp (μP T Z)))).hom ≫
    Profunctor.whiskerRight (μP T Z) (P.whiskerLeft (mapComp Q _)) ≫
    Profunctor.whiskerRight (μP T Z)
      (P.whiskerLeft (mapProf.map (associator Q (mapProf.obj R) (μP T Z)).inv))

end KleisliProf

open KleisliProf

/-- A `T`-operad on `X`: a monoid on `X` for the Kleisli composition of profunctors. The
elements of `hom.app a b` are the operations with output `a` and arity `b : T X`. -/
structure KOperad (T : Monad Cat.{u, u}) [KleisliProf.{u} T] (X : Cat.{u, u}) where
  /-- The operations. -/
  hom : Profunctor.{u} X (T.obj X)
  /-- The identities. -/
  unit : kid T X ⟶ hom
  /-- The composition. -/
  mul : hom ⊙ₖ hom ⟶ hom
  one_mul : kwhiskerRight unit hom ≫ mul = kleftUnitor hom
  mul_one : kwhiskerLeft hom unit ≫ mul = krightUnitor hom
  mul_assoc : kwhiskerRight mul hom ≫ mul = kassoc hom hom hom ≫ kwhiskerLeft hom mul ≫ mul

namespace KleisliProf

variable {T : Monad Cat.{u, u}} [KleisliProf.{u} T] {X Y Z : Cat.{u, u}}

@[simp] theorem kwhiskerLeft_id (P : Profunctor.{u} X (T.obj Y)) (Q : Profunctor.{u} Y (T.obj Z)) :
    kwhiskerLeft P (𝟙 Q) = 𝟙 _ := by
  simp [kwhiskerLeft]

@[simp] theorem kwhiskerLeft_comp (P : Profunctor.{u} X (T.obj Y))
    {Q Q' Q'' : Profunctor.{u} Y (T.obj Z)} (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    kwhiskerLeft P (g ≫ g') = kwhiskerLeft P g ≫ kwhiskerLeft P g' := by
  simp [kwhiskerLeft]

@[simp] theorem kwhiskerRight_id (P : Profunctor.{u} X (T.obj Y))
    (Q : Profunctor.{u} Y (T.obj Z)) : kwhiskerRight (𝟙 P) Q = 𝟙 _ := by
  simp [kwhiskerRight]

@[simp] theorem kwhiskerRight_comp {P P' P'' : Profunctor.{u} X (T.obj Y)} (f : P ⟶ P')
    (f' : P' ⟶ P'') (Q : Profunctor.{u} Y (T.obj Z)) :
    kwhiskerRight (f ≫ f') Q = kwhiskerRight f Q ≫ kwhiskerRight f' Q := by
  simp [kwhiskerRight]

@[reassoc]
theorem kwhisker_exchange {P P' : Profunctor.{u} X (T.obj Y)} {Q Q' : Profunctor.{u} Y (T.obj Z)}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    kwhiskerLeft P g ≫ kwhiskerRight f Q' = kwhiskerRight f Q ≫ kwhiskerLeft P' g := by
  simp only [kwhiskerLeft, kwhiskerRight, ← Profunctor.comp_whiskerRight,
    Profunctor.whisker_exchange]

end KleisliProf

namespace KOperad

variable {T : Monad Cat.{u, u}} [KleisliProf.{u} T] {X : Cat.{u, u}}

/-- A morphism of `T`-operads on the same object category `X` (identity on objects): a morphism
of monoids for the Kleisli composition. -/
@[ext]
structure Hom (M N : KOperad T X) where
  /-- The action on operations. -/
  map : M.hom ⟶ N.hom
  map_unit : M.unit ≫ map = N.unit
  map_mul : M.mul ≫ map = kwhiskerRight map M.hom ≫ kwhiskerLeft N.hom map ≫ N.mul

namespace Hom

/-- The identity morphism. -/
@[simps]
def id (M : KOperad T X) : Hom M M where
  map := 𝟙 _
  map_unit := Category.comp_id _
  map_mul := by simp

/-- Composition of morphisms. -/
@[simps]
def comp {L M N : KOperad T X} (φ : Hom L M) (ψ : Hom M N) : Hom L N where
  map := φ.map ≫ ψ.map
  map_unit := by rw [← Category.assoc, φ.map_unit, ψ.map_unit]
  map_mul := by
    rw [← Category.assoc, φ.map_mul]
    simp only [Category.assoc, ψ.map_mul, kwhiskerRight_comp, kwhiskerLeft_comp,
      kwhisker_exchange_assoc]

end Hom

instance : Category (KOperad T X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

end KOperad

end CategoryTheory
