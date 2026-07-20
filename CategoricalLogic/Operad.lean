/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Category.Cat
import CategoricalLogic.Profunctor.Basic


/-!
A formalization of operads based on profunctors. We avoid using the bicategory of profunctors
and instead frame things in terms of `Unit` and `BiNatTrans`. This has the benefit
of avoiding the complexities of profunctor composition and gives
a computational interpretation of operads.

References:
* [A unified framework for generalized multicategories](https://arxiv.org/abs/0907.2460)
-/

namespace CategoryTheory

universe u v

abbrev Unit {X : Cat} (h : Profunctor X X) := (a : X) → h.app a a

/-- A natural transformation from a pair of profunctors to a third profunctor. -/
structure BiNatTrans {X Y Z : Cat} (h : Profunctor Y X) (k : Profunctor Z Y) (j : Profunctor Z X) where
  app {x y z} : h.app x y → k.app y z → j.app x z
  /-- The wedge property for `app`. -/
  wedge {x y y' z} (f : h.app x y) (α : y ⟶ y') (g : k.app y' z) :
    app (h.mapR α f) g = app f (k.mapL α g)
  /-- Naturality with respect to acting on the left. -/
  natL {x x' y z} (α : x' ⟶ x) (f : h.app x y) (g : k.app y z) :
    app (h.mapL α f) g = j.mapL α (app f g)
  /-- Naturality with respect to acting on the right. -/
  natR {x y z z'} (f : h.app x y) (g : k.app y z) (α : z ⟶ z') :
    app f (k.mapR α g) = j.mapR α (app f g)

def BiNatTrans.appL {X X' Y Z : Cat} {h : Profunctor Y X'} {k : Profunctor Z Y} {j : Profunctor Z X} {f : X' ⟶ X}
    (α : BiNatTrans h k (j.actLeft f)) (x y z) (s : h.app x y) (t : k.app y z) :
      j.app (f.toFunctor.obj x) z :=
  α.app s t

def BiNatTrans.appR {X Y Z Z' : Cat} (h : Profunctor Y X) {k : Profunctor Z Y} {j : Profunctor Z' X} {f : Z ⟶ Z'}
    (α : BiNatTrans h k (j.actRight f)) {x y z} (s : h.app x y) (t : k.app y z) :
      j.app x (f.toFunctor.obj z) :=
  α.app s t

/-- A functor from `Cat` to `Cat` is a *functor of profunctors* if it suitably maps profunctors
to profunctors in a way that is compatible with the action on functors.
Moreover, we wish to map units to units and binatural transformations to binatural transformations.
Most notably, this typeclass is missing preservation properties for vertical composition of
natural transformations, units and binatural transformations.

This a simplified variant of a *functor of equipments*. -/
class FunctorProf (T : Functor Cat Cat) where
  /-- Mapping action on profunctors and morphisms of profunctors. -/
  mapProf {X Y : Cat} : Profunctor Y X ⥤ Profunctor (T.obj Y) (T.obj X)
  /-- Functoriality with respect to the left action. -/
  mapProf_actLeft {X Y Z : Cat} (f : Z ⟶ X) (p : Profunctor Y X) :
    mapProf.obj (p.actLeft f) = (mapProf.obj p).actLeft (T.map f)
  /-- Functoriality with respect to the right action. -/
  mapProf_actRight {X Y Z : Cat} (p : Profunctor Y X) (f : Z ⟶ Y) :
    mapProf.obj (p.actRight f) = (mapProf.obj p).actRight (T.map f)
  /-- Mapping action on units. -/
  mapUnit {X : Cat} {h : Profunctor X X} : Unit h → Unit (mapProf.obj h)
  /-- Mapping action on binatural transformations. -/
  mapBi {X Y Z : Cat} {h : Profunctor Y X} {k : Profunctor Z Y} {j : Profunctor Z X} :
    BiNatTrans h k j → BiNatTrans (mapProf.obj h) (mapProf.obj k) (mapProf.obj j)

-- Mapping actions for cells

def FunctorProf.mapUnitL (T : Functor Cat Cat) [FunctorProf T] {X Y : Cat} {f : X ⟶ Y} {p : Profunctor X Y}
    (a : Unit (p.actLeft f)) : Unit ((mapProf.obj p).actLeft (T.map f)) :=
  mapProf_actLeft (T := T) f p ▸ (mapUnit (T := T) a)

def FunctorProf.mapUnitR (T : Functor Cat Cat) [FunctorProf T] {X Y : Cat} {p : Profunctor X Y} {f : Y ⟶ X}
    (a : Unit (p.actRight f)) : Unit ((mapProf.obj p).actRight (T.map f)) :=
  mapProf_actRight (T := T) p f ▸ (mapUnit (T := T) a)

def FunctorProf.mapBiL (T : Functor Cat Cat) [FunctorProf T] {X Y Z W : Cat} {f : X ⟶ Y}
    {p : Profunctor Z X} {q : Profunctor W Z} {r : Profunctor W Y}
    (a : BiNatTrans p q (r.actLeft f)) :
    BiNatTrans (mapProf.obj p) (mapProf.obj q) ((mapProf.obj r).actLeft (T.map f)) :=
  mapProf_actLeft (T := T) _ _ ▸ mapBi a

def FunctorProf.mapBiR (T : Functor Cat Cat) [FunctorProf T] {X Y Z W : Cat}
    (p : Profunctor Y X) (q : Profunctor Z Y) (r : Profunctor W X) (g : Z ⟶ W) (a : BiNatTrans p q (r.actRight g)) :
    BiNatTrans (mapProf.obj p) (mapProf.obj q) ((mapProf.obj r).actRight (T.map g)) :=
  mapProf_actRight (T := T) _ _ ▸ mapBi a


/-- A monad carrying a structure of a *functor of profunctors* is a *monad of profunctors*
if the corresponding naturality squares for profunctors can be filled by 2-cells.

We omit the corresponding monad laws for those cells. -/
class MonadProf (T : Monad Cat) extends FunctorProf T where
  η_prof {X Y : Cat} (h : Profunctor Y X) : h ⟶
    Profunctor.actLeft (T.η.app X) (Profunctor.actRight (mapProf.obj h) (T.η.app Y))
  μ_prof {X Y : Cat} (h : Profunctor Y X) : mapProf.obj (mapProf.obj h) ⟶
    Profunctor.actLeft (T.μ.app X) (Profunctor.actRight (mapProf.obj h) (T.μ.app Y))

lemma left_unit_obj {T : Monad Cat} {X} (a : T.obj X) :
    (T.μ.app _).toFunctor.obj ((T.η.app _).toFunctor.obj a) = a := by
  rw [← CategoryTheory.Cat.Hom.comp_obj]
  exact congrArg (fun f : T.obj X ⟶ T.obj X ↦ f.toFunctor.obj a) (T.left_unit X)

lemma right_unit_obj {T : Monad Cat} {X} (a : T.obj X) :
    (T.μ.app _).toFunctor.obj ((T.map (T.η.app _)).toFunctor.obj a) = a := by
  rw [← CategoryTheory.Cat.Hom.comp_obj]
  exact congrArg (fun f : T.obj X ⟶ T.obj X ↦ f.toFunctor.obj a) (T.right_unit X)

lemma assoc_obj {T : Monad Cat} {X} (a : T.obj (T.obj (T.obj X))) :
    (T.μ.app X).toFunctor.obj ((T.μ.app (T.obj X)).toFunctor.obj a)
      = (T.μ.app X).toFunctor.obj ((T.map (T.μ.app X)).toFunctor.obj a) := by
  rw [← CategoryTheory.Cat.Hom.comp_obj, ← CategoryTheory.Cat.Hom.comp_obj]
  exact congrArg (fun f : T.obj (T.obj (T.obj X)) ⟶ T.obj X ↦ f.toFunctor.obj a) (T.assoc X).symm

variable (T : Monad Cat) [MonadProf T]

open Profunctor FunctorProf MonadProf

structure Operad (X : Cat) where
  hom : Profunctor X (T.obj X)
  id : Unit (actLeft (T.η.app X) hom)
  comp : BiNatTrans (mapProf.obj hom) hom (actLeft (T.μ.app X) hom)
  comp_id {a : X} {b : T.obj X} (f : hom.app b a) :
    comp.app (homAppL (η_prof hom) _ _ f) (id a) = hom.mpLeft (left_unit_obj b) f
  id_comp {a : X} (b : T.obj X) (f : hom.app b a) :
    comp.app ((mapUnitL T id) b) f = hom.mpLeft (right_unit_obj b) f
  comp_assoc  {a : X} {b : T.obj X} {c : T.obj (T.obj X)} {d : T.obj (T.obj (T.obj X))}
      (f : (mapProf.obj (mapProf.obj hom)).app d c) (g : (mapProf.obj hom).app c b)
      (h : hom.app b a) :
    assoc_obj _ ▸
      comp.appL ((T.μ.app _).toFunctor.obj d) ((T.μ.app _).toFunctor.obj c) a
        (homApp (μ_prof hom) d c f)
        (comp.app g h)
      = comp.appL ((T.map (T.μ.app _)).toFunctor.obj d) _ a ((mapBiL T comp).app f g) h


end CategoryTheory
