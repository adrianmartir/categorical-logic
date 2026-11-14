/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Profunctor.Comp
public import Mathlib.CategoryTheory.Monad.Basic

/-!
# Lax monads on the double category of profunctors

We describe a monad `T` on the pseudo double category `ℙrof` of small categories, functors and
profunctors (`Profunctor.{u}`, composed with mathlib's `Profunctor.comp`), in the sense of
Fiore–Gambino–Kock (*Monads in double categories*, 2011): a monad in the 2-category of pseudo
double categories, *lax* double functors and vertical transformations.

The vertical part is unbundled: `T : Type u → Type u` with a category structure on each `T C`
(`CatFamily`), and the action on functors and the monad laws are equalities of functors
(`CatFunctor`, `CatMonad`). This avoids the `(F ≫ G).toFunctor` versus `F.toFunctor ⋙ G.toFunctor`
friction of `Monad Cat`: for plain functors `𝟭 ⋙ F` and `F ⋙ 𝟭` are definitionally `F`, so
most laws need no transport, and functor equalities can be `subst`ed.

The only cells are the squares `Profunctor.Square P Q F G`. Cells of higher arity are squares
out of composites: a binary cell is a `Square (P.comp Q) R F G` (`Square.binaryEquiv`), a nullary
cell is a `Square Profunctor.id Q F G` (`Square.nullaryEquiv`).

## Main definitions

* `CatFamily T`, `CatFunctor T`, `CatMonad T`: the vertical part; `CatMonad.toMonad` is the
  corresponding mathlib `Monad Cat`.
* `LaxFunctor T`: a lax double functor `ℙrof → ℙrof`: an action on profunctors and squares,
  a laxator `T P ⊙ T Q ⇒ T (P ⊙ Q)` and a unit comparison `U (T C) ⇒ T (U C)`, natural and
  coherent with mathlib's associator and unitors. `LaxFunctor.mapCov`, `mapBinary` and
  `mapNullary` act on cells whose covariant boundary is the identity, without a transport along
  `map_id`.
* `LaxMonad T`: unit and multiplication cells, which are vertical transformations of lax
  functors (natural in squares, compatible with laxators and unit comparisons) and satisfy the
  monad laws.
-/

@[expose] public section

namespace CategoryTheory.Lax

universe u

open Profunctor

/-- A family of small categories `T C` indexed by small categories `C`. -/
class CatFamily (T : Type u → Type u) where
  /-- The category structure on `T C`. -/
  category (C : Type u) [SmallCategory C] : SmallCategory (T C)

set_option warn.classDefReducibility false in
attribute [instance] CatFamily.category

variable (T : Type u → Type u) [CatFamily T]

/-- A functor on small categories, with its laws as equalities of functors. -/
structure CatFunctor where
  /-- The action on functors. -/
  map {C D : Type u} [SmallCategory C] [SmallCategory D] : (C ⥤ D) → (T C ⥤ T D)
  map_id (C : Type u) [SmallCategory C] : map (𝟭 C) = 𝟭 (T C)
  map_comp {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (F : C ⥤ D) (G : D ⥤ E) : map (F ⋙ G) = map F ⋙ map G

/-- A monad on small categories, with its laws as equalities of functors. -/
structure CatMonad extends CatFunctor T where
  /-- The unit. -/
  η (C : Type u) [SmallCategory C] : C ⥤ T C
  /-- The multiplication. -/
  μ (C : Type u) [SmallCategory C] : T (T C) ⥤ T C
  η_naturality {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) :
    F ⋙ η D = η C ⋙ map F
  μ_naturality {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) :
    map (map F) ⋙ μ D = μ C ⋙ map F
  left_unit (C : Type u) [SmallCategory C] : η (T C) ⋙ μ C = 𝟭 (T C)
  right_unit (C : Type u) [SmallCategory C] : map (η C) ⋙ μ C = 𝟭 (T C)
  assoc (C : Type u) [SmallCategory C] : map (μ C) ⋙ μ C = μ (T C) ⋙ μ C

namespace CatMonad

variable {T} (M : CatMonad T)

/-- The monad on `Cat` underlying a `CatMonad`: the bridge to mathlib's `Monad`. -/
def toMonad : Monad Cat.{u, u} where
  obj C := Cat.of (T C)
  map F := (M.map F.toFunctor).toCatHom
  map_id C := Cat.ext (M.map_id C)
  map_comp F G := Cat.ext (M.map_comp F.toFunctor G.toFunctor)
  η :=
    { app C := (M.η C).toCatHom
      naturality _ _ F := Cat.ext (M.η_naturality F.toFunctor) }
  μ :=
    { app C := (M.μ C).toCatHom
      naturality _ _ F := Cat.ext (M.μ_naturality F.toFunctor) }
  assoc C := Cat.ext (M.assoc C)
  left_unit C := Cat.ext (M.left_unit C)
  right_unit C := Cat.ext (M.right_unit C)

@[simp] theorem toMonad_obj (C : Cat.{u, u}) : M.toMonad.obj C = Cat.of (T C) := rfl

@[simp] theorem toMonad_map_toFunctor {C D : Cat.{u, u}} (F : C ⟶ D) :
    (M.toMonad.map F).toFunctor = M.map F.toFunctor := rfl

@[simp] theorem toMonad_η_app_toFunctor (C : Cat.{u, u}) :
    (M.toMonad.η.app C).toFunctor = M.η C := rfl

@[simp] theorem toMonad_μ_app_toFunctor (C : Cat.{u, u}) :
    (M.toMonad.μ.app C).toFunctor = M.μ C := rfl

end CatMonad

/-- A lax double functor on the pseudo double category of small categories, functors and
profunctors, whose vertical part is `T`. The laxator and the unit comparison go *into* `T` of
a composite: they are the maps out of the coends, and so are definable (by `Quot.lift`) for
list-like `T`. -/
structure LaxFunctor extends CatFunctor T where
  /-- The action on profunctors. -/
  mapProf {C D : Type u} [SmallCategory C] [SmallCategory D] :
    Profunctor.{u} C D → Profunctor.{u} (T C) (T D)
  /-- The action on squares. -/
  mapSquare {C D C' D' : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory C']
    [SmallCategory D'] {P : Profunctor.{u} C D} {Q : Profunctor.{u} C' D'} {F : C ⥤ C'}
    {G : D ⥤ D'} : Square P Q F G → Square (mapProf P) (mapProf Q) (map F) (map G)
  mapSquare_id {C D : Type u} [SmallCategory C] [SmallCategory D] (P : Profunctor.{u} C D) :
    mapSquare (Square.id P) = (Square.id (mapProf P)).cast (map_id C).symm (map_id D).symm
  mapSquare_vComp {C D C' D' C'' D'' : Type u} [SmallCategory C] [SmallCategory D]
    [SmallCategory C'] [SmallCategory D'] [SmallCategory C''] [SmallCategory D'']
    {P : Profunctor.{u} C D} {Q : Profunctor.{u} C' D'} {R : Profunctor.{u} C'' D''}
    {F : C ⥤ C'} {G : D ⥤ D'} {F' : C' ⥤ C''} {G' : D' ⥤ D''}
    (s : Square P Q F G) (t : Square Q R F' G') :
    mapSquare (s.vComp t) =
      ((mapSquare s).vComp (mapSquare t)).cast (map_comp F F').symm (map_comp G G').symm
  /-- The laxator. -/
  lax {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) :
    Square ((mapProf P).comp (mapProf Q)) (mapProf (P.comp Q)) (𝟭 (T C)) (𝟭 (T E))
  /-- The unit comparison. -/
  unit (C : Type u) [SmallCategory C] :
    Square (Profunctor.id (C := T C)) (mapProf (Profunctor.id (C := C))) (𝟭 (T C)) (𝟭 (T C))
  lax_naturality {C D E C' D' E' : Type u} [SmallCategory C] [SmallCategory D]
    [SmallCategory E] [SmallCategory C'] [SmallCategory D'] [SmallCategory E']
    {P : Profunctor.{u} C D} {Q : Profunctor.{u} D E} {P' : Profunctor.{u} C' D'}
    {Q' : Profunctor.{u} D' E'} {F : C ⥤ C'} {G : D ⥤ D'} {H : E ⥤ E'}
    (s : Square P P' F G) (t : Square Q Q' G H) :
    ((mapSquare s).hcomp (mapSquare t)).vComp (lax P' Q') =
      (lax P Q).vComp (mapSquare (s.hcomp t))
  unit_naturality {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) :
    (Square.homMap (map F)).vComp (unit D) = (unit C).vComp (mapSquare (Square.homMap F))
  lax_assoc {C D E E' : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    [SmallCategory E'] (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E)
    (R : Profunctor.{u} E E') :
    (((lax P Q).hcomp (Square.id (mapProf R))).vComp (lax (P.comp Q) R)).vComp
        (mapSquare (Square.ofHom (P.associator Q R).hom)) =
      (((Square.ofHom ((mapProf P).associator (mapProf Q) (mapProf R)).hom).vComp
        ((Square.id (mapProf P)).hcomp (lax Q R))).vComp (lax P (Q.comp R))).cast
        (map_id C).symm (map_id E').symm
  lax_leftUnitor {C D : Type u} [SmallCategory C] [SmallCategory D] (P : Profunctor.{u} C D) :
    (((unit C).hcomp (Square.id (mapProf P))).vComp (lax Profunctor.id P)).vComp
        (mapSquare (Square.ofHom P.leftUnitor.hom)) =
      (Square.ofHom (mapProf P).leftUnitor.hom).cast (map_id C).symm (map_id D).symm
  lax_rightUnitor {C D : Type u} [SmallCategory C] [SmallCategory D] (P : Profunctor.{u} C D) :
    (((Square.id (mapProf P)).hcomp (unit D)).vComp (lax P Profunctor.id)).vComp
        (mapSquare (Square.ofHom P.rightUnitor.hom)) =
      (Square.ofHom (mapProf P).rightUnitor.hom).cast (map_id C).symm (map_id D).symm

/-- A monad on the pseudo double category of profunctors: a lax double functor with a monad
structure on its vertical part, whose unit and multiplication are vertical transformations of
lax double functors (with cell components `ηCell`, `μCell`), satisfying the monad laws. -/
structure LaxMonad extends CatMonad T, LaxFunctor T where
  /-- The cell components of the unit. -/
  ηCell {C D : Type u} [SmallCategory C] [SmallCategory D] (P : Profunctor.{u} C D) :
    Square P (mapProf P) (η C) (η D)
  /-- The cell components of the multiplication. -/
  μCell {C D : Type u} [SmallCategory C] [SmallCategory D] (P : Profunctor.{u} C D) :
    Square (mapProf (mapProf P)) (mapProf P) (μ C) (μ D)
  ηCell_naturality {C D C' D' : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory C']
    [SmallCategory D'] {P : Profunctor.{u} C D} {Q : Profunctor.{u} C' D'} {F : C ⥤ C'}
    {G : D ⥤ D'} (s : Square P Q F G) :
    s.vComp (ηCell Q) =
      ((ηCell P).vComp (mapSquare s)).cast (η_naturality F).symm (η_naturality G).symm
  μCell_naturality {C D C' D' : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory C']
    [SmallCategory D'] {P : Profunctor.{u} C D} {Q : Profunctor.{u} C' D'} {F : C ⥤ C'}
    {G : D ⥤ D'} (s : Square P Q F G) :
    (mapSquare (mapSquare s)).vComp (μCell Q) =
      ((μCell P).vComp (mapSquare s)).cast (μ_naturality F).symm (μ_naturality G).symm
  ηCell_lax {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) :
    ((ηCell P).hcomp (ηCell Q)).vComp (lax P Q) = ηCell (P.comp Q)
  ηCell_unit (C : Type u) [SmallCategory C] :
    (Square.homMap (η C)).vComp (unit C) = ηCell Profunctor.id
  μCell_lax {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) :
    ((μCell P).hcomp (μCell Q)).vComp (lax P Q) =
      (((lax (mapProf P) (mapProf Q)).vComp (mapSquare (lax P Q))).vComp
        (μCell (P.comp Q))).cast
        (congrArg (· ⋙ μ C) (map_id (T C))) (congrArg (· ⋙ μ E) (map_id (T E)))
  μCell_unit (C : Type u) [SmallCategory C] :
    (Square.homMap (μ C)).vComp (unit C) =
      (((unit (T C)).vComp (mapSquare (unit C))).vComp (μCell Profunctor.id)).cast
        (congrArg (· ⋙ μ C) (map_id (T C))) (congrArg (· ⋙ μ C) (map_id (T C)))
  ηCell_μCell {C D : Type u} [SmallCategory C] [SmallCategory D] (P : Profunctor.{u} C D) :
    (ηCell (mapProf P)).vComp (μCell P) =
      (Square.id (mapProf P)).cast (left_unit C).symm (left_unit D).symm
  mapSquare_ηCell_μCell {C D : Type u} [SmallCategory C] [SmallCategory D]
    (P : Profunctor.{u} C D) :
    (mapSquare (ηCell P)).vComp (μCell P) =
      (Square.id (mapProf P)).cast (right_unit C).symm (right_unit D).symm
  μCell_assoc {C D : Type u} [SmallCategory C] [SmallCategory D] (P : Profunctor.{u} C D) :
    (mapSquare (μCell P)).vComp (μCell P) =
      ((μCell (mapProf P)).vComp (μCell P)).cast (assoc C).symm (assoc D).symm

namespace LaxFunctor

variable {T} (L : LaxFunctor T)

/-- The action of `T` on squares commutes with transport along equal boundaries. -/
theorem mapSquare_cast {C D C' D' : Type u} [SmallCategory C] [SmallCategory D]
    [SmallCategory C'] [SmallCategory D'] {P : Profunctor.{u} C D} {Q : Profunctor.{u} C' D'}
    {F F' : C ⥤ C'} {G G' : D ⥤ D'} (hF : F = F') (hG : G = G') (s : Square P Q F G) :
    L.mapSquare (s.cast hF hG) = (L.mapSquare s).cast (congrArg L.map hF) (congrArg L.map hG) := by
  subst hF hG; simp

theorem mapSquare_cast_app_heq {C D C' D' : Type u} [SmallCategory C] [SmallCategory D]
    [SmallCategory C'] [SmallCategory D'] {P : Profunctor.{u} C D} {Q : Profunctor.{u} C' D'}
    {F F' : C ⥤ C'} {G G' : D ⥤ D'} (hF : F = F') (hG : G = G') (s : Square P Q F G)
    {c : T C} {d : T D} (x : (L.mapProf P).app c d) :
    (L.mapSquare (s.cast hF hG)).app x ≍ (L.mapSquare s).app x := by
  subst hF hG; rw [Square.cast_rfl]

theorem mapSquare_id_app_heq {C D : Type u} [SmallCategory C] [SmallCategory D]
    (P : Profunctor.{u} C D) {c : T C} {d : T D} (x : (L.mapProf P).app c d) :
    (L.mapSquare (Square.id P)).app x ≍ x := by
  rw [L.mapSquare_id]; exact Square.cast_app_heq _ _ _ x

theorem mapSquare_vComp_app_heq {C D C' D' C'' D'' : Type u} [SmallCategory C]
    [SmallCategory D] [SmallCategory C'] [SmallCategory D'] [SmallCategory C'']
    [SmallCategory D''] {P : Profunctor.{u} C D} {Q : Profunctor.{u} C' D'}
    {R : Profunctor.{u} C'' D''} {F : C ⥤ C'} {G : D ⥤ D'} {F' : C' ⥤ C''} {G' : D' ⥤ D''}
    (s : Square P Q F G) (t : Square Q R F' G') {c : T C} {d : T D}
    (x : (L.mapProf P).app c d) :
    (L.mapSquare (s.vComp t)).app x ≍ (L.mapSquare t).app ((L.mapSquare s).app x) := by
  rw [L.mapSquare_vComp]; exact Square.cast_app_heq _ _ _ x

/-- The action of `T` on squares whose covariant boundary is the identity, the shape of the
cells of an operad. It is `mapSquare` transported along `map_id`, so that its source and target
need no further transport. -/
def mapCov {C D D' : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory D']
    {P : Profunctor.{u} C D} {Q : Profunctor.{u} C D'} {G : D ⥤ D'} (s : Square P Q (𝟭 C) G) :
    Square (L.mapProf P) (L.mapProf Q) (𝟭 (T C)) (L.map G) :=
  (L.mapSquare s).cast (L.map_id C) rfl

theorem mapCov_app {C D D' : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory D']
    {P : Profunctor.{u} C D} {Q : Profunctor.{u} C D'} {G : D ⥤ D'} (s : Square P Q (𝟭 C) G)
    {c : T C} {d : T D} (x : (L.mapProf P).app c d) :
    (L.mapCov s).app x =
      (L.mapProf Q).mpLeft (Functor.congr_obj (L.map_id C) c) ((L.mapSquare s).app x) := by
  simp [mapCov, Square.cast_app]

/-- The action of `T` on binary cells with identity covariant boundary, derived from the
laxator. -/
def mapBinary {X Y Z Z' : Type u} [SmallCategory X] [SmallCategory Y] [SmallCategory Z]
    [SmallCategory Z'] {P : Profunctor.{u} X Y} {Q : Profunctor.{u} Y Z}
    {R : Profunctor.{u} X Z'} {G : Z ⥤ Z'} (β : BinaryCell P Q R (𝟭 X) G) :
    BinaryCell (L.mapProf P) (L.mapProf Q) (L.mapProf R) (𝟭 (T X)) (L.map G) :=
  Square.toBinary ((L.lax P Q).vComp (L.mapCov (Square.ofBinary β)))

/-- The action of `T` on nullary cells with identity covariant boundary, derived from the unit
comparison. -/
def mapNullary {C D : Type u} [SmallCategory C] [SmallCategory D] {Q : Profunctor.{u} C D}
    {G : C ⥤ D} (ν : NullaryCell Q (𝟭 C) G) :
    NullaryCell (L.mapProf Q) (𝟭 (T C)) (L.map G) :=
  Square.toNullary ((L.unit C).vComp (L.mapCov (Square.ofNullary ν)))

end LaxFunctor

end CategoryTheory.Lax
