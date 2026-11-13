/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import CategoricalLogic.Profunctor.Square

/-!
# Generalized operads in profunctors

A formalization of generalized multicategories (`T`-operads, the `T`-monoids of
Cruttwell–Shulman) in the virtual double category of categories, functors and profunctors.
We avoid the bicategory of profunctors and work with the cells of arity `0`, `1` and `2` of
`CategoricalLogic.Profunctor.Square`. This avoids the complexities of profunctor composition and
gives a computational interpretation of operads.

## Main definitions

* `FunctorProf T`: a functor `T : Cat ⥤ Cat` acting on profunctors and on cells of arity `≤ 2`.
* `MonadProf T`: a monad on `Cat` whose unit and multiplication have cell components.
* `Operad T X`: a `T`-operad on the category `X`.
* `Operad.Hom M N`: morphisms of `T`-operads, with identities and composition.

## Conventions

Since cells are indexed by functors while `T` acts on morphisms of `Cat`, the action of `T` on
cells takes the boundary morphisms explicitly. Where the boundaries of two cells agree only
propositionally, we transport with `cast` on cells and with `mpLeft`/`mpRight` on elements.

References:
* [A unified framework for generalized multicategories](https://arxiv.org/abs/0907.2460)
-/

@[expose] public section

namespace CategoryTheory

universe u v u' v' w w'

open Profunctor

/-! ### Functoriality and the monad laws as equalities of functors -/

namespace Functor

variable (T : Cat.{v, u} ⥤ Cat.{v', u'})

theorem map_id_toFunctor (C : Cat.{v, u}) : (T.map (𝟙 C)).toFunctor = 𝟭 (T.obj C) :=
  congrArg Cat.Hom.toFunctor (T.map_id C)

theorem map_comp_toFunctor {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) :
    (T.map (F ≫ G)).toFunctor = (T.map F).toFunctor ⋙ (T.map G).toFunctor :=
  congrArg Cat.Hom.toFunctor (T.map_comp F G)

end Functor

namespace Monad

variable (T : Monad Cat.{v, u})

theorem η_naturality_toFunctor {C D : Cat.{v, u}} (F : C ⟶ D) :
    F.toFunctor ⋙ (T.η.app D).toFunctor = (T.η.app C).toFunctor ⋙ (T.map F).toFunctor :=
  congrArg Cat.Hom.toFunctor (T.η.naturality F)

theorem μ_naturality_toFunctor {C D : Cat.{v, u}} (F : C ⟶ D) :
    (T.map (T.map F)).toFunctor ⋙ (T.μ.app D).toFunctor =
      (T.μ.app C).toFunctor ⋙ (T.map F).toFunctor :=
  congrArg Cat.Hom.toFunctor (T.μ.naturality F)

theorem left_unit_toFunctor (C : Cat.{v, u}) :
    (T.η.app (T.obj C)).toFunctor ⋙ (T.μ.app C).toFunctor = 𝟭 (T.obj C) :=
  congrArg Cat.Hom.toFunctor (T.left_unit C)

theorem right_unit_toFunctor (C : Cat.{v, u}) :
    (T.map (T.η.app C)).toFunctor ⋙ (T.μ.app C).toFunctor = 𝟭 (T.obj C) :=
  congrArg Cat.Hom.toFunctor (T.right_unit C)

theorem assoc_toFunctor (C : Cat.{v, u}) :
    (T.map (T.μ.app C)).toFunctor ⋙ (T.μ.app C).toFunctor =
      (T.μ.app (T.obj C)).toFunctor ⋙ (T.μ.app C).toFunctor :=
  congrArg Cat.Hom.toFunctor (T.assoc C)

end Monad

/-! ### Functors and monads of profunctors -/

/-- A functor `T : Cat ⥤ Cat` is a *functor of profunctors* if it acts on profunctors and on
cells of arity `≤ 2`, compatibly with its action on functors and with the composition of cells.
This is a functor of virtual double categories, truncated at the arities a `T`-operad can see. -/
class FunctorProf (T : Cat.{v, u} ⥤ Cat.{v', u'}) where
  /-- The action on profunctors. -/
  mapProf {C D : Cat.{v, u}} : Profunctor.{w} C D → Profunctor.{w'} (T.obj C) (T.obj D)
  /-- The action on squares. -/
  mapSquare {C D C' D' : Cat.{v, u}} {P : Profunctor.{w} C D} {Q : Profunctor.{w} C' D'}
    (F : C ⟶ C') (G : D ⟶ D') :
    Square P Q F.toFunctor G.toFunctor →
      Square (mapProf P) (mapProf Q) (T.map F).toFunctor (T.map G).toFunctor
  /-- The action on nullary cells. -/
  mapNullary {A C D : Cat.{v, u}} {Q : Profunctor.{w} C D} (F : A ⟶ C) (G : A ⟶ D) :
    NullaryCell Q F.toFunctor G.toFunctor →
      NullaryCell (mapProf Q) (T.map F).toFunctor (T.map G).toFunctor
  /-- The action on binary cells. -/
  mapBinary {X Y Z X' Z' : Cat.{v, u}} {h : Profunctor.{w} Y X} {k : Profunctor.{w} Z Y}
    {j : Profunctor.{w} Z' X'} (F : Z ⟶ Z') (G : X ⟶ X') :
    BinaryCell h k j F.toFunctor G.toFunctor →
      BinaryCell (mapProf h) (mapProf k) (mapProf j) (T.map F).toFunctor (T.map G).toFunctor
  /-- `T` preserves identity squares. -/
  mapSquare_id {C D : Cat.{v, u}} (P : Profunctor.{w} C D) :
    mapSquare (𝟙 C) (𝟙 D) (Square.id P) =
      (Square.id (mapProf P)).cast (T.map_id_toFunctor C).symm (T.map_id_toFunctor D).symm
  /-- `T` preserves vertical composition of squares. -/
  mapSquare_vComp {C D C' D' C'' D'' : Cat.{v, u}} {P : Profunctor.{w} C D}
    {Q : Profunctor.{w} C' D'} {R : Profunctor.{w} C'' D''} {F : C ⟶ C'} {G : D ⟶ D'}
    {F' : C' ⟶ C''} {G' : D' ⟶ D''}
    (s : Square P Q F.toFunctor G.toFunctor) (t : Square Q R F'.toFunctor G'.toFunctor) :
    mapSquare (F ≫ F') (G ≫ G') (s.vComp t) =
      ((mapSquare F G s).vComp (mapSquare F' G' t)).cast
        (T.map_comp_toFunctor F F').symm (T.map_comp_toFunctor G G').symm
  /-- `T` preserves postcomposition of nullary cells with squares. -/
  mapNullary_vComp {A C D C' D' : Cat.{v, u}} {Q : Profunctor.{w} C D}
    {R : Profunctor.{w} C' D'} {F : A ⟶ C} {G : A ⟶ D} {F' : C ⟶ C'} {G' : D ⟶ D'}
    (ν : NullaryCell Q F.toFunctor G.toFunctor) (t : Square Q R F'.toFunctor G'.toFunctor) :
    mapNullary (F ≫ F') (G ≫ G') (ν.vComp t) =
      ((mapNullary F G ν).vComp (mapSquare F' G' t)).cast
        (T.map_comp_toFunctor F F').symm (T.map_comp_toFunctor G G').symm
  /-- `T` preserves reindexing of nullary cells along functors. -/
  mapNullary_comap {A B C D : Cat.{v, u}} {Q : Profunctor.{w} C D} {F : A ⟶ C} {G : A ⟶ D}
    (K : B ⟶ A) (ν : NullaryCell Q F.toFunctor G.toFunctor) :
    mapNullary (K ≫ F) (K ≫ G) (ν.comap K.toFunctor) =
      ((mapNullary F G ν).comap (T.map K).toFunctor).cast
        (T.map_comp_toFunctor K F).symm (T.map_comp_toFunctor K G).symm
  /-- `T` preserves postcomposition of binary cells with squares. -/
  mapBinary_vComp {X Y Z X' Z' X'' Z'' : Cat.{v, u}} {h : Profunctor.{w} Y X}
    {k : Profunctor.{w} Z Y} {j : Profunctor.{w} Z' X'} {j' : Profunctor.{w} Z'' X''}
    {F : Z ⟶ Z'} {G : X ⟶ X'} {F' : Z' ⟶ Z''} {G' : X' ⟶ X''}
    (β : BinaryCell h k j F.toFunctor G.toFunctor) (t : Square j j' F'.toFunctor G'.toFunctor) :
    mapBinary (F ≫ F') (G ≫ G') (β.vComp t) =
      ((mapBinary F G β).vComp (mapSquare F' G' t)).cast
        (T.map_comp_toFunctor F F').symm (T.map_comp_toFunctor G G').symm
  /-- `T` preserves precomposition of binary cells with pairs of squares. -/
  mapBinary_precomp {X Y Z X' Z' X₀ Y₀ Z₀ : Cat.{v, u}} {h : Profunctor.{w} Y X}
    {k : Profunctor.{w} Z Y} {j : Profunctor.{w} Z' X'} {h' : Profunctor.{w} Y₀ X₀}
    {k' : Profunctor.{w} Z₀ Y₀} {F : Z ⟶ Z'} {G : X ⟶ X'} {K : Y₀ ⟶ Y} {F₀ : Z₀ ⟶ Z}
    {G₀ : X₀ ⟶ X} (s : Square h' h K.toFunctor G₀.toFunctor)
    (s' : Square k' k F₀.toFunctor K.toFunctor) (β : BinaryCell h k j F.toFunctor G.toFunctor) :
    mapBinary (F₀ ≫ F) (G₀ ≫ G) (β.precomp s s') =
      ((mapBinary F G β).precomp (mapSquare K G₀ s) (mapSquare F₀ K s')).cast
        (T.map_comp_toFunctor F₀ F).symm (T.map_comp_toFunctor G₀ G).symm

namespace FunctorProf

variable {T : Cat.{v, u} ⥤ Cat.{v', u'}} [FunctorProf.{u, v, u', v', w, w'} T]

/-- The action of `T` on a nullary cell whose covariant boundary is the identity. -/
def mapNullaryId {C D : Cat.{v, u}} {Q : Profunctor.{w} C D} {G : C ⟶ D}
    (ν : NullaryCell Q (𝟭 C) G.toFunctor) :
    NullaryCell (mapProf Q) (𝟭 (T.obj C)) (T.map G).toFunctor :=
  (mapNullary (𝟙 C) G ν).cast (T.map_id_toFunctor C) rfl

/-- The action of `T` on a binary cell whose covariant boundary is the identity. -/
def mapBinaryId {X Y Z X' : Cat.{v, u}} {h : Profunctor.{w} Y X} {k : Profunctor.{w} Z Y}
    {j : Profunctor.{w} Z X'} {G : X ⟶ X'} (β : BinaryCell h k j (𝟭 Z) G.toFunctor) :
    BinaryCell (mapProf h) (mapProf k) (mapProf j) (𝟭 (T.obj Z)) (T.map G).toFunctor :=
  (mapBinary (𝟙 Z) G β).cast (T.map_id_toFunctor Z) rfl

/-- The action of `T` on squares commutes with transport along equal boundaries. -/
theorem mapSquare_cast {C D C' D' : Cat.{v, u}} {P : Profunctor.{w} C D}
    {Q : Profunctor.{w} C' D'} {F F' : C ⟶ C'} {G G' : D ⟶ D'}
    (hF : F.toFunctor = F'.toFunctor) (hG : G.toFunctor = G'.toFunctor)
    (s : Square P Q F.toFunctor G.toFunctor) :
    mapSquare (T := T) F' G' (s.cast hF hG) =
      (mapSquare F G s).cast (congrArg (T.map · |>.toFunctor) (Cat.Hom.ext hF))
        (congrArg (T.map · |>.toFunctor) (Cat.Hom.ext hG)) := by
  obtain rfl := Cat.Hom.ext hF
  obtain rfl := Cat.Hom.ext hG
  simp

end FunctorProf

open FunctorProf

/-- A monad `T` on `Cat` that is a functor of profunctors is a *monad of profunctors* if its unit
and multiplication have cell components, natural with respect to cells of arity `≤ 2` and
satisfying the monad laws on cells. -/
class MonadProf (T : Monad Cat.{v, u}) extends FunctorProf.{u, v, u, v, w, w} T.toFunctor where
  /-- The component of the unit at a profunctor. -/
  ηCell {C D : Cat.{v, u}} (P : Profunctor.{w} C D) :
    Square P (mapProf P) (T.η.app C).toFunctor (T.η.app D).toFunctor
  /-- The component of the multiplication at a profunctor. -/
  μCell {C D : Cat.{v, u}} (P : Profunctor.{w} C D) :
    Square (mapProf (mapProf P)) (mapProf P) (T.μ.app C).toFunctor (T.μ.app D).toFunctor
  /-- Naturality of `ηCell` with respect to squares. -/
  ηCell_square {C D C' D' : Cat.{v, u}} {P : Profunctor.{w} C D} {Q : Profunctor.{w} C' D'}
    {F : C ⟶ C'} {G : D ⟶ D'} (s : Square P Q F.toFunctor G.toFunctor) :
    s.vComp (ηCell Q) = ((ηCell P).vComp (mapSquare F G s)).cast
      (T.η_naturality_toFunctor F).symm (T.η_naturality_toFunctor G).symm
  /-- Naturality of `ηCell` with respect to nullary cells. -/
  ηCell_nullary {A C D : Cat.{v, u}} {Q : Profunctor.{w} C D} {F : A ⟶ C} {G : A ⟶ D}
    (ν : NullaryCell Q F.toFunctor G.toFunctor) :
    ν.vComp (ηCell Q) = ((mapNullary F G ν).comap (T.η.app A).toFunctor).cast
      (T.η_naturality_toFunctor F).symm (T.η_naturality_toFunctor G).symm
  /-- Naturality of `ηCell` with respect to binary cells. -/
  ηCell_binary {X Y Z X' Z' : Cat.{v, u}} {h : Profunctor.{w} Y X} {k : Profunctor.{w} Z Y}
    {j : Profunctor.{w} Z' X'} {F : Z ⟶ Z'} {G : X ⟶ X'}
    (β : BinaryCell h k j F.toFunctor G.toFunctor) :
    β.vComp (ηCell j) = ((mapBinary F G β).precomp (ηCell h) (ηCell k)).cast
      (T.η_naturality_toFunctor F).symm (T.η_naturality_toFunctor G).symm
  /-- Naturality of `μCell` with respect to squares. -/
  μCell_square {C D C' D' : Cat.{v, u}} {P : Profunctor.{w} C D} {Q : Profunctor.{w} C' D'}
    {F : C ⟶ C'} {G : D ⟶ D'} (s : Square P Q F.toFunctor G.toFunctor) :
    (mapSquare (T.map F) (T.map G) (mapSquare F G s)).vComp (μCell Q) =
      ((μCell P).vComp (mapSquare F G s)).cast
        (T.μ_naturality_toFunctor F).symm (T.μ_naturality_toFunctor G).symm
  /-- Naturality of `μCell` with respect to nullary cells. -/
  μCell_nullary {A C D : Cat.{v, u}} {Q : Profunctor.{w} C D} {F : A ⟶ C} {G : A ⟶ D}
    (ν : NullaryCell Q F.toFunctor G.toFunctor) :
    (mapNullary (T.map F) (T.map G) (mapNullary F G ν)).vComp (μCell Q) =
      ((mapNullary F G ν).comap (T.μ.app A).toFunctor).cast
        (T.μ_naturality_toFunctor F).symm (T.μ_naturality_toFunctor G).symm
  /-- Naturality of `μCell` with respect to binary cells. -/
  μCell_binary {X Y Z X' Z' : Cat.{v, u}} {h : Profunctor.{w} Y X} {k : Profunctor.{w} Z Y}
    {j : Profunctor.{w} Z' X'} {F : Z ⟶ Z'} {G : X ⟶ X'}
    (β : BinaryCell h k j F.toFunctor G.toFunctor) :
    (mapBinary (T.map F) (T.map G) (mapBinary F G β)).vComp (μCell j) =
      ((mapBinary F G β).precomp (μCell h) (μCell k)).cast
        (T.μ_naturality_toFunctor F).symm (T.μ_naturality_toFunctor G).symm
  /-- The left unit law, on cells. -/
  ηCell_μCell {C D : Cat.{v, u}} (P : Profunctor.{w} C D) :
    (ηCell (mapProf P)).vComp (μCell P) =
      (Square.id (mapProf P)).cast (T.left_unit_toFunctor C).symm (T.left_unit_toFunctor D).symm
  /-- The right unit law, on cells. -/
  mapSquare_ηCell_μCell {C D : Cat.{v, u}} (P : Profunctor.{w} C D) :
    (mapSquare (T.η.app C) (T.η.app D) (ηCell P)).vComp (μCell P) =
      (Square.id (mapProf P)).cast
        (T.right_unit_toFunctor C).symm (T.right_unit_toFunctor D).symm
  /-- The associativity law, on cells. -/
  μCell_assoc {C D : Cat.{v, u}} (P : Profunctor.{w} C D) :
    (μCell (mapProf P)).vComp (μCell P) =
      ((mapSquare (T.μ.app C) (T.μ.app D) (μCell P)).vComp (μCell P)).cast
        (T.assoc_toFunctor C) (T.assoc_toFunctor D)

open MonadProf

/-! ### Operads -/

variable (T : Monad Cat.{v, u}) [MonadProf.{u, v, w} T]

/-- A `T`-operad on `X` (a `T`-monoid in the sense of Cruttwell–Shulman): a profunctor
`hom : X ⇸ T X`, whose elements `hom.app b a` are the operations with arity `b : T X` and output
`a : X`, together with identities and a composition. -/
structure Operad (X : Cat.{v, u}) where
  /-- The operations: `hom.app b a` are the operations with arity `b` and output `a`. -/
  hom : Profunctor.{w} X (T.obj X)
  /-- The identity operation on `a`, of arity `η a`. -/
  id : NullaryCell hom (𝟭 X) (T.η.app X).toFunctor
  /-- Composition: an arity-`c` family `f` of operations with outputs `b`, and an operation `g`
  of arity `b`, compose to an operation of arity `μ c`. -/
  comp : BinaryCell (mapProf hom) hom hom (𝟭 X) (T.μ.app X).toFunctor
  /-- Composing an operation `f`, viewed as a family of operations through `η`, with the
  identity is `f`. -/
  comp_id {a : X} {b : T.obj X} (f : hom.app b a) :
    comp.app ((ηCell hom).app f) (id.app a) =
      hom.mpLeft (Functor.congr_obj (T.left_unit_toFunctor X) b) f
  /-- Composing the family of identities of arity `b` with an operation `f` of arity `b` is
  `f`. -/
  id_comp {a : X} {b : T.obj X} (f : hom.app b a) :
    comp.app ((mapNullaryId id).app b) f =
      hom.mpLeft (Functor.congr_obj (T.right_unit_toFunctor X) b) f
  /-- Composition is associative: for a family of families `f`, a family `g` and an operation
  `h`, flattening `f` and composing with `g ∘ h` agrees with composing `f` and `g` pointwise
  (by `T` applied to `comp`) and then composing with `h`. -/
  comp_assoc {a : X} {b : T.obj X} {c : T.obj (T.obj X)} {d : T.obj (T.obj (T.obj X))}
      (f : (mapProf (mapProf hom)).app d c) (g : (mapProf hom).app c b) (h : hom.app b a) :
    comp.app ((μCell hom).app f) (comp.app g h) =
      hom.mpLeft (Functor.congr_obj (T.assoc_toFunctor X) d).symm
        (comp.app ((mapBinaryId comp).app f g) h)

namespace Operad

variable {T} {X Y Z : Cat.{v, u}}

/-- A morphism of `T`-operads: a functor on objects together with a square between the
profunctors of operations, preserving identities and composition. -/
structure Hom (M : Operad T X) (N : Operad T Y) where
  /-- The action on objects. -/
  functor : X ⟶ Y
  /-- The action on operations. -/
  map : Square M.hom N.hom functor.toFunctor (T.map functor).toFunctor
  /-- Identities are preserved, up to the naturality of `η`. -/
  map_id (a : X) :
    map.app (M.id.app a) =
      N.hom.mpLeft (Functor.congr_obj (T.η_naturality_toFunctor functor) a).symm
        (N.id.app (functor.toFunctor.obj a))
  /-- Composition is preserved, up to the naturality of `μ`. -/
  map_comp {a : X} {b : T.obj X} {c : T.obj (T.obj X)} (f : (mapProf M.hom).app c b)
      (g : M.hom.app b a) :
    map.app (M.comp.app f g) =
      N.hom.mpLeft (Functor.congr_obj (T.μ_naturality_toFunctor functor) c).symm
        (N.comp.app ((mapSquare functor (T.map functor) map).app f) (map.app g))

namespace Hom

/-- The identity morphism of operads. -/
def id (M : Operad T X) : Hom M M where
  functor := 𝟙 X
  map := (Square.id M.hom).cast rfl (T.map_id_toFunctor X).symm
  map_id a := by simp [Square.cast_app]
  map_comp f g := by
    rw [mapSquare_cast (F := 𝟙 X) (G := 𝟙 (T.obj X)), mapSquare_id]
    simp [Square.cast_app]

variable {L : Operad T X} {M : Operad T Y} {N : Operad T Z}

/-- The composition of morphisms of operads. -/
def comp (φ : Hom L M) (ψ : Hom M N) : Hom L N where
  functor := φ.functor ≫ ψ.functor
  map := (φ.map.vComp ψ.map).cast rfl (T.map_comp_toFunctor φ.functor ψ.functor).symm
  map_id a := by simp [Square.cast_app, φ.map_id, ψ.map_id]
  map_comp f g := by
    rw [mapSquare_cast (F := φ.functor ≫ ψ.functor) (G := T.map φ.functor ≫ T.map ψ.functor),
      mapSquare_vComp]
    simp [Square.cast_app, φ.map_comp, ψ.map_comp]

end Hom

end Operad

end CategoryTheory
