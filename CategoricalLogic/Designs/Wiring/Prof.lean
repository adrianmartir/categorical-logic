/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Wiring.FreeW
public import CategoricalLogic.Profunctor.Square

/-!
# The action of `FreeW W` on profunctors and cells

For a profunctor `P : Profunctor C D`, an element of `(prof W P).app cs ds` assigns to every
variable `c` of `cs` a variable `d` of `ds` and a heteromorphism `P.app c d`, with an allowed
wiring. This is the same construction as the morphisms of `FreeW W C` (which are the case
`P = Profunctor.id`), so `FreeW W` acts on profunctors by applying itself to the collage.

The action on cells is *defined* here, for exactly the cells a `W`-operad needs:

* `FreeW.mapSquare`: squares, with arbitrary vertical boundaries;
* `FreeW.mapNullary`: nullary cells whose source boundary is the identity;
* `FreeW.mapBinary`: binary cells whose source boundary is the identity;
* `FreeW.ηCell`, `FreeW.μCell`: the unit and multiplication at a profunctor.

Restricting `mapNullary` and `mapBinary` to identity source boundaries avoids the object
`(FreeW.map (𝟭 C)).obj cs = ⟨cs.as.map id⟩`, which is only propositionally `cs`.
-/

@[expose] public section

namespace CategoryTheory

open Profunctor

universe u v₁ v₂ v₃ v₄ w w' w''

namespace FreeW

variable {W : WiringClass.{u}}

section Prof

variable {C : Type u} [Category.{v₁} C] {D : Type u} [Category.{v₂} D]
  (P : Profunctor.{w} C D)

/-- The underlying function of the action of `prof W P` on morphisms. -/
def profMap {cs cs' : FreeW W C} {ds ds' : FreeW W D} (f : cs ⟶ cs') (g : ds ⟶ ds')
    (e : Wired W (fun d c ↦ P.app c d) ds'.as cs.as) :
    Wired W (fun d c ↦ P.app c d) ds.as cs'.as :=
  Wired.comp (R := fun d c ↦ P.app c d) (S := fun c c' : C ↦ c ⟶ c')
    (U := fun d c ↦ P.app c d) (fun _ _ _ p α ↦ P.mapL α p)
    (Wired.comp (R := fun d d' : D ↦ d ⟶ d') (S := fun d c ↦ P.app c d)
      (U := fun d c ↦ P.app c d) (fun _ _ _ β p ↦ P.mapR β p) g e) f

theorem profMap_assign {cs cs' : FreeW W C} {ds ds' : FreeW W D} (f : cs ⟶ cs')
    (g : ds ⟶ ds') (e : Wired W (fun d c ↦ P.app c d) ds'.as cs.as) {c : C}
    (k : Var cs'.as c) :
    (profMap P f g e).assign k =
      ⟨(assign g (e.assign (assign f k).2.1).2.1).1,
        (assign g (e.assign (assign f k).2.1).2.1).2.1,
        P.mapL (assign f k).2.2
          (P.mapR (assign g (e.assign (assign f k).2.1).2.1).2.2
            (e.assign (assign f k).2.1).2.2)⟩ := rfl

theorem profMap_id {cs : FreeW W C} {ds : FreeW W D}
    (e : Wired W (fun d c ↦ P.app c d) ds.as cs.as) : profMap P (𝟙 cs) (𝟙 ds) e = e :=
  Wired.ext (Assign.ext fun _ k ↦ by
    rw [profMap_assign]; dsimp only [id_assign]; rw [mapR_id, mapL_id])

theorem profMap_comp {X₁ X₂ X₃ : FreeW W C} {Y₁ Y₂ Y₃ : FreeW W D} (f : X₁ ⟶ X₂) (f' : X₂ ⟶ X₃)
    (g : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃) (e : Wired W (fun d c ↦ P.app c d) Y₃.as X₁.as) :
    profMap P (f ≫ f') (g ≫ g') e = profMap P f' g (profMap P f g' e) :=
  Wired.ext (Assign.ext fun _ k ↦ by
    rw [profMap_assign, profMap_assign]; dsimp only [comp_assign]; rw [profMap_assign]
    simp [mapL_comp, mapR_comp, mapL_mapR_comm])

theorem profMap_comm {cs cs' : FreeW W C} {ds ds' : FreeW W D} (f : cs ⟶ cs') (g : ds ⟶ ds')
    (e : Wired W (fun d c ↦ P.app c d) ds'.as cs.as) :
    profMap P f (𝟙 ds) (profMap P (𝟙 cs) g e) = profMap P (𝟙 cs') g (profMap P f (𝟙 ds') e) := by
  rw [← profMap_comp, ← profMap_comp]; simp

/-- `FreeW W` applied to a profunctor. -/
def prof (W : WiringClass.{u}) (P : Profunctor.{w} C D) :
    Profunctor.{max u w} (FreeW W C) (FreeW W D) :=
  Profunctor.ofCore
    { obj cs ds := Wired W (fun d c ↦ P.app c d) ds.as cs.as
      map f g := TypeCat.ofHom (profMap P f g)
      map_id _ _ := congrArg TypeCat.ofHom (funext (profMap_id P))
      map_comp f f' g g' := congrArg TypeCat.ofHom (funext (profMap_comp P f f' g g')) }

variable {P}

/-- View an element of `prof W P` as a wired assignment. -/
def elt {cs : FreeW W C} {ds : FreeW W D} (e : (prof W P).app cs ds) :
    Wired W (fun d c ↦ P.app c d) ds.as cs.as := e

/-- View a wired assignment as an element of `prof W P`. -/
def mkElt {cs : FreeW W C} {ds : FreeW W D} (e : Wired W (fun d c ↦ P.app c d) ds.as cs.as) :
    (prof W P).app cs ds := e

@[simp] theorem elt_mkElt {cs : FreeW W C} {ds : FreeW W D}
    (e : Wired W (fun d c ↦ P.app c d) ds.as cs.as) : elt (mkElt e) = e := rfl

@[ext]
theorem prof_ext {cs : FreeW W C} {ds : FreeW W D} {e e' : (prof W P).app cs ds}
    (h : ∀ ⦃c : C⦄ (k : Var cs.as c), (elt e).assign k = (elt e').assign k) : e = e' :=
  Wired.ext (Assign.ext h)

theorem elt_mapL {cs cs' : FreeW W C} {ds : FreeW W D} (f : cs ⟶ cs')
    (e : (prof W P).app cs ds) : elt ((prof W P).mapL f e) = profMap P f (𝟙 ds) (elt e) := rfl

theorem elt_mapR {cs : FreeW W C} {ds ds' : FreeW W D} (g : ds ⟶ ds')
    (e : (prof W P).app cs ds') : elt ((prof W P).mapR g e) = profMap P (𝟙 cs) g (elt e) := rfl

@[simp] theorem prof_mapL_assign {cs cs' : FreeW W C} {ds : FreeW W D} (f : cs ⟶ cs')
    (e : (prof W P).app cs ds) {c : C} (k : Var cs'.as c) :
    (elt ((prof W P).mapL f e)).assign k =
      ⟨((elt e).assign (assign f k).2.1).1, ((elt e).assign (assign f k).2.1).2.1,
        P.mapL (assign f k).2.2 ((elt e).assign (assign f k).2.1).2.2⟩ := by
  rw [elt_mapL, profMap_assign]; dsimp only [id_assign]; rw [mapR_id]

@[simp] theorem prof_mapR_assign {cs : FreeW W C} {ds ds' : FreeW W D} (g : ds ⟶ ds')
    (e : (prof W P).app cs ds') {c : C} (k : Var cs.as c) :
    (elt ((prof W P).mapR g e)).assign k =
      ⟨(assign g ((elt e).assign k).2.1).1, (assign g ((elt e).assign k).2.1).2.1,
        P.mapR (assign g ((elt e).assign k).2.1).2.2 ((elt e).assign k).2.2⟩ := by
  rw [elt_mapR, profMap_assign]; dsimp only [id_assign]; rw [mapL_id]

end Prof

/-! ### Squares -/

section Square

variable {C D C' D' : Type u} [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C']
  [Category.{v₄} D'] {P : Profunctor.{w} C D} {Q : Profunctor.{w'} C' D'} {F : C ⥤ C'}
  {G : D ⥤ D'}

/-- The components of `mapSquare`. -/
def squareApp (s : Square P Q F G) {cs : FreeW W C} {ds : FreeW W D}
    (e : (prof W P).app cs ds) : Wired W (fun d c ↦ Q.app c d) (ds.as.map G.obj) (cs.as.map F.obj) :=
  Wired.mapSrc G.obj (fun _ _ q ↦ q) (Wired.mapTgt F.obj (fun _ _ p ↦ s.app p) (elt e))

theorem squareApp_assign_map (s : Square P Q F G) {cs : FreeW W C} {ds : FreeW W D}
    (e : (prof W P).app cs ds) {c : C} (j : Var cs.as c) :
    (squareApp s e).assign (j.map F.obj) =
      ⟨G.obj ((elt e).assign j).1, ((elt e).assign j).2.1.map G.obj,
        s.app ((elt e).assign j).2.2⟩ := by
  dsimp only [squareApp, Wired.mapSrc_assign, Assign.mapSrc, Wired.mapTgt_assign]
  rw [Assign.mapTgt_map]

/-- The action of `FreeW W` on squares: apply the square positionwise. -/
def mapSquare (s : Square P Q F G) : Square (prof W P) (prof W Q) (map F) (map G) where
  app e := mkElt (squareApp s e)
  natL f e := prof_ext fun _ k ↦ by
    induction k using Var.map_induction with
    | h j =>
      rw [prof_mapL_assign]
      dsimp only [elt_mkElt]
      rw [squareApp_assign_map, prof_mapL_assign, map_assign_map]
      dsimp only [elt_mkElt]
      rw [squareApp_assign_map, s.natL]
  natR e g := prof_ext fun _ k ↦ by
    induction k using Var.map_induction with
    | h j =>
      rw [prof_mapR_assign]
      dsimp only [elt_mkElt]
      rw [squareApp_assign_map, squareApp_assign_map, prof_mapR_assign, map_assign_map, s.natR]

@[simp] theorem mapSquare_assign_map (s : Square P Q F G) {cs : FreeW W C} {ds : FreeW W D}
    (e : (prof W P).app cs ds) {c : C} (j : Var cs.as c) :
    (elt ((mapSquare s).app e)).assign (j.map F.obj) =
      ⟨G.obj ((elt e).assign j).1, ((elt e).assign j).2.1.map G.obj,
        s.app ((elt e).assign j).2.2⟩ :=
  squareApp_assign_map s e j

end Square

/-! ### Nullary cells -/

section Nullary

variable {C D : Type u} [Category.{v₁} C] [Category.{v₂} D] {Q : Profunctor.{w} C D}
  {G : C ⥤ D}

/-- The action of `FreeW W` on nullary cells with identity source boundary: the family of
components at the objects of a list. -/
def mapNullary (ν : NullaryCell Q (𝟭 C) G) : NullaryCell (prof W Q) (𝟭 (FreeW W C)) (map G) where
  app cs := mkElt (Wired.mapSrc G.obj (fun _ _ q ↦ q)
    (Wired.refl (R := fun c c' ↦ Q.app c' (G.obj c)) (fun c ↦ ν.app c) (as := cs.as)))
  naturality {cs cs'} α := prof_ext fun _ k ↦ by
    rw [prof_mapL_assign, prof_mapR_assign]
    dsimp only [elt_mkElt, Wired.mapSrc_assign, Assign.mapSrc, Wired.refl_assign, Assign.refl,
      Functor.id_map]
    rw [Wired.mapTgt_assign, Assign.mapTgt_map]
    simpa using ν.naturality (assign α k).2.2

@[simp] theorem mapNullary_assign (ν : NullaryCell Q (𝟭 C) G) (cs : FreeW W C) {c : C}
    (k : Var cs.as c) :
    (elt ((mapNullary ν).app cs)).assign k = ⟨G.obj c, k.map G.obj, ν.app c⟩ := rfl

end Nullary

/-! ### Binary cells -/

section Binary

variable {X Y Z Z' : Type u} [Category.{v₁} X] [Category.{v₂} Y] [Category.{v₃} Z]
  [Category.{v₄} Z'] {P : Profunctor.{w} X Y} {Q : Profunctor.{w'} Y Z}
  {R : Profunctor.{w''} X Z'} {G : Z ⥤ Z'}

/-- The components of `mapBinary`. -/
def binaryApp (β : BinaryCell P Q R (𝟭 X) G) {xs : FreeW W X} {ys : FreeW W Y}
    {zs : FreeW W Z} (e : (prof W P).app xs ys) (e' : (prof W Q).app ys zs) :
    (prof W R).app xs ((map G).obj zs) :=
  mkElt (Wired.mapSrc G.obj (fun _ _ r ↦ r)
    (Wired.comp (R := fun z y ↦ Q.app y z) (S := fun y x ↦ P.app x y)
      (U := fun z x ↦ R.app x (G.obj z)) (fun _ _ _ q p ↦ β.app p q) (elt e') (elt e)))

@[simp] theorem binaryApp_assign (β : BinaryCell P Q R (𝟭 X) G) {xs : FreeW W X}
    {ys : FreeW W Y} {zs : FreeW W Z} (e : (prof W P).app xs ys) (e' : (prof W Q).app ys zs)
    {x : X} (k : Var xs.as x) :
    (elt (binaryApp β e e')).assign k =
      ⟨G.obj ((elt e').assign ((elt e).assign k).2.1).1,
        ((elt e').assign ((elt e).assign k).2.1).2.1.map G.obj,
        β.app ((elt e).assign k).2.2 ((elt e').assign ((elt e).assign k).2.1).2.2⟩ := rfl

/-- The action of `FreeW W` on binary cells with identity source boundary: compose the two
families and apply the cell positionwise. -/
def mapBinary (β : BinaryCell P Q R (𝟭 X) G) :
    BinaryCell (prof W P) (prof W Q) (prof W R) (𝟭 (FreeW W X)) (map G) where
  app e e' := binaryApp β e e'
  wedge f α g := prof_ext fun _ k ↦ by
    rw [binaryApp_assign, binaryApp_assign, prof_mapR_assign, prof_mapL_assign, β.wedge]
  natL α f g := prof_ext fun _ k ↦ by
    rw [binaryApp_assign, prof_mapL_assign, prof_mapL_assign, binaryApp_assign, β.natL]; rfl
  natR f g α := prof_ext fun _ k ↦ by
    rw [binaryApp_assign, prof_mapR_assign, prof_mapR_assign, binaryApp_assign, map_assign_map,
      β.natR]

@[simp] theorem mapBinary_assign (β : BinaryCell P Q R (𝟭 X) G) {xs : FreeW W X}
    {ys : FreeW W Y} {zs : FreeW W Z} (e : (prof W P).app xs ys) (e' : (prof W Q).app ys zs)
    {x : X} (k : Var xs.as x) :
    (elt ((mapBinary β).app e e')).assign k =
      ⟨G.obj ((elt e').assign ((elt e).assign k).2.1).1,
        ((elt e').assign ((elt e).assign k).2.1).2.1.map G.obj,
        β.app ((elt e).assign k).2.2 ((elt e').assign ((elt e).assign k).2.1).2.2⟩ := rfl

end Binary

/-! ### Unit and multiplication -/

section Monad

variable {C D : Type u} [Category.{v₁} C] [Category.{v₂} D] (P : Profunctor.{w} C D)

/-- The unit at a profunctor: an element as a singleton family. -/
def ηCell : Square P (prof W P) unit unit where
  app p := mkElt (Wired.single p)
  natL f p := prof_ext fun _ k ↦ match k with
    | .zero => by rw [prof_mapL_assign]; dsimp only [elt_mkElt, Wired.single_assign]; rfl
  natR p g := prof_ext fun _ k ↦ match k with
    | .zero => by rw [prof_mapR_assign]; dsimp only [elt_mkElt, Wired.single_assign]; rfl

@[simp] theorem ηCell_assign {c : C} {d : D} (p : P.app c d) :
    (elt ((ηCell (W := W) P).app p)).assign .zero = ⟨d, .zero, p⟩ := rfl

/-- The components of `μCell`. -/
def μApp {css : FreeW W (FreeW W C)} {dss : FreeW W (FreeW W D)}
    (e : (prof W (prof W P)).app css dss) :
    (prof W P).app ((flatten (W := W)).obj css) ((flatten (W := W)).obj dss) :=
  mkElt (Wired.bind FreeW.as FreeW.as (fun _ _ x ↦ elt x) (elt e))

@[simp] theorem μApp_assign_join {css : FreeW W (FreeW W C)} {dss : FreeW W (FreeW W D)}
    (e : (prof W (prof W P)).app css dss) {cs : FreeW W C} {c : C} (j : Var css.as cs)
    (v : Var cs.as c) :
    (elt (μApp P e)).assign (Var.join FreeW.as j v) =
      ⟨((elt ((elt e).assign j).2.2).assign v).1,
        Var.join FreeW.as ((elt e).assign j).2.1 ((elt ((elt e).assign j).2.2).assign v).2.1,
        ((elt ((elt e).assign j).2.2).assign v).2.2⟩ := by
  dsimp only [μApp, elt_mkElt, Wired.bind_assign]; rw [Assign.bind_join]

/-- The multiplication at a profunctor: flatten a family of families. -/
def μCell : Square (prof W (prof W P)) (prof W P) flatten flatten where
  app e := μApp P e
  natL f e := prof_ext fun _ k ↦ by
    induction k using Var.flatMap_induction with
    | h j v =>
      rw [μApp_assign_join, prof_mapL_assign, prof_mapL_assign, prof_mapL_assign,
        flatten_assign_join, μApp_assign_join]
  natR e g := prof_ext fun _ k ↦ by
    induction k using Var.flatMap_induction with
    | h j v =>
      rw [μApp_assign_join, prof_mapR_assign, prof_mapR_assign, prof_mapR_assign,
        μApp_assign_join, flatten_assign_join]

@[simp] theorem μCell_assign_join {css : FreeW W (FreeW W C)} {dss : FreeW W (FreeW W D)}
    (e : (prof W (prof W P)).app css dss) {cs : FreeW W C} {c : C} (j : Var css.as cs)
    (v : Var cs.as c) :
    (elt ((μCell (W := W) P).app e)).assign (Var.join FreeW.as j v) =
      ⟨((elt ((elt e).assign j).2.2).assign v).1,
        Var.join FreeW.as ((elt e).assign j).2.1 ((elt ((elt e).assign j).2.2).assign v).2.1,
        ((elt ((elt e).assign j).2.2).assign v).2.2⟩ :=
  μApp_assign_join P e j v

end Monad

end FreeW

end CategoryTheory
