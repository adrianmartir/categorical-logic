/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Profunctor.Basic
public import Mathlib.CategoryTheory.Profunctor.Comp

/-!
# Cells between profunctors

This file defines the cells of arity `0`, `1` and `2` of the virtual double category whose
objects are categories, vertical arrows are functors and horizontal arrows are profunctors.
Cells are given elementwise, as bespoke structures.

## Conventions

* A profunctor `P : Profunctor C D` is a functor `C ⥤ Dᵒᵖ ⥤ Type w`, a horizontal arrow from
  `C` to `D`. Its elements are written `P.app c d` with `c : C` (the covariant side) first and
  `d : D` (the contravariant side) second; `P.mapL` acts on `c` and `P.mapR` on `d`.
* Functors on the vertical boundary of a cell are listed in the same order: the one on the
  source side `C` first and the one on the target side `D` second.
* The source of a cell is listed in the order of composition of mathlib, `P.comp Q`.

## Main definitions

* `Square P Q F G`: a cell with unary source, i.e. a natural map `P c d → Q (F c) (G d)`.
* `NullaryCell Q F G`: a cell with empty source over a category `A`, i.e. a natural family
  `Q (F a) (G a)`.
* `BinaryCell P Q R F G`: a cell with source the composable pair `P, Q`, i.e. a map
  `P x y → Q y z → R (F x) (G z)` that is natural in `x, z` and dinatural (a wedge) in `y`.
* `Square.cast`, `NullaryCell.cast`, `BinaryCell.cast`: transport along equalities of the
  boundary functors.
* `Square.homEquiv`: squares correspond to natural transformations `P ⟶ Q.whiskerLeft₂ F G`.
* `BinaryCell.homEquiv`: binary cells `P, Q ⇒ R` correspond to natural transformations
  `P.comp Q ⟶ R.whiskerLeft₂ F G` out of mathlib's composite profunctor.
-/

@[expose] public section

namespace CategoryTheory.Profunctor

universe u w w' w'' w''' w₁ w₂

open Opposite Limits

section Square

variable {C D C' D' C'' D'' C''' D''' : Type*}
  [Category* C] [Category* D] [Category* C'] [Category* D']
  [Category* C''] [Category* D''] [Category* C'''] [Category* D''']

/-- A cell with unary source `P` and target `Q`, with the functor `F` on the source side and
`G` on the target side: a natural transformation `P ⇒ Q(F, G)`. -/
structure Square (P : Profunctor.{w} C D) (Q : Profunctor.{w'} C' D')
    (F : C ⥤ C') (G : D ⥤ D') where
  /-- The components of the square. -/
  app {c : C} {d : D} : P.app c d → Q.app (F.obj c) (G.obj d)
  natL {c c' : C} {d : D} (α : c ⟶ c') (f : P.app c d) :
    app (P.mapL α f) = Q.mapL (F.map α) (app f)
  natR {c : C} {d d' : D} (f : P.app c d') (α : d ⟶ d') :
    app (P.mapR α f) = Q.mapR (G.map α) (app f)

namespace Square

variable {P : Profunctor.{w} C D} {Q : Profunctor.{w'} C' D'} {R : Profunctor.{w''} C'' D''}
  {F : C ⥤ C'} {G : D ⥤ D'}

@[ext]
theorem ext {s t : Square P Q F G} (h : ∀ {c d} (f : P.app c d), s.app f = t.app f) : s = t := by
  cases s; cases t; congr; funext c d f; exact h f

/-- The identity square on a profunctor. -/
def id (P : Profunctor.{w} C D) : Square P P (𝟭 _) (𝟭 _) where
  app f := f
  natL _ _ := rfl
  natR _ _ := rfl

/-- Vertical composition of squares. -/
def vComp {F' : C' ⥤ C''} {G' : D' ⥤ D''} (s : Square P Q F G) (t : Square Q R F' G') :
    Square P R (F ⋙ F') (G ⋙ G') where
  app f := t.app (s.app f)
  natL α f := (congrArg t.app (s.natL α f)).trans (t.natL _ _)
  natR f α := (congrArg t.app (s.natR f α)).trans (t.natR _ _)

@[simp] theorem id_app {c : C} {d : D} (f : P.app c d) : (id P).app f = f := rfl

@[simp] theorem vComp_app {F' : C' ⥤ C''} {G' : D' ⥤ D''} (s : Square P Q F G)
    (t : Square Q R F' G') {c : C} {d : D} (f : P.app c d) :
    (s.vComp t).app f = t.app (s.app f) := rfl

@[simp] theorem id_vComp (s : Square P Q F G) : (id P).vComp s = s := rfl

@[simp] theorem vComp_id (s : Square P Q F G) : s.vComp (id Q) = s := rfl

@[simp] theorem app_mpLeft (s : Square P Q F G) {c c' : C} {d : D} (e : c = c')
    (f : P.app c d) : s.app (P.mpLeft e f) = Q.mpLeft (congrArg F.obj e) (s.app f) := by
  subst e; simp

@[simp] theorem app_mpRight (s : Square P Q F G) {c : C} {d d' : D} (f : P.app c d')
    (e : d = d') : s.app (P.mpRight f e) = Q.mpRight (s.app f) (congrArg G.obj e) := by
  subst e; simp

theorem vComp_assoc {S : Profunctor.{w'''} C''' D'''} {F' : C' ⥤ C''} {G' : D' ⥤ D''}
    {F'' : C'' ⥤ C'''} {G'' : D'' ⥤ D'''}
    (s : Square P Q F G) (t : Square Q R F' G') (u : Square R S F'' G'') :
    (s.vComp t).vComp u = s.vComp (t.vComp u) := rfl

/-- Transport a square along equalities of its boundary functors. -/
def cast {F' : C ⥤ C'} {G' : D ⥤ D'} (hF : F = F') (hG : G = G') (s : Square P Q F G) :
    Square P Q F' G' where
  app {c d} f :=
    Q.mpLeft (congrArg (·.obj c) hF) (Q.mpRight (s.app f) (congrArg (·.obj d) hG).symm)
  natL α f := by subst hF hG; simpa using s.natL α f
  natR f α := by subst hF hG; simpa using s.natR f α

theorem cast_app {F' : C ⥤ C'} {G' : D ⥤ D'} (hF : F = F') (hG : G = G') (s : Square P Q F G)
    {c : C} {d : D} (f : P.app c d) :
    (s.cast hF hG).app f =
      Q.mpLeft (congrArg (·.obj c) hF) (Q.mpRight (s.app f) (congrArg (·.obj d) hG).symm) :=
  rfl

@[simp] theorem cast_rfl (s : Square P Q F G) : s.cast rfl rfl = s := by
  ext; simp [cast_app]

@[simp] theorem cast_cast {F' F'' : C ⥤ C'} {G' G'' : D ⥤ D'} (hF : F = F') (hG : G = G')
    (hF' : F' = F'') (hG' : G' = G'') (s : Square P Q F G) :
    (s.cast hF hG).cast hF' hG' = s.cast (hF.trans hF') (hG.trans hG') := by
  subst hF hG hF' hG'; simp

/-- Squares `P ⇒ Q` with boundary `F, G` are natural transformations `P ⟶ Q.whiskerLeft₂ F G`
(this requires `P` and `Q` to live in the same universe). -/
def homEquiv {Q : Profunctor.{w} C' D'} : Square P Q F G ≃ (P ⟶ Q.whiskerLeft₂ F G) where
  toFun s :=
    { app c :=
        { app d := TypeCat.ofHom (s.app (c := c) (d := unop d))
          naturality _ _ α :=
            TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun f => s.natR f α.unop)) }
      naturality _ _ α := by ext d f; exact s.natL α f }
  invFun α :=
    { app {c d} f := (α.app c).app (op d) f
      natL β f := ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality β) _) f
      natR f β := ConcreteCategory.congr_hom ((α.app _).naturality β.op) f }
  left_inv _ := rfl
  right_inv _ := rfl

end Square

end Square

section NullaryCell

variable {A B C D C' D' : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* C'] [Category* D']

/-- A cell with nullary source the category `A` and target `Q`, with the functor `F` on the
source side and `G` on the target side: a natural family of elements `Q (F a) (G a)`. -/
structure NullaryCell (Q : Profunctor.{w} C D) (F : A ⥤ C) (G : A ⥤ D) where
  /-- The components of the cell. -/
  app (a : A) : Q.app (F.obj a) (G.obj a)
  naturality {a a' : A} (α : a ⟶ a') : Q.mapL (F.map α) (app a) = Q.mapR (G.map α) (app a')

namespace NullaryCell

variable {Q : Profunctor.{w} C D} {R : Profunctor.{w'} C' D'} {F : A ⥤ C} {G : A ⥤ D}

@[ext]
theorem ext {ν μ : NullaryCell Q F G} (h : ∀ a, ν.app a = μ.app a) : ν = μ := by
  cases ν; cases μ; congr; funext a; exact h a

/-- Postcompose a nullary cell with a square. -/
def vComp {F' : C ⥤ C'} {G' : D ⥤ D'} (ν : NullaryCell Q F G) (t : Square Q R F' G') :
    NullaryCell R (F ⋙ F') (G ⋙ G') where
  app a := t.app (ν.app a)
  naturality α := (t.natL _ _).symm.trans ((congrArg t.app (ν.naturality α)).trans (t.natR _ _))

/-- Precompose a nullary cell with a functor `K : B ⥤ A`. -/
def comap (K : B ⥤ A) (ν : NullaryCell Q F G) : NullaryCell Q (K ⋙ F) (K ⋙ G) where
  app b := ν.app (K.obj b)
  naturality α := ν.naturality (K.map α)

@[simp] theorem vComp_app {F' : C ⥤ C'} {G' : D ⥤ D'} (ν : NullaryCell Q F G)
    (t : Square Q R F' G') (a : A) : (ν.vComp t).app a = t.app (ν.app a) := rfl

@[simp] theorem comap_app (K : B ⥤ A) (ν : NullaryCell Q F G) (b : B) :
    (ν.comap K).app b = ν.app (K.obj b) := rfl

/-- Transport a nullary cell along equalities of its boundary functors. -/
def cast {F' : A ⥤ C} {G' : A ⥤ D} (hF : F = F') (hG : G = G') (ν : NullaryCell Q F G) :
    NullaryCell Q F' G' where
  app a := Q.mpLeft (congrArg (·.obj a) hF) (Q.mpRight (ν.app a) (congrArg (·.obj a) hG).symm)
  naturality α := by subst hF hG; simpa using ν.naturality α

theorem cast_app {F' : A ⥤ C} {G' : A ⥤ D} (hF : F = F') (hG : G = G')
    (ν : NullaryCell Q F G) (a : A) :
    (ν.cast hF hG).app a =
      Q.mpLeft (congrArg (·.obj a) hF) (Q.mpRight (ν.app a) (congrArg (·.obj a) hG).symm) :=
  rfl

@[simp] theorem cast_rfl (ν : NullaryCell Q F G) : ν.cast rfl rfl = ν := by
  ext; simp [cast_app]

@[simp] theorem cast_cast {F' F'' : A ⥤ C} {G' G'' : A ⥤ D} (hF : F = F') (hG : G = G')
    (hF' : F' = F'') (hG' : G' = G'') (ν : NullaryCell Q F G) :
    (ν.cast hF hG).cast hF' hG' = ν.cast (hF.trans hF') (hG.trans hG') := by
  subst hF hG hF' hG'; simp

end NullaryCell

end NullaryCell

section BinaryCell

variable {X Y Z X' Z' X₀ Y₀ Z₀ X'' Z'' : Type*}
  [Category* X] [Category* Y] [Category* Z] [Category* X'] [Category* Z']
  [Category* X₀] [Category* Y₀] [Category* Z₀] [Category* X''] [Category* Z'']

/-- A cell with binary source `P, Q` and target `R`, with the functor `F` on the source side
and `G` on the target side: a family of maps `P x y → Q y z → R (F x) (G z)`, natural in
`x` and `z` and a wedge in `y`. -/
structure BinaryCell (P : Profunctor.{w} X Y) (Q : Profunctor.{w'} Y Z)
    (R : Profunctor.{w''} X' Z') (F : X ⥤ X') (G : Z ⥤ Z') where
  /-- The components of the cell. -/
  app {x : X} {y : Y} {z : Z} : P.app x y → Q.app y z → R.app (F.obj x) (G.obj z)
  wedge {x : X} {y y' : Y} {z : Z} (f : P.app x y') (α : y ⟶ y') (g : Q.app y z) :
    app (P.mapR α f) g = app f (Q.mapL α g)
  natL {x x' : X} {y : Y} {z : Z} (α : x ⟶ x') (f : P.app x y) (g : Q.app y z) :
    app (P.mapL α f) g = R.mapL (F.map α) (app f g)
  natR {x : X} {y : Y} {z z' : Z} (f : P.app x y) (g : Q.app y z') (α : z ⟶ z') :
    app f (Q.mapR α g) = R.mapR (G.map α) (app f g)

namespace BinaryCell

variable {P : Profunctor.{w} X Y} {Q : Profunctor.{w'} Y Z} {R : Profunctor.{w''} X' Z'}
  {F : X ⥤ X'} {G : Z ⥤ Z'}

@[ext]
theorem ext {β γ : BinaryCell P Q R F G}
    (H : ∀ {x y z} (f : P.app x y) (g : Q.app y z), β.app f g = γ.app f g) : β = γ := by
  cases β; cases γ; congr; funext x y z f g; exact H f g

/-- Postcompose a binary cell with a square. -/
def vComp {R' : Profunctor.{w'''} X'' Z''} {F' : X' ⥤ X''} {G' : Z' ⥤ Z''}
    (β : BinaryCell P Q R F G) (t : Square R R' F' G') :
    BinaryCell P Q R' (F ⋙ F') (G ⋙ G') where
  app f g := t.app (β.app f g)
  wedge f α g := congrArg t.app (β.wedge f α g)
  natL α f g := (congrArg t.app (β.natL α f g)).trans (t.natL _ _)
  natR f g α := (congrArg t.app (β.natR f g α)).trans (t.natR _ _)

/-- Precompose a binary cell with a pair of squares sharing the middle functor `K`. -/
def precomp {P' : Profunctor.{w₁} X₀ Y₀} {Q' : Profunctor.{w₂} Y₀ Z₀}
    {K : Y₀ ⥤ Y} {F₀ : X₀ ⥤ X} {G₀ : Z₀ ⥤ Z}
    (s : Square P' P F₀ K) (s' : Square Q' Q K G₀) (β : BinaryCell P Q R F G) :
    BinaryCell P' Q' R (F₀ ⋙ F) (G₀ ⋙ G) where
  app f g := β.app (s.app f) (s'.app g)
  wedge f α g := by rw [s.natR, s'.natL, β.wedge]
  natL α f g := by rw [s.natL, β.natL]; rfl
  natR f g α := by rw [s'.natR, β.natR]; rfl

@[simp] theorem vComp_app {R' : Profunctor.{w'''} X'' Z''} {F' : X' ⥤ X''} {G' : Z' ⥤ Z''}
    (β : BinaryCell P Q R F G) (t : Square R R' F' G') {x : X} {y : Y} {z : Z}
    (f : P.app x y) (g : Q.app y z) : (β.vComp t).app f g = t.app (β.app f g) := rfl

@[simp] theorem precomp_app {P' : Profunctor.{w₁} X₀ Y₀} {Q' : Profunctor.{w₂} Y₀ Z₀}
    {K : Y₀ ⥤ Y} {F₀ : X₀ ⥤ X} {G₀ : Z₀ ⥤ Z}
    (s : Square P' P F₀ K) (s' : Square Q' Q K G₀) (β : BinaryCell P Q R F G)
    {x : X₀} {y : Y₀} {z : Z₀} (f : P'.app x y) (g : Q'.app y z) :
    (β.precomp s s').app f g = β.app (s.app f) (s'.app g) := rfl

@[simp] theorem app_mpLeft (β : BinaryCell P Q R F G) {x x' : X} {y : Y} {z : Z} (e : x = x')
    (f : P.app x y) (g : Q.app y z) :
    β.app (P.mpLeft e f) g = R.mpLeft (congrArg F.obj e) (β.app f g) := by
  subst e; simp

@[simp] theorem app_mpRight (β : BinaryCell P Q R F G) {x : X} {y : Y} {z z' : Z}
    (f : P.app x y) (g : Q.app y z') (e : z = z') :
    β.app f (Q.mpRight g e) = R.mpRight (β.app f g) (congrArg G.obj e) := by
  subst e; simp

/-- The wedge condition for transports: a transport in the middle variable moves from the
first argument to the second. -/
@[simp] theorem mpRight_app (β : BinaryCell P Q R F G) {x : X} {y y' : Y} {z : Z}
    (f : P.app x y') (e : y = y') (g : Q.app y z) :
    β.app (P.mpRight f e) g = β.app f (Q.mpLeft e g) :=
  β.wedge f (eqToHom e) g

/-- Transport a binary cell along equalities of its boundary functors. -/
def cast {F' : X ⥤ X'} {G' : Z ⥤ Z'} (hF : F = F') (hG : G = G') (β : BinaryCell P Q R F G) :
    BinaryCell P Q R F' G' where
  app {x _ z} f g :=
    R.mpLeft (congrArg (·.obj x) hF) (R.mpRight (β.app f g) (congrArg (·.obj z) hG).symm)
  wedge f α g := by rw [β.wedge]
  natL α f g := by subst hF hG; simpa using β.natL α f g
  natR f g α := by subst hF hG; simpa using β.natR f g α

theorem cast_app {F' : X ⥤ X'} {G' : Z ⥤ Z'} (hF : F = F') (hG : G = G')
    (β : BinaryCell P Q R F G) {x : X} {y : Y} {z : Z} (f : P.app x y) (g : Q.app y z) :
    (β.cast hF hG).app f g =
      R.mpLeft (congrArg (·.obj x) hF) (R.mpRight (β.app f g) (congrArg (·.obj z) hG).symm) :=
  rfl

@[simp] theorem cast_rfl (β : BinaryCell P Q R F G) : β.cast rfl rfl = β := by
  ext; simp [cast_app]

@[simp] theorem cast_cast {F' F'' : X ⥤ X'} {G' G'' : Z ⥤ Z'} (hF : F = F') (hG : G = G')
    (hF' : F' = F'') (hG' : G' = G'') (β : BinaryCell P Q R F G) :
    (β.cast hF hG).cast hF' hG' = β.cast (hF.trans hF') (hG.trans hG') := by
  subst hF hG hF' hG'; simp

end BinaryCell

end BinaryCell

section Comp

/-! ### Binary cells and composition of profunctors -/

variable {X Z : Type*} {Y : Type u} [Category* X] [Category* Y] [Category* Z]
  (P : Profunctor.{max u w} X Y) (Q : Profunctor.{max u w} Y Z)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The covariant action of a composite profunctor on a representative of the coend. -/
@[simp]
lemma comp_mapL_mk {x x' : X} (α : x ⟶ x') {z : Z} (y : Y) (f : P.app x y) (g : Q.app y z) :
    (P.comp Q).mapL α (Quot.mk _ ⟨y, f, g⟩) = Quot.mk _ ⟨y, P.mapL α f, g⟩ := by
  simp [chosenCoend.map_apply, Types.chosenCoend_def, mapL]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The contravariant action of a composite profunctor on a representative of the coend. -/
@[simp]
lemma comp_mapR_mk {x : X} {z z' : Z} (α : z ⟶ z') (y : Y) (f : P.app x y) (g : Q.app y z') :
    (P.comp Q).mapR α (Quot.mk _ ⟨y, f, g⟩) = Quot.mk _ ⟨y, f, Q.mapR α g⟩ := by
  simp [chosenCoend.map_apply, Types.chosenCoend_def, mapR]

end Comp

namespace BinaryCell

variable {X Z X' Z' : Type*} {Y : Type u}
  [Category* X] [Category* Y] [Category* Z] [Category* X'] [Category* Z']
  {P : Profunctor.{max u w} X Y} {Q : Profunctor.{max u w} Y Z}
  {R : Profunctor.{max u w} X' Z'} {F : X ⥤ X'} {G : Z ⥤ Z'}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] Types.chosenCoend_def chosenCoend.map_apply in
/-- Binary cells `P, Q ⇒ R` with boundary `F, G` are natural transformations out of the
composite profunctor, `P.comp Q ⟶ R.whiskerLeft₂ F G`. -/
def homEquiv : BinaryCell P Q R F G ≃ (P.comp Q ⟶ R.whiskerLeft₂ F G) where
  toFun β :=
    { app x :=
        { app z := TypeCat.ofHom <| Quot.lift (fun ⟨_, f, g⟩ ↦ β.app f g) <| by
            rintro _ _ ⟨α, f, g⟩
            exact β.wedge f α g
          naturality _ _ α := by
            ext ⟨_, f, g⟩
            simpa [mapR] using β.natR f g α.unop }
      naturality _ _ α := by
        ext z ⟨_, f, g⟩
        simpa [mapL] using β.natL α f g }
  invFun α :=
    { app {x y z} f g := (α.app x).app (op z) (Quot.mk _ ⟨y, f, g⟩)
      wedge {x _ _ z} f β g := congrArg ((α.app x).app (op z))
        (Quot.sound (Types.coendRel.mk (F := P.compDiagram Q x z) β (f, g)))
      natL {_ x' y z} β f g :=
        (congrArg ((α.app x').app (op z)) (comp_mapL_mk P Q β y f g).symm).trans
          (ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality β) (op z))
            (Quot.mk _ ⟨y, f, g⟩))
      natR {x y z _} f g β :=
        (congrArg ((α.app x).app (op z)) (comp_mapR_mk P Q β y f g).symm).trans
          (ConcreteCategory.congr_hom ((α.app x).naturality β.op) (Quot.mk _ ⟨y, f, g⟩)) }
  left_inv _ := rfl
  right_inv α := NatTrans.ext <| funext fun _ => NatTrans.ext <| funext fun _ =>
    TypeCat.Hom.ext <| TypeCat.Fun.ext <| funext fun q => Quot.inductionOn q fun _ => rfl

end BinaryCell

end CategoryTheory.Profunctor
