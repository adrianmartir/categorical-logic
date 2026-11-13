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

* A profunctor `P : Profunctor C D` is a functor `C ⥤ Dᵒᵖ ⥤ Type w`. Its elements are written
  `P.app d c` with `d : D` (the contravariant side) first and `c : C` (the covariant side)
  second; `P.mapL` acts on `d` and `P.mapR` on `c`.
* Whenever a cell has functors on its vertical boundary, the functor on the covariant side
  comes first and the one on the contravariant side second.

## Main definitions

* `Square P Q F G`: a cell with unary source, i.e. a natural map `P d c → Q (G d) (F c)`.
* `NullaryCell Q F G`: a cell with empty source over a category `A`, i.e. a natural family
  `Q (G a) (F a)`.
* `BinaryCell h k j F G`: a cell with source the composable pair `h, k`, i.e. a map
  `h x y → k y z → j (G x) (F z)` that is natural in `x, z` and dinatural (a wedge) in `y`.
* `Square.cast`, `NullaryCell.cast`, `BinaryCell.cast`: transport along equalities of the
  boundary functors.
* `Square.homEquiv`: squares correspond to natural transformations `P ⟶ Q.whiskerLeft₂ F G`.
* `BinaryCell.homEquiv`: binary cells `h, k ⇒ j` correspond to natural transformations
  `k.comp h ⟶ j.whiskerLeft₂ F G` out of mathlib's composite profunctor.
-/

@[expose] public section

namespace CategoryTheory.Profunctor

universe u w w' w'' w''' w₁ w₂

open Opposite Limits

section Square

variable {C D C' D' C'' D'' C''' D''' : Type*}
  [Category* C] [Category* D] [Category* C'] [Category* D']
  [Category* C''] [Category* D''] [Category* C'''] [Category* D''']

/-- A cell with unary source `P` and target `Q`, with the functor `F` on the covariant side and
`G` on the contravariant side: a natural transformation `P ⇒ Q(G, F)`. -/
structure Square (P : Profunctor.{w} C D) (Q : Profunctor.{w'} C' D')
    (F : C ⥤ C') (G : D ⥤ D') where
  /-- The components of the square. -/
  app {d : D} {c : C} : P.app d c → Q.app (G.obj d) (F.obj c)
  natL {d d' : D} {c : C} (α : d' ⟶ d) (f : P.app d c) :
    app (P.mapL α f) = Q.mapL (G.map α) (app f)
  natR {d : D} {c c' : C} (f : P.app d c) (α : c ⟶ c') :
    app (P.mapR α f) = Q.mapR (F.map α) (app f)

namespace Square

variable {P : Profunctor.{w} C D} {Q : Profunctor.{w'} C' D'} {R : Profunctor.{w''} C'' D''}
  {F : C ⥤ C'} {G : D ⥤ D'}

@[ext]
theorem ext {s t : Square P Q F G} (h : ∀ {d c} (f : P.app d c), s.app f = t.app f) : s = t := by
  cases s; cases t; congr; funext d c f; exact h f

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

@[simp] theorem id_app {d : D} {c : C} (f : P.app d c) : (id P).app f = f := rfl

@[simp] theorem vComp_app {F' : C' ⥤ C''} {G' : D' ⥤ D''} (s : Square P Q F G)
    (t : Square Q R F' G') {d : D} {c : C} (f : P.app d c) :
    (s.vComp t).app f = t.app (s.app f) := rfl

@[simp] theorem id_vComp (s : Square P Q F G) : (id P).vComp s = s := rfl

@[simp] theorem vComp_id (s : Square P Q F G) : s.vComp (id Q) = s := rfl

@[simp] theorem app_mpLeft (s : Square P Q F G) {d d' : D} {c : C} (e : d = d')
    (f : P.app d' c) : s.app (P.mpLeft e f) = Q.mpLeft (congrArg G.obj e) (s.app f) := by
  subst e; simp

@[simp] theorem app_mpRight (s : Square P Q F G) {d : D} {c c' : C} (f : P.app d c)
    (e : c = c') : s.app (P.mpRight f e) = Q.mpRight (s.app f) (congrArg F.obj e) := by
  subst e; simp

theorem vComp_assoc {S : Profunctor.{w'''} C''' D'''} {F' : C' ⥤ C''} {G' : D' ⥤ D''}
    {F'' : C'' ⥤ C'''} {G'' : D'' ⥤ D'''}
    (s : Square P Q F G) (t : Square Q R F' G') (u : Square R S F'' G'') :
    (s.vComp t).vComp u = s.vComp (t.vComp u) := rfl

/-- Transport a square along equalities of its boundary functors. -/
def cast {F' : C ⥤ C'} {G' : D ⥤ D'} (hF : F = F') (hG : G = G') (s : Square P Q F G) :
    Square P Q F' G' where
  app {d c} f :=
    Q.mpLeft (congrArg (·.obj d) hG).symm (Q.mpRight (s.app f) (congrArg (·.obj c) hF))
  natL α f := by subst hF hG; simpa using s.natL α f
  natR f α := by subst hF hG; simpa using s.natR f α

theorem cast_app {F' : C ⥤ C'} {G' : D ⥤ D'} (hF : F = F') (hG : G = G') (s : Square P Q F G)
    {d : D} {c : C} (f : P.app d c) :
    (s.cast hF hG).app f =
      Q.mpLeft (congrArg (·.obj d) hG).symm (Q.mpRight (s.app f) (congrArg (·.obj c) hF)) :=
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
        { app d := TypeCat.ofHom (s.app (d := unop d) (c := c))
          naturality _ _ α := TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun f => s.natL α.unop f)) }
      naturality _ _ α := by ext d f; exact s.natR f α }
  invFun α :=
    { app {d c} f := (α.app c).app (op d) f
      natL β f := ConcreteCategory.congr_hom ((α.app _).naturality β.op) f
      natR f β := ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality β) _) f }
  left_inv _ := rfl
  right_inv _ := rfl

end Square

end Square

section NullaryCell

variable {A B C D C' D' : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* C'] [Category* D']

/-- A cell with nullary source the category `A` and target `Q`, with the functor `F` on the
covariant side and `G` on the contravariant side: a natural family of elements
`Q (G a) (F a)`. -/
structure NullaryCell (Q : Profunctor.{w} C D) (F : A ⥤ C) (G : A ⥤ D) where
  /-- The components of the cell. -/
  app (a : A) : Q.app (G.obj a) (F.obj a)
  naturality {a a' : A} (α : a ⟶ a') : Q.mapR (F.map α) (app a) = Q.mapL (G.map α) (app a')

namespace NullaryCell

variable {Q : Profunctor.{w} C D} {R : Profunctor.{w'} C' D'} {F : A ⥤ C} {G : A ⥤ D}

@[ext]
theorem ext {ν μ : NullaryCell Q F G} (h : ∀ a, ν.app a = μ.app a) : ν = μ := by
  cases ν; cases μ; congr; funext a; exact h a

/-- Postcompose a nullary cell with a square. -/
def vComp {F' : C ⥤ C'} {G' : D ⥤ D'} (ν : NullaryCell Q F G) (t : Square Q R F' G') :
    NullaryCell R (F ⋙ F') (G ⋙ G') where
  app a := t.app (ν.app a)
  naturality α := (t.natR _ _).symm.trans ((congrArg t.app (ν.naturality α)).trans (t.natL _ _))

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
  app a := Q.mpLeft (congrArg (·.obj a) hG).symm (Q.mpRight (ν.app a) (congrArg (·.obj a) hF))
  naturality α := by subst hF hG; simpa using ν.naturality α

theorem cast_app {F' : A ⥤ C} {G' : A ⥤ D} (hF : F = F') (hG : G = G')
    (ν : NullaryCell Q F G) (a : A) :
    (ν.cast hF hG).app a =
      Q.mpLeft (congrArg (·.obj a) hG).symm (Q.mpRight (ν.app a) (congrArg (·.obj a) hF)) :=
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

/-- A cell with binary source `h, k` and target `j`, with the functor `F` on the covariant side
and `G` on the contravariant side: a family of maps `h x y → k y z → j (G x) (F z)`, natural in
`x` and `z` and a wedge in `y`. -/
structure BinaryCell (h : Profunctor.{w} Y X) (k : Profunctor.{w'} Z Y)
    (j : Profunctor.{w''} Z' X') (F : Z ⥤ Z') (G : X ⥤ X') where
  /-- The components of the cell. -/
  app {x : X} {y : Y} {z : Z} : h.app x y → k.app y z → j.app (G.obj x) (F.obj z)
  wedge {x : X} {y y' : Y} {z : Z} (f : h.app x y) (α : y ⟶ y') (g : k.app y' z) :
    app (h.mapR α f) g = app f (k.mapL α g)
  natL {x x' : X} {y : Y} {z : Z} (α : x' ⟶ x) (f : h.app x y) (g : k.app y z) :
    app (h.mapL α f) g = j.mapL (G.map α) (app f g)
  natR {x : X} {y : Y} {z z' : Z} (f : h.app x y) (g : k.app y z) (α : z ⟶ z') :
    app f (k.mapR α g) = j.mapR (F.map α) (app f g)

namespace BinaryCell

variable {h : Profunctor.{w} Y X} {k : Profunctor.{w'} Z Y} {j : Profunctor.{w''} Z' X'}
  {F : Z ⥤ Z'} {G : X ⥤ X'}

@[ext]
theorem ext {β γ : BinaryCell h k j F G}
    (H : ∀ {x y z} (f : h.app x y) (g : k.app y z), β.app f g = γ.app f g) : β = γ := by
  cases β; cases γ; congr; funext x y z f g; exact H f g

/-- Postcompose a binary cell with a square. -/
def vComp {j' : Profunctor.{w'''} Z'' X''} {F' : Z' ⥤ Z''} {G' : X' ⥤ X''}
    (β : BinaryCell h k j F G) (t : Square j j' F' G') :
    BinaryCell h k j' (F ⋙ F') (G ⋙ G') where
  app f g := t.app (β.app f g)
  wedge f α g := congrArg t.app (β.wedge f α g)
  natL α f g := (congrArg t.app (β.natL α f g)).trans (t.natL _ _)
  natR f g α := (congrArg t.app (β.natR f g α)).trans (t.natR _ _)

/-- Precompose a binary cell with a pair of squares sharing the middle functor `K`. -/
def precomp {h' : Profunctor.{w₁} Y₀ X₀} {k' : Profunctor.{w₂} Z₀ Y₀}
    {K : Y₀ ⥤ Y} {F₀ : Z₀ ⥤ Z} {G₀ : X₀ ⥤ X}
    (s : Square h' h K G₀) (s' : Square k' k F₀ K) (β : BinaryCell h k j F G) :
    BinaryCell h' k' j (F₀ ⋙ F) (G₀ ⋙ G) where
  app f g := β.app (s.app f) (s'.app g)
  wedge f α g := by rw [s.natR, s'.natL, β.wedge]
  natL α f g := by rw [s.natL, β.natL]; rfl
  natR f g α := by rw [s'.natR, β.natR]; rfl

@[simp] theorem vComp_app {j' : Profunctor.{w'''} Z'' X''} {F' : Z' ⥤ Z''} {G' : X' ⥤ X''}
    (β : BinaryCell h k j F G) (t : Square j j' F' G') {x : X} {y : Y} {z : Z}
    (f : h.app x y) (g : k.app y z) : (β.vComp t).app f g = t.app (β.app f g) := rfl

@[simp] theorem precomp_app {h' : Profunctor.{w₁} Y₀ X₀} {k' : Profunctor.{w₂} Z₀ Y₀}
    {K : Y₀ ⥤ Y} {F₀ : Z₀ ⥤ Z} {G₀ : X₀ ⥤ X}
    (s : Square h' h K G₀) (s' : Square k' k F₀ K) (β : BinaryCell h k j F G)
    {x : X₀} {y : Y₀} {z : Z₀} (f : h'.app x y) (g : k'.app y z) :
    (β.precomp s s').app f g = β.app (s.app f) (s'.app g) := rfl

@[simp] theorem app_mpLeft (β : BinaryCell h k j F G) {x x' : X} {y : Y} {z : Z} (e : x = x')
    (f : h.app x' y) (g : k.app y z) :
    β.app (h.mpLeft e f) g = j.mpLeft (congrArg G.obj e) (β.app f g) := by
  subst e; simp

@[simp] theorem app_mpRight (β : BinaryCell h k j F G) {x : X} {y : Y} {z z' : Z}
    (f : h.app x y) (g : k.app y z) (e : z = z') :
    β.app f (k.mpRight g e) = j.mpRight (β.app f g) (congrArg F.obj e) := by
  subst e; simp

/-- The wedge condition for transports: a transport in the middle variable moves from the
first argument to the second. -/
@[simp] theorem mpRight_app (β : BinaryCell h k j F G) {x : X} {y y' : Y} {z : Z}
    (f : h.app x y) (e : y = y') (g : k.app y' z) :
    β.app (h.mpRight f e) g = β.app f (k.mpLeft e g) :=
  β.wedge f (eqToHom e) g

/-- Transport a binary cell along equalities of its boundary functors. -/
def cast {F' : Z ⥤ Z'} {G' : X ⥤ X'} (hF : F = F') (hG : G = G') (β : BinaryCell h k j F G) :
    BinaryCell h k j F' G' where
  app {x _ z} f g :=
    j.mpLeft (congrArg (·.obj x) hG).symm (j.mpRight (β.app f g) (congrArg (·.obj z) hF))
  wedge f α g := by rw [β.wedge]
  natL α f g := by subst hF hG; simpa using β.natL α f g
  natR f g α := by subst hF hG; simpa using β.natR f g α

theorem cast_app {F' : Z ⥤ Z'} {G' : X ⥤ X'} (hF : F = F') (hG : G = G')
    (β : BinaryCell h k j F G) {x : X} {y : Y} {z : Z} (f : h.app x y) (g : k.app y z) :
    (β.cast hF hG).app f g =
      j.mpLeft (congrArg (·.obj x) hG).symm (j.mpRight (β.app f g) (congrArg (·.obj z) hF)) :=
  rfl

@[simp] theorem cast_rfl (β : BinaryCell h k j F G) : β.cast rfl rfl = β := by
  ext; simp [cast_app]

@[simp] theorem cast_cast {F' F'' : Z ⥤ Z'} {G' G'' : X ⥤ X'} (hF : F = F') (hG : G = G')
    (hF' : F' = F'') (hG' : G' = G'') (β : BinaryCell h k j F G) :
    (β.cast hF hG).cast hF' hG' = β.cast (hF.trans hF') (hG.trans hG') := by
  subst hF hG hF' hG'; simp

end BinaryCell

end BinaryCell

section Comp

/-! ### Binary cells and composition of profunctors -/

variable {X Z : Type*} {Y : Type u} [Category* X] [Category* Y] [Category* Z]
  (h : Profunctor.{max u w} Y X) (k : Profunctor.{max u w} Z Y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The covariant action of a composite profunctor on a representative of the coend. -/
@[simp]
lemma comp_map_app_mk {z z' : Z} (α : z ⟶ z') (x : Xᵒᵖ) (y : Y) (g : k.app y z)
    (f : h.app x.unop y) :
    ((k.comp h).map α).app x (Quot.mk _ ⟨y, g, f⟩) = Quot.mk _ ⟨y, k.mapR α g, f⟩ := by
  simp [chosenCoend.map_apply, Types.chosenCoend_def, mapR]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The contravariant action of a composite profunctor on a representative of the coend. -/
@[simp]
lemma comp_obj_map_mk (z : Z) {x x' : Xᵒᵖ} (α : x ⟶ x') (y : Y) (g : k.app y z)
    (f : h.app x.unop y) :
    ((k.comp h).obj z).map α (Quot.mk _ ⟨y, g, f⟩) = Quot.mk _ ⟨y, g, h.mapL α.unop f⟩ := by
  simp [chosenCoend.map_apply, Types.chosenCoend_def, mapL]

end Comp

namespace BinaryCell

variable {X Z X' Z' : Type*} {Y : Type u}
  [Category* X] [Category* Y] [Category* Z] [Category* X'] [Category* Z']
  {h : Profunctor.{max u w} Y X} {k : Profunctor.{max u w} Z Y}
  {j : Profunctor.{max u w} Z' X'} {F : Z ⥤ Z'} {G : X ⥤ X'}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] Types.chosenCoend_def chosenCoend.map_apply in
/-- Binary cells `h, k ⇒ j` with boundary `F, G` are natural transformations out of the
composite profunctor, `k.comp h ⟶ j.whiskerLeft₂ F G`. Note that mathlib composes profunctors
in the opposite order to the one in which `BinaryCell` lists its source. -/
def homEquiv : BinaryCell h k j F G ≃ (k.comp h ⟶ j.whiskerLeft₂ F G) where
  toFun β :=
    { app z :=
        { app x := TypeCat.ofHom <| Quot.lift (fun ⟨_, g, f⟩ ↦ β.app f g) <| by
            rintro _ _ ⟨α, g, f⟩
            exact (β.wedge f α g).symm
          naturality _ _ α := by
            ext ⟨_, g, f⟩
            simpa [mapL] using β.natL α.unop f g }
      naturality _ _ α := by
        ext x ⟨_, g, f⟩
        simpa [mapR] using β.natR f g α }
  invFun α :=
    { app {x y z} f g := (α.app z).app (op x) (Quot.mk _ ⟨y, g, f⟩)
      wedge {x _ _ z} f β g := congrArg ((α.app z).app (op x))
        (Quot.sound (Types.coendRel.mk (F := k.compDiagram h z x) β (g, f))).symm
      natL {_ x' y z} β f g :=
        (congrArg ((α.app z).app (op x')) (comp_obj_map_mk h k z β.op y g f).symm).trans
          (ConcreteCategory.congr_hom ((α.app z).naturality β.op) (Quot.mk _ ⟨y, g, f⟩))
      natR {x y _ z'} f g β :=
        (congrArg ((α.app z').app (op x)) (comp_map_app_mk h k β (op x) y g f).symm).trans
          (ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality β) (op x))
            (Quot.mk _ ⟨y, g, f⟩)) }
  left_inv _ := rfl
  right_inv α := NatTrans.ext <| funext fun _ => NatTrans.ext <| funext fun _ =>
    TypeCat.Hom.ext <| TypeCat.Fun.ext <| funext fun q => Quot.inductionOn q fun _ => rfl

end BinaryCell

end CategoryTheory.Profunctor
