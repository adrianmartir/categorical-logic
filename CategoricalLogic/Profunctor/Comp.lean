/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Profunctor.Square

/-!
# Squares and composition of profunctors

Elementwise API for mathlib's composite `P.comp Q` (a chosen coend, i.e. a `Quot`) and the
horizontal composition of squares with arbitrary vertical boundaries.

## Main definitions

* `Profunctor.compMk f g`: the element of `(P.comp Q).app x z` represented by
  `f : P.app x y`, `g : Q.app y z`; `compMk_wedge` is the coend relation, `comp_induction` the
  induction principle and `compLift` the recursor (into a type, by `Quot.lift`).
* `Square.hcomp s t : Square (P.comp Q) (P'.comp Q') F H` for `s : Square P P' F G` and
  `t : Square Q Q' G H`.
* `Square.homMap F : Square Profunctor.id Profunctor.id F F`: the identity square on a functor.
* `Square.ofHom α`: the square with identity boundary of a morphism of profunctors.
* `Square.ofBinary β`, `Square.binaryEquiv`: squares out of a composite are binary cells.
* `Square.ofNullary ν`, `Square.nullaryEquiv`: squares out of `Profunctor.id` are nullary cells
  (the Yoneda lemma).
* `Square.assoc`, `Square.leftUnitor`, `Square.rightUnitor`: the structure isomorphisms of
  mathlib's composition, as squares, with `rfl` lemmas on representatives.
-/

@[expose] public section

namespace CategoryTheory.Profunctor

universe u w

open Opposite Limits

section CompMk

variable {X Z : Type*} {Y : Type u} [Category* X] [Category* Y] [Category* Z]
  {P : Profunctor.{max u w} X Y} {Q : Profunctor.{max u w} Y Z}

/-- The element of the composite represented by a composable pair. -/
def compMk {x : X} {y : Y} {z : Z} (f : P.app x y) (g : Q.app y z) : (P.comp Q).app x z :=
  Quot.mk _ ⟨y, f, g⟩

/-- The coend relation: a morphism in the middle variable can be moved across. -/
theorem compMk_wedge {x : X} {y y' : Y} {z : Z} (f : P.app x y') (α : y ⟶ y')
    (g : Q.app y z) : compMk (P.mapR α f) g = compMk f (Q.mapL α g) :=
  Quot.sound (Types.coendRel.mk (F := P.compDiagram Q x z) α (f, g))

/-- Induction principle for elements of a composite. -/
@[elab_as_elim]
theorem comp_induction {x : X} {z : Z} {motive : (P.comp Q).app x z → Prop}
    (h : ∀ (y : Y) (f : P.app x y) (g : Q.app y z), motive (compMk f g))
    (q : (P.comp Q).app x z) : motive q :=
  Quot.ind (fun ⟨y, f, g⟩ => h y f g) q

/-- Two maps out of a composite agree if they agree on representatives. -/
theorem comp_funext {x : X} {z : Z} {T : Sort*} {φ ψ : (P.comp Q).app x z → T}
    (h : ∀ (y : Y) (f : P.app x y) (g : Q.app y z), φ (compMk f g) = ψ (compMk f g)) :
    φ = ψ :=
  funext fun q => by induction q using comp_induction with | h y f g => exact h y f g

/-- The recursor for elements of a composite: a function of composable pairs that is a wedge
in the middle variable. -/
def compLift {x : X} {z : Z} {T : Sort*} (φ : ∀ {y : Y}, P.app x y → Q.app y z → T)
    (wedge : ∀ {y y' : Y} (f : P.app x y') (α : y ⟶ y') (g : Q.app y z),
      φ (P.mapR α f) g = φ f (Q.mapL α g)) :
    (P.comp Q).app x z → T :=
  Quot.lift (fun ⟨_, f, g⟩ => φ f g) (by rintro _ _ ⟨α, f, g⟩; exact wedge f α g)

@[simp] theorem compLift_compMk {x : X} {y : Y} {z : Z} {T : Sort*}
    (φ : ∀ {y : Y}, P.app x y → Q.app y z → T) (wedge) (f : P.app x y) (g : Q.app y z) :
    compLift φ wedge (compMk f g) = φ f g := rfl

@[simp] theorem comp_mapL_compMk {x x' : X} (α : x ⟶ x') {y : Y} {z : Z} (f : P.app x y)
    (g : Q.app y z) : (P.comp Q).mapL α (compMk f g) = compMk (P.mapL α f) g :=
  comp_mapL_mk P Q α y f g

@[simp] theorem comp_mapR_compMk {x : X} {y : Y} {z z' : Z} (α : z ⟶ z') (f : P.app x y)
    (g : Q.app y z') : (P.comp Q).mapR α (compMk f g) = compMk f (Q.mapR α g) :=
  comp_mapR_mk P Q α y f g

end CompMk

/-- Transports are heterogeneously equal to the identity. -/
theorem mpRight_heq {C D : Type*} [Category* C] [Category* D] (H : Profunctor.{w} C D)
    {c : C} {d d' : D} (e : H.app c d') (h : d = d') : H.mpRight e h ≍ e := by
  subst h; simp

/-- Transports are heterogeneously equal to the identity. -/
theorem mpLeft_heq {C D : Type*} [Category* C] [Category* D] (H : Profunctor.{w} C D)
    {c c' : C} {d : D} (h : c = c') (e : H.app c d) : H.mpLeft h e ≍ e := by
  subst h; simp

namespace Square

section HComp

variable {X Y Z X' Y' Z' X'' Y'' Z'' : Type u}
  [Category* X] [Category* Y] [Category* Z] [Category* X'] [Category* Y'] [Category* Z']
  [Category* X''] [Category* Y''] [Category* Z'']
  {P : Profunctor.{max u w} X Y} {Q : Profunctor.{max u w} Y Z}
  {P' : Profunctor.{max u w} X' Y'} {Q' : Profunctor.{max u w} Y' Z'}
  {P'' : Profunctor.{max u w} X'' Y''} {Q'' : Profunctor.{max u w} Y'' Z''}
  {F : X ⥤ X'} {G : Y ⥤ Y'} {H : Z ⥤ Z'}

/-- Horizontal composition of squares, along a common vertical boundary `G`. -/
def hcomp (s : Square P P' F G) (t : Square Q Q' G H) :
    Square (P.comp Q) (P'.comp Q') F H where
  app := compLift (fun f g => compMk (s.app f) (t.app g)) fun f α g => by
    rw [s.natR, t.natL, compMk_wedge]
  natL α q := by induction q using comp_induction with | h _ f g => simp [s.natL]
  natR q α := by induction q using comp_induction with | h _ f g => simp [t.natR]

@[simp] theorem hcomp_app_compMk (s : Square P P' F G) (t : Square Q Q' G H) {x : X} {y : Y}
    {z : Z} (f : P.app x y) (g : Q.app y z) :
    (hcomp s t).app (compMk f g) = compMk (s.app f) (t.app g) := rfl

theorem hcomp_id : hcomp (Square.id P) (Square.id Q) = Square.id (P.comp Q) :=
  Square.ext fun q => by induction q using comp_induction with | h => rfl

theorem hcomp_vComp {F' : X' ⥤ X''} {G' : Y' ⥤ Y''} {H' : Z' ⥤ Z''}
    (s : Square P P' F G) (t : Square Q Q' G H) (s' : Square P' P'' F' G')
    (t' : Square Q' Q'' G' H') :
    hcomp (s.vComp s') (t.vComp t') = (hcomp s t).vComp (hcomp s' t') :=
  Square.ext fun q => by induction q using comp_induction with | h => rfl

end HComp

section Hom

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']

/-- The identity square on a functor: the action of `F` on morphisms. -/
def homMap (F : C ⥤ D) : Square (Profunctor.id (C := C)) (Profunctor.id (C := D)) F F where
  app f := F.map f
  natL α f := F.map_comp f α
  natR f α := F.map_comp α f

@[simp] theorem homMap_app (F : C ⥤ D) {c c' : C} (f : c' ⟶ c) :
    (homMap F).app (c := c) (d := c') f = F.map f := rfl

theorem homMap_id : homMap (𝟭 C) = Square.id _ := rfl

theorem homMap_comp (F : C ⥤ D) (G : D ⥤ C') :
    homMap (F ⋙ G) = (homMap F).vComp (homMap G) := rfl

/-- The square with identity boundaries given by a morphism of profunctors. -/
def ofHom {P Q : Profunctor.{w} C D} (α : P ⟶ Q) : Square P Q (𝟭 C) (𝟭 D) where
  app {c d} f := (α.app c).app (op d) f
  natL β f := ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality β) _) f
  natR f β := ConcreteCategory.congr_hom ((α.app _).naturality β.op) f

@[simp] theorem ofHom_app {P Q : Profunctor.{w} C D} (α : P ⟶ Q) {c : C} {d : D}
    (f : P.app c d) : (ofHom α).app f = (α.app c).app (op d) f := rfl

end Hom

section Nullary

variable {A C D : Type*} [Category* A] [Category* C] [Category* D] {Q : Profunctor.{w} C D}
  {F : A ⥤ C} {G : A ⥤ D}

/-- The square out of the identity profunctor corresponding to a nullary cell. -/
def ofNullary (ν : NullaryCell Q F G) : Square Profunctor.id Q F G where
  app {c d} (f : d ⟶ c) := Q.mapR (G.map f) (ν.app c)
  natL {c c' d} α (f : d ⟶ c) := by
    change Q.mapR (G.map (f ≫ α)) (ν.app c') = Q.mapL (F.map α) (Q.mapR (G.map f) (ν.app c))
    rw [G.map_comp f α, Q.mapR_comp, ← ν.naturality α, ← Q.mapL_mapR_comm]
  natR {c d d'} (f : d' ⟶ c) α := by
    change Q.mapR (G.map (α ≫ f)) (ν.app c) = Q.mapR (G.map α) (Q.mapR (G.map f) (ν.app c))
    rw [G.map_comp α f, Q.mapR_comp]

@[simp] theorem ofNullary_app (ν : NullaryCell Q F G) {c d : A} (f : d ⟶ c) :
    (ofNullary ν).app f = Q.mapR (G.map f) (ν.app c) := rfl

/-- The nullary cell underlying a square out of the identity profunctor (Yoneda lemma). -/
def toNullary (s : Square Profunctor.id Q F G) : NullaryCell Q F G where
  app a := s.app (𝟙 a)
  naturality {a a'} α :=
    (s.natL α (𝟙 a)).symm.trans ((congrArg s.app ((Category.id_comp α).trans
      (Category.comp_id α).symm)).trans (s.natR (𝟙 a') α))

/-- Squares out of the identity profunctor are nullary cells. -/
def nullaryEquiv : Square Profunctor.id Q F G ≃ NullaryCell Q F G where
  toFun := toNullary
  invFun := ofNullary
  left_inv s := Square.ext fun {c d} (f : d ⟶ c) =>
    (s.natR (𝟙 c) f).symm.trans (congrArg s.app (Category.comp_id f))
  right_inv ν := NullaryCell.ext fun a => by simp [toNullary]

end Nullary

section Binary

variable {X Z X' Z' : Type*} {Y : Type u}
  [Category* X] [Category* Y] [Category* Z] [Category* X'] [Category* Z']
  {P : Profunctor.{max u w} X Y} {Q : Profunctor.{max u w} Y Z}
  {R : Profunctor.{max u w} X' Z'} {F : X ⥤ X'} {G : Z ⥤ Z'}

/-- The square out of the composite corresponding to a binary cell. -/
def ofBinary (β : BinaryCell P Q R F G) : Square (P.comp Q) R F G where
  app := compLift β.app β.wedge
  natL α q := by induction q using comp_induction with | h _ f g => simp [β.natL]
  natR q α := by induction q using comp_induction with | h _ f g => simp [β.natR]

@[simp] theorem ofBinary_app_compMk (β : BinaryCell P Q R F G) {x : X} {y : Y} {z : Z}
    (f : P.app x y) (g : Q.app y z) : (ofBinary β).app (compMk f g) = β.app f g := rfl

/-- The binary cell underlying a square out of a composite. -/
def toBinary (s : Square (P.comp Q) R F G) : BinaryCell P Q R F G where
  app f g := s.app (compMk f g)
  wedge f α g := congrArg s.app (compMk_wedge f α g)
  natL α f g := (congrArg s.app (comp_mapL_compMk α f g).symm).trans (s.natL _ _)
  natR f g α := (congrArg s.app (comp_mapR_compMk α f g).symm).trans (s.natR _ _)

/-- Congruence for a square out of a composite, applied to a representative. -/
theorem app_compMk_congr (s : Square (P.comp Q) R F G) {x : X} {y y' : Y} {z z' : Z}
    (hy : y = y') (hz : z = z') {f : P.app x y} {f' : P.app x y'} {g : Q.app y z}
    {g' : Q.app y' z'} (hf : f ≍ f') (hg : g ≍ g') : s.app (compMk f g) ≍ s.app (compMk f' g') := by
  subst hy hz; cases hf; cases hg; rfl

/-- Squares out of a composite are binary cells. -/
def binaryEquiv : Square (P.comp Q) R F G ≃ BinaryCell P Q R F G where
  toFun := toBinary
  invFun := ofBinary
  left_inv _ := Square.ext fun q => by induction q using comp_induction with | h => rfl
  right_inv _ := rfl

end Binary

section Cast

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {P : Profunctor.{w} C D} {Q : Profunctor.{w} C' D'}

/-- An equation with a transported square is a family of heterogeneous equalities. -/
theorem eq_cast_iff {F F' : C ⥤ C'} {G G' : D ⥤ D'} {s : Square P Q F' G'}
    {t : Square P Q F G} (hF : F = F') (hG : G = G') :
    s = t.cast hF hG ↔ ∀ {c : C} {d : D} (f : P.app c d), s.app f ≍ t.app f := by
  subst hF hG
  rw [cast_rfl]
  exact ⟨fun h _ _ f => h ▸ HEq.rfl, fun h => Square.ext fun f => eq_of_heq (h f)⟩

theorem cast_app_heq {F F' : C ⥤ C'} {G G' : D ⥤ D'} (s : Square P Q F G) (hF : F = F')
    (hG : G = G') {c : C} {d : D} (f : P.app c d) : (s.cast hF hG).app f ≍ s.app f := by
  subst hF hG; rw [cast_rfl]

/-- Congruence for the components of a square, along an equality in the second variable. -/
theorem app_congr_heq {F : C ⥤ C'} {G : D ⥤ D'} (s : Square P Q F G) {c : C} {d d' : D}
    (h : d = d') {x : P.app c d} {y : P.app c d'} (hxy : x ≍ y) : s.app x ≍ s.app y := by
  subst h; cases hxy; rfl

end Cast

end Square

end CategoryTheory.Profunctor
