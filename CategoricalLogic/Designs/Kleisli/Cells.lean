/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import Mathlib.CategoryTheory.Profunctor.Bicategory
public import CategoricalLogic.Profunctor.Square

/-!
# Elementwise constructors for natural transformations of profunctors

Helpers to build morphisms out of composites of profunctors (coends) from elementwise data, and
the companion `F.toProfunctor` of a functor (`(F.toProfunctor).app c d = (d ⟶ F.obj c)`).

* `Profunctor.compDesc β : P.comp Q ⟶ R` from a binary cell with identity boundary, computing by
  `rfl` on representatives (`compDesc_mk`).
* `Profunctor.ofSquare s : P ⟶ Q` from a square with identity boundary.
* `Profunctor.comp_hom_ext`: morphisms out of a composite are determined on representatives.
* `Functor.companionMap`, `Functor.compCompanion`: functoriality of companions.
-/

@[expose] public section

namespace CategoryTheory

universe u

open Opposite Limits

namespace Profunctor

variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]

/-- A natural transformation out of a composite from a binary cell with identity boundary. -/
def compDesc {P : Profunctor.{u} C D} {Q : Profunctor.{u} D E} {R : Profunctor.{u} C E}
    (β : BinaryCell P Q R (𝟭 C) (𝟭 E)) : P.comp Q ⟶ R :=
  BinaryCell.homEquiv β

@[simp]
theorem compDesc_mk {P : Profunctor.{u} C D} {Q : Profunctor.{u} D E} {R : Profunctor.{u} C E}
    (β : BinaryCell P Q R (𝟭 C) (𝟭 E)) {c : C} {d : D} {e : E} (p : P.app c d)
    (q : Q.app d e) :
    ((compDesc β).app c).app (op e) (Quot.mk _ ⟨d, p, q⟩) = β.app p q :=
  rfl

/-- A natural transformation from a square with identity boundary. -/
def ofSquare {P Q : Profunctor.{u} C D} (s : Square P Q (𝟭 C) (𝟭 D)) : P ⟶ Q :=
  Square.homEquiv s

@[simp]
theorem ofSquare_app {P Q : Profunctor.{u} C D} (s : Square P Q (𝟭 C) (𝟭 D)) {c : C} {d : D}
    (p : P.app c d) : ((ofSquare s).app c).app (op d) p = s.app p :=
  rfl

/-- Morphisms out of a composite of profunctors agree if they agree on representatives. -/
theorem comp_hom_ext {P : Profunctor.{u} C D} {Q : Profunctor.{u} D E} {R : Profunctor.{u} C E}
    {f g : P.comp Q ⟶ R}
    (h : ∀ (c : C) (d : D) (e : E) (p : P.app c d) (q : Q.app d e),
      (f.app c).app (op e) (Quot.mk _ ⟨d, p, q⟩) = (g.app c).app (op e) (Quot.mk _ ⟨d, p, q⟩)) :
    f = g :=
  NatTrans.ext <| funext fun c => NatTrans.ext <| funext fun e =>
    TypeCat.Hom.ext <| TypeCat.Fun.ext <| funext fun x =>
      Quot.inductionOn x fun ⟨d, p, q⟩ => h c d e.unop p q

/-- Morphisms of profunctors agree if they agree on elements. -/
theorem hom_ext' {P Q : Profunctor.{u} C D} {f g : P ⟶ Q}
    (h : ∀ (c : C) (d : D) (p : P.app c d), (f.app c).app (op d) p = (g.app c).app (op d) p) :
    f = g :=
  NatTrans.ext <| funext fun c => NatTrans.ext <| funext fun d =>
    TypeCat.Hom.ext <| TypeCat.Fun.ext <| funext fun p => h c d.unop p

theorem app_mapL {P Q : Profunctor.{u} C D} (α : P ⟶ Q) {c c' : C} (f : c ⟶ c') {d : D}
    (p : P.app c d) : (α.app c').app (op d) (P.mapL f p) = Q.mapL f ((α.app c).app (op d) p) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality f) (op d)) p

theorem app_mapR {P Q : Profunctor.{u} C D} (α : P ⟶ Q) {c : C} {d d' : D} (g : d ⟶ d')
    (p : P.app c d') : (α.app c).app (op d) (P.mapR g p) = Q.mapR g ((α.app c).app (op d') p) :=
  ConcreteCategory.congr_hom ((α.app c).naturality g.op) p

/-! ### Companions -/

@[simp] theorem toProfunctor_mapL (F : C ⥤ D) {c c' : C} (f : c ⟶ c') {d : D}
    (g : F.toProfunctor.app c d) : F.toProfunctor.mapL f g = g ≫ F.map f := rfl

@[simp] theorem toProfunctor_mapR (F : C ⥤ D) {d d' : D} (g : d ⟶ d') {c : C}
    (h : F.toProfunctor.app c d') : F.toProfunctor.mapR g h = g ≫ h := rfl

section Aux



theorem companion_aux_map {F G : C ⥤ D} (α : F ⟶ G) {c c' : C} {d : D} (β : c ⟶ c')
    (x : d ⟶ F.obj c) : (x ≫ F.map β) ≫ α.app c' = (x ≫ α.app c) ≫ G.map β := by
  simp

theorem companion_aux_wedge {G : D ⥤ E} {d d' : D} {e : E} {X : E} {y : D} (f : d' ⟶ y)
    (β : d ⟶ d') (g : e ⟶ G.obj d) (k : G.obj y ⟶ X) :
    g ≫ G.map (β ≫ f) ≫ k = (g ≫ G.map β) ≫ G.map f ≫ k := by
  simp

theorem companion_aux_comp {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (α : F ⋙ G ⟶ H) {c c' : C}
    {d : D} {e : E} (β : c ⟶ c') (f : d ⟶ F.obj c) (g : e ⟶ G.obj d) :
    g ≫ G.map (f ≫ F.map β) ≫ α.app c' = (g ≫ G.map f ≫ α.app c) ≫ H.map β := by
  have h := α.naturality β
  simp only [Functor.comp_map] at h
  simp [h]

theorem companion_aux_counit {F : C ⥤ D} {G : D ⥤ C} (α : F ⋙ G ⟶ 𝟭 C) {c c' : C}
    {d : D} {e : C} (β : c ⟶ c') (f : d ⟶ F.obj c) (g : e ⟶ G.obj d) :
    g ≫ G.map (f ≫ F.map β) ≫ α.app c' = (g ≫ G.map f ≫ α.app c) ≫ β := by
  have h := α.naturality β
  simp only [Functor.comp_map, Functor.id_map] at h
  simp [h]

theorem companion_aux_decomp {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (α : H ⟶ F ⋙ G) {c c' : C}
    {e : E} (β : c ⟶ c') (h : e ⟶ H.obj c) :
    (h ≫ H.map β) ≫ α.app c' = (h ≫ α.app c) ≫ G.map (F.map β) := by
  have h' := α.naturality β
  simp only [Functor.comp_map] at h'
  simp [h']

end Aux

/-- A natural transformation of functors induces a morphism of companions. -/
def companionMap {F G : C ⥤ D} (α : F ⟶ G) : F.toProfunctor ⟶ G.toProfunctor :=
  ofSquare
    { app {c d} (h : d ⟶ F.obj c) := h ≫ α.app c
      natL β x := companion_aux_map α β x
      natR x g := Category.assoc g x _ }

@[simp] theorem companionMap_app {F G : C ⥤ D} (α : F ⟶ G) {c : C} {d : D}
    (h : F.toProfunctor.app c d) : ((companionMap α).app c).app (op d) h = h ≫ α.app c := rfl

/-- Composition of companions: `F_* ⊙ G_* ⟶ H_*` from `F ⋙ G ⟶ H`. -/
def companionComp {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (α : F ⋙ G ⟶ H) :
    F.toProfunctor.comp G.toProfunctor ⟶ H.toProfunctor :=
  compDesc
    { app {c d e} (f : d ⟶ F.obj c) (g : e ⟶ G.obj d) := g ≫ G.map f ≫ α.app c
      wedge f β g := companion_aux_wedge f β g _
      natL β f g := companion_aux_comp α β f g
      natR _ g γ := Category.assoc γ g _ }

@[simp] theorem companionComp_mk {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (α : F ⋙ G ⟶ H) {c : C}
    {d : D} {e : E} (f : F.toProfunctor.app c d) (g : G.toProfunctor.app d e) :
    ((companionComp α).app c).app (op e) (Quot.mk _ ⟨d, f, g⟩) =
      (g : e ⟶ G.obj d) ≫ G.map (f : d ⟶ F.obj c) ≫ α.app c :=
  rfl

@[simp] theorem id_mapL {c c' : C} (f : c ⟶ c') {d : C} (g : (Profunctor.id (C := C)).app c d) :
    (Profunctor.id (C := C)).mapL f g = (g : d ⟶ c) ≫ f := rfl

@[simp] theorem id_mapR {d d' : C} (g : d ⟶ d') {c : C} (h : (Profunctor.id (C := C)).app c d') :
    (Profunctor.id (C := C)).mapR g h = g ≫ (h : d' ⟶ c) := rfl

/-- The counit of companions, `F_* ⊙ G_* ⟶ id` from `F ⋙ G ⟶ 𝟭`. -/
def companionCounit {F : C ⥤ D} {G : D ⥤ C} (α : F ⋙ G ⟶ 𝟭 C) :
    F.toProfunctor.comp G.toProfunctor ⟶ Profunctor.id :=
  compDesc
    { app {c d e} (f : d ⟶ F.obj c) (g : e ⟶ G.obj d) := (g ≫ G.map f ≫ α.app c : e ⟶ c)
      wedge f β g := companion_aux_wedge f β g _
      natL β f g := companion_aux_counit α β f g
      natR _ g γ := Category.assoc γ g _ }

@[simp] theorem companionCounit_mk {F : C ⥤ D} {G : D ⥤ C} (α : F ⋙ G ⟶ 𝟭 C) {c : C}
    {d : D} {e : C} (f : F.toProfunctor.app c d) (g : G.toProfunctor.app d e) :
    ((companionCounit α).app c).app (op e) (Quot.mk _ ⟨d, f, g⟩) =
      ((g : e ⟶ G.obj d) ≫ G.map (f : d ⟶ F.obj c) ≫ α.app c : e ⟶ c) :=
  rfl

/-- Representatives of a composite, with the type fixed. -/
abbrev compMk {P : Profunctor.{u} C D} {Q : Profunctor.{u} D E} {c : C} {e : E} (d : D)
    (p : P.app c d) (q : Q.app d e) : (P.comp Q).app c e :=
  Quot.mk _ ⟨d, p, q⟩

/-- Decomposition of companions: `H_* ⟶ F_* ⊙ G_*` from `H ⟶ F ⋙ G`. -/
def companionDecomp {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (α : H ⟶ F ⋙ G) :
    H.toProfunctor ⟶ F.toProfunctor.comp G.toProfunctor :=
  ofSquare
    { app {c e} (h : e ⟶ H.obj c) :=
        compMk (P := F.toProfunctor) (Q := G.toProfunctor) (F.obj c) (𝟙 (F.obj c)) (h ≫ α.app c)
      natL {c c' e} β h := by
        refine Eq.trans ?_ (comp_mapL_mk _ _ β _ _ _).symm
        refine Eq.trans (congrArg (fun k => compMk (P := F.toProfunctor) (Q := G.toProfunctor)
          (F.obj c') (𝟙 (F.obj c')) k) (companion_aux_decomp α β h)) ?_
        refine Eq.trans (Quot.sound (Types.coendRel.mk
          (F := F.toProfunctor.compDiagram G.toProfunctor c' e) (F.map β)
          (𝟙 (F.obj c'), h ≫ α.app c))).symm ?_
        exact congrArg (fun k => compMk (P := F.toProfunctor) (Q := G.toProfunctor)
          (F.obj c) k (h ≫ α.app c))
          ((Category.comp_id (F.map β)).trans (Category.id_comp (F.map β)).symm)
      natR {c e e'} h γ :=
        (congrArg (fun k => compMk (P := F.toProfunctor) (Q := G.toProfunctor) (F.obj c)
          (𝟙 (F.obj c)) k) (Category.assoc γ h (α.app c))).trans
          (comp_mapR_mk _ _ γ _ _ _).symm }

@[simp] theorem companionDecomp_app {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (α : H ⟶ F ⋙ G)
    {c : C} {e : E} (h : H.toProfunctor.app c e) :
    ((companionDecomp α).app c).app (op e) h =
      compMk (F.obj c) (𝟙 (F.obj c)) ((h : e ⟶ H.obj c) ≫ α.app c) :=
  rfl

/-- Composing with a companion on the left is restriction (co-Yoneda), in the direction
`F_* ⊙ S ⟶ S(F -, -)`. -/
def companionRestrict (F : C ⥤ D) (S : Profunctor.{u} D E) :
    F.toProfunctor.comp S ⟶ S.whiskerLeft₂ F (𝟭 E) :=
  compDesc
    { app f s := S.mapL f s
      wedge f α s := S.mapL_comp α f s
      natL β f s := S.mapL_comp f (F.map β) s
      natR f s α := S.mapL_mapR_comm f α s }

@[simp] theorem companionRestrict_mk (F : C ⥤ D) (S : Profunctor.{u} D E) {c : C} {d : D}
    {e : E} (f : F.toProfunctor.app c d) (s : S.app d e) :
    ((companionRestrict F S).app c).app (op e) (Quot.mk _ ⟨d, f, s⟩) = S.mapL f s :=
  rfl

/-- The universal property of the pushforward `S ⊙ F_*` along a functor `F` (the Kan
extension): a morphism `S ⟶ R(-, F -)` induces `S ⊙ F_* ⟶ R`. -/
def pushDesc {S : Profunctor.{u} C D} {R : Profunctor.{u} C E} {F : D ⥤ E}
    (α : S ⟶ R.whiskerLeft₂ (𝟭 C) F) : S.comp F.toProfunctor ⟶ R :=
  compDesc
    { app s h := R.mapR h ((α.app _).app _ s)
      wedge s β h :=
        (congrArg (R.mapR h) (app_mapR α β s)).trans (R.mapR_comp h (F.map β) _).symm
      natL γ s h :=
        (congrArg (R.mapR h) (app_mapL α γ s)).trans (R.mapL_mapR_comm γ h _).symm
      natR _ h γ := R.mapR_comp γ h _ }

@[simp] theorem pushDesc_mk {S : Profunctor.{u} C D} {R : Profunctor.{u} C E} {F : D ⥤ E}
    (α : S ⟶ R.whiskerLeft₂ (𝟭 C) F) {c : C} {d : D} {e : E} (s : S.app c d)
    (h : F.toProfunctor.app d e) :
    ((pushDesc α).app c).app (op e) (Quot.mk _ ⟨d, s, h⟩) = R.mapR h ((α.app c).app (op d) s) :=
  rfl

/-- Representatives of a composite with equal (up to `HEq`) components are equal. -/
theorem comp_mk_heq {P : Profunctor.{u} C D} {Q : Profunctor.{u} D E} {c : C} {e : E}
    {d d' : D} (h : d = d') {p : P.app c d} {p' : P.app c d'} {q : Q.app d e} {q' : Q.app d' e}
    (hp : p ≍ p') (hq : q ≍ q') :
    (Quot.mk _ ⟨d, p, q⟩ : (P.comp Q).app c e) = Quot.mk _ ⟨d', p', q'⟩ := by
  subst h; cases hp; cases hq; rfl

end Profunctor

end CategoryTheory
