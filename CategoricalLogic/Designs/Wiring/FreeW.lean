/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Wiring.Class
public import Mathlib.CategoryTheory.EqToHom

/-!
# The free category with `W`-structure

For a class of wirings `W` and a category `X`, `FreeW W X` is the category whose objects are
lists of objects of `X` and whose morphisms `xs ⟶ ys` assign to every variable `y` of `ys` a
variable `x` of `xs` and a morphism `x ⟶ y`, such that the underlying wiring is allowed by `W`.
For `W = cartesian` this is the free category with finite products, for `W = planar` the free
strict monoidal category.

## Main definitions

* `Wired W R as bs`: assignments relative to `R` whose wiring is allowed by `W`.
* `FreeW W X` with its `Category` instance.
* `FreeW.map F`, `FreeW.unit`, `FreeW.flatten`: the functorial action, unit and multiplication
  of the monad, as plain functors.

All three functors are unbundled: there is no `Cat`, no `Monad` and no functor equality in
any definition.
-/

@[expose] public section

namespace CategoryTheory

universe u v v' v'' w w' w''

/-- An assignment relative to `R` whose underlying wiring is allowed by `W`. -/
@[ext]
structure Wired (W : WiringClass.{u}) {α β : Type u} (R : α → β → Type w) (as : List α)
    (bs : List β) where
  /-- The underlying assignment. -/
  assign : Assign R as bs
  /-- The wiring is allowed. -/
  mem : W.mem assign.wires

namespace Wired

variable {W : WiringClass.{u}} {α β γ α' β' : Type u}
  {R : α → β → Type w} {S : β → γ → Type w'} {U : α → γ → Type w''}
  {as : List α} {bs : List β} {cs : List γ}

theorem isPlanar_refl (as : List α) :
    IsPlanar (Assign.refl (R := fun _ _ ↦ PUnit.{1}) (fun _ ↦ PUnit.unit) (as := as)) :=
  ⟨rfl, fun _ _ ↦ rfl⟩

theorem isPlanar_relabelSrc (f : α → α') (as : List α) :
    IsPlanar (Assign.mapSrc (S := fun _ _ ↦ PUnit.{1}) f (fun _ _ _ ↦ PUnit.unit)
      (Assign.refl (R := fun _ _ ↦ PUnit.{1}) (fun _ ↦ PUnit.unit) (as := as))) :=
  ⟨List.length_map f, fun _ k ↦ Var.idx_map f k⟩

theorem isPlanar_relabelTgt (g : β → β') (bs : List β) :
    IsPlanar (Assign.mapTgt (S := fun _ _ ↦ PUnit.{1}) g (fun _ _ _ ↦ PUnit.unit)
      (Assign.refl (R := fun _ _ ↦ PUnit.{1}) (fun _ ↦ PUnit.unit) (as := bs))) := by
  refine ⟨(List.length_map g).symm, fun _ k ↦ ?_⟩
  induction k using Var.map_induction with
  | h j => rw [Assign.mapTgt_map]; exact (Var.idx_map g j).symm

theorem isPlanar_single {a : α} {b : β} (r : R a b) : IsPlanar (Assign.single r).wires :=
  ⟨rfl, fun _ k ↦ match k with | .zero => rfl⟩

theorem mapTgt_wires_eq_comp (g : β → β') (c : Wires as bs) :
    Assign.mapTgt (S := fun _ _ ↦ PUnit.{1}) g (fun _ _ _ ↦ PUnit.unit) c =
      Assign.comp (U := fun _ _ ↦ PUnit.{1}) (fun _ _ _ _ _ ↦ PUnit.unit) c
        (Assign.mapTgt (S := fun _ _ ↦ PUnit.{1}) g (fun _ _ _ ↦ PUnit.unit)
          (Assign.refl (R := fun _ _ ↦ PUnit.{1}) (fun _ ↦ PUnit.unit))) := by
  refine Assign.ext fun _ k ↦ ?_
  induction k using Var.map_induction with
  | h j => simp only [Assign.comp]; rw [Assign.mapTgt_map, Assign.mapTgt_map]; rfl

/-- The identity, labelled by `r`. -/
def refl {R : α → α → Type w} (r : ∀ a, R a a) {as : List α} : Wired W R as as :=
  ⟨Assign.refl r, W.planar_mem (isPlanar_refl as)⟩

/-- Composition, combining labels with `h`. -/
def comp (h : ∀ ⦃a b c⦄, R a b → S b c → U a c) (c₁ : Wired W R as bs)
    (c₂ : Wired W S bs cs) : Wired W U as cs :=
  ⟨Assign.comp h c₁.assign c₂.assign, W.comp_mem c₁.mem c₂.mem⟩

/-- Relabel the source along `f`. -/
def mapSrc {S : α' → β → Type w'} (f : α → α') (h : ∀ ⦃a b⦄, R a b → S (f a) b)
    (c : Wired W R as bs) : Wired W S (as.map f) bs :=
  ⟨Assign.mapSrc f h c.assign, W.comp_mem (W.planar_mem (isPlanar_relabelSrc f as)) c.mem⟩

theorem mem_mapTgt {S : α → β' → Type w'} (g : β → β') (h : ∀ ⦃a b⦄, R a b → S a (g b))
    (c : Wired W R as bs) : W.mem (Assign.mapTgt g h c.assign).wires := by
  rw [Assign.wires_mapTgt, mapTgt_wires_eq_comp]
  exact W.comp_mem c.mem (W.planar_mem (isPlanar_relabelTgt g bs))

/-- Relabel the target along `g`. -/
def mapTgt {S : α → β' → Type w'} (g : β → β') (h : ∀ ⦃a b⦄, R a b → S a (g b))
    (c : Wired W R as bs) : Wired W S as (bs.map g) :=
  ⟨Assign.mapTgt g h c.assign, mem_mapTgt g h c⟩

/-- The wired assignment `[a] → [b]` labelled by `r`. -/
def single {a : α} {b : β} (r : R a b) : Wired W R [a] [b] :=
  ⟨Assign.single r, W.planar_mem (isPlanar_single r)⟩

/-- Flatten a wired assignment between lists of blocks whose labels are wired assignments. -/
def bind {γ δ : Type u} (p : γ → List α) (q : δ → List β) {R : γ → δ → Type w}
    {S : α → β → Type w'} (h : ∀ ⦃c d⦄, R c d → Wired W S (p c) (q d)) {cs : List γ}
    {ds : List δ} (e : Wired W R cs ds) : Wired W S (cs.flatMap p) (ds.flatMap q) :=
  ⟨Assign.bind p q (fun _ _ r ↦ (h r).assign) e.assign,
    W.bind_mem p q (fun _ j ↦ ⟨(e.assign j).1, (e.assign j).2.1, (h (e.assign j).2.2).assign.wires⟩)
      e.mem (fun _ j ↦ (h (e.assign j).2.2).mem)⟩

@[simp] theorem refl_assign {R : α → α → Type w} (r : ∀ a, R a a) {as : List α} :
    (refl (W := W) r (as := as)).assign = Assign.refl r := rfl

@[simp] theorem comp_assign' (h : ∀ ⦃a b c⦄, R a b → S b c → U a c) (c₁ : Wired W R as bs)
    (c₂ : Wired W S bs cs) : (comp h c₁ c₂).assign = Assign.comp h c₁.assign c₂.assign := rfl

@[simp] theorem mapSrc_assign {S : α' → β → Type w'} (f : α → α')
    (h : ∀ ⦃a b⦄, R a b → S (f a) b) (c : Wired W R as bs) :
    (mapSrc f h c).assign = Assign.mapSrc f h c.assign := rfl

@[simp] theorem mapTgt_assign {S : α → β' → Type w'} (g : β → β')
    (h : ∀ ⦃a b⦄, R a b → S a (g b)) (c : Wired W R as bs) :
    (mapTgt g h c).assign = Assign.mapTgt g h c.assign := rfl

@[simp] theorem single_assign {a : α} {b : β} (r : R a b) :
    (single (W := W) r).assign = Assign.single r := rfl

@[simp] theorem bind_assign {γ δ : Type u} (p : γ → List α) (q : δ → List β)
    {R : γ → δ → Type w} {S : α → β → Type w'} (h : ∀ ⦃c d⦄, R c d → Wired W S (p c) (q d))
    {cs : List γ} {ds : List δ} (e : Wired W R cs ds) :
    (bind p q h e).assign = Assign.bind p q (fun _ _ r ↦ (h r).assign) e.assign := rfl

end Wired

/-- The free category with `W`-structure on `X`: objects are lists of objects of `X`. -/
@[ext]
structure FreeW (_W : WiringClass.{u}) (X : Type u) where
  /-- The object of `FreeW W X` given by a list of objects of `X`. -/
  mk ::
  /-- The underlying list. -/
  as : List X

namespace FreeW

variable {W : WiringClass.{u}} {X : Type u} [Category.{v} X]

/-- The morphisms of `FreeW W X`. -/
protected abbrev Hom (xs ys : FreeW W X) : Type (max u v) :=
  Wired W (fun x y : X ↦ x ⟶ y) xs.as ys.as

/-- The identity morphism. -/
protected def Hom.id (xs : FreeW W X) : FreeW.Hom xs xs := Wired.refl (fun x ↦ 𝟙 x)

/-- Composition of morphisms. -/
protected def Hom.comp {xs ys zs : FreeW W X} (f : FreeW.Hom xs ys) (g : FreeW.Hom ys zs) :
    FreeW.Hom xs zs :=
  Wired.comp (R := fun x y : X ↦ x ⟶ y) (S := fun x y : X ↦ x ⟶ y)
    (U := fun x y : X ↦ x ⟶ y) (fun _ _ _ f g ↦ f ≫ g) f g

instance : Category.{max u v} (FreeW W X) where
  Hom := FreeW.Hom
  id := FreeW.Hom.id
  comp := FreeW.Hom.comp
  id_comp f := by
    apply Wired.ext; apply Assign.ext; intro _ k
    simp [Hom.comp, Hom.id, Wired.comp, Assign.comp, Wired.refl, Assign.refl]
  comp_id f := by
    apply Wired.ext; apply Assign.ext; intro _ k
    simp [Hom.comp, Hom.id, Wired.comp, Assign.comp, Wired.refl, Assign.refl]
  assoc f g h := by
    apply Wired.ext; apply Assign.ext; intro _ k
    simp [Hom.comp, Wired.comp, Assign.comp]

/-- The underlying assignment of a morphism of `FreeW W X`. -/
abbrev assign {xs ys : FreeW W X} (f : xs ⟶ ys) : Assign (fun x y : X ↦ x ⟶ y) xs.as ys.as :=
  Wired.assign f

@[ext]
theorem hom_ext {xs ys : FreeW W X} {f g : xs ⟶ ys}
    (h : ∀ ⦃y : X⦄ (k : Var ys.as y), assign f k = assign g k) : f = g :=
  Wired.ext (Assign.ext h)

@[simp] theorem id_assign (xs : FreeW W X) {x : X} (k : Var xs.as x) :
    assign (𝟙 xs) k = ⟨x, k, 𝟙 x⟩ := rfl

@[simp] theorem comp_assign {xs ys zs : FreeW W X} (f : xs ⟶ ys) (g : ys ⟶ zs) {z : X}
    (k : Var zs.as z) :
    assign (f ≫ g) k =
      ⟨(assign f (assign g k).2.1).1, (assign f (assign g k).2.1).2.1,
        (assign f (assign g k).2.1).2.2 ≫ (assign g k).2.2⟩ := rfl

/-- `eqToHom` in `FreeW W X` reads every variable from the same position. -/
theorem eqToHom_assign {xs ys : FreeW W X} (h : xs = ys) {y : X} (k : Var ys.as y) :
    assign (eqToHom h) k = ⟨y, (h ▸ k : Var xs.as y), 𝟙 y⟩ := by
  subst h; rfl

/-- `eqToHom` in `FreeW W X` is given by any index-preserving map of variables. -/
theorem eqToHom_assign_of_idx {xs ys : FreeW W X} (h : xs = ys)
    (σ : ∀ ⦃y : X⦄, Var ys.as y → Var xs.as y) (hσ : ∀ ⦃y : X⦄ (k : Var ys.as y), (σ k).idx = k.idx)
    {y : X} (k : Var ys.as y) : assign (eqToHom h) k = ⟨y, σ k, 𝟙 y⟩ := by
  rw [eqToHom_assign]
  congr
  subst h
  exact Var.ext_idx _ _ (hσ k).symm

/-! ### The functors -/

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v'} D]
  {E : Type u} [Category.{v''} E]

/-- The action of a functor, positionwise. (Reducible, so that the object lists of the image
are seen as `List.map` at every transparency.) -/
@[reducible] def map (F : C ⥤ D) : FreeW W C ⥤ FreeW W D where
  obj xs := ⟨xs.as.map F.obj⟩
  map f := Wired.mapSrc F.obj (fun _ _ g ↦ g) (Wired.mapTgt F.obj (fun _ _ g ↦ F.map g) f)
  map_id xs := hom_ext fun _ k ↦ by
    induction k using Var.map_induction with
    | h j =>
      simp only [Wired.mapSrc_assign, Wired.mapTgt_assign, Assign.mapSrc]
      rw [Assign.mapTgt_map]; simp
  map_comp f g := hom_ext fun _ k ↦ by
    induction k using Var.map_induction with
    | h j =>
      simp only [Wired.mapSrc_assign, Wired.mapTgt_assign, Assign.mapSrc, comp_assign]
      rw [Assign.mapTgt_map, Assign.mapTgt_map, Assign.mapTgt_map]; simp

@[simp] theorem map_obj (F : C ⥤ D) (xs : FreeW W C) :
    ((map F).obj xs).as = xs.as.map F.obj := rfl

@[simp] theorem map_assign_map (F : C ⥤ D) {xs ys : FreeW W C} (f : xs ⟶ ys) {y : C}
    (j : Var ys.as y) :
    assign ((map F).map f) (j.map F.obj) =
      ⟨F.obj (assign f j).1, (assign f j).2.1.map F.obj, F.map (assign f j).2.2⟩ := by
  simp only [map, Wired.mapSrc_assign, Wired.mapTgt_assign, Assign.mapSrc]
  rw [Assign.mapTgt_map]

/-- The unit: singleton lists. -/
@[reducible] def unit : C ⥤ FreeW W C where
  obj x := ⟨[x]⟩
  map f := Wired.single f
  map_id _ := hom_ext fun _ k ↦ match k with | .zero => rfl
  map_comp _ _ := hom_ext fun _ k ↦ match k with | .zero => rfl

@[simp] theorem unit_obj (x : C) : ((unit (W := W)).obj x).as = [x] := rfl

@[simp] theorem unit_assign {x y : C} (f : x ⟶ y) :
    assign ((unit (W := W)).map f) .zero = ⟨x, .zero, f⟩ := rfl

/-- The multiplication: flattening of lists of lists. -/
@[reducible] def flatten : FreeW W (FreeW W C) ⥤ FreeW W C where
  obj css := ⟨css.as.flatMap FreeW.as⟩
  map f := Wired.bind FreeW.as FreeW.as (fun _ _ g ↦ g) f
  map_id css := hom_ext fun _ k ↦ by
    induction k using Var.flatMap_induction with
    | h j v => simp only [Wired.bind_assign]; rw [Assign.bind_join]; rfl
  map_comp f g := hom_ext fun _ k ↦ by
    induction k using Var.flatMap_induction with
    | h j v =>
      simp only [Wired.bind_assign, comp_assign]
      rw [Assign.bind_join, Assign.bind_join, Assign.bind_join]
      rfl

@[simp] theorem flatten_obj (css : FreeW W (FreeW W C)) :
    ((flatten (W := W)).obj css).as = css.as.flatMap FreeW.as := rfl

@[simp] theorem flatten_assign_join {css dss : FreeW W (FreeW W C)} (f : css ⟶ dss)
    {ds : FreeW W C} {y : C} (j : Var dss.as ds) (v : Var ds.as y) :
    assign ((flatten (W := W)).map f) (Var.join FreeW.as j v) =
      ⟨(assign (assign f j).2.2 v).1,
        Var.join FreeW.as (assign f j).2.1 (assign (assign f j).2.2 v).2.1,
        (assign (assign f j).2.2 v).2.2⟩ := by
  simp only [flatten, Wired.bind_assign]; rw [Assign.bind_join]

end FreeW

end CategoryTheory
