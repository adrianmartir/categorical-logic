/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Wiring.Operad

/-!
# Endomorphism operads

For a functor `X : C ⥤ Type w` (for a discrete category: a family of types), the endomorphism
`W`-operad has as operations with inputs `bs` and output `a` the functions
`(∀ positions of bs, X _) → X a`. It is a `W`-operad for every class of wirings `W`, since
`Type` is cartesian.
-/

@[expose] public section

namespace CategoryTheory

open Profunctor FreeW

universe u v w

namespace WOperad

/-! ### Index bookkeeping for the unit and associativity laws -/

namespace Var

variable {α γ : Type u}

theorem idx_join_inl (p : γ → List α) {l : List γ} (l' : List γ) {c : γ} {a : α}
    (j : Var l c) (x : Var (p c) a) : (Var.join p (j.inl l') x).idx = (Var.join p j x).idx := by
  induction j with
  | zero => simp [Var.inl, Var.join]
  | succ j ih => simp only [Var.inl, Var.join, Var.idx_inr, ih, List.flatMap_cons]

theorem idx_join_inr (p : γ → List α) (l : List γ) {l' : List γ} {c : γ} {a : α}
    (j : Var l' c) (x : Var (p c) a) :
    (Var.join p (Var.inr l j) x).idx = (l.flatMap p).length + (Var.join p j x).idx := by
  induction l with
  | nil => simp [Var.inr]
  | cons c' l ih =>
    rw [show Var.join p (Var.inr (c' :: l) j) x = Var.inr (p c') (Var.join p (Var.inr l j) x)
      from rfl, Var.idx_inr, ih, List.flatMap_cons, List.length_append]
    omega

end Var

variable {W : WiringClass.{u}} {C : Type u} [Category.{v} C] (X : C ⥤ Type w)

theorem idx_join_map_unit {b : List C} {c : C} (k : Var b c) :
    (Var.join FreeW.as (k.map (unit (W := W)).obj) .zero).idx = k.idx := by
  induction k with
  | zero => rfl
  | succ k ih => sorry

theorem idx_join_join {d : List (FreeW W (FreeW W C))} {ds : FreeW W (FreeW W C)}
    {cs : FreeW W C} {y : C} (i : Var d ds) (w : Var ds.as cs) (x : Var cs.as y) :
    (Var.join FreeW.as (Var.join FreeW.as i w) x).idx =
      (Var.join FreeW.as (i.map (flatten (W := W)).obj) (Var.join FreeW.as w x)).idx := by
  induction i with
  | zero =>
    simp only [Var.join, Var.map, Var.idx_inl]
    try exact Var.idx_join_inl FreeW.as _ w x
  | succ i ih =>
    simp only [Var.join, Var.map, Var.idx_inr]
    rw [Var.idx_join_inr, ih]
    rfl

/-- An environment: a value of `X` for every variable of `bs`. -/
def Env (bs : FreeW W C) : Type (max u w) := ∀ ⦃b : C⦄, Var bs.as b → X.obj b

variable {X}

/-- Transport an environment along a morphism `bs ⟶ bs'`: weakening, contraction, exchange,
and the action of `X` on the components. -/
def Env.reindex {bs bs' : FreeW W C} (ρ : bs ⟶ bs') (e : Env X bs) : Env X bs' :=
  fun _ k ↦ X.map (assign ρ k).2.2 (e (assign ρ k).2.1)

/-- Restrict an environment of a flattened list to one block. -/
def Env.block {c : FreeW W (FreeW W C)} (e : Env X ((flatten (W := W)).obj c)) {cs : FreeW W C}
    (i : Var c.as cs) : Env X cs :=
  fun _ v ↦ e (Var.join FreeW.as i v)

theorem Env.reindex_id {bs : FreeW W C} (e : Env X bs) : e.reindex (𝟙 bs) = e := by
  funext b k; simp only [reindex, id_assign, Functor.map_id]; rfl

theorem Env.reindex_comp {bs bs' bs'' : FreeW W C} (ρ : bs ⟶ bs') (σ : bs' ⟶ bs'')
    (e : Env X bs) : e.reindex (ρ ≫ σ) = (e.reindex ρ).reindex σ := by
  funext b k; simp only [reindex, comp_assign, Functor.map_comp]; rfl

variable (W X)

variable {W X}

/-- The action of the endomorphism profunctor on morphisms. -/
def endoMap {a a' : C} {bs bs' : FreeW W C} (α : a ⟶ a') (ρ : bs ⟶ bs')
    (f : Env X bs' → X.obj a) : Env X bs → X.obj a' :=
  fun e ↦ X.map α (f (e.reindex ρ))

theorem endoMap_id {a : C} {bs : FreeW W C} (f : Env X bs → X.obj a) :
    endoMap (𝟙 a) (𝟙 bs) f = f :=
  funext fun e ↦ by simp only [endoMap, Env.reindex_id, Functor.map_id]; rfl

theorem endoMap_comp {a a' a'' : C} {bs bs' bs'' : FreeW W C} (α : a ⟶ a') (α' : a' ⟶ a'')
    (ρ : bs ⟶ bs') (ρ' : bs' ⟶ bs'') (f : Env X bs'' → X.obj a) :
    endoMap (α ≫ α') (ρ ≫ ρ') f = endoMap α' ρ (endoMap α ρ' f) :=
  funext fun e ↦ by simp only [endoMap, Env.reindex_comp, Functor.map_comp]; rfl

variable (W X)

/-- The profunctor of operations of the endomorphism operad. -/
def endoHom : Profunctor.{max u w} C (FreeW W C) :=
  Profunctor.ofCore
    { obj a bs := Env X bs → X.obj a
      map α ρ := TypeCat.ofHom (endoMap α ρ)
      map_id _ _ := congrArg TypeCat.ofHom (funext endoMap_id)
      map_comp α α' ρ ρ' := congrArg TypeCat.ofHom (funext (endoMap_comp α α' ρ ρ')) }

variable {W X}

/-- View an operation of the endomorphism operad as a function. -/
def endoFun {a : C} {bs : FreeW W C} (f : (endoHom W X).app a bs) : Env X bs → X.obj a := f

theorem endo_ext {a : C} {bs : FreeW W C} {f g : (endoHom W X).app a bs}
    (h : ∀ e, endoFun f e = endoFun g e) : f = g := funext h

theorem endoFun_mapL {a a' : C} {bs : FreeW W C} (α : a ⟶ a') (f : (endoHom W X).app a bs)
    (e : Env X bs) : endoFun ((endoHom W X).mapL α f) e = X.map α (endoFun f e) := by
  change endoMap α (𝟙 bs) f e = _
  simp only [endoMap, Env.reindex_id]; rfl

theorem endoFun_mapR {a : C} {bs bs' : FreeW W C} (ρ : bs ⟶ bs') (f : (endoHom W X).app a bs')
    (e : Env X bs) : endoFun ((endoHom W X).mapR ρ f) e = endoFun f (e.reindex ρ) := by
  change endoMap (𝟙 a) ρ f e = _
  simp only [endoMap, Functor.map_id]; rfl

/-- The composite of the endomorphism operad: substitute the family `f` into `g`. -/
def endoComp {a : C} {b : FreeW W C} {c : FreeW W (FreeW W C)} (g : (endoHom W X).app a b)
    (f : (prof W (endoHom W X)).app b c) : (endoHom W X).app a ((flatten (W := W)).obj c) :=
  fun e ↦ endoFun g fun _ j ↦ endoFun ((elt f).assign j).2.2 (e.block ((elt f).assign j).2.1)

variable (W X)

/-- The identity operations of the endomorphism operad. -/
def endoId : NullaryCell (endoHom W X) (𝟭 C) unit where
  app a := fun e ↦ e .zero
  naturality α := by
    refine endo_ext fun e ↦ ?_
    rw [endoFun_mapL, endoFun_mapR]
    rfl

/-- The composition cell of the endomorphism operad. -/
def endoCompCell : BinaryCell (endoHom W X) (prof W (endoHom W X)) (endoHom W X) (𝟭 C) flatten where
  app g f := endoComp g f
  wedge g α f := by
    funext e
    change endoFun _ (fun _ j ↦ _) = endoFun _ (fun _ j ↦ _)
    rw [endoFun_mapR]
    congr 1
    funext b k
    simp only [Env.reindex, prof_mapL_assign, endoFun_mapL]
    rfl
  natL α g f := by
    funext e
    change endoFun _ _ = endoFun _ e
    rw [endoFun_mapL, endoFun_mapL]
    rfl
  natR g f ρ := by
    funext e
    change endoFun _ _ = endoFun _ e
    rw [endoFun_mapR]
    change endoFun g _ = endoFun g _
    congr 1
    funext b k
    simp only [prof_mapR_assign, endoFun_mapR]
    congr 1
    funext x v
    simp only [Env.reindex, Env.block]
    rw [flatten_assign_join]

variable {W X}

theorem endoFun_mpRight {a : C} {bs bs' : FreeW W C} (f : (endoHom W X).app a bs')
    (h : bs = bs') (e : Env X bs) :
    endoFun ((endoHom W X).mpRight f h) e = endoFun f (e.reindex (eqToHom h)) :=
  endoFun_mapR _ f e

theorem Env.reindex_eqToHom {bs bs' : FreeW W C} (h : bs = bs') (e : Env X bs) {b : C}
    (k : Var bs'.as b) (v : Var bs.as b) (hv : v.idx = k.idx) : e.reindex (eqToHom h) k = e v := by
  simp only [reindex]; rw [eqToHom_assign_eq h k v hv]; simp

variable (W X)

/-- The endomorphism `W`-operad of a functor `X : C ⥤ Type w`. -/
def endo : WOperad.{u, v, max u w} W C where
  hom := endoHom W X
  id := endoId W X
  comp := endoCompCell W X
  comp_id f := by
    funext e
    change endoFun f _ = endoFun _ e
    rw [endoFun_mpRight]
    congr 1
    funext b k
    rw [Env.reindex_eqToHom _ e k (Var.join FreeW.as .zero k) (by simp [Var.join])]
    rfl
  id_comp f := by
    funext e
    change endoFun f _ = endoFun _ e
    rw [endoFun_mpRight]
    congr 1
    funext b k
    rw [Env.reindex_eqToHom _ e k _ (idx_join_map_unit k)]
    rfl
  comp_assoc h g f := by
    funext e
    change endoFun h _ = endoFun _ e
    rw [endoFun_mpRight]
    change endoFun h _ = endoFun h _
    congr 1
    funext b k
    change endoFun _ _ = endoFun _ _
    congr 1
    funext b' v
    change endoFun _ _ = endoFun _ _
    rw [μCell_assign_join]
    congr 1
    funext y x
    exact (Env.reindex_eqToHom _ e _ _ (idx_join_join _ _ _)).symm

end WOperad

/-! ### Example: arithmetic on `ℕ` -/

namespace WOperad.Example

/-- The single sort. -/
abbrev S : Type := Discrete Unit

/-- `ℕ` as a family over the single sort. -/
abbrev N : S ⥤ Type := Discrete.functor fun _ ↦ ℕ

/-- The sort. -/
abbrev s : S := ⟨()⟩

variable (W : WiringClass.{0})

/-- Binary addition, as an operation of the endomorphism operad. -/
def add : (endo W N).hom.app s ⟨[s, s]⟩ := fun e ↦ (e .zero : ℕ) + (e (.succ .zero) : ℕ)

/-- The family `(add, id)`, with identity wiring. -/
def addId : Assign (fun d c ↦ (endo W N).hom.app c d) [⟨[s, s]⟩, ⟨[s]⟩] [s, s]
  | _, .zero => ⟨_, .zero, add W⟩
  | _, .succ .zero => ⟨_, .succ .zero, (endo W N).id.app s⟩

theorem isPlanar_addId : IsPlanar (addId W).wires :=
  ⟨rfl, fun _ k ↦ match k with | .zero => rfl | .succ .zero => rfl⟩

/-- The family `(add, id)` as an element of `prof W (endo W N).hom`. -/
def addIdFam : (prof W (endo W N).hom).app ⟨[s, s]⟩ ⟨[⟨[s, s]⟩, ⟨[s]⟩]⟩ :=
  mkElt ⟨addId W, W.planar_mem (isPlanar_addId W)⟩

/-- `add ∘ (add, id)`: a ternary operation. -/
def add3 : (endo W N).hom.app s ⟨[s, s, s]⟩ := (endo W N).comp.app (add W) (addIdFam W)

/-- The environment `[1, 2, 3]`. -/
def env123 : Env (W := W) N ⟨[s, s, s]⟩ := fun _ k ↦ (k.idx + 1 : ℕ)

example : endoFun (add3 WiringClass.planar) (env123 _) = 6 := rfl
example : endoFun (add3 WiringClass.cartesian) (env123 _) = 6 := by decide

/-- Contraction (cartesian only): `x ↦ x + x`, by precomposing `add` with the diagonal. -/
def diag : (FreeW.mk [s] : FreeW WiringClass.cartesian S) ⟶ FreeW.mk [s, s] :=
  ⟨fun _ k ↦ match k with | .zero => ⟨s, .zero, 𝟙 s⟩ | .succ .zero => ⟨s, .zero, 𝟙 s⟩, trivial⟩

def double : (endo WiringClass.cartesian N).hom.app s ⟨[s]⟩ :=
  (endo WiringClass.cartesian N).hom.mapR diag (add _)

example : endoFun double (fun _ _ ↦ (21 : ℕ)) = 42 := rfl

#eval endoFun (add3 WiringClass.cartesian) (env123 _)
#eval endoFun double (fun _ _ ↦ (21 : ℕ))

end WOperad.Example

end CategoryTheory
