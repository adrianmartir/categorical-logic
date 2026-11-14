/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import Mathlib.Data.List.Basic

/-!
# Variables in lists and assignments

This file provides the structural (de Bruijn style) bookkeeping underlying the free categories
with structural rules of `CategoricalLogic.Designs.Wiring.FreeW`.

## Main definitions

* `Var as a`: a *variable* of type `a` in the list `as`, i.e. a position of `as` holding `a`.
* `Assign R as bs`: an assignment that sends every variable `b` of `bs` to a variable `a` of `as`
  together with an element of `R a b`. With `R` the morphisms of a category this is a morphism
  `as ⟶ bs` of the free cartesian category; with `R` a profunctor it is a family of
  heteromorphisms.
* `Wires as bs`: an assignment without labels, i.e. just the underlying map of positions.
* `Assign.refl`, `Assign.comp`, `Assign.mapSrc`, `Assign.mapTgt`, `Assign.single`,
  `Assign.bind`: identities, composition, relabelling, singletons and flattening.

## Design notes

Positions are an inductive family indexed by the object they hold, so a family of objects
indexed by the positions of `bs` is a function `∀ ⦃b⦄, Var bs b → _` and no `List.get` or
`Fin`-arithmetic ever appears in data. The only operation defined by recursion on a list
(rather than on a variable) is `Assign.mapTgt`; `Assign.bind` uses the non-dependent
decomposition `Var.unjoin`.
-/

@[expose] public section

namespace CategoryTheory

universe u u' u'' u''' w w' w''

/-- A *variable* of type `a` in the list `as`: a position of `as` at which `a` occurs. -/
inductive Var {α : Type u} : List α → α → Type u
  /-- The first position. -/
  | zero {a : α} {as : List α} : Var (a :: as) a
  /-- A position in the tail. -/
  | succ {a b : α} {as : List α} : Var as a → Var (b :: as) a

namespace Var

variable {α : Type u} {β : Type u'}

/-- The index of a variable. -/
def idx {as : List α} {a : α} : Var as a → ℕ
  | zero => 0
  | succ v => v.idx + 1

/-- The variable at the same position of a relabelled list. -/
def map (f : α → β) {as : List α} {a : α} : Var as a → Var (as.map f) (f a)
  | zero => zero
  | succ v => succ (v.map f)

/-- A variable of `l`, seen as a variable of `l ++ l'`. -/
def inl {l : List α} (l' : List α) {a : α} : Var l a → Var (l ++ l') a
  | zero => zero
  | succ v => succ (v.inl l')

/-- A variable of `l'`, seen as a variable of `l ++ l'`. -/
def inr : (l : List α) → {l' : List α} → {a : α} → Var l' a → Var (l ++ l') a
  | [], _, _, v => v
  | _ :: l, _, _, v => succ (inr l v)

/-- A variable of `l ++ l'` lies either in `l` or in `l'`. -/
def split : {l l' : List α} → {a : α} → Var (l ++ l') a → Var l a ⊕ Var l' a
  | [], _, _, v => .inr v
  | _ :: _, _, _, zero => .inl zero
  | _ :: _, _, _, succ v => (split v).map succ id

/-- A variable `v` of the block `p c`, for `c` at position `j` of `cs`, is a variable of
`cs.flatMap p`. -/
def join {γ : Type u'} (p : γ → List α) : {cs : List γ} → {c : γ} → {a : α} →
    Var cs c → Var (p c) a → Var (cs.flatMap p) a
  | _ :: _, _, _, zero, v => v.inl _
  | c :: _, _, _, succ j, v => inr (p c) (join p j v)

/-- Every variable of `cs.flatMap p` lies in one of the blocks `p c`. -/
def unjoin {γ : Type u'} (p : γ → List α) : {cs : List γ} → {a : α} →
    Var (cs.flatMap p) a → Σ c, Var cs c × Var (p c) a
  | c :: _, _, v =>
    (split (l := p c) v).elim (fun v ↦ ⟨c, zero, v⟩)
      (fun v ↦ ⟨(unjoin p v).1, succ (unjoin p v).2.1, (unjoin p v).2.2⟩)

/-- The variable at a given index. -/
def ofFin : (l : List α) → (n : Fin l.length) → Var l (l.get n)
  | _ :: _, ⟨0, _⟩ => zero
  | _ :: l, ⟨n + 1, h⟩ => succ (ofFin l ⟨n, Nat.lt_of_succ_lt_succ h⟩)

/-! ### Lemmas -/

@[simp] theorem split_inl {l : List α} (l' : List α) {a : α} (v : Var l a) :
    split (v.inl l') = .inl v := by
  induction v with
  | zero => rfl
  | succ v ih => simp [inl, split, ih]

@[simp] theorem split_inr (l : List α) {l' : List α} {a : α} (v : Var l' a) :
    split (inr l v) = .inr v := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [inr, split, ih]

theorem inl_inr_of_split : {l l' : List α} → {a : α} → (v : Var (l ++ l') a) →
    Sum.elim (inl l') (inr l) (split v) = v
  | [], _, _, _ => rfl
  | _ :: _, _, _, zero => rfl
  | _ :: l, l', _, succ v => by
    have := inl_inr_of_split (l := l) (l' := l') v
    rcases h : split v with v' | v' <;> simp_all [split, inl, inr]

@[simp] theorem unjoin_join {γ : Type u'} (p : γ → List α) {cs : List γ} {c : γ} {a : α}
    (j : Var cs c) (v : Var (p c) a) : unjoin p (join p j v) = ⟨c, j, v⟩ := by
  induction j with
  | zero => simp [join, unjoin]
  | succ j ih => simp only [join, unjoin, split_inr, Sum.elim_inr]; rw [ih]

@[simp] theorem join_unjoin {γ : Type u'} (p : γ → List α) : {cs : List γ} → {a : α} →
    (k : Var (cs.flatMap p) a) → join p (unjoin p k).2.1 (unjoin p k).2.2 = k
  | c :: cs, a, k => by
    have h := inl_inr_of_split (l := p c) (l' := cs.flatMap p) k
    rcases hs : split (l := p c) k with v | v
    · simp only [hs, Sum.elim_inl] at h
      simp only [unjoin]; rw [hs]
      exact h
    · simp only [hs, Sum.elim_inr] at h
      simp only [unjoin]; rw [hs]
      exact (congrArg (inr (p c)) (join_unjoin p v)).trans h

/-- Every variable of `cs.flatMap p` is `join p j v` for some variable `j` of `cs` and some
variable `v` of the block `p c`. -/
theorem flatMap_induction {γ : Type u'} (p : γ → List α) {cs : List γ}
    {motive : ∀ {a : α}, Var (cs.flatMap p) a → Prop}
    (h : ∀ {c : γ} {a : α} (j : Var cs c) (v : Var (p c) a), motive (join p j v))
    {a : α} (k : Var (cs.flatMap p) a) : motive k :=
  join_unjoin p k ▸ h _ _

/-- Every variable of a relabelled list is the relabelling of a variable. -/
theorem map_induction (f : α → β) : {as : List α} →
    {motive : ∀ {b : β}, Var (as.map f) b → Prop} →
    (h : ∀ {a : α} (j : Var as a), motive (j.map f)) → {b : β} → (k : Var (as.map f) b) →
    motive k
  | [], _, _, _, k => nomatch k
  | _ :: _, _, h, _, zero => h zero
  | _ :: _, motive, h, _, succ k =>
    map_induction f (motive := fun k => motive (succ k)) (fun j => h (succ j)) k

@[simp] theorem idx_map (f : α → β) {as : List α} {a : α} (v : Var as a) :
    (v.map f).idx = v.idx := by
  induction v with
  | zero => rfl
  | succ v ih => simp [map, idx, ih]

@[simp] theorem idx_inl {l : List α} (l' : List α) {a : α} (v : Var l a) :
    (v.inl l').idx = v.idx := by
  induction v with
  | zero => rfl
  | succ v ih => simp [inl, idx, ih]

@[simp] theorem idx_inr (l : List α) {l' : List α} {a : α} (v : Var l' a) :
    (inr l v).idx = l.length + v.idx := by
  induction l with
  | nil => simp [inr]
  | cons b l ih => simp [inr, idx, ih]; omega

theorem idx_join {γ : Type u'} (p : γ → List α) {cs : List γ} {c : γ} {a : α} (j : Var cs c)
    (v : Var (p c) a) :
    (join p j v).idx = ((cs.take j.idx).map (fun c ↦ (p c).length)).sum + v.idx := by
  induction j with
  | zero => simp [join, idx]
  | succ j ih => simp [join, idx, ih]; omega

@[simp] theorem idx_ofFin : (l : List α) → (n : Fin l.length) → (ofFin l n).idx = n
  | _ :: _, ⟨0, _⟩ => rfl
  | _ :: l, ⟨n + 1, h⟩ => by simp [ofFin, idx, idx_ofFin l]

theorem idx_lt_length {as : List α} {a : α} (v : Var as a) : v.idx < as.length := by
  induction v with
  | zero => simp [idx]
  | succ v ih => simp [idx, ih]

theorem getElem?_idx {as : List α} {a : α} (v : Var as a) : as[v.idx]? = some a := by
  induction v with
  | zero => rfl
  | succ v ih => simpa [idx] using ih

/-- A variable is determined by its index. -/
theorem ext_idx {as : List α} {a : α} : (v v' : Var as a) → v.idx = v'.idx → v = v'
  | zero, zero, _ => rfl
  | succ v, succ v', h => congrArg succ (ext_idx v v' (Nat.succ.inj h))
  | zero, succ _, h => nomatch h
  | succ _, zero, h => nomatch h

theorem idx_cast {as as' : List α} {a : α} (h : as = as') (v : Var as a) :
    (h ▸ v : Var as' a).idx = v.idx := by
  subst h; rfl

end Var

/-- An *assignment* from `as` to `bs` relative to `R`: every variable `b` of `bs` is sent to a
variable `a` of `as` together with an element of `R a b`. -/
abbrev Assign {α : Type u} {β : Type u'} (R : α → β → Type w) (as : List α) (bs : List β) :
    Type (max u u' w) :=
  ∀ ⦃b : β⦄, Var bs b → Σ a : α, Var as a × R a b

/-- The underlying map of positions of an assignment: an assignment without labels. -/
abbrev Wires {α : Type u} {β : Type u'} (as : List α) (bs : List β) : Type (max u u') :=
  Assign (fun _ _ => PUnit.{1}) as bs

namespace Assign

variable {α : Type u} {β : Type u'} {γ : Type u''} {δ : Type u'''}
  {R : α → β → Type w} {S : β → γ → Type w'} {U : α → γ → Type w''}
  {as : List α} {bs : List β} {cs : List γ}

theorem ext {c c' : Assign R as bs} (h : ∀ ⦃b⦄ (j : Var bs b), c j = c' j) : c = c' :=
  funext fun _ => funext fun j => h j

/-- Forget the labels of an assignment. -/
def wires (c : Assign R as bs) : Wires as bs := fun _ k => ⟨(c k).1, (c k).2.1, ⟨⟩⟩

/-- The identity assignment, labelled by `r`. -/
def refl {R : α → α → Type w} (r : ∀ a, R a a) {as : List α} : Assign R as as :=
  fun _ k => ⟨_, k, r _⟩

/-- Composition of assignments, combining the labels with `h`. -/
def comp (h : ∀ ⦃a b c⦄, R a b → S b c → U a c) (c₁ : Assign R as bs) (c₂ : Assign S bs cs) :
    Assign U as cs :=
  fun _ k => ⟨(c₁ (c₂ k).2.1).1, (c₁ (c₂ k).2.1).2.1, h (c₁ (c₂ k).2.1).2.2 (c₂ k).2.2⟩

/-- Relabel the source of an assignment along `f`. -/
def mapSrc {α' : Type u''} {S : α' → β → Type w'} (f : α → α') (h : ∀ ⦃a b⦄, R a b → S (f a) b)
    (c : Assign R as bs) : Assign S (as.map f) bs :=
  fun _ k => ⟨f (c k).1, (c k).2.1.map f, h (c k).2.2⟩

/-- Relabel the target of an assignment along `g`. -/
def mapTgt {β' : Type u''} {S : α → β' → Type w'} (g : β → β') (h : ∀ ⦃a b⦄, R a b → S a (g b)) :
    {bs : List β} → Assign R as bs → Assign S as (bs.map g)
  | [], _, _, k => nomatch k
  | _ :: _, c, _, .zero => ⟨(c .zero).1, (c .zero).2.1, h (c .zero).2.2⟩
  | _ :: _, c, _, .succ k => mapTgt g h (fun _ j => c j.succ) k

/-- The assignment `[a] → [b]` labelled by `r`. -/
def single {a : α} {b : β} (r : R a b) : Assign R [a] [b]
  | _, .zero => ⟨a, .zero, r⟩

/-- Flatten an assignment between lists of blocks whose labels are themselves assignments
between the blocks (the blocks of `c : γ` being `p c`). -/
def bind {γ : Type u''} {δ : Type u'''} (p : γ → List α) (q : δ → List β)
    {R : γ → δ → Type w} {S : α → β → Type w'} (h : ∀ ⦃c d⦄, R c d → Assign S (p c) (q d))
    {cs : List γ} {ds : List δ} (e : Assign R cs ds) : Assign S (cs.flatMap p) (ds.flatMap q) :=
  fun _ k ↦
    ⟨(h (e (Var.unjoin q k).2.1).2.2 (Var.unjoin q k).2.2).1,
      Var.join p (e (Var.unjoin q k).2.1).2.1
        (h (e (Var.unjoin q k).2.1).2.2 (Var.unjoin q k).2.2).2.1,
      (h (e (Var.unjoin q k).2.1).2.2 (Var.unjoin q k).2.2).2.2⟩

/-! ### Computation rules -/

@[simp] theorem mapTgt_map {β' : Type u''} {S : α → β' → Type w'} (g : β → β')
    (h : ∀ ⦃a b⦄, R a b → S a (g b)) (c : Assign R as bs) {b : β} (j : Var bs b) :
    mapTgt g h c (j.map g) = ⟨(c j).1, (c j).2.1, h (c j).2.2⟩ := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih (fun _ j => c j.succ)

@[simp] theorem bind_join {γ : Type u''} {δ : Type u'''} (p : γ → List α) (q : δ → List β)
    {R : γ → δ → Type w} {S : α → β → Type w'} (h : ∀ ⦃c d⦄, R c d → Assign S (p c) (q d))
    {cs : List γ} {ds : List δ} (e : Assign R cs ds) {d : δ} {b : β} (j : Var ds d)
    (v : Var (q d) b) :
    bind p q h e (Var.join q j v) =
      ⟨(h (e j).2.2 v).1, Var.join p (e j).2.1 (h (e j).2.2 v).2.1, (h (e j).2.2 v).2.2⟩ := by
  simp only [bind]; rw [Var.unjoin_join]

@[simp] theorem single_zero {a : α} {b : β} (r : R a b) : single r .zero = ⟨a, .zero, r⟩ := rfl

theorem wires_mapTgt {β' : Type u''} {S : α → β' → Type w'} (g : β → β')
    (h : ∀ ⦃a b⦄, R a b → S a (g b)) (c : Assign R as bs) :
    (mapTgt g h c).wires = mapTgt g (fun _ _ _ => ⟨⟩) c.wires := by
  refine ext fun b k => ?_
  induction k using Var.map_induction with
  | h j => simp only [wires]; rw [mapTgt_map, mapTgt_map]; rfl

theorem wires_bind {γ : Type u''} {δ : Type u'''} (p : γ → List α) (q : δ → List β)
    {R : γ → δ → Type w} {S : α → β → Type w'} (h : ∀ ⦃c d⦄, R c d → Assign S (p c) (q d))
    {cs : List γ} {ds : List δ} (e : Assign R cs ds) :
    (bind p q h e).wires =
      bind (R := fun c d ↦ Wires (p c) (q d)) p q (fun _ _ w ↦ w)
        (fun _ j ↦ ⟨(e j).1, (e j).2.1, (h (e j).2.2).wires⟩) :=
  rfl

end Assign

end CategoryTheory
