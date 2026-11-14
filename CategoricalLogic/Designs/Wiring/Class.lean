/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Wiring.Var

/-!
# Classes of wirings

A *wiring* `w : Wires as bs` sends every position of `bs` to a position of `as`. A *class of
wirings* selects the wirings that are allowed as structural rules:

| class        | wirings                         | `FreeW W X` is the free ... category |
|--------------|---------------------------------|--------------------------------------|
| `planar`     | order-preserving bijections     | strict monoidal                      |
| `cartesian`  | all                             | cartesian (finite products)          |

(Symmetric = bijections, affine = injections, relevant = surjections fit the same scheme.)

A class of wirings must contain the planar wirings and be closed under composition and under
flattening (block substitution). It is a predicate on label-free data, but since positions are
structural (`Var`), the predicate is stated for wirings between lists of arbitrary types of a
fixed universe `u`.

## Conventions

The *variance*: an operation in `hom.app a bs` of an operad has inputs `bs`, and a morphism
`xs ⟶ ys` of `FreeW W X` acts on operations by `mapR : hom.app a ys → hom.app a xs`. A wiring
`xs ⟶ ys` assigns to every position of `ys` a position of `xs`, so precomposing an operation with
inputs `ys` by it reads every input from `xs`: positions of `xs` that are not hit are *weakened*,
positions hit several times are *contracted*. This is the free category with finite products
(morphisms into a product are tuples, morphisms out of a free product are projections).
-/

@[expose] public section

namespace CategoryTheory

universe u

/-- A wiring is *planar* if it is the identity on positions: both lists have the same length
and every position is sent to the position with the same index. -/
def IsPlanar {α β : Type u} {as : List α} {bs : List β} (w : Wires as bs) : Prop :=
  as.length = bs.length ∧ ∀ ⦃b⦄ (j : Var bs b), (w j).2.1.idx = j.idx

/-- A *class of wirings*: a predicate on wirings that contains the planar wirings and is closed
under composition and under flattening. -/
structure WiringClass : Type (u + 1) where
  /-- The allowed wirings. -/
  mem {α β : Type u} {as : List α} {bs : List β} : Wires as bs → Prop
  /-- Planar wirings (in particular identities and relabellings) are allowed. -/
  planar_mem {α β : Type u} {as : List α} {bs : List β} {w : Wires as bs} : IsPlanar w → mem w
  /-- Allowed wirings are closed under composition. -/
  comp_mem {α β γ : Type u} {as : List α} {bs : List β} {cs : List γ} {w : Wires as bs}
    {w' : Wires bs cs} : mem w → mem w' → mem (Assign.comp (fun _ _ _ _ _ ↦ ⟨⟩) w w')
  /-- Block substitution: an allowed wiring of allowed wirings flattens to an allowed wiring. -/
  bind_mem {α β γ δ : Type u} (p : γ → List α) (q : δ → List β) {cs : List γ} {ds : List δ}
    (w : Assign (fun c d ↦ Wires (p c) (q d)) cs ds) : mem w.wires →
      (∀ ⦃d⦄ (j : Var ds d), mem (w j).2.2) → mem (Assign.bind p q (fun _ _ w ↦ w) w)

namespace WiringClass

/-- The cartesian class: all wirings. -/
def cartesian : WiringClass.{u} where
  mem _ := True
  planar_mem _ := trivial
  comp_mem _ _ := trivial
  bind_mem _ _ _ _ _ _ _ := trivial

theorem IsPlanar.comp {α β γ : Type u} {as : List α} {bs : List β} {cs : List γ}
    {w : Wires as bs} {w' : Wires bs cs} (h : IsPlanar w) (h' : IsPlanar w') :
    IsPlanar (Assign.comp (fun _ _ _ _ _ ↦ ⟨⟩) w w') :=
  ⟨h.1.trans h'.1, fun _ k ↦ (h.2 _).trans (h'.2 k)⟩

/-- Under a planar wiring of planar wirings, corresponding blocks have the same length. -/
theorem map_length_eq_of_isPlanar {α β γ δ : Type u} (p : γ → List α) (q : δ → List β)
    {cs : List γ} {ds : List δ} (w : Assign (fun c d ↦ Wires (p c) (q d)) cs ds)
    (h : IsPlanar w.wires) (h' : ∀ ⦃d⦄ (j : Var ds d), IsPlanar (w j).2.2) :
    cs.map (fun c ↦ (p c).length) = ds.map (fun d ↦ (q d).length) := by
  refine List.ext_getElem?' fun n ↦ ?_
  by_cases hn : n < ds.length
  · have hi := (w (Var.ofFin ds ⟨n, hn⟩)).2.1.getElem?_idx
    have hidx := h.2 (Var.ofFin ds ⟨n, hn⟩)
    simp only [Assign.wires, Var.idx_ofFin] at hidx
    rw [hidx] at hi
    simp only [List.getElem?_map, hi, Option.map_some, List.getElem?_eq_getElem hn]
    exact fun _ ↦ congrArg some (h' (Var.ofFin ds ⟨n, hn⟩)).1
  · have : cs.length ≤ n := h.1 ▸ Nat.le_of_not_lt hn
    simp [List.getElem?_eq_none this, List.getElem?_eq_none (Nat.le_of_not_lt hn)]

theorem IsPlanar.bind {α β γ δ : Type u} (p : γ → List α) (q : δ → List β)
    {cs : List γ} {ds : List δ} (w : Assign (fun c d ↦ Wires (p c) (q d)) cs ds)
    (h : IsPlanar w.wires) (h' : ∀ ⦃d⦄ (j : Var ds d), IsPlanar (w j).2.2) :
    IsPlanar (Assign.bind p q (fun _ _ w ↦ w) w) := by
  have hl := map_length_eq_of_isPlanar p q w h h'
  refine ⟨?_, fun _ k ↦ ?_⟩
  · simp only [List.length_flatMap]
    exact congrArg List.sum hl
  induction k using Var.flatMap_induction with
  | h j v =>
    rw [Assign.bind_join]
    have hj := h.2 j
    simp only [Assign.wires] at hj
    simp only [Var.idx_join, (h' j).2 v, hj, List.map_take, hl]

/-- The planar class: order-preserving bijections only. -/
def planar : WiringClass.{u} where
  mem := IsPlanar
  planar_mem h := h
  comp_mem := IsPlanar.comp
  bind_mem := IsPlanar.bind

end WiringClass

end CategoryTheory
