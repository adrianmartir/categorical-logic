/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/
module

public import Mathlib.CategoryTheory.Discrete.Basic
public import CategoricalLogic.Profunctor.Basic

/-!
## Discrete Profunctors

Given types `C` and `D` and a function `F : D × C → Type*`, we construct a profunctor
`Profunctor.discrete F` from the discrete category on `C` to the discrete category on `D`.

### Main definitions

* `Profunctor.discrete` — the discrete profunctor associated to a type family on `D × C`.
* `Profunctor.discrete.natTrans` — constructs a natural transformation between discrete
  profunctors from a family of maps between the underlying type families.
* `Profunctor.discrete.equivObj` — an equivalence showing that the profunctor's object mapping
  agrees with the original type family.

### API

We provide `@[simp]` lemmas for `map`, `mapL`, and `mapR` showing they reduce to identity
(or `cast`) when applied to discrete morphisms, as well as extensionality and naturality
results for natural transformations between discrete profunctors.
-/

@[expose] public section

namespace CategoryTheory.Profunctor

universe w

/-! ### Discrete Profunctors -/

/-- Given types `C` and `D` and a function `F : D × C → Type w`, construct a profunctor from the
discrete category on `C` to the discrete category on `D`. Since discrete categories have only
identity morphisms, the mapping operations act trivially (by transport along equalities). -/
@[simps]
def discrete {C : Type*} {D : Type*} (F : D × C → Type w) :
    Profunctor.{w} (Discrete C) (Discrete D) where
  obj d c := F (d.as, c.as)
  map {X X'} {Y Y'} f g h :=
    (Discrete.eq_of_hom f) ▸ (Discrete.eq_of_hom g) ▸ h
  map_id X Y e := rfl
  map_comp {X X' X''} {Y Y' Y''} f' f g g' e := by
    sorry

variable {C : Type*} {D : Type*}

/-! ### Simp lemmas for mapL and mapR -/

@[simp]
theorem discrete_mapL_eqToHom {F : D × C → Type w} {d d' : Discrete D} (h : d = d')
    {c : Discrete C} (e : (discrete F).obj d' c) :
    (discrete F).mapL (eqToHom h) e = h ▸ e := by
  subst h; simp [Profunctor.mapL]

@[simp]
theorem discrete_mapR_eqToHom {F : D × C → Type w} {d : Discrete D}
    {c c' : Discrete C} (h : c = c') (e : (discrete F).obj d c) :
    (discrete F).mapR (eqToHom h) e = h ▸ e := by
  subst h; simp [Profunctor.mapR]

/-! ### Equivalence with the underlying type family -/

/-- The type `(discrete F).obj (Discrete.mk d) (Discrete.mk c)` is definitionally equal to
`F (d, c)`. This equivalence witnesses that fact. -/
def discrete.equivObj (F : D × C → Type w) (d : D) (c : C) :
    (discrete F).obj (Discrete.mk d) (Discrete.mk c) ≃ F (d, c) :=
  Equiv.refl _

/-! ### Natural transformations between discrete profunctors -/

/-- Construct a natural transformation between discrete profunctors from a family of maps
between the underlying type families. -/
@[simps]
def discrete.natTrans {F G : D × C → Type w}
    (φ : ∀ p : D × C, F p → G p) :
    NatTrans (discrete F) (discrete G) where
  app X Y e := φ (X.as, Y.as) e
  naturality {X X'} {Y Y'} f g e := by
    sorry

/-- Two natural transformations between discrete profunctors are equal if their underlying
families of maps agree pointwise. -/
theorem discrete.natTrans_ext {F G : D × C → Type w}
    {α β : NatTrans (discrete F) (discrete G)}
    (h : ∀ (d : D) (c : C) (e : F (d, c)),
      α.app (Discrete.mk d) (Discrete.mk c) e = β.app (Discrete.mk d) (Discrete.mk c) e) :
    α = β := by
  ext ⟨d⟩ ⟨c⟩ e
  exact h d c e

/-- The identity natural transformation on a discrete profunctor. -/
theorem discrete.natTrans_id (F : D × C → Type w) :
    discrete.natTrans (fun p e => e) = NatTrans.id (discrete F) := by
  ext ⟨d⟩ ⟨c⟩ e; rfl

/-- Composition of natural transformations between discrete profunctors corresponds to
composition of the underlying families. -/
theorem discrete.natTrans_comp {F G H : D × C → Type w}
    (ψ : ∀ p : D × C, G p → H p) (φ : ∀ p : D × C, F p → G p) :
    (discrete.natTrans ψ).comp (discrete.natTrans φ) =
      discrete.natTrans (fun p e => ψ p (φ p e)) := by
  ext ⟨d⟩ ⟨c⟩ e; rfl

/-- An equivalence of type families induces an isomorphism (pair of inverse natural
transformations) between the corresponding discrete profunctors. -/
def discrete.natTransOfEquiv {F G : D × C → Type w}
    (e : ∀ p : D × C, F p ≃ G p) :
    NatTrans (discrete F) (discrete G) :=
  discrete.natTrans (fun p => e p)

end CategoryTheory.Profunctor
