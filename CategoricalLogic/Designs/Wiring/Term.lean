/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Wiring.Var

/-!
# Terms over a signature (towards the free cartesian operad)

For a many-sorted signature `Sig : List S → S → Type` (operation symbols with input sorts and an
output sort), `Term Sig ctx s` is the inductive type of terms of sort `s` in the context `ctx`.
Since the context is a list and variables are `Var ctx s`, this is directly an operation of the
free cartesian operad on `Sig` over the discrete category on `S`, with inputs `ctx`:

* the identity is `var .zero : Term Sig [s] s`;
* the action of a cartesian wiring is renaming;
* composition is simultaneous substitution followed by the block embeddings `Var.join`.

Here we define the terms, renaming and substitution and prove the substitution laws; the
operad laws of `free` reduce to these (see the report).
-/

@[expose] public section

namespace CategoryTheory

universe u

variable {S : Type u} (Sig : List S → S → Type u)

/-- Terms of sort `s` in context `ctx` over the signature `Sig`. -/
inductive Term (ctx : List S) : S → Type u
  /-- A variable of the context. -/
  | var {s : S} : Var ctx s → Term ctx s
  /-- An operation symbol applied to a tuple of terms. -/
  | op {ts : List S} {s : S} : Sig ts s → (∀ ⦃t⦄, Var ts t → Term ctx t) → Term ctx s

namespace Term

variable {Sig} {ctx ctx' ctx'' : List S}

/-- Simultaneous substitution. -/
def subst (σ : ∀ ⦃s⦄, Var ctx s → Term Sig ctx' s) : ∀ {s}, Term Sig ctx s → Term Sig ctx' s
  | _, var k => σ k
  | _, op f args => op f fun _ k ↦ subst σ (args k)

/-- Renaming of variables (the action of a cartesian wiring). -/
def rename (ρ : ∀ ⦃s⦄, Var ctx s → Var ctx' s) {s : S} (t : Term Sig ctx s) : Term Sig ctx' s :=
  t.subst fun _ k ↦ var (ρ k)

@[simp] theorem subst_var' (σ : ∀ ⦃s⦄, Var ctx s → Term Sig ctx' s) {s : S} (k : Var ctx s) :
    (var k).subst σ = σ k := rfl

@[simp] theorem subst_var {s : S} (t : Term Sig ctx s) : t.subst (fun _ k ↦ var k) = t := by
  induction t with
  | var k => rfl
  | op f args ih => simp only [subst]; congr; funext t k; exact ih k

theorem subst_subst (σ : ∀ ⦃s⦄, Var ctx s → Term Sig ctx' s)
    (τ : ∀ ⦃s⦄, Var ctx' s → Term Sig ctx'' s) {s : S} (t : Term Sig ctx s) :
    (t.subst σ).subst τ = t.subst fun _ k ↦ (σ k).subst τ := by
  induction t with
  | var k => rfl
  | op f args ih => simp only [subst]; congr; funext t k; exact ih k

/-- Composition of the free operad: substitute a family of terms, each in its own block of the
flattened context. -/
def comp {b : List S} {a : S} {cs : List (List S)} (g : Term Sig b a)
    (f : Assign (fun c b ↦ Term Sig c b) cs b) : Term Sig (cs.flatMap id) a :=
  g.subst fun _ j ↦ (f j).2.2.rename fun _ v ↦ Var.join id (f j).2.1 v

end Term

namespace Term.Example

/-- The signature of monoids (one sort). -/
inductive MonSig : List Unit → Unit → Type
  | mul : MonSig [(), ()] ()
  | one : MonSig [] ()

/-- `x * y`. -/
def mulXY : Term MonSig [(), ()] () :=
  .op .mul fun _ k ↦ .var k

/-- `(x * y) * z` as `mulXY ∘ (mulXY, id)`, computed by substitution. -/
def mul3 : Term MonSig [(), (), ()] () :=
  Term.comp mulXY fun _ k ↦ match k with
    | .zero => ⟨[(), ()], .zero, mulXY⟩
    | .succ .zero => ⟨[()], .succ .zero, .var .zero⟩

/-- Evaluation of terms in a family of types interpreting the signature. -/
def eval {S : Type} {Sig : List S → S → Type} (A : S → Type)
    (I : ∀ {ts s}, Sig ts s → (∀ ⦃t⦄, Var ts t → A t) → A s) {ctx : List S}
    (e : ∀ ⦃t⦄, Var ctx t → A t) : ∀ {s}, Term Sig ctx s → A s
  | _, .var k => e k
  | _, .op f args => I f fun _ k ↦ eval A I e (args k)

/-- `ℕ` with addition as a model of `MonSig`. -/
def natAdd : ∀ {ts s}, MonSig ts s → (∀ ⦃t⦄, Var ts t → ℕ) → ℕ
  | _, _, .mul, x => x .zero + x (.succ .zero)
  | _, _, .one, _ => 0

example : eval (fun _ ↦ ℕ) natAdd (fun _ k ↦ k.idx + 1) mul3 = 6 := rfl

end Term.Example

end CategoryTheory
