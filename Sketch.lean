import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.List.Basic

open CategoryTheory
universe u

structure Ctx (S : Type u) where
  n : ℕ
  ty : Fin n → S

namespace Ctx
variable {S S' S'' : Type u}
abbrev single (s : S) : Ctx S := ⟨1, fun _ => s⟩
def map (f : S → S') (Γ : Ctx S) : Ctx S' := ⟨Γ.n, fun i => f (Γ.ty i)⟩
def restrict (Γ : Ctx S) {m : ℕ} (ρ : Fin m → Fin Γ.n) : Ctx S := ⟨m, fun i => Γ.ty (ρ i)⟩
example (Γ : Ctx S) : Γ.map id = Γ := rfl
example (f : S → S') (g : S' → S'') (Γ : Ctx S) : (Γ.map f).map g = Γ.map (g ∘ f) := rfl
example (f : S → S') (s : S) : (single s).map f = single (f s) := rfl
example (Γ : Ctx S) {m k : ℕ} (ρ : Fin m → Fin Γ.n) (τ : Fin k → Fin m) :
    (Γ.restrict ρ).restrict τ = Γ.restrict (ρ ∘ τ) := rfl
end Ctx

/-- Category of operators: a substitution is a tuple of its components. `Adm` says which tuples exist. -/
structure Operators (S : Type u) where
  [cat : Category.{u} (Ctx S)]
  proj : ∀ (Γ : Ctx S) (i : Fin Γ.n), Γ ⟶ Ctx.single (Γ.ty i)
  proj_single : ∀ s : S, proj (Ctx.single s) (0 : Fin 1) = 𝟙 _
  ext : ∀ {Δ Γ : Ctx S} (f g : Δ ⟶ Γ), (∀ i, f ≫ proj Γ i = g ≫ proj Γ i) → f = g
  Adm : ∀ {Δ Γ : Ctx S}, (∀ i, Δ ⟶ Ctx.single (Γ.ty i)) → Prop
  tuple : ∀ {Δ Γ : Ctx S} (f : ∀ i, Δ ⟶ Ctx.single (Γ.ty i)), Adm f → (Δ ⟶ Γ)
  tuple_proj : ∀ {Δ Γ : Ctx S} (f : ∀ i, Δ ⟶ Ctx.single (Γ.ty i)) (h : Adm f) (i : Fin Γ.n),
    tuple f h ≫ proj Γ i = f i
  adm : ∀ {Δ Γ : Ctx S} (g : Δ ⟶ Γ), Adm fun i => g ≫ proj Γ i


/-- morphisms: no transport in the statement -/
structure Operators.Hom {S S' : Type u} (A : Operators S) (B : Operators S') where
  f : S → S'
  map : ∀ {Δ Γ : Ctx S}, A.cat.Hom Δ Γ → B.cat.Hom (Δ.map f) (Γ.map f)
  map_id : ∀ Γ : Ctx S, map (A.cat.id Γ) = B.cat.id _
  map_comp : ∀ {Δ Γ E : Ctx S} (x : A.cat.Hom Δ Γ) (y : A.cat.Hom Γ E),
    map (A.cat.comp x y) = B.cat.comp (map x) (map y)
  map_proj : ∀ (Γ : Ctx S) (i : Fin Γ.n), map (A.proj Γ i) = B.proj (Γ.map f) i

/-- cartesian endomorphism operad -/
def Tup {S : Type} (X : S → Type) (Γ : Ctx S) : Type := ∀ i, X (Γ.ty i)

def End {S : Type} (X : S → Type) : Operators S where
  cat := { Hom := fun Δ Γ => Tup X Δ → Tup X Γ, id := fun _ => id, comp := fun f g => g ∘ f }
  proj Γ i := fun t _ => t i
  proj_single s := by funext t (i : Fin 1); obtain rfl := Subsingleton.elim i 0; rfl
  ext f g h := by
    funext t i
    exact congrFun (congrFun (h i) t) (0 : Fin 1)
  Adm _ := True
  tuple f _ := fun t i => f i t (0 : Fin 1)
  tuple_proj f _ i := by funext t (k : Fin 1); obtain rfl := Subsingleton.elim k 0; rfl
  adm _ := trivial

/-- raw terms, shared context -/
structure Sig (S : Type) where
  Op : Type
  ar : Op → Ctx S
  out : Op → S

inductive Term {S : Type} (σ : Sig S) (Δ : Ctx S) : S → Type
  | var (i : Fin Δ.n) : Term σ Δ (Δ.ty i)
  | op (o : σ.Op) (args : ∀ j, Term σ Δ ((σ.ar o).ty j)) : Term σ Δ (σ.out o)

namespace Term
variable {S : Type} {σ : Sig S}

def subst {Δ Γ : Ctx S} (τ : ∀ i, Term σ Δ (Γ.ty i)) : ∀ {s}, Term σ Γ s → Term σ Δ s
  | _, var i => τ i
  | _, op o args => op o fun j => subst τ (args j)

theorem subst_var {Γ : Ctx S} : ∀ {s} (t : Term σ Γ s), subst (fun i => var i) t = t
  | _, var _ => rfl
  | _, op o args => congrArg (op o) (funext fun j => subst_var (args j))

theorem subst_subst {E Δ Γ : Ctx S} (τ : ∀ i, Term σ Δ (Γ.ty i)) (υ : ∀ i, Term σ E (Δ.ty i)) :
    ∀ {s} (t : Term σ Γ s), subst υ (subst τ t) = subst (fun i => subst υ (τ i)) t
  | _, var _ => rfl
  | _, op o args => congrArg (op o) (funext fun j => subst_subst τ υ (args j))

/-- variable occurrences, left to right -/
def leaves {Δ : Ctx S} : ∀ {s}, Term σ Δ s → List (Fin Δ.n)
  | _, var i => [i]
  | _, op o args => (List.finRange (σ.ar o).n).flatMap fun j => leaves (args j)

theorem leaves_subst {Δ Γ : Ctx S} (τ : ∀ i, Term σ Δ (Γ.ty i)) :
    ∀ {s} (t : Term σ Γ s), leaves (subst τ t) = (leaves t).flatMap fun i => leaves (τ i)
  | _, var _ => by simp [subst, leaves]
  | _, op o args => by
    simp only [subst, leaves, List.flatMap_assoc]
    congr 1; funext j; exact leaves_subst τ (args j)
end Term
