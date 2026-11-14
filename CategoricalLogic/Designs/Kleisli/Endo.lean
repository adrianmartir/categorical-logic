/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Kleisli.FreeMon
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The endomorphism operad of a family of types

For `Xf : S → Type u`, the planar operad on the discrete category on `S` whose operations with
output `s` and inputs `ss` are the functions `Tuple Xf ss → Xf s`.

All morphisms of `Discrete S`, `FreeMon (Discrete S)` and `FreeMon (FreeMon (Discrete S))` are
identities (thin and skeletal), so all naturality conditions are trivial.
-/

@[expose] public section

namespace CategoryTheory

universe u

open Profunctor Opposite KleisliProf

namespace FreeMon

variable {X : Type u} [Category.{u} X]

instance [Quiver.IsThin X] (A B : FreeMon X) : Subsingleton (A ⟶ B) := by
  obtain ⟨as⟩ := A
  obtain ⟨bs⟩ := B
  induction as generalizing bs with
  | nil => cases bs with
    | nil => exact ⟨fun _ _ => rfl⟩
    | cons b bs => exact ⟨fun f => PEmpty.elim f⟩
  | cons a as ih => cases bs with
    | nil => exact ⟨fun f => PEmpty.elim f⟩
    | cons b bs =>
      exact ⟨fun f g => Prod.ext (Subsingleton.elim (α := a ⟶ b) f.1 g.1)
        (@Subsingleton.elim (mk as ⟶ mk bs) (ih bs) f.2 g.2)⟩

/-- In `FreeMon X`, morphisms force equality if they do so in `X`. -/
theorem eq_of_hom (hX : ∀ {a b : X}, (a ⟶ b) → a = b) {A B : FreeMon X} (f : A ⟶ B) :
    A = B := by
  obtain ⟨as⟩ := A
  obtain ⟨bs⟩ := B
  induction as generalizing bs with
  | nil => cases bs with
    | nil => rfl
    | cons => exact PEmpty.elim f
  | cons a as ih => cases bs with
    | nil => exact PEmpty.elim f
    | cons b bs =>
      obtain rfl := hX f.1
      exact congrArg (fun l => mk (a :: l.as)) (ih bs f.2)

end FreeMon

section Endo

variable {S : Type u} (Xf : S → Type u)

theorem Discrete.eq_of_hom' {a b : Discrete S} (f : a ⟶ b) : a = b :=
  Discrete.ext (Discrete.eq_of_hom f)

theorem FreeMon.eq_of_hom₁ {A B : FreeMon (Discrete S)} (f : A ⟶ B) : A = B :=
  FreeMon.eq_of_hom Discrete.eq_of_hom' f

theorem FreeMon.eq_of_hom₂ {A B : FreeMon (FreeMon (Discrete S))} (f : A ⟶ B) : A = B :=
  FreeMon.eq_of_hom FreeMon.eq_of_hom₁ f

/-- Tuples of elements of the family `Xf`. -/
def Tuple : List (Discrete S) → Type u
  | [] => PUnit
  | s :: ss => Xf s.as × Tuple ss

/-- Tuples of tuples. -/
def Tuple₂ : List (FreeMon (Discrete S)) → Type u
  | [] => PUnit
  | A :: W => Tuple Xf A.as × Tuple₂ W

variable {Xf}

/-- Transport of tuples along a (necessarily trivial) morphism of lists. -/
def tupMap : ∀ {ss ss' : List (Discrete S)}, FreeMon.Hom ss ss' → Tuple Xf ss → Tuple Xf ss'
  | [], [], _, _ => PUnit.unit
  | _ :: _, _ :: _, f, xs => (cast (congrArg Xf (Discrete.eq_of_hom f.1)) xs.1, tupMap f.2 xs.2)
  | [], _ :: _, f, _ => PEmpty.elim f
  | _ :: _, [], f, _ => PEmpty.elim f

theorem tupMap_id : ∀ {ss : List (Discrete S)} (xs : Tuple Xf ss),
    tupMap (𝟙 (FreeMon.mk ss)) xs = xs
  | [], _ => rfl
  | s :: _, xs => Prod.ext (cast_eq (congrArg Xf (Discrete.eq_of_hom (𝟙 s))) xs.1) (tupMap_id xs.2)

theorem tupMap_comp : ∀ {ss ss' ss'' : List (Discrete S)} (f : FreeMon.mk ss ⟶ FreeMon.mk ss')
    (f' : FreeMon.mk ss' ⟶ FreeMon.mk ss'') (xs : Tuple Xf ss),
    tupMap (f ≫ f') xs = tupMap f' (tupMap f xs)
  | [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, f', xs =>
    Prod.ext (cast_cast (congrArg Xf (Discrete.eq_of_hom f.1))
      (congrArg Xf (Discrete.eq_of_hom f'.1)) xs.1).symm (tupMap_comp f.2 f'.2 xs.2)
  | [], _ :: _, _, f, _, _ => PEmpty.elim f
  | _ :: _, [], _, f, _, _ => PEmpty.elim f
  | [], [], _ :: _, _, f', _ => PEmpty.elim f'
  | _ :: _, _ :: _, [], _, f', _ => PEmpty.elim f'

theorem tupMap_self {A : FreeMon (Discrete S)} (f : A ⟶ A) (xs : Tuple Xf A.as) :
    tupMap f xs = xs := by
  rw [Subsingleton.elim f (𝟙 _)]
  exact tupMap_id xs

/-- The first `as.length` entries of a tuple. -/
def takeT : ∀ (as : List (Discrete S)) {bs : List (Discrete S)}, Tuple Xf (as ++ bs) → Tuple Xf as
  | [], _, _ => PUnit.unit
  | _ :: _, _, xs => (xs.1, takeT _ xs.2)

/-- The entries after the first `as.length`. -/
def dropT : ∀ (as : List (Discrete S)) {bs : List (Discrete S)}, Tuple Xf (as ++ bs) → Tuple Xf bs
  | [], _, xs => xs
  | _ :: _, _, xs => dropT _ xs.2

/-- Split a tuple over a flattening into a tuple of tuples. -/
def splitT : ∀ (W : List (FreeMon (Discrete S))), Tuple Xf (W.flatMap FreeMon.as) → Tuple₂ Xf W
  | [], _ => PUnit.unit
  | A :: _, xs => (takeT A.as xs, splitT _ (dropT A.as xs))

variable (Xf) in
/-- The profunctor of operations of the endomorphism operad. -/
def endoProf : Profunctor.{u} (Discrete S) (FreeMon (Discrete S)) where
  obj s :=
    { obj ss := Tuple Xf ss.unop.as → Xf s.as
      map g := TypeCat.ofHom fun φ xs => φ (tupMap g.unop xs)
      map_id _ := TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun φ => funext fun xs =>
        congrArg φ (tupMap_id xs)))
      map_comp g g' := TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun φ => funext fun xs =>
        congrArg φ (tupMap_comp g'.unop g.unop xs))) }
  map f :=
    { app _ := TypeCat.ofHom fun φ xs => cast (congrArg Xf (Discrete.eq_of_hom f)) (φ xs)
      naturality _ _ _ := rfl }
  map_id s := NatTrans.ext (funext fun _ => TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun φ =>
    funext fun xs => cast_eq (congrArg Xf (Discrete.eq_of_hom (𝟙 s))) (φ xs))))
  map_comp f f' := NatTrans.ext (funext fun _ => TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun φ =>
    funext fun xs => (cast_cast (congrArg Xf (Discrete.eq_of_hom f))
      (congrArg Xf (Discrete.eq_of_hom f')) (φ xs)).symm)))

theorem endoProf_app (s : Discrete S) (ss : FreeMon (Discrete S)) :
    (endoProf Xf).app s ss = (Tuple Xf ss.as → Xf s.as) := rfl

theorem endoProf_mapL_self {s : Discrete S} (f : s ⟶ s) {ss : FreeMon (Discrete S)}
    (φ : (endoProf Xf).app s ss) : (endoProf Xf).mapL f φ = φ := by
  rw [Subsingleton.elim f (𝟙 _)]
  exact (endoProf Xf).mapL_id _ _ φ

theorem endoProf_mapR_self {s : Discrete S} {ss : FreeMon (Discrete S)} (g : ss ⟶ ss)
    (φ : (endoProf Xf).app s ss) : (endoProf Xf).mapR g φ = φ := by
  rw [Subsingleton.elim g (𝟙 _)]
  exact (endoProf Xf).mapR_id _ _ φ

theorem kprof_mapL_self {P : Profunctor.{u} (Discrete S) (FreeMon (Discrete S))}
    {A : FreeMon (Discrete S)} (f : A ⟶ A) {W : FreeMon (FreeMon (Discrete S))}
    (e : (FreeMon.kprof P).app A W) : (FreeMon.kprof P).mapL f e = e := by
  rw [Subsingleton.elim f (𝟙 _)]
  exact (FreeMon.kprof P).mapL_id _ _ e

theorem kprof_mapR_self {P : Profunctor.{u} (Discrete S) (FreeMon (Discrete S))}
    {A : FreeMon (Discrete S)} {W : FreeMon (FreeMon (Discrete S))} (g : W ⟶ W)
    (e : (FreeMon.kprof P).app A W) : (FreeMon.kprof P).mapR g e = e := by
  rw [Subsingleton.elim g (𝟙 _)]
  exact (FreeMon.kprof P).mapR_id _ _ e

/-- Apply a list of operations to a tuple of tuples. -/
def applyAll : ∀ {bs : List (Discrete S)} {W : List (FreeMon (Discrete S))},
    FreeMon.KProfApp (endoProf Xf) bs W → Tuple₂ Xf W → Tuple Xf bs
  | [], [], _, _ => PUnit.unit
  | _ :: _, _ :: _, fs, xss => (fs.1 xss.1, applyAll fs.2 xss.2)
  | [], _ :: _, fs, _ => PEmpty.elim fs
  | _ :: _, [], fs, _ => PEmpty.elim fs

variable (Xf)

/-- The identities of the endomorphism operad, as a morphism out of the companion of `η`. -/
def endoUnit : kid Cat.freeMon (Cat.of (Discrete S)) ⟶ endoProf Xf :=
  ofSquare
    { app f xs := (tupMap f xs).1
      natL β f := sorry
      natR f β := sorry }

/-- Composition in the endomorphism operad, as a binary cell. -/
def endoCompCell : BinaryCell (endoProf Xf) (FreeMon.kprof (endoProf Xf)) (endoProf Xf)
    (𝟭 _) (FreeMon.flatten (Discrete S)) where
  app {_ _ W} g fs xs := g (applyAll fs (splitT W.as xs))
  wedge g α fs := sorry
  natL α g fs := sorry
  natR g fs α := sorry


/-- The endomorphism operad. -/
def endoOperad : KOperad Cat.freeMon (Cat.of (Discrete S)) where
  hom := endoProf Xf
  unit := endoUnit Xf
  mul := pushDesc (BinaryCell.homEquiv (endoCompCell Xf))
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry

end Endo

/-! ### Computation -/

namespace EndoExample

/-- The single sort. -/
abbrev pt : Discrete Unit := ⟨()⟩

/-- Natural numbers on the single sort. -/
abbrev Nat' : Unit → Type := fun _ => ℕ

/-- Addition, a binary operation. -/
def add : (endoProf Nat').app pt (FreeMon.mk [pt, pt]) := fun xs => xs.1 + xs.2.1

/-- The identity, a unary operation. -/
def idOp : (endoProf Nat').app pt (FreeMon.mk [pt]) := fun xs => xs.1

/-- The representative of `add ∘ (add, id)` in the Kleisli composite. -/
def addAddId : ((endoOperad Nat').hom ⊙ₖ (endoOperad Nat').hom).app pt (FreeMon.mk [pt, pt, pt]) :=
  Quot.mk _ ⟨FreeMon.mk [FreeMon.mk [pt, pt], FreeMon.mk [pt]],
    Quot.mk _ ⟨FreeMon.mk [pt, pt], add, (add, (idOp, PUnit.unit))⟩, 𝟙 _⟩

/-- The composite `add ∘ (add, id)`. -/
def addAddIdOp : (endoProf Nat').app pt (FreeMon.mk [pt, pt, pt]) :=
  (((endoOperad Nat').mul.app pt).app (op (FreeMon.mk [pt, pt, pt]))) addAddId

example : addAddIdOp (1, 2, 3, PUnit.unit) = 6 := rfl

example : addAddIdOp (1, 2, 3, PUnit.unit) = 6 := by decide

/- `#eval addAddIdOp (1, 2, 3, PUnit.unit)` fails in this project: the interpreter finds no
native implementation of `CategoryTheory.discreteCategory` (mathlib is not compiled to native
code here), and `#eval` additionally refuses because of the `sorry`s above. -/

end EndoExample

end CategoryTheory
