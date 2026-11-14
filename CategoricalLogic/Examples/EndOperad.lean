/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Operad
public import CategoricalLogic.FreeMon.LaxMonad
meta import CategoricalLogic.FreeMon.LaxMonad

/-!
# The endomorphism operad of a family of types

For `X : S → Type`, the planar operad on the discrete category on `S` whose operations with
inputs `ss` and output `s` are the functions `Tup X ss → X s` from tuples.
-/

@[expose] public section

namespace CategoryTheory.Lax.Endo

open Profunctor FreeMon

variable {S : Type} (X : S → Type)

/-- Tuples of elements of `X` indexed by a list of objects. -/
def Tup : List (Discrete S) → Type
  | [] => PUnit
  | s :: ss => X s.as × Tup ss

variable {X}

/-- Transport along a morphism of the discrete category. -/
def tr {s s' : Discrete S} (α : s ⟶ s') (x : X s.as) : X s'.as := Discrete.eq_of_hom α ▸ x

@[simp] theorem tr_id {s : Discrete S} (x : X s.as) : tr (𝟙 s) x = x := rfl

@[simp] theorem tr_comp {s s' s'' : Discrete S} (α : s ⟶ s') (β : s' ⟶ s'') (x : X s.as) :
    tr (α ≫ β) x = tr β (tr α x) := by
  cases s; cases s'; cases s''
  have h₁ := Discrete.eq_of_hom α
  have h₂ := Discrete.eq_of_hom β
  simp only at h₁ h₂
  subst h₁ h₂
  rfl

/-- Transport of tuples along a list of morphisms. -/
def Tup.map : ∀ {as bs : List (Discrete S)}, FreeMon.Hom as bs → Tup X as → Tup X bs
  | [], [], _, t => t
  | _ :: _, _ :: _, f, t => (tr f.1 t.1, Tup.map f.2 t.2)
  | [], _ :: _, f, _ => PEmpty.elim f
  | _ :: _, [], f, _ => PEmpty.elim f

theorem Tup.map_id : ∀ {as : List (Discrete S)} (t : Tup X as), Tup.map (𝟙 (mk as)) t = t
  | [], _ => rfl
  | _ :: _, t => congrArg (Prod.mk t.1) (Tup.map_id t.2)

theorem Tup.map_comp : ∀ {as bs cs : List (Discrete S)} (f : mk as ⟶ mk bs) (g : mk bs ⟶ mk cs)
    (t : Tup X as), Tup.map (f ≫ g) t = Tup.map g (Tup.map f t)
  | [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, g, t =>
    Prod.ext (tr_comp f.1 g.1 t.1) (Tup.map_comp f.2 g.2 t.2)
  | [], _ :: _, _, f, _, _ => PEmpty.elim f
  | _ :: _, [], _, f, _, _ => PEmpty.elim f
  | [], [], _ :: _, _, g, _ => PEmpty.elim g
  | _ :: _, _ :: _, [], _, g, _ => PEmpty.elim g

variable (X) in
/-- The endomorphism profunctor: `(endo X).app s ss` is `Tup X ss → X s`. -/
def endo : Profunctor.{0} (Discrete S) (FreeMon (Discrete S)) where
  obj s :=
    { obj B := Tup X B.unop.as → X s.as
      map g := TypeCat.ofHom fun φ => φ ∘ Tup.map g.unop
      map_id _ := TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun φ => funext fun t =>
        congrArg φ (Tup.map_id t)))
      map_comp g g' := TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun φ => funext fun t =>
        congrArg φ (Tup.map_comp g'.unop g.unop t))) }
  map α := { app _ := TypeCat.ofHom fun φ t => tr α (φ t) }
  map_id _ := NatTrans.ext (funext fun _ => TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun _ => rfl)))
  map_comp α β := NatTrans.ext (funext fun _ => TypeCat.Hom.ext (TypeCat.Fun.ext
    (funext fun φ => funext fun t => tr_comp α β (φ t))))

@[simp] theorem endo_mapL {s s' : Discrete S} {B : FreeMon (Discrete S)} (α : s ⟶ s')
    (φ : (endo X).app s B) : (endo X).mapL α φ = fun t => tr α (φ t) := rfl

@[simp] theorem endo_mapR {s : Discrete S} {B B' : FreeMon (Discrete S)} (g : B ⟶ B')
    (φ : (endo X).app s B') : (endo X).mapR g φ = φ ∘ Tup.map g := rfl

/-! ### Splitting tuples and evaluating families -/

/-- Split a tuple over a concatenation. -/
def split : ∀ {as : List (Discrete S)} {bs : List (Discrete S)}, Tup X (as ++ bs) →
    Tup X as × Tup X bs
  | [], _, t => (PUnit.unit, t)
  | _ :: _, _, t => ((t.1, (split t.2).1), (split t.2).2)

theorem split_map : ∀ {as as' bs bs' : List (Discrete S)} (f : FreeMon.Hom as as')
    (g : FreeMon.Hom bs bs') (t : Tup X (as ++ bs)),
    split (Tup.map (FreeMon.append (A := mk as) (B := mk as') (A' := mk bs) (B' := mk bs') f g) t) =
      (Tup.map f (split t).1, Tup.map g (split t).2)
  | [], [], _, _, _, _, _ => rfl
  | _ :: _, _ :: _, _, _, f, g, t => by
    change ((tr f.1 t.1, (split (Tup.map (FreeMon.append (A := mk _) (B := mk _) (A' := mk _)
        (B' := mk _) f.2 g) t.2)).1), (split (Tup.map (FreeMon.append (A := mk _) (B := mk _)
        (A' := mk _) (B' := mk _) f.2 g) t.2)).2) = _
    rw [split_map f.2 g t.2]
    rfl
  | [], _ :: _, _, _, f, _, _ => PEmpty.elim f
  | _ :: _, [], _, _, f, _, _ => PEmpty.elim f

/-- Evaluate a family of operations on a tuple over the concatenation of their inputs. -/
def eval : ∀ {bs : List (Discrete S)} {Cs : List (FreeMon (Discrete S))},
    LP (endo X) bs Cs → Tup X (Cs.flatMap FreeMon.as) → Tup X bs
  | [], [], _, _ => PUnit.unit
  | _ :: _, _ :: _, fs, t => (fs.1 (split t).1, eval fs.2 (split t).2)
  | [], _ :: _, fs, _ => isEmptyElim fs
  | _ :: _, [], fs, _ => isEmptyElim fs

theorem eval_mapL : ∀ {bs bs' : List (Discrete S)} {Cs : List (FreeMon (Discrete S))}
    (α : FreeMon.Hom bs bs') (fs : LP (endo X) bs Cs) (t : Tup X (Cs.flatMap FreeMon.as)),
    eval (LP.mapL α fs) t = Tup.map α (eval fs t)
  | [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, α, fs, _ =>
    congrArg (Prod.mk _) (eval_mapL α.2 fs.2 _)
  | [], _ :: _, _, α, _, _ => PEmpty.elim α
  | _ :: _, [], _, α, _, _ => PEmpty.elim α
  | [], [], _ :: _, _, fs, _ => isEmptyElim fs
  | _ :: _, _ :: _, [], _, fs, _ => isEmptyElim fs

theorem eval_mapR : ∀ {bs : List (Discrete S)} {Cs Cs' : List (FreeMon (Discrete S))}
    (fs : LP (endo X) bs Cs') (g : mk Cs ⟶ mk Cs') (t : Tup X (Cs.flatMap FreeMon.as)),
    eval (LP.mapR g fs) t = eval fs (Tup.map ((FreeMon.flatten _).map g) t)
  | [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, fs, g, t => by
    have h := split_map g.1 ((FreeMon.flatten _).map (FreeMon.tail g)) t
    have ih := eval_mapR fs.2 g.2 (split t).2
    have h₁' := congrArg _root_.Prod.fst h
    have h₂' := congrArg _root_.Prod.snd h
    have h₁ : (split (Tup.map ((FreeMon.flatten _).map g) t)).1 = Tup.map g.1 (split t).1 := h₁'
    have h₂ : (split (Tup.map ((FreeMon.flatten _).map g) t)).2 =
        Tup.map ((FreeMon.flatten _).map g.2) (split t).2 := h₂'
    change (fs.1 (Tup.map g.1 (split t).1), eval (LP.mapR g.2 fs.2) (split t).2) =
      (fs.1 (split (Tup.map ((FreeMon.flatten _).map g) t)).1,
        eval fs.2 (split (Tup.map ((FreeMon.flatten _).map g) t)).2)
    rw [h₁, h₂, ih]
    rfl
  | _, [], _ :: _, _, g, _ => PEmpty.elim g
  | _, _ :: _, [], _, g, _ => PEmpty.elim g
  | [], _ :: _, _ :: _, fs, _, _ => isEmptyElim fs
  | _ :: _, [], [], fs, _, _ => isEmptyElim fs


/-! ### Identities and composition -/

variable (X) in
/-- The identities of the endomorphism operad: the projection out of a singleton tuple. -/
def ident : NullaryCell (endo X) (𝟭 _) (FreeMon.unit _) where
  app _ := fun t => t.1
  naturality _ := rfl

variable (X) in
/-- The composition of the endomorphism operad: substitution of a family of functions. -/
def comp : BinaryCell (endo X) (LP.prof (endo X)) (endo X) (𝟭 _) (FreeMon.flatten _) where
  app φ fs := fun t => φ (eval fs t)
  wedge φ α fs := funext fun t => congrArg φ (eval_mapL α fs t).symm
  natL _ _ _ := rfl
  natR φ fs g := funext fun t => congrArg φ (eval_mapR fs g t)

@[simp] theorem comp_app {a : Discrete S} {B : FreeMon (Discrete S)}
    {Cs : FreeMon (FreeMon (Discrete S))} (φ : (endo X).app a B)
    (fs : (LP.prof (endo X)).app B Cs) :
    (comp X).app φ fs = fun t => φ (eval fs t) := rfl


/-! ### Tuples over concatenations -/

/-- Concatenation of tuples. -/
def tupAppend {bs : List (Discrete S)} : ∀ {as : List (Discrete S)}, Tup X as → Tup X bs →
    Tup X (as ++ bs)
  | [], _, u => u
  | _ :: _, t, u => (t.1, tupAppend t.2 u)

theorem split_tupAppend {bs : List (Discrete S)} : ∀ {as : List (Discrete S)} (t : Tup X as)
    (u : Tup X bs), split (tupAppend t u) = (t, u)
  | [], _, _ => rfl
  | _ :: _, t, u => by
    change ((t.1, (split (tupAppend t.2 u)).1), (split (tupAppend t.2 u)).2) = (t, u)
    rw [split_tupAppend t.2 u]
    rfl

theorem tupAppend_split {bs : List (Discrete S)} : ∀ {as : List (Discrete S)}
    (t : Tup X (as ++ bs)), tupAppend (split t).1 (split t).2 = t
  | [], _ => rfl
  | _ :: _, t => congrArg (Prod.mk t.1) (tupAppend_split t.2)

theorem Tup.cons_heq {a : Discrete S} {as bs : List (Discrete S)} (h : as = bs) (x : X a.as)
    {t : Tup X as} {t' : Tup X bs} (ht : t ≍ t') :
    (show Tup X (a :: as) from (x, t)) ≍ (show Tup X (a :: bs) from (x, t')) := by
  subst h; cases ht; rfl

theorem tupAppend_assoc_heq {bs cs : List (Discrete S)} : ∀ {as : List (Discrete S)}
    (a : Tup X as) (b : Tup X bs) (c : Tup X cs),
    tupAppend (tupAppend a b) c ≍ tupAppend a (tupAppend b c)
  | [], _, _, _ => HEq.rfl
  | _ :: as, a, b, c => Tup.cons_heq (List.append_assoc as bs cs) a.1
      (tupAppend_assoc_heq a.2 b c)

theorem Tup.map_eqToHom_heq {A B : FreeMon (Discrete S)} (h : A = B) (t : Tup X A.as) :
    Tup.map (as := A.as) (bs := B.as) (eqToHom h) t ≍ t := by
  subst h; exact heq_of_eq (Tup.map_id t)

theorem split_nil_heq : ∀ {as : List (Discrete S)} (t : Tup X (as ++ [])),
    (split (bs := []) t).1 ≍ t
  | [], _ => HEq.rfl
  | _ :: as, t => Tup.cons_heq (List.append_nil as).symm t.1 (split_nil_heq t.2)

theorem split_heq {as bs bs' : List (Discrete S)} (h : bs = bs') (t : Tup X (as ++ bs))
    (t' : Tup X (as ++ bs')) (ht : t ≍ t') : (split t).1 = (split t').1 ∧ (split t).2 ≍ (split t').2 := by
  subst h; obtain rfl := eq_of_heq ht; exact ⟨rfl, HEq.rfl⟩

theorem eval_append : ∀ {bs bs' : List (Discrete S)} {Cs Cs' : List (FreeMon (Discrete S))}
    (fs : LP (endo X) bs Cs) (fs' : LP (endo X) bs' Cs')
    (t : Tup X ((Cs ++ Cs').flatMap FreeMon.as))
    (u : Tup X (Cs.flatMap FreeMon.as ++ Cs'.flatMap FreeMon.as)), t ≍ u →
    eval (LP.append fs fs') t = tupAppend (eval fs (split u).1) (eval fs' (split u).2)
  | [], _, [], _, _, fs', _, _, h => congrArg (eval fs') (eq_of_heq h)
  | _ :: _, _, C :: Cs, Cs', fs, fs', t, u, h => by
    have e : tupAppend (tupAppend (split (split u).1).1 (split (split u).1).2) (split u).2 = u := by
      rw [tupAppend_split, tupAppend_split]
    have h' := h.trans ((heq_of_eq e).symm.trans (tupAppend_assoc_heq _ _ _))
    obtain ⟨h1, h2⟩ := split_heq (as := C.as) (List.flatMap_append (xs := Cs) (ys := Cs')) t _ h'
    simp only [split_tupAppend] at h1 h2
    change (fs.1 (split t).1, eval (LP.append fs.2 fs') (split t).2) =
      (fs.1 (split (split u).1).1,
        tupAppend (eval fs.2 (split (split u).1).2) (eval fs' (split u).2))
    rw [h1, eval_append fs.2 fs' _ _ h2, split_tupAppend]
  | [], _, _ :: _, _, fs, _, _, _, _ => isEmptyElim fs
  | _ :: _, _, [], _, fs, _, _, _, _ => isEmptyElim fs

theorem flatMap_flatten (Ds : List (FreeMon (FreeMon (Discrete S)))) :
    (Ds.flatMap FreeMon.as).flatMap FreeMon.as =
      (Ds.map (FreeMon.flatten (Discrete S)).obj).flatMap FreeMon.as := by
  exact LP.flatMap_flatten Ds

theorem eval_assoc : ∀ {bs : List (Discrete S)} {Cs : List (FreeMon (Discrete S))}
    {Ds : List (FreeMon (FreeMon (Discrete S)))} (g : LP (endo X) bs Cs)
    (f : LP (LP.prof (endo X)) Cs Ds) (t : Tup X ((Ds.flatMap FreeMon.as).flatMap FreeMon.as))
    (t' : Tup X ((Ds.map (FreeMon.flatten _).obj).flatMap FreeMon.as)), t ≍ t' →
    eval g (eval (LP.flat f) t) ≍ eval (LP.smap (Square.ofBinary (comp X)) (LP.zip g f)) t'
  | [], [], [], _, _, _, _, _ => HEq.rfl
  | b :: bs, C :: Cs, D :: Ds, g, f, t, t', h => by
    let u : Tup X (D.as.flatMap FreeMon.as ++ (Ds.flatMap FreeMon.as).flatMap FreeMon.as) :=
      cast (congrArg (Tup X) (List.flatMap_append (xs := D.as)
        (ys := Ds.flatMap FreeMon.as) (f := FreeMon.as))) t
    have hu : t ≍ u := (cast_heq _ t).symm
    obtain ⟨h1, h2⟩ := split_heq (as := D.as.flatMap FreeMon.as) (flatMap_flatten Ds) u t'
      (hu.symm.trans h)
    change eval g (eval (LP.append f.1 (LP.flat f.2)) t) ≍
      (show Tup X (b :: bs.map (𝟭 _).obj) from
        (g.1 (eval f.1 (split t').1), eval (LP.smap (Square.ofBinary (comp X)) (LP.zip g.2 f.2)) (split t').2))
    rw [eval_append f.1 (LP.flat f.2) t u hu]
    change (show Tup X (b :: bs) from
        (g.1 (split (tupAppend (eval f.1 (split u).1) (eval (LP.flat f.2) (split u).2))).1,
          eval g.2 (split (tupAppend (eval f.1 (split u).1)
            (eval (LP.flat f.2) (split u).2))).2)) ≍ _
    rw [split_tupAppend, h1]
    exact Tup.cons_heq (List.map_id' bs).symm _ (eval_assoc g.2 f.2 _ _ h2)
  | [], _ :: _, _, g, _, _, _, _ => isEmptyElim g
  | _ :: _, [], _, g, _, _, _, _ => isEmptyElim g
  | _, [], _ :: _, _, f, _, _, _ => isEmptyElim f
  | _, _ :: _, [], _, f, _, _, _ => isEmptyElim f

theorem eval_ident_heq : ∀ (as : List (Discrete S))
    (t : Tup X ((as.map (FreeMon.unit (Discrete S)).obj).flatMap FreeMon.as)),
    eval (LP.smap (Square.ofNullary (ident X)) (LP.ofHom (𝟙 (mk as)))) t ≍ t
  | [], _ => HEq.rfl
  | _ :: as, t => Tup.cons_heq (as := as.map (𝟭 _).obj)
      ((LP.map_id_list as).trans (LP.flatMap_unit as).symm) t.1 (eval_ident_heq as t.2)

variable (X) in
/-- The endomorphism operad of a family of types. -/
def operad : Operad freeMon (Discrete S) :=
  .ofCells (endo X) (ident X) (comp X)
  (fun f => by
    funext t
    exact congrArg f (eq_of_heq ((split_nil_heq _).trans
      (Tup.map_eqToHom_heq (Functor.congr_obj (freeMon.left_unit (Discrete S)) _) t).symm)))
  (fun {a b} f => by
    funext t
    change f (eval (freeMon.mapCov (Square.ofNullary (ident X))
      |>.app ((freeMon.unit (Discrete S)).app (𝟙 b))) t) = _
    rw [LaxFunctor.mapCov_app]
    change f (eval (LP.mapL (eqToHom (Functor.congr_obj (freeMon.map_id (Discrete S)) _))
        (LP.smap (Square.ofNullary (ident X)) (LP.ofHom (FreeMon.Hom.id _)))) t) =
      f (Tup.map (eqToHom (Functor.congr_obj (freeMon.right_unit (Discrete S)) _)) t)
    exact congrArg f (eq_of_heq ((heq_of_eq (eval_mapL _ _ _)).trans
      ((Tup.map_eqToHom_heq (Functor.congr_obj (freeMon.map_id (Discrete S)) _) _).trans
      ((eval_ident_heq _ t).trans
        (Tup.map_eqToHom_heq (Functor.congr_obj (freeMon.right_unit (Discrete S)) _) t).symm)))))
  (fun h g f => by
    funext t
    change h (eval g (eval (LP.flat f) t)) = h (eval (freeMon.mapCov (Square.ofBinary (comp X))
      |>.app ((freeMon.lax _ _).app (compMk g f))) (Tup.map (eqToHom
        (Functor.congr_obj (freeMon.assoc (Discrete S)) _).symm) t))
    rw [LaxFunctor.mapCov_app]
    change h (eval g (eval (LP.flat f) t)) =
      h (eval (LP.mapL (eqToHom (Functor.congr_obj (freeMon.map_id (Discrete S)) _))
        (LP.smap (Square.ofBinary (comp X)) (LP.zip g f)))
        (Tup.map (eqToHom (Functor.congr_obj (freeMon.assoc (Discrete S)) _).symm) t))
    exact congrArg h (eq_of_heq ((eval_assoc g f t _
      (Tup.map_eqToHom_heq (Functor.congr_obj (freeMon.assoc (Discrete S)) _).symm t).symm).trans
      ((Tup.map_eqToHom_heq (Functor.congr_obj (freeMon.map_id (Discrete S)) _) _).symm.trans
        (heq_of_eq (eval_mapL _ _ _).symm)))))

end CategoryTheory.Lax.Endo

/-! ### Computing -/

namespace CategoryTheory.Lax.Endo.Example

open FreeMon

/-- The unique object. -/
abbrev pt : Discrete Unit := ⟨()⟩

/-- The natural numbers, as a family over `Unit`. -/
abbrev N : Unit → Type := fun _ => ℕ

/-- Addition, a binary operation. -/
def add : (endo N).app pt (mk [pt, pt]) := fun t => t.1 + t.2.1

/-- The identity, a unary operation. -/
def idOp : (endo N).app pt (mk [pt]) := fun t => t.1

/-- The family `(add, id)`. -/
def fam : (LP.prof (endo N)).app (mk [pt, pt]) (mk [mk [pt, pt], mk [pt]]) :=
  LP.cons add (LP.cons idOp LP.nil)

/-- `add ∘ (add, id)`, a ternary operation. -/
def composite := (operad N).mul add fam

example : composite ((1 : ℕ), (2 : ℕ), (3 : ℕ), PUnit.unit) = 6 := rfl

example : composite ((1 : ℕ), (2 : ℕ), (3 : ℕ), PUnit.unit) = 6 := by decide

#eval composite ((1 : ℕ), (2 : ℕ), (3 : ℕ), PUnit.unit)

end CategoryTheory.Lax.Endo.Example
