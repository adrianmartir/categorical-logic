/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Bespoke.Instance

/-!
# The endomorphism operad of a functor to types

For a category `X` and a functor `V : X ⥤ Type w`, the planar (`Cat.freeMon`-)operad
`endOperad V` has as operations with output `a` and inputs `as` the functions
`Tuple V as → V.obj a`, where `Tuple V as` is the type of tuples of values matching `as`.
For a family of types `X : S → Type`, the endomorphism operad of the family on the discrete
category on `S` is `endOperad (Discrete.functor X)`.

Working over an arbitrary category `X` costs nothing over the discrete case and avoids the
transports of `Discrete`.
-/

@[expose] public section

namespace CategoryTheory

universe w v u

open Profunctor FreeMon FreeMon.ProfApp

namespace FreeMon

variable {X : Type u} [Category.{v} X] (V : X ⥤ Type w)

/-- Tuples of values of `V`, matching a list of objects. -/
def Tuple : List X → Type w
  | [] => PUnit
  | x :: xs => V.obj x × Tuple xs

namespace Tuple

variable {V}

/-- The action of a list of morphisms on tuples, positionwise. -/
def map : ∀ {xs ys : List X}, (mk xs ⟶ mk ys) → Tuple V xs → Tuple V ys
  | [], [], _, t => t
  | _ :: _, _ :: _, f, t => (V.map (FreeMon.head f) t.1, map (FreeMon.tail f) t.2)
  | [], _ :: _, f, _ => isEmptyElim f
  | _ :: _, [], f, _ => isEmptyElim f

theorem map_id : ∀ {xs : List X} (t : Tuple V xs), map (𝟙 (mk xs)) t = t
  | [], _ => rfl
  | _ :: _, t => Prod.ext (show V.map (𝟙 _) t.1 = t.1 by simp) (map_id t.2)

theorem map_comp : ∀ {xs ys zs : List X} (f : mk xs ⟶ mk ys) (g : mk ys ⟶ mk zs)
    (t : Tuple V xs), map (f ≫ g) t = map g (map f t)
  | [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, g, t =>
    Prod.ext (show V.map (FreeMon.head f ≫ FreeMon.head g) t.1 =
        V.map (FreeMon.head g) (V.map (FreeMon.head f) t.1) by simp)
      (map_comp (FreeMon.tail f) (FreeMon.tail g) t.2)
  | [], _ :: _, _, f, _, _ => isEmptyElim f
  | _ :: _, [], _, f, _, _ => isEmptyElim f
  | [], [], _ :: _, _, g, _ => isEmptyElim g
  | _ :: _, _ :: _, [], _, g, _ => isEmptyElim g

@[simp] theorem map_id' (A : FreeMon X) (t : Tuple V A.as) : map (𝟙 A) t = t := map_id t

theorem map_eqToHom_heq {A B : FreeMon X} (h : A = B) (t : Tuple V A.as) :
    map (eqToHom h) t ≍ t := by
  subst h
  exact heq_of_eq (map_id t)

/-- Concatenation of tuples. -/
def append : ∀ {xs ys : List X}, Tuple V xs → Tuple V ys → Tuple V (xs ++ ys)
  | [], _, _, u => u
  | _ :: _, _, t, u => (t.1, append t.2 u)

/-- Splitting a tuple. -/
def split : ∀ {xs ys : List X}, Tuple V (xs ++ ys) → Tuple V xs × Tuple V ys
  | [], _, t => (PUnit.unit, t)
  | _ :: _, _, t => ((t.1, (split t.2).1), (split t.2).2)

theorem split_append : ∀ {xs ys : List X} (t : Tuple V xs) (u : Tuple V ys),
    split (append t u) = (t, u)
  | [], _, _, _ => rfl
  | _ :: _, _, t, u => Prod.ext (Prod.ext rfl (Prod.ext_iff.mp (split_append t.2 u)).1)
    (Prod.ext_iff.mp (split_append t.2 u)).2

theorem append_split : ∀ {xs ys : List X} (t : Tuple V (xs ++ ys)),
    append (split t).1 (split t).2 = t
  | [], _, _ => rfl
  | _ :: _, _, t => Prod.ext rfl (append_split t.2)

theorem cons_heq_cons {x x' : X} {xs xs' : List X} {v : V.obj x} {v' : V.obj x'}
    {t : Tuple V xs} {t' : Tuple V xs'} (hx : x = x') (hxs : xs = xs') (hv : v ≍ v')
    (ht : t ≍ t') : ((v, t) : Tuple V (x :: xs)) ≍ ((v', t') : Tuple V (x' :: xs')) := by
  subst hx hxs
  cases hv
  cases ht
  rfl

theorem append_heq_append {xs xs' ys ys' : List X} {t : Tuple V xs} {t' : Tuple V xs'}
    {u : Tuple V ys} {u' : Tuple V ys'} (hx : xs = xs') (hy : ys = ys') (ht : t ≍ t')
    (hu : u ≍ u') : append t u ≍ append t' u' := by
  subst hx hy
  cases ht
  cases hu
  rfl

theorem split_heq {xs xs' ys ys' : List X} {t : Tuple V (xs ++ ys)} {t' : Tuple V (xs' ++ ys')}
    (hx : xs = xs') (hy : ys = ys') (ht : t ≍ t') :
    (split t).1 ≍ (split t').1 ∧ (split t).2 ≍ (split t').2 := by
  subst hx hy
  cases ht
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem append_assoc_heq : ∀ {xs ys zs : List X} (t : Tuple V xs) (u : Tuple V ys)
    (r : Tuple V zs), append (append t u) r ≍ append t (append u r)
  | [], _, _, _, _, _ => HEq.rfl
  | _ :: _, _, _, t, u, r =>
    cons_heq_cons rfl (List.append_assoc _ _ _) HEq.rfl (append_assoc_heq t.2 u r)

theorem split_nil_heq : ∀ {xs : List X} (t : Tuple V (xs ++ [])), (split t).1 ≍ t
  | [], _ => HEq.rfl
  | _ :: _, t => cons_heq_cons rfl (List.append_nil _).symm HEq.rfl (split_nil_heq t.2)

theorem split_map : ∀ {xs xs' ys ys' : List X} (f : mk xs ⟶ mk xs') (g : mk ys ⟶ mk ys')
    (t : Tuple V (xs ++ ys)),
    split (map (FreeMon.append f g) t) = (map f (split t).1, map g (split t).2)
  | [], [], _, _, _, _, _ => rfl
  | _ :: _, _ :: _, _, _, f, g, t => by
    have ih := split_map (FreeMon.tail f) g t.2
    exact Prod.ext (Prod.ext rfl (Prod.ext_iff.mp ih).1) (Prod.ext_iff.mp ih).2
  | [], _ :: _, _, _, f, _, _ => isEmptyElim f
  | _ :: _, [], _, _, f, _, _ => isEmptyElim f

end Tuple

/-- The profunctor of operations of the endomorphism operad: `(endProf V).app a B` is the type
of functions `Tuple V B.as → V.obj a`. -/
def endProf : Profunctor.{w} X (FreeMon X) where
  obj a :=
    { obj B := Tuple V B.unop.as → V.obj a
      map g := TypeCat.ofHom fun φ t => φ (Tuple.map g.unop t)
      map_id _ := TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun φ => funext fun t =>
        congrArg φ (Tuple.map_id t)))
      map_comp g g' := TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun φ => funext fun t =>
        congrArg φ (Tuple.map_comp g'.unop g.unop t))) }
  map f :=
    { app _ := TypeCat.ofHom fun φ t => V.map f (φ t)
      naturality _ _ _ := rfl }
  map_id _ := NatTrans.ext (funext fun _ => TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun φ =>
    funext fun t => show V.map (𝟙 _) (φ t) = φ t by simp)))
  map_comp f f' := NatTrans.ext (funext fun _ => TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun φ =>
    funext fun t => show V.map (f ≫ f') (φ t) = V.map f' (V.map f (φ t)) by simp)))

variable {V}

@[simp] theorem endProf_mapL_apply {a a' : X} {B : FreeMon X} (f : a ⟶ a')
    (φ : (endProf V).app a B) (t : Tuple V B.as) : (endProf V).mapL f φ t = V.map f (φ t) := rfl

@[simp] theorem endProf_mapR_apply {a : X} {B B' : FreeMon X} (g : B ⟶ B')
    (φ : (endProf V).app a B') (t : Tuple V B.as) :
    (endProf V).mapR g φ t = φ (Tuple.map g t) := rfl

/-- Evaluate a list of operations on a tuple of the concatenation of their inputs. -/
def eval : ∀ {bs : List X} {Cs : List (FreeMon X)}, ProfApp (endProf V) bs Cs →
    Tuple V (Cs.flatMap FreeMon.as) → Tuple V bs
  | [], [], _, _ => PUnit.unit
  | _ :: _, C :: Cs, e, t =>
    (ProfApp.head e (Tuple.split (xs := C.as) (ys := Cs.flatMap FreeMon.as) t).1,
      eval (ProfApp.tail e) (Tuple.split (xs := C.as) (ys := Cs.flatMap FreeMon.as) t).2)
  | [], _ :: _, e, _ => isEmptyElim e
  | _ :: _, [], e, _ => isEmptyElim e

theorem eval_mapL : ∀ {bs bs' : List X} {Cs : List (FreeMon X)} (f : mk bs ⟶ mk bs')
    (e : ProfApp (endProf V) bs Cs) (t : Tuple V (Cs.flatMap FreeMon.as)),
    eval (ProfApp.mapL f e) t = Tuple.map f (eval e t)
  | [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, e, t => Prod.ext rfl (eval_mapL (FreeMon.tail f) (ProfApp.tail e) (Tuple.split t).2)
  | [], _ :: _, _, f, _, _ => isEmptyElim f
  | _ :: _, [], _, f, _, _ => isEmptyElim f
  | [], [], _ :: _, _, e, _ => isEmptyElim e
  | _ :: _, _ :: _, [], _, e, _ => isEmptyElim e

theorem eval_mapR : ∀ {bs : List X} {Cs Cs' : List (FreeMon X)} (g : mk Cs ⟶ mk Cs')
    (e : ProfApp (endProf V) bs Cs') (t : Tuple V (Cs.flatMap FreeMon.as)),
    eval (ProfApp.mapR g e) t = eval e (Tuple.map ((flatten X).map g) t)
  | [], [], [], _, _, _ => rfl
  | _ :: _, C :: Cs, C' :: Cs', g, e, t => by
    have h : Tuple.split (xs := C'.as) (Tuple.map ((flatten X).map g) t) =
        (Tuple.map (FreeMon.head g) (Tuple.split (xs := C.as) t).1,
          Tuple.map ((flatten X).map (FreeMon.tail g)) (Tuple.split (xs := C.as) t).2) :=
      Tuple.split_map _ _ t
    change (ProfApp.head e (Tuple.map (FreeMon.head g) (Tuple.split (xs := C.as) t).1),
        eval (ProfApp.mapR (FreeMon.tail g) (ProfApp.tail e)) (Tuple.split (xs := C.as) t).2) =
      (ProfApp.head e (Tuple.split (xs := C'.as) (Tuple.map ((flatten X).map g) t)).1,
        eval (ProfApp.tail e) (Tuple.split (xs := C'.as) (Tuple.map ((flatten X).map g) t)).2)
    rw [h]
    exact Prod.ext rfl (eval_mapR (FreeMon.tail g) (ProfApp.tail e) _)
  | _, [], _ :: _, g, _, _ => isEmptyElim g
  | _, _ :: _, [], g, _, _ => isEmptyElim g
  | [], _ :: _, _ :: _, _, e, _ => isEmptyElim e
  | _ :: _, [], [], _, e, _ => isEmptyElim e

variable (V)

/-- The identity operations: projection from a singleton tuple. -/
def endId : NullaryCell (endProf V) (𝟭 X) (unit X) where
  app _ t := t.1
  naturality _ := rfl

/-- Composition of operations: evaluate the family, then the operation. -/
def endComp : BinaryCell (endProf V) (prof (endProf V)) (endProf V) (𝟭 X) (flatten X) where
  app g e t := g (eval e t)
  wedge g f e := funext fun t => congrArg g (eval_mapL f e t).symm
  natL _ _ _ := rfl
  natR g e γ := funext fun t => congrArg g (eval_mapR γ e t)

variable {V}

theorem eval_mapNu_heq : ∀ (bs : List X) (t : Tuple V ((bs.map (unit X).obj).flatMap FreeMon.as)),
    eval (mapNu (endId V) bs) t ≍ t
  | [], _ => HEq.rfl
  | _ :: bs, t => Tuple.cons_heq_cons (v' := t.1) (t' := t.2) rfl
    ((congrArg FreeMon.as (map_id_obj X (mk bs))).trans
      (congrArg FreeMon.as (map_unit_flatten_obj X (mk bs))).symm) HEq.rfl
    (eval_mapNu_heq bs t.2)

theorem eval_append {ks ks' : List X} {Ls Ls' : List (FreeMon X)} :
    ∀ (e : ProfApp (endProf V) ks Ls) (e' : ProfApp (endProf V) ks' Ls')
    (t : Tuple V ((Ls ++ Ls').flatMap FreeMon.as)) (t₁ : Tuple V (Ls.flatMap FreeMon.as))
    (t₂ : Tuple V (Ls'.flatMap FreeMon.as)), t ≍ Tuple.append t₁ t₂ →
    eval (ProfApp.append e e') t = Tuple.append (eval e t₁) (eval e' t₂) := by
  intro e
  induction e using ProfApp.rec' with
  | nil =>
    intro e' t t₁ t₂ ht
    exact congrArg (eval e') (eq_of_heq ht)
  | @cons k L ks Ls p ps ih =>
    intro e' t t₁ t₂ ht
    have hu : t ≍ Tuple.append (Tuple.split (xs := L.as) t₁).1
        (Tuple.append (Tuple.split (xs := L.as) t₁).2 t₂) :=
      ht.trans ((Tuple.append_heq_append rfl rfl
        (heq_of_eq (Tuple.append_split t₁)).symm HEq.rfl).trans (Tuple.append_assoc_heq _ _ _))
    have hs := Tuple.split_heq (xs := L.as) (xs' := L.as) rfl
      (congrArg FreeMon.as (flatten_obj_append (mk Ls) (mk Ls'))) hu
    have k := Tuple.split_append (Tuple.split (xs := L.as) t₁).1
      (Tuple.append (Tuple.split (xs := L.as) t₁).2 t₂)
    exact Prod.ext (congrArg p (eq_of_heq (hs.1.trans (heq_of_eq (Prod.ext_iff.mp k).1))))
      (ih e' _ _ t₂ (hs.2.trans (heq_of_eq (Prod.ext_iff.mp k).2)))

theorem eval_flat_heq : ∀ {bs : List X} {Cs : List (FreeMon X)}
    {Ds : List (FreeMon (FreeMon X))} (g : ProfApp (endProf V) bs Cs)
    (f : ProfApp (prof (endProf V)) Cs Ds)
    (t : Tuple V ((Ds.flatMap FreeMon.as).flatMap FreeMon.as))
    (t' : Tuple V ((Ds.map (flatten X).obj).flatMap FreeMon.as)), t ≍ t' →
    eval g (eval (flat f) t) ≍ eval (mapBi (endComp V) g f) t'
  | [], [], [], _, _, _, _, _ => HEq.rfl
  | _ :: _, C :: Cs, D :: Ds, g, f, t, t', ht => by
    have hL : (Ds.map (flatten X).obj).flatMap FreeMon.as =
        (Ds.flatMap FreeMon.as).flatMap FreeMon.as :=
      congrArg FreeMon.as (map_flatten_flatten_obj X (mk Ds))
    let t₂ := cast (congrArg (Tuple V) hL)
      (Tuple.split (xs := D.as.flatMap FreeMon.as)
        (ys := (Ds.map (flatten X).obj).flatMap FreeMon.as) t').2
    have ht' : t ≍ Tuple.append (Tuple.split (xs := D.as.flatMap FreeMon.as)
        (ys := (Ds.map (flatten X).obj).flatMap FreeMon.as) t').1 t₂ :=
      ht.trans ((heq_of_eq (Tuple.append_split t')).symm.trans
        (Tuple.append_heq_append rfl hL HEq.rfl (cast_heq _ _).symm))
    have h := eval_append (ProfApp.head f) (flat (ProfApp.tail f)) t _ t₂ ht'
    have e1 : eval g (Tuple.append (eval (ProfApp.head f) (Tuple.split (xs := D.as.flatMap FreeMon.as)
          (ys := (Ds.map (flatten X).obj).flatMap FreeMon.as) t').1) (eval (flat (ProfApp.tail f)) t₂)) =
        (ProfApp.head g (eval (ProfApp.head f) (Tuple.split (xs := D.as.flatMap FreeMon.as)
          (ys := (Ds.map (flatten X).obj).flatMap FreeMon.as) t').1),
          eval (ProfApp.tail g) (eval (flat (ProfApp.tail f)) t₂)) := by
      change (ProfApp.head g (Tuple.split (Tuple.append _ _)).1,
        eval (ProfApp.tail g) (Tuple.split (Tuple.append _ _)).2) = _
      rw [Tuple.split_append]
    change eval g (eval (ProfApp.append (ProfApp.head f) (flat (ProfApp.tail f))) t) ≍ _
    rw [h, e1]
    exact Tuple.cons_heq_cons rfl (congrArg FreeMon.as (map_id_obj X (mk _))).symm HEq.rfl
      (eval_flat_heq (ProfApp.tail g) (ProfApp.tail f) t₂ _ (cast_heq _ _))
  | [], _ :: _, _, g, _, _, _, _ => isEmptyElim g
  | _ :: _, [], _, g, _, _, _, _ => isEmptyElim g
  | [], [], _ :: _, _, f, _, _, _ => isEmptyElim f
  | _ :: _, _ :: _, [], _, f, _, _, _ => isEmptyElim f

@[simp] theorem endComp_app {x : X} {y : FreeMon X} {z : FreeMon (FreeMon X)} (g : (endProf V).app x y)
    (e : (prof (endProf V)).app y z) (t : Tuple V (z.as.flatMap FreeMon.as)) :
    (endComp V).app g e t = g (eval e t) := rfl

theorem endProf_mpRight_apply {a : X} {B B' : FreeMon X} (φ : (endProf V).app a B')
    (h : B = B') (t : Tuple V B.as) :
    (endProf V).mpRight φ h t = φ (Tuple.map (eqToHom h) t) := rfl

theorem eval_mpLeft {B B' : FreeMon X} {C : FreeMon (FreeMon X)} (h : B = B')
    (e : (prof (endProf V)).app B C) (t : Tuple V (C.as.flatMap FreeMon.as)) :
    eval ((prof (endProf V)).mpLeft h e) t = Tuple.map (eqToHom h) (eval e t) := by
  subst h
  rw [mpLeft_rfl]
  exact (Tuple.map_id _).symm

theorem eval_mpRight {B : FreeMon X} {C C' : FreeMon (FreeMon X)} (e : (prof (endProf V)).app B C')
    (h : C = C') (t : Tuple V (C.as.flatMap FreeMon.as)) :
    eval ((prof (endProf V)).mpRight e h) t =
      eval e (Tuple.map (eqToHom (congrArg (flatten X).obj h)) t) := by
  subst h
  rw [mpRight_rfl]
  exact congrArg (eval e) (Tuple.map_id t).symm

variable (V)

/-- The endomorphism operad of a functor `V : X ⥤ Type w`. -/
def endOperad : Operad.{u, v, w} Cat.freeMon (Cat.of X) where
  hom := endProf V
  id := endId V
  comp := endComp V
  comp_id f := funext fun t => by
    refine Eq.trans ?_ (endProf_mpRight_apply f _ t).symm
    exact congrArg f
      (eq_of_heq ((Tuple.split_nil_heq t).trans (Tuple.map_eqToHom_heq _ t).symm))
  id_comp {a b} f := funext fun t => by
    refine Eq.trans (endComp_app f _ t) (Eq.trans ?_ (endProf_mpRight_apply f _ t).symm)
    refine congrArg f (eq_of_heq ?_)
    refine (heq_of_eq (eval_mpLeft _ _ t)).trans ?_
    refine (Tuple.map_eqToHom_heq _ _).trans ?_
    refine (heq_of_eq (eval_mpRight _ _ _)).trans ?_
    refine (eval_mapNu_heq b.as _).trans ?_
    exact (Tuple.map_eqToHom_heq _ _).trans (Tuple.map_eqToHom_heq _ _).symm
  comp_assoc {a b c d} h g f := funext fun t => by
    refine Eq.trans (endComp_app _ _ t) (Eq.trans ?_ (endProf_mpRight_apply _ _ t).symm)
    refine Eq.trans (endComp_app h g _) (Eq.trans ?_ (endComp_app h _ _).symm)
    refine congrArg h (eq_of_heq (HEq.symm ?_))
    refine (heq_of_eq (eval_mpLeft _ _ _)).trans ?_
    refine (Tuple.map_eqToHom_heq _ _).trans ?_
    refine (heq_of_eq (eval_mpRight _ _ _)).trans ?_
    exact (eval_flat_heq g f t _ ((Tuple.map_eqToHom_heq _ _).trans
      (Tuple.map_eqToHom_heq _ _)).symm).symm

end FreeMon

end CategoryTheory

/-! ### Computation -/

namespace CategoryTheory.FreeMon.EndExample

/-- Natural numbers, as a family over the one-object discrete category. -/
abbrev Nat' : Discrete Unit ⥤ Type := Discrete.functor fun _ => ℕ

/-- The operad of functions between powers of `ℕ`. -/
abbrev ops := endOperad Nat'

abbrev pt : Discrete Unit := ⟨()⟩

/-- Addition, a binary operation. -/
def add : ops.hom.app pt (mk [pt, pt]) := fun t => Nat.add t.1 t.2.1

/-- A triple of numbers. -/
def tup3 (a b c : ℕ) : Tuple Nat' [pt, pt, pt] := (a, b, c, PUnit.unit)

/-- The identity operation. -/
def idOp : ops.hom.app pt (mk [pt]) := ops.id.app pt

/-- `add ∘ (add, id)`, a ternary operation. -/
def add3 := ops.comp.app (z := mk [mk [pt, pt], mk [pt]]) add
  (ProfApp.cons add (ProfApp.cons idOp ProfApp.nil))

example : @Eq ℕ (add3 (tup3 1 2 3)) 6 := rfl

example : @Eq ℕ (add3 (tup3 1 2 3)) 6 := by decide

#eval (add3 (tup3 1 2 3) : ℕ)

end CategoryTheory.FreeMon.EndExample
