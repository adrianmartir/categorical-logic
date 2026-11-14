/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Shared.ListMonad
public import CategoricalLogic.Profunctor.Basic

/-!
# The free strict monoidal category monad on profunctors

For a profunctor `P : Profunctor C D`, `FreeMon.prof P : Profunctor (FreeMon C) (FreeMon D)` has
as elements of `(prof P).app (mk as) (mk bs)` the lists of elements of `P` matching `as` and `bs`
positionwise. Like `FreeMon.Hom`, the elements are defined by recursion on both lists
(`PUnit`, `×`, `PEmpty`), so that `prof P` lives in the same universe as `P`.

## Main definitions

* `FreeMon.ProfApp P as bs`: the elements, by recursion on the lists.
* `FreeMon.ProfApp.mapL`, `FreeMon.ProfApp.mapR`: positionwise action of morphisms.
* `FreeMon.prof P`: the profunctor.
* `FreeMon.ProfApp.append`: concatenation of elements.
* `FreeMon.ProfApp.cons_heq_cons`, `FreeMon.ProfApp.append_heq_append`: congruences for `HEq`,
  the tool for all the transports.
-/

@[expose] public section

namespace CategoryTheory

universe w v u v' u'

open Profunctor

namespace FreeMon

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- The elements of `FreeMon.prof P`: lists of elements of `P`, matched positionwise with the
lists of objects. -/
def ProfApp (P : Profunctor.{w} C D) : List C → List D → Type w
  | [], [] => PUnit
  | a :: as, b :: bs => P.app a b × ProfApp P as bs
  | [], _ :: _ => PEmpty
  | _ :: _, [] => PEmpty

namespace ProfApp

variable {P : Profunctor.{w} C D}

instance : Unique (ProfApp P [] []) := inferInstanceAs (Unique PUnit)

instance {b : D} {bs : List D} : IsEmpty (ProfApp P [] (b :: bs)) :=
  inferInstanceAs (IsEmpty PEmpty)

instance {a : C} {as : List C} : IsEmpty (ProfApp P (a :: as) []) :=
  inferInstanceAs (IsEmpty PEmpty)

/-- The empty list of elements. -/
def nil : ProfApp P [] [] := PUnit.unit

/-- Prepend an element. -/
def cons {a : C} {b : D} {as : List C} {bs : List D} (p : P.app a b) (ps : ProfApp P as bs) :
    ProfApp P (a :: as) (b :: bs) := (p, ps)

/-- The first element. -/
def head {a : C} {b : D} {as : List C} {bs : List D} (e : ProfApp P (a :: as) (b :: bs)) :
    P.app a b := e.1

/-- The remaining elements. -/
def tail {a : C} {b : D} {as : List C} {bs : List D} (e : ProfApp P (a :: as) (b :: bs)) :
    ProfApp P as bs := e.2

variable {a a' : C} {b b' : D} {as as' : List C} {bs bs' : List D}

@[simp] theorem head_cons (p : P.app a b) (ps : ProfApp P as bs) : head (cons p ps) = p := rfl

@[simp] theorem tail_cons (p : P.app a b) (ps : ProfApp P as bs) : tail (cons p ps) = ps := rfl

@[simp] theorem cons_head_tail (e : ProfApp P (a :: as) (b :: bs)) :
    cons (head e) (tail e) = e := rfl

theorem ext_nil (e e' : ProfApp P [] []) : e = e' := rfl

@[simp] theorem cons_inj {p p' : P.app a b} {ps ps' : ProfApp P as bs} :
    cons p ps = cons p' ps' ↔ p = p' ∧ ps = ps' := Prod.mk_inj

/-- Implementation of `rec`. -/
def recAux {motive : ∀ (as : List C) (bs : List D), ProfApp P as bs → Sort*}
    (nil : motive [] [] nil)
    (cons : ∀ {a b as bs} (p : P.app a b) (ps : ProfApp P as bs),
      motive as bs ps → motive (a :: as) (b :: bs) (cons p ps)) :
    ∀ {as : List C} {bs : List D} (e : ProfApp P as bs), motive as bs e
  | [], [], _ => nil
  | _ :: _, _ :: _, e => cons (head e) (tail e) (recAux nil cons (tail e))
  | [], _ :: _, e => isEmptyElim e
  | _ :: _, [], e => isEmptyElim e

/-- Induction on lists of elements. Use as `induction e using ProfApp.rec'`. -/
@[elab_as_elim]
def rec' {motive : ∀ (as : List C) (bs : List D), ProfApp P as bs → Sort*}
    (nil : motive [] [] nil)
    (cons : ∀ {a b as bs} (p : P.app a b) (ps : ProfApp P as bs),
      motive as bs ps → motive (a :: as) (b :: bs) (cons p ps))
    {as : List C} {bs : List D} (e : ProfApp P as bs) : motive as bs e :=
  recAux (motive := motive) nil cons e

/-- Case analysis on a list of elements between nonempty lists. -/
@[elab_as_elim]
def casesCons {motive : ProfApp P (a :: as) (b :: bs) → Sort*}
    (cons : ∀ (p : P.app a b) (ps : ProfApp P as bs), motive (cons p ps))
    (e : ProfApp P (a :: as) (b :: bs)) : motive e :=
  cons (head e) (tail e)

/-- Congruence for `cons` along equalities of the indices. -/
theorem cons_heq_cons {p : P.app a b} {p' : P.app a' b'} {ps : ProfApp P as bs}
    {ps' : ProfApp P as' bs'} (ha : a = a') (hb : b = b') (has : as = as') (hbs : bs = bs')
    (hp : p ≍ p') (hps : ps ≍ ps') : cons p ps ≍ cons p' ps' := by
  subst ha hb has hbs
  cases hp
  cases hps
  rfl

/-! ### The action of morphisms -/

/-- The covariant action, positionwise. -/
def mapL : ∀ {as as' : List C} {bs : List D}, Hom as as' → ProfApp P as bs → ProfApp P as' bs
  | [], [], [], _, e => e
  | _ :: _, _ :: _, _ :: _, f, e =>
    cons (P.mapL (FreeMon.head f) (head e)) (mapL (FreeMon.tail f) (tail e))
  | [], _ :: _, _, f, _ => PEmpty.elim f
  | _ :: _, [], _, f, _ => PEmpty.elim f
  | [], [], _ :: _, _, e => isEmptyElim e
  | _ :: _, _ :: _, [], _, e => isEmptyElim e

/-- The contravariant action, positionwise. -/
def mapR : ∀ {as : List C} {bs bs' : List D}, Hom bs bs' → ProfApp P as bs' → ProfApp P as bs
  | [], [], [], _, e => e
  | _ :: _, _ :: _, _ :: _, g, e =>
    cons (P.mapR (FreeMon.head g) (head e)) (mapR (FreeMon.tail g) (tail e))
  | _, [], _ :: _, g, _ => PEmpty.elim g
  | _, _ :: _, [], g, _ => PEmpty.elim g
  | [], _ :: _, _ :: _, _, e => isEmptyElim e
  | _ :: _, [], [], _, e => isEmptyElim e

@[simp] theorem mapL_nil (f : mk ([] : List C) ⟶ mk []) :
    mapL (bs := []) f (nil : ProfApp P [] []) = nil :=
  rfl

@[simp] theorem mapL_cons {A A' : FreeMon C} (f : a ⟶ a') (fs : A ⟶ A') (p : P.app a b)
    (ps : ProfApp P A.as bs) :
    mapL (FreeMon.cons f fs) (cons p ps) = cons (P.mapL f p) (mapL fs ps) := rfl

@[simp] theorem mapR_nil (g : mk ([] : List D) ⟶ mk []) :
    mapR (as := []) g (nil : ProfApp P [] []) = nil :=
  rfl

@[simp] theorem mapR_cons {B B' : FreeMon D} (g : b ⟶ b') (gs : B ⟶ B') (p : P.app a b')
    (ps : ProfApp P as B'.as) :
    mapR (FreeMon.cons g gs) (cons p ps) = cons (P.mapR g p) (mapR gs ps) := rfl

theorem mapL_id : ∀ {as : List C} {bs : List D} (e : ProfApp P as bs), mapL (𝟙 (mk as)) e = e
  | [], [], _ => rfl
  | _ :: _, _ :: _, e => congrArg₂ cons (P.mapL_id _ _ (head e)) (mapL_id (tail e))
  | [], _ :: _, e => isEmptyElim e
  | _ :: _, [], e => isEmptyElim e

theorem mapR_id : ∀ {as : List C} {bs : List D} (e : ProfApp P as bs), mapR (𝟙 (mk bs)) e = e
  | [], [], _ => rfl
  | _ :: _, _ :: _, e => congrArg₂ cons (P.mapR_id _ _ (head e)) (mapR_id (tail e))
  | [], _ :: _, e => isEmptyElim e
  | _ :: _, [], e => isEmptyElim e

theorem mapL_comp : ∀ {as as' as'' : List C} {bs : List D} (f : mk as ⟶ mk as')
    (f' : mk as' ⟶ mk as'') (e : ProfApp P as bs), mapL (f ≫ f') e = mapL f' (mapL f e)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, f, f', e =>
    congrArg₂ cons (P.mapL_comp (FreeMon.head f) (FreeMon.head f') (head e))
      (mapL_comp (FreeMon.tail f) (FreeMon.tail f') (tail e))
  | [], _ :: _, _, _, f, _, _ => isEmptyElim f
  | _ :: _, [], _, _, f, _, _ => isEmptyElim f
  | [], [], _ :: _, _, _, f', _ => isEmptyElim f'
  | _ :: _, _ :: _, [], _, _, f', _ => isEmptyElim f'
  | [], [], [], _ :: _, _, _, e => isEmptyElim e
  | _ :: _, _ :: _, _ :: _, [], _, _, e => isEmptyElim e

theorem mapR_comp : ∀ {as : List C} {bs bs' bs'' : List D} (g : mk bs ⟶ mk bs')
    (g' : mk bs' ⟶ mk bs'') (e : ProfApp P as bs''), mapR (g ≫ g') e = mapR g (mapR g' e)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, g, g', e =>
    congrArg₂ cons (P.mapR_comp (FreeMon.head g) (FreeMon.head g') (head e))
      (mapR_comp (FreeMon.tail g) (FreeMon.tail g') (tail e))
  | _, [], _ :: _, _, g, _, _ => isEmptyElim g
  | _, _ :: _, [], _, g, _, _ => isEmptyElim g
  | _, [], [], _ :: _, _, g', _ => isEmptyElim g'
  | _, _ :: _, _ :: _, [], _, g', _ => isEmptyElim g'
  | _ :: _, [], [], [], _, _, e => isEmptyElim e
  | [], _ :: _, _ :: _, _ :: _, _, _, e => isEmptyElim e

theorem mapL_mapR : ∀ {as as' : List C} {bs bs' : List D} (f : mk as ⟶ mk as')
    (g : mk bs ⟶ mk bs') (e : ProfApp P as bs'), mapL f (mapR g e) = mapR g (mapL f e)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, f, g, e =>
    congrArg₂ cons (P.mapL_mapR_comm (FreeMon.head f) (FreeMon.head g) (head e))
      (mapL_mapR (FreeMon.tail f) (FreeMon.tail g) (tail e))
  | [], _ :: _, _, _, f, _, _ => isEmptyElim f
  | _ :: _, [], _, _, f, _, _ => isEmptyElim f
  | _, _, [], _ :: _, _, g, _ => isEmptyElim g
  | _, _, _ :: _, [], _, g, _ => isEmptyElim g
  | [], [], _ :: _, _ :: _, _, _, e => isEmptyElim e
  | _ :: _, _ :: _, [], [], _, _, e => isEmptyElim e

/-! ### Concatenation -/

/-- Concatenation of lists of elements. -/
def append (e : ProfApp P as bs)
    (e' : ProfApp P as' bs') : ProfApp P (as ++ as') (bs ++ bs') :=
  rec' (motive := fun as bs _ => ProfApp P (as ++ as') (bs ++ bs')) e' (fun p _ r => cons p r) e

@[simp] theorem nil_append (e' : ProfApp P as' bs') : append (nil : ProfApp P [] []) e' = e' := rfl

@[simp] theorem cons_append (p : P.app a b) (ps : ProfApp P as bs) (e' : ProfApp P as' bs') :
    append (cons p ps) e' = cons p (append ps e') := rfl

/-- Congruence for `append` along equalities of the indices. -/
theorem append_heq_append {as₁ as₂ as₁' as₂' : List C} {bs₁ bs₂ bs₁' bs₂' : List D}
    {e₁ : ProfApp P as₁ bs₁} {e₂ : ProfApp P as₂ bs₂} {e₁' : ProfApp P as₁' bs₁'}
    {e₂' : ProfApp P as₂' bs₂'} (ha : as₁ = as₂) (hb : bs₁ = bs₂) (ha' : as₁' = as₂')
    (hb' : bs₁' = bs₂') (he : e₁ ≍ e₂) (he' : e₁' ≍ e₂') : append e₁ e₁' ≍ append e₂ e₂' := by
  subst ha hb ha' hb'
  cases he
  cases he'
  rfl

theorem append_nil_heq (e : ProfApp P as bs) : append e nil ≍ e := by
  induction e using rec' with
  | nil => rfl
  | cons p ps ih => exact cons_heq_cons rfl rfl (List.append_nil _) (List.append_nil _) HEq.rfl ih

theorem append_assoc_heq {as'' : List C} {bs'' : List D} (e : ProfApp P as bs)
    (e' : ProfApp P as' bs') (e'' : ProfApp P as'' bs'') :
    append (append e e') e'' ≍ append e (append e' e'') := by
  induction e using rec' with
  | nil => rfl
  | cons p ps ih =>
    exact cons_heq_cons rfl rfl (List.append_assoc _ _ _) (List.append_assoc _ _ _) HEq.rfl ih

theorem mapL_append : ∀ {as₁ as₁' as₂ as₂' : List C} {bs₁ bs₂ : List D} (f : mk as₁ ⟶ mk as₁')
    (f' : mk as₂ ⟶ mk as₂') (e : ProfApp P as₁ bs₁) (e' : ProfApp P as₂ bs₂),
    mapL (FreeMon.append f f') (append e e') = append (mapL f e) (mapL f' e')
  | [], [], _, _, [], _, _, _, _, _ => rfl
  | _ :: _, _ :: _, _, _, _ :: _, _, f, f', e, e' =>
    congrArg (cons _) (mapL_append (FreeMon.tail f) f' (tail e) e')
  | [], _ :: _, _, _, _, _, f, _, _, _ => isEmptyElim f
  | _ :: _, [], _, _, _, _, f, _, _, _ => isEmptyElim f
  | [], [], _, _, _ :: _, _, _, _, e, _ => isEmptyElim e
  | _ :: _, _ :: _, _, _, [], _, _, _, e, _ => isEmptyElim e

theorem mapR_append : ∀ {as₁ as₂ : List C} {bs₁ bs₁' bs₂ bs₂' : List D} (g : mk bs₁ ⟶ mk bs₁')
    (g' : mk bs₂ ⟶ mk bs₂') (e : ProfApp P as₁ bs₁') (e' : ProfApp P as₂ bs₂'),
    mapR (FreeMon.append g g') (append e e') = append (mapR g e) (mapR g' e')
  | [], _, [], [], _, _, _, _, _, _ => rfl
  | _ :: _, _, _ :: _, _ :: _, _, _, g, g', e, e' =>
    congrArg (cons _) (mapR_append (FreeMon.tail g) g' (tail e) e')
  | _, _, [], _ :: _, _, _, g, _, _, _ => isEmptyElim g
  | _, _, _ :: _, [], _, _, g, _, _, _ => isEmptyElim g
  | _ :: _, _, [], [], _, _, _, _, e, _ => isEmptyElim e
  | [], _, _ :: _, _ :: _, _, _, _, _, e, _ => isEmptyElim e

end ProfApp

/-- The free strict monoidal category monad applied to a profunctor: elements of
`(prof P).app (mk as) (mk bs)` are lists of elements of `P` matching `as` and `bs`
positionwise. -/
def prof (P : Profunctor.{w} C D) : Profunctor.{w} (FreeMon C) (FreeMon D) where
  obj A :=
    { obj B := ProfApp P A.as B.unop.as
      map g := TypeCat.ofHom (ProfApp.mapR g.unop)
      map_id _ := TypeCat.Hom.ext (TypeCat.Fun.ext (funext ProfApp.mapR_id))
      map_comp g g' :=
        TypeCat.Hom.ext (TypeCat.Fun.ext (funext (ProfApp.mapR_comp g'.unop g.unop))) }
  map f :=
    { app _ := TypeCat.ofHom (ProfApp.mapL f)
      naturality _ _ g :=
        TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun e => ProfApp.mapL_mapR f g.unop e)) }
  map_id _ :=
    NatTrans.ext (funext fun _ => TypeCat.Hom.ext (TypeCat.Fun.ext (funext ProfApp.mapL_id)))
  map_comp f f' := NatTrans.ext (funext fun _ =>
    TypeCat.Hom.ext (TypeCat.Fun.ext (funext (ProfApp.mapL_comp f f'))))

variable {P : Profunctor.{w} C D}

theorem prof_app (A : FreeMon C) (B : FreeMon D) : (prof P).app A B = ProfApp P A.as B.as := rfl

@[simp] theorem prof_mapL {A A' : FreeMon C} {B : FreeMon D} (f : A ⟶ A') (e : (prof P).app A B) :
    (prof P).mapL f e = ProfApp.mapL f e := rfl

@[simp] theorem prof_mapR {A : FreeMon C} {B B' : FreeMon D} (g : B ⟶ B') (e : (prof P).app A B') :
    (prof P).mapR g e = ProfApp.mapR g e := rfl

end FreeMon

end CategoryTheory
