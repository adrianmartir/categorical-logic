/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Bespoke.ListProf
public import CategoricalLogic.Profunctor.Square

/-!
# The action of `FreeMon` on cells

The action of the free strict monoidal category monad on squares, nullary and binary cells,
and the unit and multiplication cells, together with the elementwise lemmas (mostly `HEq`s) that
the laws of `MonadProf` reduce to.
-/

@[expose] public section

namespace CategoryTheory

universe w w' w''

open Profunctor

namespace FreeMon

namespace ProfApp

/-! ### Squares -/

section Square

variable {C D C' D' C'' D'' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Category* C''] [Category* D'']
  {P : Profunctor.{w} C D} {Q : Profunctor.{w'} C' D'} {R : Profunctor.{w''} C'' D''}
  {F : C ⥤ C'} {G : D ⥤ D'}

/-- A square applied positionwise. -/
def mapSq (s : Square P Q F G) {as : List C} {bs : List D} (e : ProfApp P as bs) :
    ProfApp Q (as.map F.obj) (bs.map G.obj) :=
  rec' (motive := fun as bs _ => ProfApp Q (as.map F.obj) (bs.map G.obj)) nil
    (fun p _ r => cons (s.app p) r) e

variable (s : Square P Q F G)

@[simp] theorem mapSq_nil : mapSq s (nil : ProfApp P [] []) = nil := rfl

@[simp] theorem mapSq_cons {a : C} {b : D} {as : List C} {bs : List D} (p : P.app a b)
    (ps : ProfApp P as bs) : mapSq s (cons p ps) = cons (s.app p) (mapSq s ps) := rfl

theorem mapSq_mapL : ∀ {as as' : List C} {bs : List D} (f : mk as ⟶ mk as')
    (e : ProfApp P as bs), mapSq s (mapL f e) = mapL ((map F).map f) (mapSq s e)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, e =>
    congrArg₂ cons (s.natL (FreeMon.head f) (head e)) (mapSq_mapL (FreeMon.tail f) (tail e))
  | [], _ :: _, _, f, _ => isEmptyElim f
  | _ :: _, [], _, f, _ => isEmptyElim f
  | [], [], _ :: _, _, e => isEmptyElim e
  | _ :: _, _ :: _, [], _, e => isEmptyElim e

theorem mapSq_mapR : ∀ {as : List C} {bs bs' : List D} (g : mk bs ⟶ mk bs')
    (e : ProfApp P as bs'), mapSq s (mapR g e) = mapR ((map G).map g) (mapSq s e)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, g, e =>
    congrArg₂ cons (s.natR (head e) (FreeMon.head g)) (mapSq_mapR (FreeMon.tail g) (tail e))
  | _, [], _ :: _, g, _ => isEmptyElim g
  | _, _ :: _, [], g, _ => isEmptyElim g
  | [], _ :: _, _ :: _, _, e => isEmptyElim e
  | _ :: _, [], [], _, e => isEmptyElim e

theorem mapSq_id_heq {as : List C} {bs : List D} (e : ProfApp P as bs) :
    mapSq (Square.id P) e ≍ e := by
  induction e using rec' with
  | nil => rfl
  | cons p ps ih =>
    exact cons_heq_cons rfl rfl (congrArg FreeMon.as (map_id_obj C (mk _)))
      (congrArg FreeMon.as (map_id_obj D (mk _))) HEq.rfl ih

theorem mapSq_vComp_heq {F' : C' ⥤ C''} {G' : D' ⥤ D''} (t : Square Q R F' G') {as : List C}
    {bs : List D} (e : ProfApp P as bs) : mapSq (s.vComp t) e ≍ mapSq t (mapSq s e) := by
  induction e using rec' with
  | nil => rfl
  | cons p ps ih =>
    exact cons_heq_cons rfl rfl (congrArg FreeMon.as (map_comp_obj F F' (mk _)))
      (congrArg FreeMon.as (map_comp_obj G G' (mk _))) HEq.rfl ih

theorem mapSq_append_heq {as as' : List C} {bs bs' : List D} (e : ProfApp P as bs)
    (e' : ProfApp P as' bs') : mapSq s (append e e') ≍ append (mapSq s e) (mapSq s e') := by
  induction e using rec' with
  | nil => rfl
  | cons p ps ih =>
    exact cons_heq_cons rfl rfl (congrArg FreeMon.as (map_obj_append F (mk _) (mk _)))
      (congrArg FreeMon.as (map_obj_append G (mk _) (mk _))) HEq.rfl ih

end Square

/-! ### Nullary cells -/

section Nullary

variable {A B C D C' D' : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* C'] [Category* D'] {Q : Profunctor.{w} C D} {R : Profunctor.{w'} C' D'}
  {F : A ⥤ C} {G : A ⥤ D}

/-- A nullary cell applied positionwise. -/
def mapNu (ν : NullaryCell Q F G) : ∀ as : List A, ProfApp Q (as.map F.obj) (as.map G.obj)
  | [] => nil
  | a :: as => cons (ν.app a) (mapNu ν as)

variable (ν : NullaryCell Q F G)

@[simp] theorem mapNu_nil : mapNu ν [] = nil := rfl

@[simp] theorem mapNu_cons (a : A) (as : List A) :
    mapNu ν (a :: as) = cons (ν.app a) (mapNu ν as) :=
  rfl

theorem mapNu_naturality : ∀ {as as' : List A} (f : mk as ⟶ mk as'),
    mapL ((map F).map f) (mapNu ν as) = mapR ((map G).map f) (mapNu ν as')
  | [], [], _ => rfl
  | _ :: _, _ :: _, f =>
    congrArg₂ cons (ν.naturality (FreeMon.head f)) (mapNu_naturality (FreeMon.tail f))
  | [], _ :: _, f => isEmptyElim f
  | _ :: _, [], f => isEmptyElim f

theorem mapNu_vComp_heq {F' : C ⥤ C'} {G' : D ⥤ D'} (t : Square Q R F' G') :
    ∀ as : List A, mapNu (ν.vComp t) as ≍ mapSq t (mapNu ν as)
  | [] => HEq.rfl
  | _ :: as => cons_heq_cons rfl rfl (congrArg FreeMon.as (map_comp_obj F F' (mk as)))
      (congrArg FreeMon.as (map_comp_obj G G' (mk as))) HEq.rfl (mapNu_vComp_heq t as)

theorem mapNu_comap_heq (K : B ⥤ A) : ∀ bs : List B,
    mapNu (ν.comap K) bs ≍ mapNu ν (bs.map K.obj)
  | [] => HEq.rfl
  | _ :: bs => cons_heq_cons rfl rfl (congrArg FreeMon.as (map_comp_obj K F (mk bs)))
      (congrArg FreeMon.as (map_comp_obj K G (mk bs))) HEq.rfl (mapNu_comap_heq K bs)

theorem mapNu_append_heq : ∀ as as' : List A,
    mapNu ν (as ++ as') ≍ append (mapNu ν as) (mapNu ν as')
  | [], _ => HEq.rfl
  | _ :: as, as' => cons_heq_cons rfl rfl
      (congrArg FreeMon.as (map_obj_append F (mk as) (mk as')))
      (congrArg FreeMon.as (map_obj_append G (mk as) (mk as'))) HEq.rfl (mapNu_append_heq as as')

end Nullary

/-! ### Binary cells -/

section Binary

variable {X Y Z X' Z' X₀ Y₀ Z₀ X'' Z'' : Type*}
  [Category* X] [Category* Y] [Category* Z] [Category* X'] [Category* Z']
  [Category* X₀] [Category* Y₀] [Category* Z₀] [Category* X''] [Category* Z'']
  {P : Profunctor.{w} X Y} {Q : Profunctor.{w} Y Z} {R : Profunctor.{w} X' Z'}
  {F : X ⥤ X'} {G : Z ⥤ Z'}

/-- A binary cell applied positionwise. -/
def mapBi (β : BinaryCell P Q R F G) : ∀ {xs : List X} {ys : List Y} {zs : List Z},
    ProfApp P xs ys → ProfApp Q ys zs → ProfApp R (xs.map F.obj) (zs.map G.obj)
  | [], [], [], _, _ => nil
  | _ :: _, _ :: _, _ :: _, e, e' => cons (β.app (head e) (head e')) (mapBi β (tail e) (tail e'))
  | [], _ :: _, _, e, _ => isEmptyElim e
  | _ :: _, [], _, e, _ => isEmptyElim e
  | [], [], _ :: _, _, e' => isEmptyElim e'
  | _ :: _, _ :: _, [], _, e' => isEmptyElim e'

variable (β : BinaryCell P Q R F G)

@[simp] theorem mapBi_nil : mapBi β (nil : ProfApp P [] []) (nil : ProfApp Q [] []) = nil := rfl

@[simp] theorem mapBi_cons {x : X} {y : Y} {z : Z} {xs : List X} {ys : List Y} {zs : List Z}
    (p : P.app x y) (ps : ProfApp P xs ys) (q : Q.app y z) (qs : ProfApp Q ys zs) :
    mapBi β (cons p ps) (cons q qs) = cons (β.app p q) (mapBi β ps qs) := rfl

theorem mapBi_wedge : ∀ {xs : List X} {ys ys' : List Y} {zs : List Z} (e : ProfApp P xs ys')
    (g : mk ys ⟶ mk ys') (e' : ProfApp Q ys zs), mapBi β (mapR g e) e' = mapBi β e (mapL g e')
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, e, g, e' =>
    congrArg₂ cons (β.wedge (head e) (FreeMon.head g) (head e'))
      (mapBi_wedge (tail e) (FreeMon.tail g) (tail e'))
  | _, [], _ :: _, _, _, g, _ => isEmptyElim g
  | _, _ :: _, [], _, _, g, _ => isEmptyElim g
  | _ :: _, [], [], _, e, _, _ => isEmptyElim e
  | [], _ :: _, _ :: _, _, e, _, _ => isEmptyElim e
  | _, [], [], _ :: _, _, _, e' => isEmptyElim e'
  | _, _ :: _, _ :: _, [], _, _, e' => isEmptyElim e'

theorem mapBi_mapL : ∀ {xs xs' : List X} {ys : List Y} {zs : List Z} (f : mk xs ⟶ mk xs')
    (e : ProfApp P xs ys) (e' : ProfApp Q ys zs),
    mapBi β (mapL f e) e' = mapL ((map F).map f) (mapBi β e e')
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, f, e, e' =>
    congrArg₂ cons (β.natL (FreeMon.head f) (head e) (head e'))
      (mapBi_mapL (FreeMon.tail f) (tail e) (tail e'))
  | [], _ :: _, _, _, f, _, _ => isEmptyElim f
  | _ :: _, [], _, _, f, _, _ => isEmptyElim f
  | [], [], _ :: _, _, _, e, _ => isEmptyElim e
  | _ :: _, _ :: _, [], _, _, e, _ => isEmptyElim e
  | [], [], [], _ :: _, _, _, e' => isEmptyElim e'
  | _ :: _, _ :: _, _ :: _, [], _, _, e' => isEmptyElim e'

theorem mapBi_mapR : ∀ {xs : List X} {ys : List Y} {zs zs' : List Z} (e : ProfApp P xs ys)
    (e' : ProfApp Q ys zs') (g : mk zs ⟶ mk zs'),
    mapBi β e (mapR g e') = mapR ((map G).map g) (mapBi β e e')
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, e, e', g =>
    congrArg₂ cons (β.natR (head e) (head e') (FreeMon.head g))
      (mapBi_mapR (tail e) (tail e') (FreeMon.tail g))
  | _, _, [], _ :: _, _, _, g => isEmptyElim g
  | _, _, _ :: _, [], _, _, g => isEmptyElim g
  | [], _ :: _, _, _, e, _, _ => isEmptyElim e
  | _ :: _, [], _, _, e, _, _ => isEmptyElim e
  | [], [], _ :: _, _ :: _, _, e', _ => isEmptyElim e'
  | _ :: _, _ :: _, [], [], _, e', _ => isEmptyElim e'

theorem mapBi_vComp_heq {R' : Profunctor.{w} X'' Z''} {F' : X' ⥤ X''} {G' : Z' ⥤ Z''}
    (t : Square R R' F' G') : ∀ {xs : List X} {ys : List Y} {zs : List Z}
    (e : ProfApp P xs ys) (e' : ProfApp Q ys zs),
    mapBi (β.vComp t) e e' ≍ mapSq t (mapBi β e e')
  | [], [], [], _, _ => HEq.rfl
  | _ :: _, _ :: _, _ :: _, e, e' =>
    cons_heq_cons rfl rfl (congrArg FreeMon.as (map_comp_obj F F' (mk _)))
      (congrArg FreeMon.as (map_comp_obj G G' (mk _))) HEq.rfl
      (mapBi_vComp_heq t (tail e) (tail e'))
  | [], _ :: _, _, e, _ => isEmptyElim e
  | _ :: _, [], _, e, _ => isEmptyElim e
  | [], [], _ :: _, _, e' => isEmptyElim e'
  | _ :: _, _ :: _, [], _, e' => isEmptyElim e'

theorem mapBi_precomp_heq {P' : Profunctor.{w} X₀ Y₀} {Q' : Profunctor.{w} Y₀ Z₀}
    {K : Y₀ ⥤ Y} {F₀ : X₀ ⥤ X} {G₀ : Z₀ ⥤ Z} (s : Square P' P F₀ K) (s' : Square Q' Q K G₀) :
    ∀ {xs : List X₀} {ys : List Y₀} {zs : List Z₀} (e : ProfApp P' xs ys)
    (e' : ProfApp Q' ys zs),
    mapBi (β.precomp s s') e e' ≍ mapBi β (mapSq s e) (mapSq s' e')
  | [], [], [], _, _ => HEq.rfl
  | _ :: _, _ :: _, _ :: _, e, e' =>
    cons_heq_cons rfl rfl (congrArg FreeMon.as (map_comp_obj F₀ F (mk _)))
      (congrArg FreeMon.as (map_comp_obj G₀ G (mk _))) HEq.rfl
      (mapBi_precomp_heq s s' (tail e) (tail e'))
  | [], _ :: _, _, e, _ => isEmptyElim e
  | _ :: _, [], _, e, _ => isEmptyElim e
  | [], [], _ :: _, _, e' => isEmptyElim e'
  | _ :: _, _ :: _, [], _, e' => isEmptyElim e'

theorem mapBi_append_heq {xs' : List X} {ys' : List Y} {zs' : List Z} :
    ∀ {xs : List X} {ys : List Y} {zs : List Z} (e₁ : ProfApp P xs ys)
    (e₁' : ProfApp Q ys zs) (e₂ : ProfApp P xs' ys') (e₂' : ProfApp Q ys' zs'),
    mapBi β (append e₁ e₂) (append e₁' e₂') ≍ append (mapBi β e₁ e₁') (mapBi β e₂ e₂')
  | [], [], [], _, _, _, _ => HEq.rfl
  | _ :: _, _ :: _, _ :: _, e₁, e₁', e₂, e₂' =>
    cons_heq_cons rfl rfl (congrArg FreeMon.as (map_obj_append F (mk _) (mk xs')))
      (congrArg FreeMon.as (map_obj_append G (mk _) (mk zs'))) HEq.rfl
      (mapBi_append_heq (tail e₁) (tail e₁') e₂ e₂')
  | [], _ :: _, _, e, _, _, _ => isEmptyElim e
  | _ :: _, [], _, e, _, _, _ => isEmptyElim e
  | [], [], _ :: _, _, e', _, _ => isEmptyElim e'
  | _ :: _, _ :: _, [], _, e', _, _ => isEmptyElim e'

end Binary

/-! ### The unit and the multiplication -/

section Monad

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {P : Profunctor.{w} C D}

/-- The multiplication: flatten a list of lists of elements. -/
def flat {As : List (FreeMon C)} {Bs : List (FreeMon D)} (e : ProfApp (prof P) As Bs) :
    ProfApp P (As.flatMap FreeMon.as) (Bs.flatMap FreeMon.as) :=
  rec' (motive := fun As Bs _ => ProfApp P (As.flatMap FreeMon.as) (Bs.flatMap FreeMon.as)) nil
    (fun p _ r => append p r) e

@[simp] theorem flat_nil : flat (nil : ProfApp (prof P) [] []) = nil := rfl

@[simp] theorem flat_cons {A : FreeMon C} {B : FreeMon D} {As : List (FreeMon C)}
    {Bs : List (FreeMon D)} (p : (prof P).app A B) (ps : ProfApp (prof P) As Bs) :
    flat (cons p ps) = append p (flat ps) := rfl

theorem flat_mapL : ∀ {As As' : List (FreeMon C)} {Bs : List (FreeMon D)} (f : mk As ⟶ mk As')
    (e : ProfApp (prof P) As Bs), flat (mapL f e) = mapL ((flatten C).map f) (flat e)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, e =>
    (congrArg (append _) (flat_mapL (FreeMon.tail f) (tail e))).trans
      (mapL_append (FreeMon.head f) ((flatten C).map (FreeMon.tail f)) (head e)
        (flat (tail e))).symm
  | [], _ :: _, _, f, _ => isEmptyElim f
  | _ :: _, [], _, f, _ => isEmptyElim f
  | [], [], _ :: _, _, e => isEmptyElim e
  | _ :: _, _ :: _, [], _, e => isEmptyElim e

theorem flat_mapR : ∀ {As : List (FreeMon C)} {Bs Bs' : List (FreeMon D)} (g : mk Bs ⟶ mk Bs')
    (e : ProfApp (prof P) As Bs'), flat (mapR g e) = mapR ((flatten D).map g) (flat e)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, g, e =>
    (congrArg (append _) (flat_mapR (FreeMon.tail g) (tail e))).trans
      (mapR_append (FreeMon.head g) ((flatten D).map (FreeMon.tail g)) (head e)
        (flat (tail e))).symm
  | _, [], _ :: _, g, _ => isEmptyElim g
  | _, _ :: _, [], g, _ => isEmptyElim g
  | [], _ :: _, _ :: _, _, e => isEmptyElim e
  | _ :: _, [], [], _, e => isEmptyElim e

theorem flat_append_heq {As As' : List (FreeMon C)} {Bs Bs' : List (FreeMon D)}
    (e : ProfApp (prof P) As Bs) (e' : ProfApp (prof P) As' Bs') :
    flat (append e e') ≍ append (flat e) (flat e') := by
  induction e using rec' with
  | nil => rfl
  | cons p ps ih =>
    exact (append_heq_append rfl rfl (congrArg FreeMon.as (flatten_obj_append (mk _) (mk _)))
      (congrArg FreeMon.as (flatten_obj_append (mk _) (mk _))) HEq.rfl ih).trans
      (append_assoc_heq _ _ _).symm

end Monad

end ProfApp

open ProfApp

section Cells

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']

/-- `FreeMon` applied to a square. -/
def mapSquare {P : Profunctor.{w} C D} {Q : Profunctor.{w'} C' D'} {F : C ⥤ C'} {G : D ⥤ D'}
    (s : Square P Q F G) : Square (prof P) (prof Q) (map F) (map G) where
  app e := mapSq s e
  natL f e := mapSq_mapL s f e
  natR e g := mapSq_mapR s g e

/-- `FreeMon` applied to a nullary cell. -/
def mapNullary {A : Type*} [Category* A] {Q : Profunctor.{w} C D} {F : A ⥤ C} {G : A ⥤ D}
    (ν : NullaryCell Q F G) : NullaryCell (prof Q) (map F) (map G) where
  app A := mapNu ν A.as
  naturality f := mapNu_naturality ν f

/-- `FreeMon` applied to a binary cell. -/
def mapBinary {X Y Z X' Z' : Type*} [Category* X] [Category* Y] [Category* Z] [Category* X']
    [Category* Z'] {P : Profunctor.{w} X Y} {Q : Profunctor.{w} Y Z} {R : Profunctor.{w} X' Z'}
    {F : X ⥤ X'} {G : Z ⥤ Z'} (β : BinaryCell P Q R F G) :
    BinaryCell (prof P) (prof Q) (prof R) (map F) (map G) where
  app e e' := mapBi β e e'
  wedge e g e' := mapBi_wedge β e g e'
  natL f e e' := mapBi_mapL β f e e'
  natR e e' g := mapBi_mapR β e e' g

variable (P : Profunctor.{w} C D)

/-- The unit cell: an element is sent to the singleton list. -/
def ηCell : Square P (prof P) (unit C) (unit D) where
  app p := ProfApp.cons p ProfApp.nil
  natL _ _ := rfl
  natR _ _ := rfl

/-- The multiplication cell: a list of lists is flattened. -/
def μCell : Square (prof (prof P)) (prof P) (flatten C) (flatten D) where
  app e := flat e
  natL f e := flat_mapL f e
  natR e g := flat_mapR g e

end Cells

/-! ### The laws involving the multiplication -/

namespace ProfApp

section MonadLaws

variable {C D C' D' A : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Category* A]

theorem flat_mapSq_heq {P : Profunctor.{w} C D} {Q : Profunctor.{w'} C' D'} {F : C ⥤ C'}
    {G : D ⥤ D'} (s : Square P Q F G) {As : List (FreeMon C)} {Bs : List (FreeMon D)}
    (e : ProfApp (prof P) As Bs) : flat (mapSq (FreeMon.mapSquare s) e) ≍ mapSq s (flat e) := by
  induction e using rec' with
  | nil => rfl
  | cons p ps ih =>
    exact (append_heq_append rfl rfl (congrArg FreeMon.as (flatten_naturality_obj F (mk _)))
      (congrArg FreeMon.as (flatten_naturality_obj G (mk _))) HEq.rfl ih).trans
      (mapSq_append_heq s p (flat ps)).symm

theorem flat_mapNu_heq {Q : Profunctor.{w} C D} {F : A ⥤ C} {G : A ⥤ D}
    (ν : NullaryCell Q F G) :
    ∀ As : List (FreeMon A), flat (mapNu (FreeMon.mapNullary ν) As) ≍ mapNu ν (As.flatMap as)
  | [] => HEq.rfl
  | A :: As =>
    (append_heq_append rfl rfl (congrArg FreeMon.as (flatten_naturality_obj F (mk As)))
      (congrArg FreeMon.as (flatten_naturality_obj G (mk As))) HEq.rfl
      (flat_mapNu_heq ν As)).trans (mapNu_append_heq ν A.as (As.flatMap as)).symm

theorem flat_mapBi_heq {X Y Z X' Z' : Type*} [Category* X] [Category* Y] [Category* Z]
    [Category* X'] [Category* Z'] {P : Profunctor.{w} X Y} {Q : Profunctor.{w} Y Z}
    {R : Profunctor.{w} X' Z'} {F : X ⥤ X'} {G : Z ⥤ Z'} (β : BinaryCell P Q R F G) :
    ∀ {As : List (FreeMon X)} {Bs : List (FreeMon Y)} {Cs : List (FreeMon Z)}
    (e : ProfApp (prof P) As Bs) (e' : ProfApp (prof Q) Bs Cs),
    flat (mapBi (FreeMon.mapBinary β) e e') ≍ mapBi β (flat e) (flat e')
  | [], [], [], _, _ => HEq.rfl
  | _ :: _, _ :: _, _ :: _, e, e' =>
    (append_heq_append rfl rfl (congrArg FreeMon.as (flatten_naturality_obj F (mk _)))
      (congrArg FreeMon.as (flatten_naturality_obj G (mk _))) HEq.rfl
      (flat_mapBi_heq β (tail e) (tail e'))).trans
      (mapBi_append_heq β (head e) (head e') (flat (tail e)) (flat (tail e'))).symm
  | [], _ :: _, _, e, _ => isEmptyElim e
  | _ :: _, [], _, e, _ => isEmptyElim e
  | [], [], _ :: _, _, e' => isEmptyElim e'
  | _ :: _, _ :: _, [], _, e' => isEmptyElim e'

variable {P : Profunctor.{w} C D}

theorem flat_mapSq_ηCell_heq {as : List C} {bs : List D} (e : ProfApp P as bs) :
    flat (mapSq (FreeMon.ηCell P) e) ≍ e := by
  induction e using rec' with
  | nil => rfl
  | cons p ps ih =>
    exact cons_heq_cons rfl rfl (congrArg FreeMon.as (map_unit_flatten_obj C (mk _)))
      (congrArg FreeMon.as (map_unit_flatten_obj D (mk _))) HEq.rfl ih

theorem flat_flat_heq {As : List (FreeMon (FreeMon C))} {Bs : List (FreeMon (FreeMon D))}
    (e : ProfApp (prof (prof P)) As Bs) : flat (flat e) ≍ flat (mapSq (FreeMon.μCell P) e) := by
  induction e using rec' with
  | nil => rfl
  | cons p ps ih =>
    exact (flat_append_heq p (flat ps)).trans (append_heq_append rfl rfl
      (congrArg FreeMon.as (map_flatten_flatten_obj C (mk _))).symm
      (congrArg FreeMon.as (map_flatten_flatten_obj D (mk _))).symm HEq.rfl ih)

end MonadLaws

end ProfApp

end FreeMon

end CategoryTheory
