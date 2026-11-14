/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Kleisli.ListProf
public import CategoricalLogic.Designs.Kleisli.Basic

/-!
# The free strict monoidal category monad acts on profunctors

The data of `KleisliProf Cat.freeMon`:

* `FreeMon.mapProf`: `P ↦ kprof P` with its positionwise action on morphisms of profunctors;
* `FreeMon.mapComp`: the laxator, zipping two lists of elements into a list of representatives
  of the coend;
* `FreeMon.mapCompanion`: lists of morphisms `b_i ⟶ F a_i` are morphisms `bs ⟶ map F as`;
* `FreeMon.ηComm`, `FreeMon.μComm`: the pseudonaturality cells of `η` and `μ`.
-/

@[expose] public section

namespace CategoryTheory

universe u

open Profunctor Opposite Limits

namespace FreeMon

variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]

namespace KProfApp

variable {P Q R : Profunctor.{u} C D}

/-- The action of a morphism of profunctors, positionwise. -/
def map₂ (α : P ⟶ Q) : ∀ {as : List C} {bs : List D}, KProfApp P as bs → KProfApp Q as bs
  | [], [], _ => nil
  | _ :: _, _ :: _, e => cons ((α.app _).app _ (head e)) (map₂ α (tail e))
  | [], _ :: _, e => isEmptyElim e
  | _ :: _, [], e => isEmptyElim e

theorem map₂_id : ∀ {as : List C} {bs : List D} (e : KProfApp P as bs), map₂ (𝟙 P) e = e
  | [], [], _ => rfl
  | _ :: _, _ :: _, e => congrArg (cons _) (map₂_id (tail e))
  | [], _ :: _, e => isEmptyElim e
  | _ :: _, [], e => isEmptyElim e

theorem map₂_comp (α : P ⟶ Q) (β : Q ⟶ R) :
    ∀ {as : List C} {bs : List D} (e : KProfApp P as bs), map₂ (α ≫ β) e = map₂ β (map₂ α e)
  | [], [], _ => rfl
  | _ :: _, _ :: _, e => congrArg (cons _) (map₂_comp α β (tail e))
  | [], _ :: _, e => isEmptyElim e
  | _ :: _, [], e => isEmptyElim e

theorem map₂_mapL (α : P ⟶ Q) : ∀ {as as' : List C} {bs : List D} (f : Hom as as')
    (e : KProfApp P as bs), map₂ α (mapL f e) = mapL f (map₂ α e)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, e =>
    congrArg₂ cons (app_mapL α _ _) (map₂_mapL α (FreeMon.tail f) (tail e))
  | [], _ :: _, _, f, _ => PEmpty.elim f
  | _ :: _, [], _, f, _ => PEmpty.elim f
  | [], [], _ :: _, _, e => isEmptyElim e
  | _ :: _, _ :: _, [], _, e => isEmptyElim e

theorem map₂_mapR (α : P ⟶ Q) : ∀ {as : List C} {bs bs' : List D} (g : Hom bs bs')
    (e : KProfApp P as bs'), map₂ α (mapR g e) = mapR g (map₂ α e)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, g, e =>
    congrArg₂ cons (app_mapR α _ _) (map₂_mapR α (FreeMon.tail g) (tail e))
  | _, [], _ :: _, g, _ => PEmpty.elim g
  | _, _ :: _, [], g, _ => PEmpty.elim g
  | [], _ :: _, _ :: _, _, e => isEmptyElim e
  | _ :: _, [], [], _, e => isEmptyElim e

end KProfApp

/-- The action of the free strict monoidal category monad on profunctors. -/
def mapProf : Profunctor.{u} C D ⥤ Profunctor.{u} (FreeMon C) (FreeMon D) where
  obj := kprof
  map α := ofSquare
    { app := KProfApp.map₂ α
      natL f e := KProfApp.map₂_mapL α f e
      natR e g := KProfApp.map₂_mapR α g e }
  map_id _ := hom_ext' fun _ _ e => KProfApp.map₂_id e
  map_comp _ _ := hom_ext' fun _ _ e => KProfApp.map₂_comp _ _ e

@[simp] theorem mapProf_map_app {P Q : Profunctor.{u} C D} (α : P ⟶ Q) {as : FreeMon C}
    {bs : FreeMon D} (e : (kprof P).app as bs) :
    ((mapProf.map α).app as).app (op bs) e = KProfApp.map₂ α e := rfl

/-! ### The laxator -/

namespace KProfApp

variable {P : Profunctor.{u} C D} {Q : Profunctor.{u} D E}

/-- Zip two lists of elements into a list of representatives of the coend. -/
def zipComp : ∀ {as : List C} {bs : List D} {cs : List E},
    KProfApp P as bs → KProfApp Q bs cs → KProfApp (P.comp Q) as cs
  | [], [], [], _, _ => nil
  | _ :: _, _ :: _, _ :: _, e, e' => cons (Quot.mk _ ⟨_, head e, head e'⟩) (zipComp (tail e) (tail e'))
  | [], _ :: _, _, e, _ => isEmptyElim e
  | _ :: _, [], _, e, _ => isEmptyElim e
  | [], [], _ :: _, _, e' => isEmptyElim e'
  | _ :: _, _ :: _, [], _, e' => isEmptyElim e'

theorem zipComp_wedge {as : List C} {bs bs' : List D} {cs : List E} (e : KProfApp P as bs')
    (g : FreeMon.Hom bs bs') (e' : KProfApp Q bs cs) :
    zipComp (mapR g e) e' = zipComp e (mapL g e') := by
  induction as generalizing bs bs' cs with
  | nil =>
    cases bs <;> cases bs' <;> cases cs <;>
      first | rfl | exact isEmptyElim e | exact isEmptyElim e' | exact PEmpty.elim g
  | cons a as ih =>
    cases bs <;> cases bs' <;> cases cs <;>
      first | exact isEmptyElim e | exact isEmptyElim e' | exact PEmpty.elim g |
        exact congrArg₂ cons
          (Quot.sound (Types.coendRel.mk (F := P.compDiagram Q _ _) g.1 (head e, head e')))
          (ih (tail e) g.2 (tail e'))

theorem zipComp_mapL {as as' : List C} {bs : List D} {cs : List E} (f : FreeMon.Hom as as')
    (e : KProfApp P as bs) (e' : KProfApp Q bs cs) :
    zipComp (mapL f e) e' = mapL f (zipComp e e') := by
  induction as generalizing as' bs cs with
  | nil =>
    cases as' <;> cases bs <;> cases cs <;>
      first | rfl | exact isEmptyElim e | exact isEmptyElim e' | exact PEmpty.elim f
  | cons a as ih =>
    cases as' <;> cases bs <;> cases cs <;>
      first | exact isEmptyElim e | exact isEmptyElim e' | exact PEmpty.elim f |
        exact congrArg₂ cons (comp_mapL_mk P Q _ _ _ _).symm (ih f.2 (tail e) (tail e'))

theorem zipComp_mapR {as : List C} {bs : List D} {cs cs' : List E} (e : KProfApp P as bs)
    (e' : KProfApp Q bs cs') (g : FreeMon.Hom cs cs') :
    zipComp e (mapR g e') = mapR g (zipComp e e') := by
  induction as generalizing bs cs cs' with
  | nil =>
    cases bs <;> cases cs <;> cases cs' <;>
      first | rfl | exact isEmptyElim e | exact isEmptyElim e' | exact PEmpty.elim g
  | cons a as ih =>
    cases bs <;> cases cs <;> cases cs' <;>
      first | exact isEmptyElim e | exact isEmptyElim e' | exact PEmpty.elim g |
        exact congrArg₂ cons (comp_mapR_mk P Q _ _ _ _).symm (ih (tail e) (tail e') g.2)

end KProfApp

/-- The laxator of `FreeMon` on profunctors: zip. -/
def mapComp (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) :
    (kprof P).comp (kprof Q) ⟶ kprof (P.comp Q) :=
  compDesc
    { app := KProfApp.zipComp
      wedge e g e' := KProfApp.zipComp_wedge e g e'
      natL f e e' := KProfApp.zipComp_mapL f e e'
      natR e e' g := KProfApp.zipComp_mapR e e' g }

/-! ### Companions -/

namespace KProfApp

variable (F : C ⥤ D)

/-- A list of elements of the companion `F_*` is a morphism into `map F`. -/
def toHom : ∀ {as : List C} {bs : List D},
    KProfApp F.toProfunctor as bs → FreeMon.Hom bs (as.map F.obj)
  | [], [], _ => PUnit.unit
  | _ :: _, _ :: _, e => (head e, toHom (tail e))
  | [], _ :: _, e => isEmptyElim e
  | _ :: _, [], e => isEmptyElim e

/-- A morphism into `map F` is a list of elements of the companion `F_*`. -/
def ofHom : ∀ {as : List C} {bs : List D},
    FreeMon.Hom bs (as.map F.obj) → KProfApp F.toProfunctor as bs
  | [], [], _ => nil
  | _ :: _, _ :: _, f => cons f.1 (ofHom f.2)
  | [], _ :: _, f => PEmpty.elim f
  | _ :: _, [], f => PEmpty.elim f

theorem ofHom_toHom {as : List C} {bs : List D} (e : KProfApp F.toProfunctor as bs) :
    ofHom F (toHom F e) = e := by
  induction as generalizing bs with
  | nil => cases bs <;> first | rfl | exact isEmptyElim e
  | cons a as ih => cases bs <;> first | exact isEmptyElim e | exact congrArg (cons _) (ih _)

theorem toHom_ofHom {as : List C} {bs : List D} (f : FreeMon.Hom bs (as.map F.obj)) :
    toHom F (ofHom F f) = f := by
  induction as generalizing bs with
  | nil => cases bs <;> first | rfl | exact PEmpty.elim f
  | cons a as ih => cases bs <;> first | exact PEmpty.elim f | exact congrArg (Prod.mk _) (ih _)

theorem toHom_mapL {as as' : List C} {bs : List D} (f : FreeMon.Hom as as')
    (e : KProfApp F.toProfunctor as bs) :
    toHom F (mapL f e) = (toHom F e : mk bs ⟶ (map F).obj (mk as)) ≫ (map F).map (f : mk as ⟶ mk as') := by
  induction as generalizing as' bs with
  | nil => cases as' <;> cases bs <;> first | rfl | exact isEmptyElim e | exact PEmpty.elim f
  | cons a as ih =>
    cases as' <;> cases bs <;> first | exact isEmptyElim e | exact PEmpty.elim f |
      exact congrArg (Prod.mk _) (ih f.2 (tail e))

theorem toHom_mapR {as : List C} {bs bs' : List D} (g : FreeMon.Hom bs bs')
    (e : KProfApp F.toProfunctor as bs') :
    toHom F (mapR g e) =
      FreeMon.Hom.comp g (toHom F e) := by
  induction as generalizing bs bs' with
  | nil => cases bs <;> cases bs' <;> first | rfl | exact isEmptyElim e | exact PEmpty.elim g
  | cons a as ih =>
    cases bs <;> cases bs' <;> first | exact isEmptyElim e | exact PEmpty.elim g |
      exact congrArg (Prod.mk _) (ih g.2 (tail e))

end KProfApp

/-- `FreeMon` commutes with companions. -/
def mapCompanion (F : C ⥤ D) : kprof F.toProfunctor ≅ (map F).toProfunctor where
  hom := ofSquare
    { app := KProfApp.toHom F
      natL f e := KProfApp.toHom_mapL F f e
      natR e g := KProfApp.toHom_mapR F g e }
  inv := ofSquare
    { app := KProfApp.ofHom F
      natL {c c' d} β f :=
        (congrArg (KProfApp.ofHom F) ((KProfApp.toHom_mapL F β (KProfApp.ofHom F f)).trans
          (congrArg (fun k : d ⟶ (map F).obj c => k ≫ (map F).map β)
            (KProfApp.toHom_ofHom F f)))).symm.trans (KProfApp.ofHom_toHom F _)
      natR {c d d'} f β :=
        (congrArg (KProfApp.ofHom F) ((KProfApp.toHom_mapR F β (KProfApp.ofHom F f)).trans
          (congrArg (fun k : d' ⟶ (map F).obj c => β ≫ k)
            (KProfApp.toHom_ofHom F f)))).symm.trans (KProfApp.ofHom_toHom F _) }
  hom_inv_id := hom_ext' fun _ _ e => KProfApp.ofHom_toHom F e
  inv_hom_id := hom_ext' fun _ _ f => KProfApp.toHom_ofHom F f

/-! ### Pseudonaturality of the unit -/

section Unit

variable {P : Profunctor.{u} C D}

/-- An element of `T P` over a singleton list `[c]` is a single element of `P`, viewed in the
pushforward `P ⊙ η_*`. -/
def ηFun {c : C} : ∀ {ws : List D}, KProfApp P [c] ws → (P.comp (unit D).toProfunctor).app c (mk ws)
  | [d], t => Quot.mk _ ⟨d, KProfApp.head t, 𝟙 (mk [d])⟩
  | [], t => isEmptyElim t
  | _ :: _ :: _, t => isEmptyElim (KProfApp.tail t)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pseudonaturality cell of `η` for `FreeMon`. -/
def ηComm (P : Profunctor.{u} C D) :
    (kprof P).whiskerLeft₂ (unit C) (𝟭 _) ⟶ P.comp (unit D).toProfunctor :=
  ofSquare
    { app {c ws} t := ηFun (ws := ws.as) t
      natL {c c' ws} β t := by
        obtain ⟨_ | ⟨d, _ | _⟩⟩ := ws
        · exact PEmpty.elim t
        · exact (comp_mapL_mk P _ β d _ _).symm
        · exact PEmpty.elim t.2
      natR {c ws ws'} t g := by
        obtain ⟨_ | ⟨d, _ | _⟩⟩ := ws <;> obtain ⟨_ | ⟨d', _ | _⟩⟩ := ws' <;>
          first | exact PEmpty.elim t | exact PEmpty.elim t.2 | exact PEmpty.elim g |
            exact PEmpty.elim g.2 | skip
        show Quot.mk _ ⟨d, P.mapR g.1 t.1, 𝟙 (mk [d])⟩ =
          (P.comp (unit D).toProfunctor).mapR g (Quot.mk _ ⟨d', t.1, 𝟙 (mk [d'])⟩)
        rw [comp_mapR_mk, toProfunctor_mapR, Category.comp_id]
        exact (Quot.sound (Types.coendRel.mk (F := P.compDiagram (unit D).toProfunctor c
          (mk [d])) g.1 (t.1, 𝟙 (mk [d])))).trans
          (congrArg (fun h => compMk (P := P) (Q := (unit D).toProfunctor) d' t.1 h)
            (Category.id_comp (cons g.1 nil))) }

end Unit

/-! ### Pseudonaturality of the multiplication: splitting lists -/

section Mult

namespace KProfApp

variable {P : Profunctor.{u} C D}

/-- The elements over the first `as₁.length` positions. -/
def takeE : ∀ (as₁ : List C) {as₂ : List C} {vs : List D}, KProfApp P (as₁ ++ as₂) vs →
    KProfApp P as₁ (vs.take as₁.length)
  | [], _, _, _ => nil
  | _ :: as₁, _, _ :: _, t => cons t.1 (takeE as₁ t.2)
  | _ :: _, _, [], t => PEmpty.elim t
termination_by structural as₁ _ _ _ => as₁

/-- The elements after the first `as₁.length` positions. -/
def dropE : ∀ (as₁ : List C) {as₂ : List C} {vs : List D}, KProfApp P (as₁ ++ as₂) vs →
    KProfApp P as₂ (vs.drop as₁.length)
  | [], _, _, t => t
  | _ :: as₁, _, _ :: _, t => dropE as₁ t.2
  | _ :: _, _, [], t => PEmpty.elim t
termination_by structural as₁ _ _ _ => as₁

theorem length_eq : ∀ {as : List C} {vs : List D}, KProfApp P as vs → as.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, t => congrArg (· + 1) (length_eq (tail t))
  | [], _ :: _, t => PEmpty.elim t
  | _ :: _, [], t => PEmpty.elim t

end KProfApp

/-- Split a list `vs` into blocks of the lengths of the blocks of `W`. -/
def shape : List (FreeMon C) → List D → List (FreeMon D)
  | [], _ => []
  | A :: W, vs => mk (vs.take A.as.length) :: shape W (vs.drop A.as.length)

theorem shape_flatMap : ∀ (W : List (FreeMon C)) (vs : List D),
    (W.flatMap FreeMon.as).length = vs.length → (shape W vs).flatMap FreeMon.as = vs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | A :: W, vs, h => by
    have h' : (W.flatMap FreeMon.as).length = (vs.drop A.as.length).length := by
      simp only [List.flatMap_cons, List.length_append, List.length_drop] at h ⊢
      omega
    simp only [shape, List.flatMap_cons, shape_flatMap W _ h', List.take_append_drop]

namespace KProfApp

variable {P : Profunctor.{u} C D}

/-- Split a list of elements over a flattening into a list of lists of elements. -/
def splitE : ∀ (W : List (FreeMon C)) {vs : List D}, KProfApp P (W.flatMap FreeMon.as) vs →
    KProfApp (kprof P) W (shape W vs)
  | [], _, _ => nil
  | A :: W, _, t => cons (takeE A.as t) (splitE W (dropE A.as t))

end KProfApp

/-- The pseudonaturality cell of `μ` for `FreeMon`, on representatives. -/
def μFun (P : Profunctor.{u} C D) (W : List (FreeMon C)) {vs : List D}
    (t : KProfApp P (W.flatMap FreeMon.as) vs) :
    ((kprof (kprof P)).comp (flatten D).toProfunctor).app (mk W) (mk vs) :=
  Quot.mk _ ⟨mk (shape W vs), KProfApp.splitE W t,
    eqToHom (congrArg mk (shape_flatMap W vs (KProfApp.length_eq t)).symm)⟩

end Mult

/-! ### Naturality of the splitting -/

section MultNat

theorem Hom.length_eq : ∀ {as as' : List C}, FreeMon.Hom as as' → as.length = as'.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, f => congrArg (· + 1) (Hom.length_eq f.2)
  | [], _ :: _, f => PEmpty.elim f
  | _ :: _, [], f => PEmpty.elim f

/-- The first `n` components of a morphism. -/
def takeHom : ∀ (n : ℕ) {vs vs' : List D}, FreeMon.Hom vs vs' →
    FreeMon.Hom (vs.take n) (vs'.take n)
  | 0, _, _, _ => PUnit.unit
  | _ + 1, [], [], _ => PUnit.unit
  | n + 1, _ :: _, _ :: _, h => (h.1, takeHom n h.2)
  | _ + 1, [], _ :: _, h => PEmpty.elim h
  | _ + 1, _ :: _, [], h => PEmpty.elim h
termination_by structural n _ _ _ => n

/-- The components of a morphism after the first `n`. -/
def dropHom : ∀ (n : ℕ) {vs vs' : List D}, FreeMon.Hom vs vs' →
    FreeMon.Hom (vs.drop n) (vs'.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => PUnit.unit
  | n + 1, _ :: _, _ :: _, h => dropHom n h.2
  | _ + 1, [], _ :: _, h => PEmpty.elim h
  | _ + 1, _ :: _, [], h => PEmpty.elim h
termination_by structural n _ _ _ => n

/-- Split a morphism into blocks of the lengths of the blocks of `W`. -/
def splitHom : ∀ (W : List (FreeMon C)) {vs vs' : List D}, FreeMon.Hom vs vs' →
    FreeMon.Hom (shape W vs) (shape W vs')
  | [], _, _, _ => PUnit.unit
  | A :: W, _, _, h => (takeHom A.as.length h, splitHom W (dropHom A.as.length h))

theorem append_takeHom_dropHom : ∀ (n : ℕ) {vs vs' : List D} (h : FreeMon.Hom vs vs'),
    FreeMon.append (A := mk (vs.take n)) (B := mk (vs'.take n)) (takeHom n h)
      (A' := mk (vs.drop n)) (B' := mk (vs'.drop n)) (dropHom n h) ≍
      (h : mk vs ⟶ mk vs')
  | 0, _, _, _ => HEq.rfl
  | _ + 1, [], [], _ => HEq.rfl
  | n + 1, _ :: _, _ :: _, h =>
    cons_heq_cons rfl rfl (by simp) (by simp) HEq.rfl (append_takeHom_dropHom n h.2)
  | _ + 1, [], _ :: _, h => PEmpty.elim h
  | _ + 1, _ :: _, [], h => PEmpty.elim h

theorem flatten_map_splitHom : ∀ (W : List (FreeMon C)) {vs vs' : List D}
    (h : FreeMon.Hom vs vs'), (W.flatMap FreeMon.as).length = vs.length →
    (flatten D).map (splitHom W h : mk (shape W vs) ⟶ mk (shape W vs')) ≍ (h : mk vs ⟶ mk vs')
  | [], [], [], _, _ => HEq.rfl
  | [], _ :: _, _, _, hl => by simp at hl
  | [], [], _ :: _, h, _ => PEmpty.elim h
  | A :: W, vs, vs', h, hl => by
    have hl' : (W.flatMap FreeMon.as).length = (vs.drop A.as.length).length := by
      simp only [List.flatMap_cons, List.length_append, List.length_drop] at hl ⊢
      omega
    have hvs := Hom.length_eq h
    refine HEq.trans ?_ (append_takeHom_dropHom A.as.length h)
    refine append_heq_append rfl rfl ?_ ?_ HEq.rfl (flatten_map_splitHom W _ hl')
    · exact congrArg mk (shape_flatMap W _ hl')
    · refine congrArg mk (shape_flatMap W _ ?_)
      simp only [List.length_drop]
      simp only [List.flatMap_cons, List.length_append] at hl
      omega

namespace KProfApp

variable {P : Profunctor.{u} C D}

theorem takeE_mapR : ∀ (as₁ : List C) {as₂ : List C} {vs vs' : List D}
    (h : FreeMon.Hom vs vs') (t : KProfApp P (as₁ ++ as₂) vs'),
    takeE as₁ (mapR h t) = mapR (takeHom as₁.length h) (takeE as₁ t)
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, _ :: _, _ :: _, h, t => congrArg (cons _) (takeE_mapR _ h.2 t.2)
  | _ :: _, _, _, [], _, t => PEmpty.elim t
  | _ :: _, _, [], _ :: _, h, _ => PEmpty.elim h

theorem dropE_mapR : ∀ (as₁ : List C) {as₂ : List C} {vs vs' : List D}
    (h : FreeMon.Hom vs vs') (t : KProfApp P (as₁ ++ as₂) vs'),
    dropE as₁ (mapR h t) = mapR (dropHom as₁.length h) (dropE as₁ t)
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, _ :: _, _ :: _, h, t => dropE_mapR _ h.2 t.2
  | _ :: _, _, _, [], _, t => PEmpty.elim t
  | _ :: _, _, [], _ :: _, h, _ => PEmpty.elim h

theorem splitE_mapR : ∀ (W : List (FreeMon C)) {vs vs' : List D} (h : FreeMon.Hom vs vs')
    (t : KProfApp P (W.flatMap FreeMon.as) vs'),
    splitE W (mapR h t) = mapR (P := kprof P) (splitHom W h) (splitE W t)
  | [], _, _, _, _ => rfl
  | A :: W, _, _, h, t => by
    simp only [splitE, splitHom]
    rw [takeE_mapR, dropE_mapR, splitE_mapR W]
    rfl

theorem takeE_mapL_heq : ∀ (as as' : List C) (f : FreeMon.Hom as as') {bs bs' : List C}
    (f' : FreeMon.Hom bs bs') {vs : List D} (t : KProfApp P (as ++ bs) vs),
    takeE as' (mapL (FreeMon.append (A := mk as) (B := mk as') f (A' := mk bs) (B' := mk bs') f') t) ≍
      mapL f (takeE as t)
  | [], [], _, _, _, _, _, _ => HEq.rfl
  | _ :: _, _ :: _, f, _, _, f', _ :: _, t =>
    cons_heq_cons rfl rfl rfl (by rw [Hom.length_eq f.2]) HEq.rfl
      (takeE_mapL_heq _ _ f.2 f' t.2)
  | [], _ :: _, f, _, _, _, _, _ => PEmpty.elim f
  | _ :: _, [], f, _, _, _, _, _ => PEmpty.elim f
  | _ :: _, _ :: _, _, _, _, _, [], t => PEmpty.elim t

theorem dropE_mapL_heq : ∀ (as as' : List C) (f : FreeMon.Hom as as') {bs bs' : List C}
    (f' : FreeMon.Hom bs bs') {vs : List D} (t : KProfApp P (as ++ bs) vs),
    dropE as' (mapL (FreeMon.append (A := mk as) (B := mk as') f (A' := mk bs) (B' := mk bs') f') t) ≍
      mapL f' (dropE as t)
  | [], [], _, _, _, _, _, _ => HEq.rfl
  | _ :: _, _ :: _, f, _, _, f', _ :: _, t => dropE_mapL_heq _ _ f.2 f' t.2
  | [], _ :: _, f, _, _, _, _, _ => PEmpty.elim f
  | _ :: _, [], f, _, _, _, _, _ => PEmpty.elim f
  | _ :: _, _ :: _, _, _, _, _, [], t => PEmpty.elim t

theorem shape_congr : ∀ {W W' : List (FreeMon C)} (β : FreeMon.Hom W W') (vs : List D),
    shape W' vs = shape W vs
  | [], [], _, _ => rfl
  | A :: W, A' :: W', β, vs => by
    simp only [shape, Hom.length_eq (β.1 : FreeMon.Hom A.as A'.as), shape_congr β.2]
  | [], _ :: _, β, _ => PEmpty.elim β
  | _ :: _, [], β, _ => PEmpty.elim β

theorem splitE_heq (W : List (FreeMon C)) {vs vs' : List D} (h : vs = vs')
    {t : KProfApp P (W.flatMap FreeMon.as) vs} {t' : KProfApp P (W.flatMap FreeMon.as) vs'}
    (ht : t ≍ t') : splitE W t ≍ splitE W t' := by
  subst h; cases ht; rfl

theorem splitE_mapL_heq : ∀ {W W' : List (FreeMon C)} (β : FreeMon.Hom W W') {vs : List D}
    (t : KProfApp P (W.flatMap FreeMon.as) vs),
    splitE W' (mapL ((flatten C).map (β : mk W ⟶ mk W')) t) ≍ mapL (P := kprof P) β (splitE W t)
  | [], [], _, _, _ => HEq.rfl
  | A :: W, A' :: W', β, vs, t => by
    have hA := Hom.length_eq (β.1 : FreeMon.Hom A.as A'.as)
    refine cons_heq_cons rfl (by rw [hA]) rfl (by rw [hA, shape_congr β.2]) ?_ ?_
    · exact takeE_mapL_heq A.as A'.as β.1 _ t
    · refine (splitE_heq W' (by rw [hA]) (dropE_mapL_heq A.as A'.as β.1 _ t)).trans ?_
      exact splitE_mapL_heq β.2 (dropE A.as t)
  | [], _ :: _, β, _, _ => PEmpty.elim β
  | _ :: _, [], β, _, _ => PEmpty.elim β

end KProfApp

end MultNat

theorem eqToHom_heq_eqToHom {X : Type u} [Category.{u} X] {a b b' : X} (h : b = b') (e : a = b)
    (e' : a = b') : eqToHom e ≍ eqToHom e' := by
  subst h; rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pseudonaturality cell of `μ` for `FreeMon`: split a list of elements over a flattening
`μ W` into blocks matching `W`. -/
def μComm (P : Profunctor.{u} C D) :
    (kprof P).whiskerLeft₂ (flatten C) (𝟭 _) ⟶ (kprof (kprof P)).comp (flatten D).toProfunctor :=
  ofSquare
    { app {W vs} t := μFun P W.as (vs := vs.as) t
      natL {W W' vs} β t := by
        refine Eq.trans ?_ (comp_mapL_mk _ _ β _ _ _).symm
        exact comp_mk_heq (congrArg mk (KProfApp.shape_congr β vs.as))
          (KProfApp.splitE_mapL_heq β t)
          (eqToHom_heq_eqToHom (congrArg (fun V => (flatten D).obj (mk V))
            (KProfApp.shape_congr β vs.as)) _ _)
      natR {W vs vs'} t h := by
        refine Eq.trans ?_ (comp_mapR_mk _ _ h _ _ _).symm
        have hl := KProfApp.length_eq t
        have hl' : (W.as.flatMap FreeMon.as).length = vs.as.length :=
          hl.trans (Hom.length_eq (h : FreeMon.Hom vs.as vs'.as)).symm
        have H := (conj_eqToHom_iff_heq _ _ (congrArg mk (shape_flatMap W.as vs.as hl'))
          (congrArg mk (shape_flatMap W.as vs'.as hl))).2 (flatten_map_splitHom W.as h hl')
        change compMk (P := kprof (kprof P)) (Q := (flatten D).toProfunctor)
          (mk (shape W.as vs.as)) (KProfApp.splitE W.as (KProfApp.mapR h t)) (eqToHom _) = _
        rw [KProfApp.splitE_mapR W.as h t]
        refine (Quot.sound (Types.coendRel.mk
          (F := (kprof (kprof P)).compDiagram (flatten D).toProfunctor W vs)
          (splitHom W.as h) (KProfApp.splitE W.as t, eqToHom _))).trans ?_
        refine congrArg (fun g => compMk (P := kprof (kprof P)) (Q := (flatten D).toProfunctor)
          (mk (shape W.as vs'.as)) (KProfApp.splitE W.as t) g) ?_
        change eqToHom _ ≫ (flatten D).map _ = h ≫ eqToHom _
        rw [H]
        simp }

end FreeMon

open FreeMon in
/-- The free strict monoidal category monad acts on profunctors. -/
instance Cat.freeMon.kleisliProf : KleisliProf.{u} Cat.freeMon where
  mapProf := FreeMon.mapProf
  mapComp P Q := mapComp P Q
  mapCompanion F := mapCompanion F.toFunctor
  ηComm P := ηComm P
  μComm P := μComm P

namespace FreeMon

end FreeMon

end CategoryTheory
