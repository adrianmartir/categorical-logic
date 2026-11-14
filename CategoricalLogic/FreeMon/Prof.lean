/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.FreeMon.Basic
public import CategoricalLogic.Profunctor.Comp

/-!
# The free strict monoidal category monad on profunctors: elements

For a profunctor `P : Profunctor C D`, `Lax.LP P as bs` is the type of lists of elements of `P`
matching the lists `as`, `bs` positionwise (by recursion on both lists, like `FreeMon.Hom`), and
`Lax.LP.prof P : Profunctor (FreeMon C) (FreeMon D)` is the corresponding profunctor.
-/

@[expose] public section

namespace CategoryTheory.Lax

universe w v u v' u'

open Profunctor FreeMon

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Lists of elements of `P`, matched positionwise with the lists of objects. -/
def LP (P : Profunctor.{w} C D) : List C → List D → Type w
  | [], [] => PUnit
  | a :: as, b :: bs => P.app a b × LP P as bs
  | [], _ :: _ => PEmpty
  | _ :: _, [] => PEmpty

namespace LP

variable {P : Profunctor.{w} C D}

/-- The empty list of elements. -/
def nil : LP P [] [] := PUnit.unit

/-- Prepend an element. -/
def cons {a : C} {b : D} {as : List C} {bs : List D} (p : P.app a b) (ps : LP P as bs) :
    LP P (a :: as) (b :: bs) := (p, ps)

instance {b : D} {bs : List D} : IsEmpty (LP P [] (b :: bs)) := inferInstanceAs (IsEmpty PEmpty)

instance {a : C} {as : List C} : IsEmpty (LP P (a :: as) []) := inferInstanceAs (IsEmpty PEmpty)

variable {a a' : C} {b b' : D} {as as' : List C} {bs bs' : List D}

theorem ext_nil (e e' : LP P [] []) : e = e' := rfl

/-- Induction on lists of elements. -/
@[elab_as_elim]
def rec' {motive : ∀ (as : List C) (bs : List D), LP P as bs → Sort*}
    (nil : motive [] [] nil)
    (cons : ∀ {a b as bs} (p : P.app a b) (ps : LP P as bs),
      motive as bs ps → motive (a :: as) (b :: bs) (cons p ps)) :
    ∀ {as : List C} {bs : List D} (e : LP P as bs), motive as bs e
  | [], [], _ => nil
  | _ :: _, _ :: _, e => cons e.1 e.2 (rec' nil cons e.2)
  | [], _ :: _, e => isEmptyElim e
  | _ :: _, [], e => isEmptyElim e

theorem cons_heq_cons {p : P.app a b} {p' : P.app a' b'} {ps : LP P as bs}
    {ps' : LP P as' bs'} (ha : a = a') (hb : b = b') (has : as = as') (hbs : bs = bs')
    (hp : p ≍ p') (hps : ps ≍ ps') : cons p ps ≍ cons p' ps' := by
  subst ha hb has hbs; cases hp; cases hps; rfl

/-! ### The action of morphisms -/

/-- The covariant action, positionwise. -/
def mapL : ∀ {as as' : List C} {bs : List D}, Hom as as' → LP P as bs → LP P as' bs
  | [], [], [], _, e => e
  | _ :: _, _ :: _, _ :: _, f, e => cons (P.mapL f.1 e.1) (mapL f.2 e.2)
  | [], _ :: _, _, f, _ => PEmpty.elim f
  | _ :: _, [], _, f, _ => PEmpty.elim f
  | [], [], _ :: _, _, e => isEmptyElim e
  | _ :: _, _ :: _, [], _, e => isEmptyElim e

/-- The contravariant action, positionwise. -/
def mapR : ∀ {as : List C} {bs bs' : List D}, Hom bs bs' → LP P as bs' → LP P as bs
  | [], [], [], _, e => e
  | _ :: _, _ :: _, _ :: _, g, e => cons (P.mapR g.1 e.1) (mapR g.2 e.2)
  | _, [], _ :: _, g, _ => PEmpty.elim g
  | _, _ :: _, [], g, _ => PEmpty.elim g
  | [], _ :: _, _ :: _, _, e => isEmptyElim e
  | _ :: _, [], [], _, e => isEmptyElim e

@[simp] theorem mapL_cons {A A' : FreeMon C} (f : a ⟶ a') (fs : A ⟶ A') (p : P.app a b)
    (ps : LP P A.as bs) : mapL (FreeMon.cons f fs) (cons p ps) = cons (P.mapL f p) (mapL fs ps) :=
  rfl

@[simp] theorem mapR_cons {B B' : FreeMon D} (g : b ⟶ b') (gs : B ⟶ B') (p : P.app a b')
    (ps : LP P as B'.as) :
    mapR (FreeMon.cons g gs) (cons p ps) = cons (P.mapR g p) (mapR gs ps) := rfl

theorem mapL_id : ∀ {as : List C} {bs : List D} (e : LP P as bs), mapL (𝟙 (mk as)) e = e
  | [], [], _ => rfl
  | _ :: _, _ :: _, e => congrArg₂ cons (P.mapL_id _ _ e.1) (mapL_id e.2)
  | [], _ :: _, e => isEmptyElim e
  | _ :: _, [], e => isEmptyElim e

theorem mapR_id : ∀ {as : List C} {bs : List D} (e : LP P as bs), mapR (𝟙 (mk bs)) e = e
  | [], [], _ => rfl
  | _ :: _, _ :: _, e => congrArg₂ cons (P.mapR_id _ _ e.1) (mapR_id e.2)
  | [], _ :: _, e => isEmptyElim e
  | _ :: _, [], e => isEmptyElim e

theorem mapL_comp : ∀ {as as' as'' : List C} {bs : List D} (f : mk as ⟶ mk as')
    (f' : mk as' ⟶ mk as'') (e : LP P as bs), mapL (f ≫ f') e = mapL f' (mapL f e)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, f, f', e =>
    congrArg₂ cons (P.mapL_comp f.1 f'.1 e.1) (mapL_comp f.2 f'.2 e.2)
  | [], _ :: _, _, _, f, _, _ => isEmptyElim f
  | _ :: _, [], _, _, f, _, _ => isEmptyElim f
  | [], [], _ :: _, _, _, f', _ => isEmptyElim f'
  | _ :: _, _ :: _, [], _, _, f', _ => isEmptyElim f'
  | [], [], [], _ :: _, _, _, e => isEmptyElim e
  | _ :: _, _ :: _, _ :: _, [], _, _, e => isEmptyElim e

theorem mapR_comp : ∀ {as : List C} {bs bs' bs'' : List D} (g : mk bs ⟶ mk bs')
    (g' : mk bs' ⟶ mk bs'') (e : LP P as bs''), mapR (g ≫ g') e = mapR g (mapR g' e)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, g, g', e =>
    congrArg₂ cons (P.mapR_comp g.1 g'.1 e.1) (mapR_comp g.2 g'.2 e.2)
  | _, [], _ :: _, _, g, _, _ => isEmptyElim g
  | _, _ :: _, [], _, g, _, _ => isEmptyElim g
  | _, [], [], _ :: _, _, g', _ => isEmptyElim g'
  | _, _ :: _, _ :: _, [], _, g', _ => isEmptyElim g'
  | _ :: _, [], [], [], _, _, e => isEmptyElim e
  | [], _ :: _, _ :: _, _ :: _, _, _, e => isEmptyElim e

theorem mapL_mapR : ∀ {as as' : List C} {bs bs' : List D} (f : mk as ⟶ mk as')
    (g : mk bs ⟶ mk bs') (e : LP P as bs'), mapL f (mapR g e) = mapR g (mapL f e)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, f, g, e =>
    congrArg₂ cons (P.mapL_mapR_comm f.1 g.1 e.1)
      (mapL_mapR f.2 g.2 e.2)
  | [], _ :: _, _, _, f, _, _ => isEmptyElim f
  | _ :: _, [], _, _, f, _, _ => isEmptyElim f
  | _, _, [], _ :: _, _, g, _ => isEmptyElim g
  | _, _, _ :: _, [], _, g, _ => isEmptyElim g
  | [], [], _ :: _, _ :: _, _, _, e => isEmptyElim e
  | _ :: _, _ :: _, [], [], _, _, e => isEmptyElim e

/-- The free strict monoidal category monad applied to a profunctor. -/
def prof (P : Profunctor.{w} C D) : Profunctor.{w} (FreeMon C) (FreeMon D) where
  obj A :=
    { obj B := LP P A.as B.unop.as
      map g := TypeCat.ofHom (mapR g.unop)
      map_id _ := TypeCat.Hom.ext (TypeCat.Fun.ext (funext mapR_id))
      map_comp g g' := TypeCat.Hom.ext (TypeCat.Fun.ext (funext (mapR_comp g'.unop g.unop))) }
  map f :=
    { app _ := TypeCat.ofHom (mapL f)
      naturality _ _ g := TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun e => mapL_mapR f g.unop e)) }
  map_id _ := NatTrans.ext (funext fun _ => TypeCat.Hom.ext (TypeCat.Fun.ext (funext mapL_id)))
  map_comp f f' := NatTrans.ext (funext fun _ =>
    TypeCat.Hom.ext (TypeCat.Fun.ext (funext (mapL_comp f f'))))

theorem prof_app (A : FreeMon C) (B : FreeMon D) : (prof P).app A B = LP P A.as B.as := rfl

@[simp] theorem prof_mapL {A A' : FreeMon C} {B : FreeMon D} (f : A ⟶ A') (e : (prof P).app A B) :
    (prof P).mapL f e = mapL f e := rfl

@[simp] theorem prof_mapR {A : FreeMon C} {B B' : FreeMon D} (g : B ⟶ B')
    (e : (prof P).app A B') : (prof P).mapR g e = mapR g e := rfl

/-- Transports in `prof P` are heterogeneously trivial. -/
theorem prof_mpRight_heq {A : FreeMon C} {B B' : FreeMon D} (e : (prof P).app A B') (h : B = B') :
    (prof P).mpRight e h ≍ e := mpRight_heq _ e h

/-! ### Squares -/

section Square

variable {C' : Type u} [Category.{v} C'] {D' : Type u'} [Category.{v'} D']
  {Q : Profunctor.{w} C' D'} {F : C ⥤ C'} {G : D ⥤ D'}

/-- Apply a square positionwise. -/
def smap (s : Square P Q F G) : ∀ {as : List C} {bs : List D},
    LP P as bs → LP Q (as.map F.obj) (bs.map G.obj)
  | [], [], _ => nil
  | _ :: _, _ :: _, e => cons (s.app e.1) (smap s e.2)
  | [], _ :: _, e => isEmptyElim e
  | _ :: _, [], e => isEmptyElim e

theorem smap_mapL (s : Square P Q F G) : ∀ {as as' : List C} {bs : List D}
    (f : mk as ⟶ mk as') (e : LP P as bs),
    smap s (mapL f e) = mapL ((FreeMon.map F).map f) (smap s e)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, e =>
    congrArg₂ cons (s.natL f.1 e.1) (smap_mapL s f.2 e.2)
  | [], _ :: _, _, f, _ => isEmptyElim f
  | _ :: _, [], _, f, _ => isEmptyElim f
  | [], [], _ :: _, _, e => isEmptyElim e
  | _ :: _, _ :: _, [], _, e => isEmptyElim e

theorem smap_mapR (s : Square P Q F G) : ∀ {as : List C} {bs bs' : List D}
    (e : LP P as bs') (g : mk bs ⟶ mk bs'),
    smap s (mapR g e) = mapR ((FreeMon.map G).map g) (smap s e)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, e, g =>
    congrArg₂ cons (s.natR e.1 g.1) (smap_mapR s e.2 g.2)
  | _, [], _ :: _, _, g => isEmptyElim g
  | _, _ :: _, [], _, g => isEmptyElim g
  | [], _ :: _, _ :: _, e, _ => isEmptyElim e
  | _ :: _, [], [], e, _ => isEmptyElim e

/-- The action of the free strict monoidal category monad on squares. -/
def mapSquare (s : Square P Q F G) :
    Square (prof P) (prof Q) (FreeMon.map F) (FreeMon.map G) where
  app e := smap s e
  natL f e := smap_mapL s f e
  natR e g := smap_mapR s e g

end Square

end LP

end CategoryTheory.Lax
