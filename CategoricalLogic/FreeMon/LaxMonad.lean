/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.FreeMon.Prof
public import CategoricalLogic.LaxMonad

/-!
# The free strict monoidal category monad as a lax monad on profunctors

All laws are proved elementwise; the laws that involve transports along the propositional
monad laws of `FreeMon` are reduced to heterogeneous equalities (`Square.eq_cast_iff_heq`).

The laxator `prof P ⊙ prof Q ⇒ prof (P ⊙ Q)` zips a pair of composable lists into the list of
composable pairs; it is defined by `Quot.lift` (`compLift`) and computes. The unit comparison
`U (FreeMon C) ⇒ prof (U C)` reads a list of morphisms as a list of elements of the hom
profunctor (it is an isomorphism).
-/

@[expose] public section

namespace CategoryTheory.Lax

universe u

open Profunctor FreeMon

instance : CatFamily FreeMon.{u} where
  category _ _ := FreeMon.category

namespace LP

section Zip

variable {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
  {P : Profunctor.{u} C D} {R : Profunctor.{u} D E}

/-- Zip a pair of composable lists of elements into a list of composable pairs. -/
def zip : ∀ {as : List C} {bs : List D} {cs : List E},
    LP P as bs → LP R bs cs → LP (P.comp R) as cs
  | [], [], [], _, _ => nil
  | _ :: _, _ :: _, _ :: _, x, y => cons (compMk x.1 y.1) (zip x.2 y.2)
  | [], _ :: _, _, x, _ => isEmptyElim x
  | _ :: _, [], _, x, _ => isEmptyElim x
  | [], [], _ :: _, _, y => isEmptyElim y
  | _ :: _, _ :: _, [], _, y => isEmptyElim y

theorem zip_wedge : ∀ {as : List C} {bs bs' : List D} {cs : List E} (x : LP P as bs')
    (g : FreeMon.Hom bs bs') (y : LP R bs cs), zip (mapR g x) y = zip x (mapL g y)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, x, g, y =>
    congrArg₂ cons (compMk_wedge x.1 g.1 y.1) (zip_wedge x.2 g.2 y.2)
  | [], _, _ :: _, _, x, _, _ => isEmptyElim x
  | _ :: _, _, [], _, x, _, _ => isEmptyElim x
  | _, [], _ :: _, _, _, g, _ => PEmpty.elim g
  | _, _ :: _, [], _, _, g, _ => PEmpty.elim g
  | _, [], [], _ :: _, _, _, y => isEmptyElim y
  | _, _ :: _, _ :: _, [], _, _, y => isEmptyElim y

theorem zip_mapL : ∀ {as as' : List C} {bs : List D} {cs : List E} (f : FreeMon.Hom as as')
    (x : LP P as bs) (y : LP R bs cs), zip (mapL f x) y = mapL f (zip x y)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, f, x, y =>
    congrArg₂ cons (comp_mapL_compMk f.1 x.1 y.1).symm (zip_mapL f.2 x.2 y.2)
  | [], _ :: _, _, _, f, _, _ => PEmpty.elim f
  | _ :: _, [], _, _, f, _, _ => PEmpty.elim f
  | [], [], _ :: _, _, _, x, _ => isEmptyElim x
  | _ :: _, _ :: _, [], _, _, x, _ => isEmptyElim x
  | _, _, [], _ :: _, _, _, y => isEmptyElim y
  | _, _, _ :: _, [], _, _, y => isEmptyElim y

theorem zip_mapR : ∀ {as : List C} {bs : List D} {cs cs' : List E} (x : LP P as bs)
    (y : LP R bs cs') (g : FreeMon.Hom cs cs'), zip x (mapR g y) = mapR g (zip x y)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, x, y, g =>
    congrArg₂ cons (comp_mapR_compMk g.1 x.1 y.1).symm (zip_mapR x.2 y.2 g.2)
  | _, _, [], _ :: _, _, _, g => PEmpty.elim g
  | _, _, _ :: _, [], _, _, g => PEmpty.elim g
  | [], _ :: _, _, _, x, _, _ => isEmptyElim x
  | _ :: _, [], _, _, x, _, _ => isEmptyElim x
  | _, [], _, _ :: _, _, y, _ => isEmptyElim y
  | _, _ :: _, _, [], _, y, _ => isEmptyElim y

variable (P R) in
/-- The laxator of the free strict monoidal category monad on profunctors. -/
def lax : Square ((prof P).comp (prof R)) (prof (P.comp R)) (𝟭 (FreeMon C)) (𝟭 (FreeMon E)) where
  app := compLift (fun x y => zip x y) fun x g y => zip_wedge x g y
  natL f q := by
    induction q using comp_induction with
    | h _ x y =>
      simp only [comp_mapL_compMk, prof_mapL]; exact zip_mapL f x y
  natR q g := by
    induction q using comp_induction with
    | h _ x y =>
      simp only [comp_mapR_compMk, prof_mapR]; exact zip_mapR x y g

@[simp] theorem lax_app_compMk {A : FreeMon C} {B : FreeMon D} {E' : FreeMon E}
    (x : (prof P).app A B) (y : (prof R).app B E') :
    (lax P R).app (compMk x y) = zip (P := P) (R := R) x y := rfl

end Zip

section Unit

variable {C : Type u} [SmallCategory C]

/-- A list of morphisms as a list of elements of the hom profunctor. -/
def ofHom : ∀ {as bs : List C}, FreeMon.Hom bs as → LP (Profunctor.id (C := C)) as bs
  | [], [], _ => nil
  | _ :: _, _ :: _, f => cons f.1 (ofHom f.2)
  | [], _ :: _, f => PEmpty.elim f
  | _ :: _, [], f => PEmpty.elim f

theorem ofHom_comp_left : ∀ {as as' bs : List C} (f : FreeMon.Hom bs as)
    (α : FreeMon.Hom as as'), ofHom (FreeMon.Hom.comp f α) = mapL α (ofHom f)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, α => congrArg (cons _) (ofHom_comp_left f.2 α.2)
  | [], _ :: _, _, _, α => PEmpty.elim α
  | _ :: _, [], _, _, α => PEmpty.elim α
  | [], [], _ :: _, f, _ => PEmpty.elim f
  | _ :: _, _ :: _, [], f, _ => PEmpty.elim f

theorem ofHom_comp_right : ∀ {as bs bs' : List C} (α : FreeMon.Hom bs bs')
    (f : FreeMon.Hom bs' as), ofHom (FreeMon.Hom.comp α f) = mapR α (ofHom f)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, α, f => congrArg (cons _) (ofHom_comp_right α.2 f.2)
  | _, [], _ :: _, α, _ => PEmpty.elim α
  | _, _ :: _, [], α, _ => PEmpty.elim α
  | [], _ :: _, _ :: _, _, f => PEmpty.elim f
  | _ :: _, [], [], _, f => PEmpty.elim f

variable (C) in
/-- The unit comparison of the free strict monoidal category monad on profunctors. -/
def unit : Square (Profunctor.id (C := FreeMon C)) (prof (Profunctor.id (C := C)))
    (𝟭 (FreeMon C)) (𝟭 (FreeMon C)) where
  app f := ofHom f
  natL α f := ofHom_comp_left f α
  natR f α := ofHom_comp_right α f

end Unit

section Cells

variable {C D : Type u} [SmallCategory C] [SmallCategory D] {P : Profunctor.{u} C D}

variable (P) in
/-- The unit cells: an element is a singleton list. -/
def ηCell : Square P (prof P) (FreeMon.unit C) (FreeMon.unit D) where
  app x := cons x nil
  natL _ _ := rfl
  natR _ _ := rfl

/-- Concatenation of lists of elements. -/
def append {as' : List C} {bs' : List D} : ∀ {as : List C} {bs : List D},
    LP P as bs → LP P as' bs' → LP P (as ++ as') (bs ++ bs')
  | [], [], _, y => y
  | _ :: _, _ :: _, x, y => cons x.1 (append x.2 y)
  | [], _ :: _, x, _ => isEmptyElim x
  | _ :: _, [], x, _ => isEmptyElim x

theorem append_mapL {A A' : FreeMon C} {bs' : List D} (f' : A ⟶ A') (y : LP P A.as bs') :
    ∀ {B B' : FreeMon C} {bs : List D} (f : B ⟶ B') (x : LP P B.as bs),
    append (mapL f x) (mapL f' y) = mapL (FreeMon.append f f') (append x y)
  | ⟨[]⟩, ⟨[]⟩, [], _, _ => rfl
  | ⟨_ :: _⟩, ⟨_ :: _⟩, _ :: _, f, x => congrArg (cons _) (append_mapL f' y (B := ⟨_⟩)
      (B' := ⟨_⟩) f.2 x.2)
  | ⟨[]⟩, ⟨_ :: _⟩, _, f, _ => PEmpty.elim f
  | ⟨_ :: _⟩, ⟨[]⟩, _, f, _ => PEmpty.elim f
  | ⟨[]⟩, ⟨[]⟩, _ :: _, _, x => isEmptyElim x
  | ⟨_ :: _⟩, ⟨_ :: _⟩, [], _, x => isEmptyElim x

theorem append_mapR {as' : List C} {B B' : FreeMon D} (g' : B ⟶ B') (y : LP P as' B'.as) :
    ∀ {as : List C} {A A' : FreeMon D} (g : A ⟶ A') (x : LP P as A'.as),
    append (mapR g x) (mapR g' y) = mapR (FreeMon.append g g') (append x y)
  | [], ⟨[]⟩, ⟨[]⟩, _, _ => rfl
  | _ :: _, ⟨_ :: _⟩, ⟨_ :: _⟩, g, x => congrArg (cons _) (append_mapR g' y (A := ⟨_⟩)
      (A' := ⟨_⟩) g.2 x.2)
  | _, ⟨[]⟩, ⟨_ :: _⟩, g, _ => PEmpty.elim g
  | _, ⟨_ :: _⟩, ⟨[]⟩, g, _ => PEmpty.elim g
  | _ :: _, ⟨[]⟩, ⟨[]⟩, _, x => isEmptyElim x
  | [], ⟨_ :: _⟩, ⟨_ :: _⟩, _, x => isEmptyElim x

/-- Flatten a list of lists of elements. -/
def flat : ∀ {As : List (FreeMon C)} {Bs : List (FreeMon D)},
    LP (prof P) As Bs → LP P (As.flatMap FreeMon.as) (Bs.flatMap FreeMon.as)
  | [], [], _ => nil
  | _ :: _, _ :: _, x => append x.1 (flat x.2)
  | [], _ :: _, x => isEmptyElim x
  | _ :: _, [], x => isEmptyElim x

theorem flat_mapL : ∀ {As As' : List (FreeMon C)} {Bs : List (FreeMon D)}
    (f : mk As ⟶ mk As') (x : LP (prof P) As Bs),
    flat (mapL f x) = mapL ((FreeMon.flatten C).map f) (flat x)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, x =>
    (congrArg (append _) (flat_mapL f.2 x.2)).trans
      (append_mapL _ _ f.1 x.1)
  | [], _ :: _, _, f, _ => PEmpty.elim f
  | _ :: _, [], _, f, _ => PEmpty.elim f
  | [], [], _ :: _, _, x => isEmptyElim x
  | _ :: _, _ :: _, [], _, x => isEmptyElim x

theorem flat_mapR : ∀ {As : List (FreeMon C)} {Bs Bs' : List (FreeMon D)}
    (x : LP (prof P) As Bs') (g : mk Bs ⟶ mk Bs'),
    flat (mapR g x) = mapR ((FreeMon.flatten D).map g) (flat x)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, x, g =>
    (congrArg (append _) (flat_mapR x.2 g.2)).trans
      (append_mapR _ _ g.1 x.1)
  | _, [], _ :: _, _, g => PEmpty.elim g
  | _, _ :: _, [], _, g => PEmpty.elim g
  | [], _ :: _, _ :: _, x, _ => isEmptyElim x
  | _ :: _, [], [], x, _ => isEmptyElim x

variable (P) in
/-- The multiplication cells: flatten a list of lists. -/
def μCell : Square (prof (prof P)) (prof P) (FreeMon.flatten C) (FreeMon.flatten D) where
  app x := flat x
  natL f x := flat_mapL f x
  natR x g := flat_mapR x g

end Cells


variable {C D E C' D' E' C'' D'' : Type u} [SmallCategory C] [SmallCategory D]
  [SmallCategory E] [SmallCategory C'] [SmallCategory D'] [SmallCategory E']
  [SmallCategory C''] [SmallCategory D'']

theorem map_id_list (as : List C) : as.map (𝟭 C).obj = as := List.map_id' as

theorem smap_id_heq {P : Profunctor.{u} C D} : ∀ {as : List C} {bs : List D} (e : LP P as bs),
    smap (Square.id P) e ≍ e
  | [], [], _ => HEq.rfl
  | _ :: as, _ :: bs, e =>
    cons_heq_cons rfl rfl (map_id_list as) (map_id_list bs) HEq.rfl (smap_id_heq e.2)
  | [], _ :: _, e => isEmptyElim e
  | _ :: _, [], e => isEmptyElim e

theorem smap_vComp_heq {P : Profunctor.{u} C D} {Q : Profunctor.{u} C' D'}
    {R : Profunctor.{u} C'' D''} {F : C ⥤ C'} {G : D ⥤ D'} {F' : C' ⥤ C''} {G' : D' ⥤ D''}
    (s : Square P Q F G) (t : Square Q R F' G') : ∀ {as : List C} {bs : List D} (e : LP P as bs),
    smap (s.vComp t) e ≍ smap t (smap s e)
  | [], [], _ => HEq.rfl
  | _ :: as, _ :: bs, e =>
    cons_heq_cons rfl rfl (List.map_map (g := F'.obj) (f := F.obj) (l := as)).symm
      (List.map_map (g := G'.obj) (f := G.obj) (l := bs)).symm HEq.rfl
      (smap_vComp_heq s t e.2)
  | [], _ :: _, e => isEmptyElim e
  | _ :: _, [], e => isEmptyElim e

theorem zip_smap {P : Profunctor.{u} C D} {Q : Profunctor.{u} D E} {P' : Profunctor.{u} C' D'}
    {Q' : Profunctor.{u} D' E'} {F : C ⥤ C'} {G : D ⥤ D'} {H : E ⥤ E'}
    (s : Square P P' F G) (t : Square Q Q' G H) : ∀ {as : List C} {bs : List D} {cs : List E}
    (x : LP P as bs) (y : LP Q bs cs), zip (smap s x) (smap t y) = smap (s.hcomp t) (zip x y)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, x, y => congrArg (cons _) (zip_smap s t x.2 y.2)
  | [], _ :: _, _, x, _ => isEmptyElim x
  | _ :: _, [], _, x, _ => isEmptyElim x
  | _, [], _ :: _, _, y => isEmptyElim y
  | _, _ :: _, [], _, y => isEmptyElim y

theorem ofHom_map (F : C ⥤ D) : ∀ {as bs : List C} (f : FreeMon.Hom bs as),
    ofHom ((FreeMon.map F).map (X := mk bs) (Y := mk as) f) = smap (Square.homMap F) (ofHom f)
  | [], [], _ => rfl
  | _ :: _, _ :: _, f => congrArg (cons _) (ofHom_map F f.2)
  | [], _ :: _, f => PEmpty.elim f
  | _ :: _, [], f => PEmpty.elim f

theorem zip_assoc_heq {F' : Type u} [SmallCategory F'] {P : Profunctor.{u} C D}
    {Q : Profunctor.{u} D E} {R : Profunctor.{u} E F'} :
    ∀ {as : List C} {bs : List D} {cs : List E} {ds : List F'} (x : LP P as bs) (y : LP Q bs cs)
    (z : LP R cs ds), smap (Square.ofHom (P.associator Q R).hom) (zip (zip x y) z) ≍
      zip x (zip y z)
  | [], [], [], [], _, _, _ => HEq.rfl
  | _ :: as, _ :: _, _ :: _, _ :: ds, x, y, z =>
    cons_heq_cons rfl rfl (map_id_list as) (map_id_list ds) HEq.rfl (zip_assoc_heq x.2 y.2 z.2)
  | [], _ :: _, _, _, x, _, _ => isEmptyElim x
  | _ :: _, [], _, _, x, _, _ => isEmptyElim x
  | _, [], _ :: _, _, _, y, _ => isEmptyElim y
  | _, _ :: _, [], _, _, y, _ => isEmptyElim y
  | _, _, [], _ :: _, _, _, z => isEmptyElim z
  | _, _, _ :: _, [], _, _, z => isEmptyElim z

theorem leftUnitor_heq {P : Profunctor.{u} C D} : ∀ {as bs : List C} {ds : List D}
    (f : FreeMon.Hom bs as) (x : LP P bs ds),
    smap (Square.ofHom P.leftUnitor.hom) (zip (ofHom f) x) ≍ mapL f x
  | [], [], [], _, _ => HEq.rfl
  | _ :: as, _ :: _, _ :: ds, f, x =>
    cons_heq_cons rfl rfl (map_id_list as) (map_id_list ds) HEq.rfl (leftUnitor_heq f.2 x.2)
  | [], _ :: _, _, f, _ => PEmpty.elim f
  | _ :: _, [], _, f, _ => PEmpty.elim f
  | [], [], _ :: _, _, x => isEmptyElim x
  | _ :: _, _ :: _, [], _, x => isEmptyElim x

theorem rightUnitor_heq {P : Profunctor.{u} C D} : ∀ {as : List C} {bs ds : List D}
    (x : LP P as bs) (g : FreeMon.Hom ds bs),
    smap (Square.ofHom P.rightUnitor.hom) (zip x (ofHom g)) ≍ mapR g x
  | [], [], [], _, _ => HEq.rfl
  | _ :: as, _ :: _, _ :: ds, x, g =>
    cons_heq_cons rfl rfl (map_id_list as) (map_id_list ds) HEq.rfl (rightUnitor_heq x.2 g.2)
  | _, [], _ :: _, _, g => PEmpty.elim g
  | _, _ :: _, [], _, g => PEmpty.elim g
  | [], _ :: _, _, x, _ => isEmptyElim x
  | _ :: _, [], _, x, _ => isEmptyElim x

/-! ### Lists -/

theorem flatMap_unit : ∀ as : List C, (as.map (FreeMon.unit C).obj).flatMap FreeMon.as = as
  | [] => rfl
  | a :: as => congrArg (a :: ·) (flatMap_unit as)

theorem flatMap_map_id (As : List (FreeMon C)) :
    (As.map (𝟭 (FreeMon C)).obj).flatMap FreeMon.as = As.flatMap FreeMon.as := by
  rw [map_id_list]

theorem flatMap_flatten : ∀ As : List (FreeMon (FreeMon C)),
    (As.flatMap FreeMon.as).flatMap FreeMon.as =
      (As.map (FreeMon.flatten C).obj).flatMap FreeMon.as
  | [] => rfl
  | _ :: As => (List.flatMap_append ..).trans (congrArg (_ ++ ·) (flatMap_flatten As))

theorem flatMap_map_obj (F : C ⥤ D) : ∀ As : List (FreeMon C),
    (As.map (FreeMon.map F).obj).flatMap FreeMon.as = (As.flatMap FreeMon.as).map F.obj
  | [] => rfl
  | _ :: As => (congrArg (_ ++ ·) (flatMap_map_obj F As)).trans (List.map_append ..).symm

/-! ### Concatenation -/

section Append

variable {P : Profunctor.{u} C D}

theorem append_heq_append {as as₁ cs cs₁ : List C} {bs bs₁ ds ds₁ : List D}
    {x : LP P as bs} {x' : LP P as₁ bs₁} {y : LP P cs ds} {y' : LP P cs₁ ds₁}
    (h₁ : as = as₁) (h₂ : bs = bs₁) (h₃ : cs = cs₁) (h₄ : ds = ds₁) (hx : x ≍ x')
    (hy : y ≍ y') : append x y ≍ append x' y' := by
  subst h₁ h₂ h₃ h₄; cases hx; cases hy; rfl

theorem append_nil_heq : ∀ {as : List C} {bs : List D} (x : LP P as bs),
    append x (nil : LP P [] []) ≍ x
  | [], [], _ => HEq.rfl
  | _ :: as, _ :: bs, x =>
    cons_heq_cons rfl rfl (List.append_nil as) (List.append_nil bs) HEq.rfl (append_nil_heq x.2)
  | [], _ :: _, x => isEmptyElim x
  | _ :: _, [], x => isEmptyElim x

theorem append_assoc_heq {as' as'' : List C} {bs' bs'' : List D} (y : LP P as' bs')
    (z : LP P as'' bs'') : ∀ {as : List C} {bs : List D} (x : LP P as bs),
    append (append x y) z ≍ append x (append y z)
  | [], [], _ => HEq.rfl
  | _ :: as, _ :: bs, x =>
    cons_heq_cons rfl rfl (List.append_assoc as as' as'') (List.append_assoc bs bs' bs'') HEq.rfl
      (append_assoc_heq y z x.2)
  | [], _ :: _, x => isEmptyElim x
  | _ :: _, [], x => isEmptyElim x

theorem smap_append_heq {Q : Profunctor.{u} C' D'} {F : C ⥤ C'} {G : D ⥤ D'}
    (s : Square P Q F G) {as' : List C} {bs' : List D} (y : LP P as' bs') :
    ∀ {as : List C} {bs : List D} (x : LP P as bs),
    smap s (append x y) ≍ append (smap s x) (smap s y)
  | [], [], _ => HEq.rfl
  | _ :: as, _ :: bs, x =>
    cons_heq_cons rfl rfl (List.map_append (l₁ := as)) (List.map_append (l₁ := bs)) HEq.rfl
      (smap_append_heq s y x.2)
  | [], _ :: _, x => isEmptyElim x
  | _ :: _, [], x => isEmptyElim x

theorem flat_append_heq {As' : List (FreeMon C)} {Bs' : List (FreeMon D)}
    (y : LP (prof P) As' Bs') : ∀ {As : List (FreeMon C)} {Bs : List (FreeMon D)}
    (x : LP (prof P) As Bs), flat (append x y) ≍ append (flat x) (flat y)
  | [], [], _ => HEq.rfl
  | _ :: As, _ :: Bs, x =>
    (append_heq_append rfl rfl (List.flatMap_append (xs := As)) (List.flatMap_append (xs := Bs))
      HEq.rfl (flat_append_heq y x.2)).trans (append_assoc_heq _ _ x.1).symm
  | [], _ :: _, x => isEmptyElim x
  | _ :: _, [], x => isEmptyElim x

theorem zip_append {E : Type u} [SmallCategory E] {R : Profunctor.{u} D E} {as' : List C}
    {bs' : List D} {cs' : List E} (x' : LP P as' bs') (y' : LP R bs' cs') :
    ∀ {as : List C} {bs : List D} {cs : List E} (x : LP P as bs) (y : LP R bs cs),
    zip (append x x') (append y y') = append (zip x y) (zip x' y')
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, x, y => congrArg (cons _) (zip_append x' y' x.2 y.2)
  | [], _ :: _, _, x, _ => isEmptyElim x
  | _ :: _, [], _, x, _ => isEmptyElim x
  | _, [], _ :: _, _, y => isEmptyElim y
  | _, _ :: _, [], _, y => isEmptyElim y

end Append

theorem ofHom_append {as' bs' : List C} (g : FreeMon.Hom bs' as') :
    ∀ {as bs : List C} (f : FreeMon.Hom bs as),
    ofHom (FreeMon.append (A := mk bs) (B := mk as) (A' := mk bs') (B' := mk as') f g) =
      append (ofHom f) (ofHom g)
  | [], [], _ => rfl
  | _ :: _, _ :: _, f => congrArg (cons _) (ofHom_append g f.2)
  | [], _ :: _, f => PEmpty.elim f
  | _ :: _, [], f => PEmpty.elim f

/-! ### The laws involving the multiplication -/

theorem flat_smap_heq {P : Profunctor.{u} C D} {Q : Profunctor.{u} C' D'} {F : C ⥤ C'}
    {G : D ⥤ D'} (s : Square P Q F G) : ∀ {As : List (FreeMon C)} {Bs : List (FreeMon D)}
    (x : LP (prof P) As Bs), flat (smap (mapSquare s) x) ≍ smap s (flat x)
  | [], [], _ => HEq.rfl
  | _ :: As, _ :: Bs, x =>
    (append_heq_append rfl rfl (flatMap_map_obj F As) (flatMap_map_obj G Bs) HEq.rfl
      (flat_smap_heq s x.2)).trans (smap_append_heq s _ x.1).symm
  | [], _ :: _, x => isEmptyElim x
  | _ :: _, [], x => isEmptyElim x

theorem zip_flat_heq {P : Profunctor.{u} C D} {Q : Profunctor.{u} D E} :
    ∀ {As : List (FreeMon C)} {Bs : List (FreeMon D)} {Cs : List (FreeMon E)}
    (x : LP (prof P) As Bs) (y : LP (prof Q) Bs Cs),
    zip (flat x) (flat y) ≍ flat (smap (lax P Q) (zip x y))
  | [], [], [], _, _ => HEq.rfl
  | _ :: As, _ :: _, _ :: Cs, x, y =>
    (heq_of_eq (zip_append _ _ x.1 y.1)).trans
      (append_heq_append rfl rfl (flatMap_map_id As).symm (flatMap_map_id Cs).symm HEq.rfl
        (zip_flat_heq x.2 y.2))
  | [], _ :: _, _, x, _ => isEmptyElim x
  | _ :: _, [], _, x, _ => isEmptyElim x
  | _, [], _ :: _, _, y => isEmptyElim y
  | _, _ :: _, [], _, y => isEmptyElim y

theorem ofHom_flatten_heq : ∀ {As Bs : List (FreeMon C)} (f : FreeMon.Hom Bs As),
    ofHom ((FreeMon.flatten C).map (X := mk Bs) (Y := mk As) f) ≍
      flat (smap (unit C) (ofHom (C := FreeMon C) f))
  | [], [], _ => HEq.rfl
  | _ :: As, _ :: Bs, f =>
    (heq_of_eq (ofHom_append _ f.1)).trans
      (append_heq_append rfl rfl (flatMap_map_id As).symm (flatMap_map_id Bs).symm HEq.rfl
        (ofHom_flatten_heq f.2))
  | [], _ :: _, f => PEmpty.elim f
  | _ :: _, [], f => PEmpty.elim f

theorem flat_ηCell_heq {P : Profunctor.{u} C D} : ∀ {as : List C} {bs : List D}
    (x : LP P as bs), flat (smap (ηCell P) x) ≍ x
  | [], [], _ => HEq.rfl
  | _ :: as, _ :: bs, x =>
    cons_heq_cons rfl rfl (flatMap_unit as) (flatMap_unit bs) HEq.rfl (flat_ηCell_heq x.2)
  | [], _ :: _, x => isEmptyElim x
  | _ :: _, [], x => isEmptyElim x

theorem flat_μCell_heq {P : Profunctor.{u} C D} :
    ∀ {As : List (FreeMon (FreeMon C))} {Bs : List (FreeMon (FreeMon D))}
    (x : LP (prof (prof P)) As Bs), flat (smap (μCell P) x) ≍ flat (flat x)
  | [], [], _ => HEq.rfl
  | _ :: As, _ :: Bs, x =>
    (append_heq_append rfl rfl (flatMap_flatten As).symm (flatMap_flatten Bs).symm HEq.rfl
      (flat_μCell_heq x.2)).trans (flat_append_heq _ x.1).symm
  | [], _ :: _, x => isEmptyElim x
  | _ :: _, [], x => isEmptyElim x

end LP

/-- The free strict monoidal category monad, as a lax monad on profunctors. -/
def freeMon : LaxMonad FreeMon.{u} where
  map F := FreeMon.map F
  map_id C _ := FreeMon.map_id C
  map_comp F G := FreeMon.map_comp F G
  η C _ := FreeMon.unit C
  μ C _ := FreeMon.flatten C
  η_naturality F := FreeMon.unit_naturality F
  μ_naturality F := FreeMon.flatten_naturality F
  left_unit C _ := FreeMon.unit_flatten C
  right_unit C _ := FreeMon.map_unit_flatten C
  assoc C _ := FreeMon.map_flatten_flatten C
  mapProf P := LP.prof P
  mapSquare s := LP.mapSquare s
  lax P Q := LP.lax P Q
  unit C _ := LP.unit C
  ηCell P := LP.ηCell P
  μCell P := LP.μCell P
  mapSquare_id P := (Square.eq_cast_iff _ _).2 fun e => LP.smap_id_heq e
  mapSquare_vComp s t := (Square.eq_cast_iff _ _).2 fun e => LP.smap_vComp_heq s t e
  lax_naturality s t := Square.ext fun q => by
    induction q using comp_induction with
    | h _ x y => exact LP.zip_smap s t x y
  unit_naturality F := Square.ext fun f => LP.ofHom_map F f
  lax_assoc P Q R := by
    rw [Square.eq_cast_iff]
    intro _ _ q
    induction q using comp_induction with
    | h _ w z =>
      induction w using comp_induction with
      | h _ x y => exact LP.zip_assoc_heq x y z
  lax_leftUnitor P := by
    rw [Square.eq_cast_iff]
    intro _ _ q
    induction q using comp_induction with
    | h _ f x => exact LP.leftUnitor_heq f x
  lax_rightUnitor P := by
    rw [Square.eq_cast_iff]
    intro _ _ q
    induction q using comp_induction with
    | h _ x g => exact LP.rightUnitor_heq x g
  ηCell_naturality s := (Square.eq_cast_iff _ _).2 fun _ => HEq.rfl
  μCell_naturality s := (Square.eq_cast_iff _ _).2 fun x => LP.flat_smap_heq s x
  ηCell_lax P Q := Square.ext fun q => by
    induction q using comp_induction with
    | h _ x y => rfl
  ηCell_unit C _ := rfl
  μCell_lax P Q := by
    rw [Square.eq_cast_iff]
    intro _ _ q
    induction q using comp_induction with
    | h _ x y => exact LP.zip_flat_heq x y
  μCell_unit C _ := (Square.eq_cast_iff _ _).2 fun f => LP.ofHom_flatten_heq f
  ηCell_μCell P := (Square.eq_cast_iff _ _).2 fun x => LP.append_nil_heq x
  mapSquare_ηCell_μCell P := (Square.eq_cast_iff _ _).2 fun x => LP.flat_ηCell_heq x
  μCell_assoc P := (Square.eq_cast_iff _ _).2 fun x => LP.flat_μCell_heq x

end CategoryTheory.Lax
