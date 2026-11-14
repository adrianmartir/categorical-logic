/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Native.Monad
public import CategoricalLogic.Designs.Shared.ListMonad

/-!
# The free strict monoidal category monad acting on profunctors

For a profunctor `P : C ⇸ D`, the profunctor `T P : FreeMon C ⇸ FreeMon D` has as elements at
lists `cs`, `ds` the lists of elements of `P` matching `cs` and `ds` positionwise
(`FreeMonProf.Elts P cs ds`).

The elementwise layer is defined by recursion on lists, with one-sided actions `mapL`, `mapR`
(the covariant and contravariant actions), from which the profunctor is assembled as a functor
`FreeMon C ⥤ (FreeMon D)ᵒᵖ ⥤ Type u`.
-/

@[expose] public section

namespace CategoryTheory.Native.FreeMonProf

universe u

open Profunctor Opposite TypeCat Limits

set_option backward.isDefEq.respectTransparency false

section Elts

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (P : Profunctor.{u} C D)

/-- The elements of `T P` at lists `cs`, `ds`: elements of `P` matching positionwise. -/
def Elts : List C → List D → Type u
  | [], [] => PUnit
  | c :: cs, d :: ds => (P.obj c).obj (op d) × Elts cs ds
  | [], _ :: _ => PEmpty
  | _ :: _, [] => PEmpty

variable {P}

/-- The empty list of elements. -/
def Elts.nil : Elts P [] [] := PUnit.unit

/-- Prepend an element. -/
def Elts.cons {c : C} {d : D} {cs : List C} {ds : List D} (x : (P.obj c).obj (op d))
    (xs : Elts P cs ds) : Elts P (c :: cs) (d :: ds) := (x, xs)

instance {d : D} {ds : List D} : IsEmpty (Elts P [] (d :: ds)) := ⟨fun x => PEmpty.elim x⟩

instance {c : C} {cs : List C} : IsEmpty (Elts P (c :: cs) []) := ⟨fun x => PEmpty.elim x⟩

variable (P)

/-- The covariant action, positionwise. -/
def mapL : ∀ {cs cs' : List C} {ds : List D}, FreeMon.Hom cs cs' → Elts P cs ds → Elts P cs' ds
  | [], [], [], _, _ => PUnit.unit
  | _ :: _, _ :: _, _ :: _, f, x => ((P.map f.1).app _ x.1, mapL f.2 x.2)
  | [], _ :: _, _, f, _ => PEmpty.elim f
  | _ :: _, [], _, f, _ => PEmpty.elim f
  | [], [], _ :: _, _, x => PEmpty.elim x
  | _ :: _, _ :: _, [], _, x => PEmpty.elim x

/-- The contravariant action, positionwise. -/
def mapR : ∀ {cs : List C} {ds ds' : List D}, FreeMon.Hom ds ds' → Elts P cs ds' → Elts P cs ds
  | [], [], [], _, _ => PUnit.unit
  | _ :: _, _ :: _, _ :: _, g, x => ((P.obj _).map g.1.op x.1, mapR g.2 x.2)
  | _, [], _ :: _, g, _ => PEmpty.elim g
  | _, _ :: _, [], g, _ => PEmpty.elim g
  | _ :: _, [], [], _, x => PEmpty.elim x
  | [], _ :: _, _ :: _, _, x => PEmpty.elim x

theorem mapL_id : ∀ {cs : List C} {ds : List D} (x : Elts P cs ds),
    mapL P (FreeMon.Hom.id cs) x = x
  | [], [], _ => rfl
  | _ :: _, _ :: _, x => Prod.ext (by simp [mapL, FreeMon.Hom.id]) (mapL_id x.2)
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

theorem mapR_id : ∀ {cs : List C} {ds : List D} (x : Elts P cs ds),
    mapR P (FreeMon.Hom.id ds) x = x
  | [], [], _ => rfl
  | _ :: _, _ :: _, x => Prod.ext (by simp [mapR, FreeMon.Hom.id]) (mapR_id x.2)
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

theorem mapL_comp : ∀ {cs cs' cs'' : List C} {ds : List D} (f : FreeMon.Hom cs cs')
    (f' : FreeMon.Hom cs' cs'') (x : Elts P cs ds),
    mapL P (FreeMon.Hom.comp f f') x = mapL P f' (mapL P f x)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, f, f', x =>
    Prod.ext (by simp [FreeMon.Hom.comp, mapL]) (mapL_comp f.2 f'.2 x.2)
  | [], _ :: _, _, _, f, _, _ => PEmpty.elim f
  | _ :: _, [], _, _, f, _, _ => PEmpty.elim f
  | [], [], _ :: _, _, _, f', _ => PEmpty.elim f'
  | _ :: _, _ :: _, [], _, _, f', _ => PEmpty.elim f'
  | [], [], [], _ :: _, _, _, x => PEmpty.elim x
  | _ :: _, _ :: _, _ :: _, [], _, _, x => PEmpty.elim x

theorem mapR_comp : ∀ {cs : List C} {ds ds' ds'' : List D} (g : FreeMon.Hom ds ds')
    (g' : FreeMon.Hom ds' ds'') (x : Elts P cs ds''),
    mapR P (FreeMon.Hom.comp g g') x = mapR P g (mapR P g' x)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, g, g', x =>
    Prod.ext (by simp [FreeMon.Hom.comp, mapR]) (mapR_comp g.2 g'.2 x.2)
  | _, [], _ :: _, _, g, _, _ => PEmpty.elim g
  | _, _ :: _, [], _, g, _, _ => PEmpty.elim g
  | _, [], [], _ :: _, _, g', _ => PEmpty.elim g'
  | _, _ :: _, _ :: _, [], _, g', _ => PEmpty.elim g'
  | _ :: _, [], [], [], _, _, x => PEmpty.elim x
  | [], _ :: _, _ :: _, _ :: _, _, _, x => PEmpty.elim x

theorem mapL_mapR : ∀ {cs cs' : List C} {ds ds' : List D} (f : FreeMon.Hom cs cs')
    (g : FreeMon.Hom ds ds') (x : Elts P cs ds'),
    mapL P f (mapR P g x) = mapR P g (mapL P f x)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, f, g, x =>
    Prod.ext (by simp [mapL, mapR, NatTrans.naturality_apply]) (mapL_mapR f.2 g.2 x.2)
  | [], _ :: _, _, _, f, _, _ => PEmpty.elim f
  | _ :: _, [], _, _, f, _, _ => PEmpty.elim f
  | _, _, [], _ :: _, _, g, _ => PEmpty.elim g
  | _, _, _ :: _, [], _, g, _ => PEmpty.elim g
  | [], [], _ :: _, _ :: _, _, _, x => PEmpty.elim x
  | _ :: _, _ :: _, [], [], _, _, x => PEmpty.elim x

/-- `T P` as a profunctor `FreeMon C ⇸ FreeMon D`. -/
def obj (P : Profunctor.{u} C D) : Profunctor.{u} (FreeMon C) (FreeMon D) where
  obj A :=
    { obj B := Elts P A.as B.unop.as
      map g := ↾mapR P g.unop
      map_id _ := by ext; exact mapR_id P _
      map_comp _ _ := by ext; exact mapR_comp P _ _ _ }
  map f :=
    { app _ := ↾mapL P f
      naturality _ _ g := by ext x; exact mapL_mapR P f g.unop x }
  map_id A := by ext B x; exact mapL_id P x
  map_comp f g := by ext B x; exact mapL_comp P f g x

end Elts

section Map

variable {C D : Type u} [Category.{u} C] [Category.{u} D] {P Q R : Profunctor.{u} C D}

/-- The action of `T` on a morphism of profunctors, positionwise. -/
def hmap (α : P ⟶ Q) : ∀ {cs : List C} {ds : List D}, Elts P cs ds → Elts Q cs ds
  | [], [], _ => PUnit.unit
  | _ :: _, _ :: _, x => ((α.app _).app _ x.1, hmap α x.2)
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

theorem hmap_mapL (α : P ⟶ Q) : ∀ {cs cs' : List C} {ds : List D} (f : FreeMon.Hom cs cs')
    (x : Elts P cs ds), hmap α (mapL P f x) = mapL Q f (hmap α x)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, x =>
    Prod.ext (by
        rw [hmap, mapL, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, α.naturality]
        rfl)
      (hmap_mapL α f.2 x.2)
  | [], _ :: _, _, f, _ => PEmpty.elim f
  | _ :: _, [], _, f, _ => PEmpty.elim f
  | [], [], _ :: _, _, x => PEmpty.elim x
  | _ :: _, _ :: _, [], _, x => PEmpty.elim x

theorem hmap_mapR (α : P ⟶ Q) : ∀ {cs : List C} {ds ds' : List D} (g : FreeMon.Hom ds ds')
    (x : Elts P cs ds'), hmap α (mapR P g x) = mapR Q g (hmap α x)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, g, x =>
    Prod.ext (by simp [hmap, mapR, NatTrans.naturality_apply]) (hmap_mapR α g.2 x.2)
  | _, [], _ :: _, g, _ => PEmpty.elim g
  | _, _ :: _, [], g, _ => PEmpty.elim g
  | _ :: _, [], [], _, x => PEmpty.elim x
  | [], _ :: _, _ :: _, _, x => PEmpty.elim x

theorem hmap_id : ∀ {cs : List C} {ds : List D} (x : Elts P cs ds), hmap (𝟙 P) x = x
  | [], [], _ => rfl
  | _ :: _, _ :: _, x => Prod.ext rfl (hmap_id x.2)
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

theorem hmap_comp (α : P ⟶ Q) (β : Q ⟶ R) : ∀ {cs : List C} {ds : List D} (x : Elts P cs ds),
    hmap (α ≫ β) x = hmap β (hmap α x)
  | [], [], _ => rfl
  | _ :: _, _ :: _, x => Prod.ext rfl (hmap_comp α β x.2)
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

variable (C D) in
/-- The action of `T` on profunctors, as a functor. -/
def mapProf : Profunctor.{u} C D ⥤ Profunctor.{u} (FreeMon C) (FreeMon D) where
  obj := obj
  map α :=
    { app A :=
        { app B := ↾hmap α
          naturality _ _ g := by ext x; exact hmap_mapR α g.unop x }
      naturality _ _ f := by ext _ x; exact hmap_mapL α f x }
  map_id _ := by ext _ _ x; exact hmap_id x
  map_comp _ _ := by ext _ _ x; exact hmap_comp _ _ x

end Map

section Restrict

variable {A B C D : Type u} [Category.{u} A] [Category.{u} B] [Category.{u} C] [Category.{u} D]
  (P : Profunctor.{u} C D) (F : A ⥤ C) (G : B ⥤ D)

/-- `T (P(F, G)) ⟶ (T P)(T F, T G)` on elements: the identity, positionwise. -/
def restr : ∀ {as : List A} {bs : List B},
    Elts (P.whiskerLeft₂ F G) as bs → Elts P (as.map F.obj) (bs.map G.obj)
  | [], [], _ => PUnit.unit
  | _ :: _, _ :: _, x => (x.1, restr x.2)
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

theorem restr_mapL : ∀ {as as' : List A} {bs : List B} (f : FreeMon.Hom as as')
    (x : Elts (P.whiskerLeft₂ F G) as bs),
    restr P F G (mapL _ f x) = mapL P ((FreeMon.map F).map (X := .mk as) (Y := .mk as') f)
      (restr P F G x)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, x => Prod.ext rfl (restr_mapL f.2 x.2)
  | [], _ :: _, _, f, _ => PEmpty.elim f
  | _ :: _, [], _, f, _ => PEmpty.elim f
  | [], [], _ :: _, _, x => PEmpty.elim x
  | _ :: _, _ :: _, [], _, x => PEmpty.elim x

theorem restr_mapR : ∀ {as : List A} {bs bs' : List B} (g : FreeMon.Hom bs bs')
    (x : Elts (P.whiskerLeft₂ F G) as bs'),
    restr P F G (mapR _ g x) = mapR P ((FreeMon.map G).map (X := .mk bs) (Y := .mk bs') g)
      (restr P F G x)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, g, x => Prod.ext rfl (restr_mapR g.2 x.2)
  | _, [], _ :: _, g, _ => PEmpty.elim g
  | _, _ :: _, [], g, _ => PEmpty.elim g
  | _ :: _, [], [], _, x => PEmpty.elim x
  | [], _ :: _, _ :: _, _, x => PEmpty.elim x

variable {P} in
theorem restr_hmap {Q : Profunctor.{u} C D} (α : P ⟶ Q) : ∀ {as : List A} {bs : List B}
    (x : Elts (P.whiskerLeft₂ F G) as bs),
    restr Q F G (hmap ((restrict F G).map α) x) = hmap α (restr P F G x)
  | [], [], _ => rfl
  | _ :: _, _ :: _, x => Prod.ext rfl (restr_hmap α x.2)
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

end Restrict

section Comp

variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E)

/-- Zip two matching lists of elements into a list of elements of the composite. -/
def zip : ∀ {cs : List C} {ds : List D} {es : List E},
    Elts P cs ds → Elts Q ds es → Elts (P.comp Q) cs es
  | [], [], [], _, _ => PUnit.unit
  | c :: _, d :: _, e :: _, x, y =>
    (Quot.mk (Types.coendRel (P.compDiagram Q c e)) ⟨d, (x.1, y.1)⟩, zip x.2 y.2)
  | [], _ :: _, _, x, _ => PEmpty.elim x
  | _ :: _, [], _, x, _ => PEmpty.elim x
  | [], [], _ :: _, _, y => PEmpty.elim y
  | _ :: _, _ :: _, [], _, y => PEmpty.elim y

theorem zip_mapR_mapL : ∀ {cs : List C} {ds ds' : List D} {es : List E}
    (g : FreeMon.Hom ds ds') (x : Elts P cs ds') (y : Elts Q ds es),
    zip P Q (mapR P g x) y = zip P Q x (mapL Q g y)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, g, x, y => by
    refine Prod.ext ?_ (zip_mapR_mapL g.2 x.2 y.2)
    apply Quot.sound
    rw [Types.coendRel_iff]
    exact ⟨g.1, (x.1, y.1), rfl, rfl⟩
  | _, [], _ :: _, _, g, _, _ => PEmpty.elim g
  | _, _ :: _, [], _, g, _, _ => PEmpty.elim g
  | [], _ :: _, _ :: _, _, _, x, _ => PEmpty.elim x
  | _ :: _, [], [], _, _, x, _ => PEmpty.elim x
  | _, [], [], _ :: _, _, _, y => PEmpty.elim y
  | _ :: _, _ :: _, _ :: _, [], _, _, y => PEmpty.elim y

theorem zip_mapL : ∀ {cs cs' : List C} {ds : List D} {es : List E}
    (f : FreeMon.Hom cs cs') (x : Elts P cs ds) (y : Elts Q ds es),
    zip P Q (mapL P f x) y = mapL (P.comp Q) f (zip P Q x y)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, f, x, y =>
    Prod.ext (comp_mapL_mk P Q f.1 _ _ x.1 y.1).symm (zip_mapL f.2 x.2 y.2)
  | [], _ :: _, _, _, f, _, _ => PEmpty.elim f
  | _ :: _, [], _, _, f, _, _ => PEmpty.elim f
  | [], [], _ :: _, _, _, x, _ => PEmpty.elim x
  | _ :: _, _ :: _, [], _, _, x, _ => PEmpty.elim x
  | [], [], [], _ :: _, _, _, y => PEmpty.elim y
  | _ :: _, _ :: _, _ :: _, [], _, _, y => PEmpty.elim y

theorem zip_mapR : ∀ {cs : List C} {ds : List D} {es es' : List E}
    (g : FreeMon.Hom es es') (x : Elts P cs ds) (y : Elts Q ds es'),
    zip P Q x (mapR Q g y) = mapR (P.comp Q) g (zip P Q x y)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, g, x, y =>
    Prod.ext (comp_mapR_mk P Q _ g.1.op _ x.1 y.1).symm (zip_mapR g.2 x.2 y.2)
  | _, _, [], _ :: _, g, _, _ => PEmpty.elim g
  | _, _, _ :: _, [], g, _, _ => PEmpty.elim g
  | [], _ :: _, _, _, _, x, _ => PEmpty.elim x
  | _ :: _, [], _, _, _, x, _ => PEmpty.elim x
  | [], [], _ :: _, _ :: _, _, _, y => PEmpty.elim y
  | _ :: _, _ :: _, [], [], _, _, y => PEmpty.elim y

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The laxator `T P ⊙ T Q ⟶ T (P ⊙ Q)`: zip the two lists. -/
def mapComp : (obj P).comp (obj Q) ⟶ obj (P.comp Q) where
  app A :=
    { app B := ↾Quot.lift (fun ⟨_, x, y⟩ ↦ zip P Q x y) (by
        rintro _ _ ⟨g, x, y⟩
        exact zip_mapR_mapL P Q g x y)
      naturality _ _ g := by
        ext ⟨_, x, y⟩
        exact (congrArg (fun x' ↦ zip P Q x' (mapR Q g.unop y)) (mapL_id P x)).trans
          (zip_mapR P Q g.unop x y) }
  naturality _ _ f := by
    ext _ ⟨_, x, y⟩
    exact (congrArg (fun y' ↦ zip P Q (mapL P f x) y') (mapR_id Q y)).trans
      (zip_mapL P Q f x y)

end Comp

section Id

variable {C : Type u} [Category.{u} C]

/-- A list of morphisms as a list of elements of the identity profunctor. -/
def ofHom : ∀ {cs ds : List C}, FreeMon.Hom ds cs → Elts (Profunctor.id : Profunctor C C) cs ds
  | [], [], _ => PUnit.unit
  | _ :: _, _ :: _, f => (f.1, ofHom f.2)
  | [], _ :: _, f => PEmpty.elim f
  | _ :: _, [], f => PEmpty.elim f

theorem ofHom_comp : ∀ {cs ds es : List C} (f : FreeMon.Hom ds es) (g : FreeMon.Hom es cs),
    ofHom (FreeMon.Hom.comp f g) = mapR _ f (ofHom g)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, g => Prod.ext rfl (ofHom_comp f.2 g.2)
  | _, [], _ :: _, f, _ => PEmpty.elim f
  | _, _ :: _, [], f, _ => PEmpty.elim f
  | [], _ :: _, _ :: _, _, g => PEmpty.elim g
  | _ :: _, [], [], _, g => PEmpty.elim g

theorem comp_ofHom : ∀ {cs ds es : List C} (f : FreeMon.Hom ds cs) (g : FreeMon.Hom cs es),
    ofHom (FreeMon.Hom.comp f g) = mapL _ g (ofHom f)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, g => Prod.ext rfl (comp_ofHom f.2 g.2)
  | [], _ :: _, _, f, _ => PEmpty.elim f
  | _ :: _, [], _, f, _ => PEmpty.elim f
  | [], [], _ :: _, _, g => PEmpty.elim g
  | _ :: _, _ :: _, [], _, g => PEmpty.elim g

/-- The unit comparison `id ⟶ T id`. -/
def mapId : (Profunctor.id : Profunctor (FreeMon C) (FreeMon C)) ⟶ obj Profunctor.id where
  app A :=
    { app B := ↾ofHom
      naturality _ _ g := by ext f; exact ofHom_comp g.unop f }
  naturality _ _ f := by ext _ g; exact comp_ofHom g f

end Id

section Unit

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (P : Profunctor.{u} C D)

/-- The unit at `P`: an element is sent to the singleton list. -/
def ηApp : P ⟶ (obj P).whiskerLeft₂ (FreeMon.unit C) (FreeMon.unit D) where
  app _ :=
    { app _ := ↾fun x ↦ (x, PUnit.unit)
      naturality _ _ _ := by ext; rfl }
  naturality _ _ _ := by ext; rfl

end Unit

section Flatten

variable {C D : Type u} [Category.{u} C] [Category.{u} D] {P Q : Profunctor.{u} C D}

variable (P) in
/-- Concatenation of lists of elements. -/
def append : ∀ {cs : List C} {ds : List D} {cs' : List C} {ds' : List D},
    Elts P cs ds → Elts P cs' ds' → Elts P (cs ++ cs') (ds ++ ds')
  | [], [], _, _, _, y => y
  | _ :: _, _ :: _, _, _, x, y => (x.1, append x.2 y)
  | [], _ :: _, _, _, x, _ => PEmpty.elim x
  | _ :: _, [], _, _, x, _ => PEmpty.elim x

variable (P) in
/-- Flattening a list of lists of elements. -/
def flat : ∀ {As : List (FreeMon C)} {Bs : List (FreeMon D)},
    Elts (obj P) As Bs → Elts P (As.flatMap FreeMon.as) (Bs.flatMap FreeMon.as)
  | [], [], _ => PUnit.unit
  | _ :: _, _ :: _, x => append P x.1 (flat x.2)
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

theorem mapL_append : ∀ {cs₁ cs₂ : List C} {ds : List D} {cs₁' cs₂' : List C} {ds' : List D}
    (f : FreeMon.mk cs₁ ⟶ FreeMon.mk cs₂) (f' : FreeMon.mk cs₁' ⟶ FreeMon.mk cs₂')
    (x : Elts P cs₁ ds) (y : Elts P cs₁' ds'),
    mapL P (FreeMon.append f f') (append P x y) = append P (mapL P f x) (mapL P f' y)
  | [], [], [], _, _, _, _, _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _, _, _, f, f', x, y => Prod.ext rfl (mapL_append f.2 f' x.2 y)
  | [], _ :: _, _, _, _, _, f, _, _, _ => PEmpty.elim f
  | _ :: _, [], _, _, _, _, f, _, _, _ => PEmpty.elim f
  | [], [], _ :: _, _, _, _, _, _, x, _ => PEmpty.elim x
  | _ :: _, _ :: _, [], _, _, _, _, _, x, _ => PEmpty.elim x

theorem mapR_append : ∀ {cs : List C} {ds₁ ds₂ : List D} {cs' : List C} {ds₁' ds₂' : List D}
    (g : FreeMon.mk ds₁ ⟶ FreeMon.mk ds₂) (g' : FreeMon.mk ds₁' ⟶ FreeMon.mk ds₂')
    (x : Elts P cs ds₂) (y : Elts P cs' ds₂'),
    mapR P (FreeMon.append g g') (append P x y) = append P (mapR P g x) (mapR P g' y)
  | [], [], [], _, _, _, _, _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _, _, _, g, g', x, y => Prod.ext rfl (mapR_append g.2 g' x.2 y)
  | _, [], _ :: _, _, _, _, g, _, _, _ => PEmpty.elim g
  | _, _ :: _, [], _, _, _, g, _, _, _ => PEmpty.elim g
  | [], _ :: _, _ :: _, _, _, _, _, _, x, _ => PEmpty.elim x
  | _ :: _, [], [], _, _, _, _, _, x, _ => PEmpty.elim x

theorem mapL_flat : ∀ {As As' : List (FreeMon C)} {Bs : List (FreeMon D)}
    (f : FreeMon.mk As ⟶ FreeMon.mk As') (x : Elts (obj P) As Bs),
    mapL P ((FreeMon.flatten C).map f) (flat P x) = flat P (mapL (obj P) f x)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, x => (mapL_append f.1 _ x.1 _).trans
      (congrArg (append P _) (mapL_flat (As := _) (As' := _) f.2 x.2))
  | [], _ :: _, _, f, _ => PEmpty.elim f
  | _ :: _, [], _, f, _ => PEmpty.elim f
  | [], [], _ :: _, _, x => PEmpty.elim x
  | _ :: _, _ :: _, [], _, x => PEmpty.elim x

theorem mapR_flat : ∀ {As : List (FreeMon C)} {Bs Bs' : List (FreeMon D)}
    (g : FreeMon.mk Bs ⟶ FreeMon.mk Bs') (x : Elts (obj P) As Bs'),
    mapR P ((FreeMon.flatten D).map g) (flat P x) = flat P (mapR (obj P) g x)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, g, x => (mapR_append g.1 _ x.1 _).trans
      (congrArg (append P _) (mapR_flat (Bs := _) (Bs' := _) g.2 x.2))
  | _, [], _ :: _, g, _ => PEmpty.elim g
  | _, _ :: _, [], g, _ => PEmpty.elim g
  | _ :: _, [], [], _, x => PEmpty.elim x
  | [], _ :: _, _ :: _, _, x => PEmpty.elim x

theorem hmap_append (α : P ⟶ Q) : ∀ {cs : List C} {ds : List D} {cs' : List C} {ds' : List D}
    (x : Elts P cs ds) (y : Elts P cs' ds'),
    hmap α (append P x y) = append Q (hmap α x) (hmap α y)
  | [], [], _, _, _, _ => rfl
  | _ :: _, _ :: _, _, _, x, y => Prod.ext rfl (hmap_append α x.2 y)
  | [], _ :: _, _, _, x, _ => PEmpty.elim x
  | _ :: _, [], _, _, x, _ => PEmpty.elim x

theorem hmap_flat (α : P ⟶ Q) : ∀ {As : List (FreeMon C)} {Bs : List (FreeMon D)}
    (x : Elts (obj P) As Bs), hmap α (flat P x) = flat Q (hmap ((mapProf C D).map α) x)
  | [], [], _ => rfl
  | _ :: _, _ :: _, x => (hmap_append α x.1 _).trans (congrArg (append Q _) (hmap_flat α x.2))
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

variable (P) in
/-- The multiplication at `P`: flatten. -/
def μApp : obj (obj P) ⟶ (obj P).whiskerLeft₂ (FreeMon.flatten C) (FreeMon.flatten D) where
  app _ :=
    { app _ := ↾flat P
      naturality _ _ g := by ext x; exact (mapR_flat g.unop x).symm }
  naturality _ _ f := by ext _ x; exact (mapL_flat f x).symm

end Flatten

section Restrict'

variable {A B C D : Type u} [Category.{u} A] [Category.{u} B] [Category.{u} C] [Category.{u} D]

/-- The comparison `T (P(F, G)) ⟶ (T P)(T F, T G)`. -/
def restrNat (P : Profunctor.{u} C D) (F : A ⥤ C) (G : B ⥤ D) :
    obj (P.whiskerLeft₂ F G) ⟶ (obj P).whiskerLeft₂ (FreeMon.map F) (FreeMon.map G) where
  app _ :=
    { app _ := ↾restr P F G
      naturality _ _ g := by ext x; exact restr_mapR P F G g.unop x }
  naturality _ _ f := by ext _ x; exact restr_mapL P F G f x

end Restrict'

/-! ### Elementwise lemmas for the laws -/

theorem prod_mk_heq {α β β' : Type u} (a : α) {b : β} {b' : β'} (h : b ≍ b') :
    (a, b) ≍ (a, b') := by
  obtain rfl := type_eq_of_heq h
  obtain rfl := eq_of_heq h
  rfl

theorem flatMap_flatten_map {C : Type u} (l : List (FreeMon (FreeMon C))) :
    ((l.map FreeMon.as).flatten).flatMap FreeMon.as =
      (l.map fun A ↦ A.as.flatMap FreeMon.as).flatten := by
  induction l <;> simp_all [List.flatMap_append]

section Laws

variable {A B C D E : Type u} [Category.{u} A] [Category.{u} B] [Category.{u} C]
  [Category.{u} D] [Category.{u} E]

theorem append_heq {P : Profunctor.{u} C D} {cs₁ cs₂ cs₁' cs₂' : List C}
    {ds₁ ds₂ ds₁' ds₂' : List D} {x : Elts P cs₁ ds₁} {x' : Elts P cs₂ ds₂}
    {y : Elts P cs₁' ds₁'} {y' : Elts P cs₂' ds₂'} (hc : cs₁ = cs₂) (hd : ds₁ = ds₂)
    (hc' : cs₁' = cs₂') (hd' : ds₁' = ds₂') (hx : x ≍ x') (hy : y ≍ y') :
    append P x y ≍ append P x' y' := by
  subst hc hd hc' hd'
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  rfl

theorem append_nil_heq {P : Profunctor.{u} C D} : ∀ {cs : List C} {ds : List D}
    (x : Elts P cs ds), append P x Elts.nil ≍ x
  | [], [], _ => HEq.rfl
  | _ :: _, _ :: _, x => prod_mk_heq x.1 (append_nil_heq x.2)
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

theorem append_assoc_heq {P : Profunctor.{u} C D} : ∀ {cs : List C} {ds : List D}
    {cs' : List C} {ds' : List D} {cs'' : List C} {ds'' : List D} (x : Elts P cs ds)
    (y : Elts P cs' ds') (z : Elts P cs'' ds''),
    append P (append P x y) z ≍ append P x (append P y z)
  | [], [], _, _, _, _, _, _, _ => HEq.rfl
  | _ :: _, _ :: _, _, _, _, _, x, y, z => prod_mk_heq x.1 (append_assoc_heq x.2 y z)
  | [], _ :: _, _, _, _, _, x, _, _ => PEmpty.elim x
  | _ :: _, [], _, _, _, _, x, _, _ => PEmpty.elim x

theorem flat_append_heq {P : Profunctor.{u} C D} : ∀ {As : List (FreeMon C)}
    {Bs : List (FreeMon D)} {As' : List (FreeMon C)} {Bs' : List (FreeMon D)}
    (x : Elts (obj P) As Bs) (y : Elts (obj P) As' Bs'),
    flat P (append (obj P) x y) ≍ append P (flat P x) (flat P y)
  | [], [], _, _, _, _ => HEq.rfl
  | _ :: _, _ :: _, _, _, x, y =>
    (append_heq rfl rfl (by simp) (by simp) HEq.rfl (flat_append_heq x.2 y)).trans
      (append_assoc_heq _ _ _).symm
  | [], _ :: _, _, _, x, _ => PEmpty.elim x
  | _ :: _, [], _, _, x, _ => PEmpty.elim x

theorem restr_id_heq (P : Profunctor.{u} C D) : ∀ {cs : List C} {ds : List D}
    (x : Elts (P.whiskerLeft₂ (𝟭 C) (𝟭 D)) cs ds), restr P (𝟭 C) (𝟭 D) x ≍ x
  | [], [], _ => HEq.rfl
  | _ :: _, _ :: _, x => prod_mk_heq x.1 (restr_id_heq P x.2)
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

theorem restr_comp_heq {A' B' : Type u} [Category.{u} A'] [Category.{u} B']
    (P : Profunctor.{u} C D) (F : A ⥤ C) (G : B ⥤ D) (F' : A' ⥤ A) (G' : B' ⥤ B) :
    ∀ {as : List A'} {bs : List B'} (x : Elts (P.whiskerLeft₂ (F' ⋙ F) (G' ⋙ G)) as bs),
    restr P (F' ⋙ F) (G' ⋙ G) x ≍ restr P F G (restr (P.whiskerLeft₂ F G) F' G' x)
  | [], [], _ => HEq.rfl
  | _ :: _, _ :: _, x => prod_mk_heq x.1 (restr_comp_heq P F G F' G' x.2)
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

theorem restr_append_heq (P : Profunctor.{u} C D) (F : A ⥤ C) (G : B ⥤ D) :
    ∀ {as : List A} {bs : List B} {as' : List A} {bs' : List B}
    (x : Elts (P.whiskerLeft₂ F G) as bs) (y : Elts (P.whiskerLeft₂ F G) as' bs'),
    restr P F G (append _ x y) ≍ append P (restr P F G x) (restr P F G y)
  | [], [], _, _, _, _ => HEq.rfl
  | _ :: _, _ :: _, _, _, x, y => prod_mk_heq x.1 (restr_append_heq P F G x.2 y)
  | [], _ :: _, _, _, x, _ => PEmpty.elim x
  | _ :: _, [], _, _, x, _ => PEmpty.elim x

theorem restr_flat_heq (P : Profunctor.{u} C D) (F : A ⥤ C) (G : B ⥤ D) :
    ∀ {As : List (FreeMon A)} {Bs : List (FreeMon B)} (x : Elts (obj (P.whiskerLeft₂ F G)) As Bs),
    restr P F G (flat _ x) ≍
      flat P (restr (obj P) (FreeMon.map F) (FreeMon.map G) (hmap (restrNat P F G) x))
  | [], [], _ => HEq.rfl
  | _ :: _, _ :: _, x =>
    (restr_append_heq P F G x.1 _).trans
      (append_heq rfl rfl (by simp [Function.comp_def, FreeMon.map_obj])
        (by simp [Function.comp_def, FreeMon.map_obj]) HEq.rfl
        (restr_flat_heq P F G x.2))
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

theorem flat_η_heq (P : Profunctor.{u} C D) : ∀ {cs : FreeMon C} {ds : FreeMon D}
    (x : Elts P cs.as ds.as), flat P (Bs := [ds]) (As := [cs]) (x, PUnit.unit) ≍ x :=
  fun x ↦ append_nil_heq x

theorem flat_restr_hmap_η_heq (P : Profunctor.{u} C D) : ∀ {cs : List C} {ds : List D}
    (x : Elts P cs ds),
    flat P (restr (obj P) (FreeMon.unit C) (FreeMon.unit D) (hmap (ηApp P) x)) ≍ x
  | [], [], _ => HEq.rfl
  | _ :: _, _ :: _, x => prod_mk_heq x.1 (flat_restr_hmap_η_heq P x.2)
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

theorem flat_flat_heq (P : Profunctor.{u} C D) : ∀ {As : List (FreeMon (FreeMon C))}
    {Bs : List (FreeMon (FreeMon D))} (x : Elts (obj (obj P)) As Bs),
    flat P (flat (obj P) x) ≍
      flat P (restr (obj P) (FreeMon.flatten C) (FreeMon.flatten D) (hmap (μApp P) x))
  | [], [], _ => HEq.rfl
  | _ :: _, _ :: _, x =>
    (flat_append_heq x.1 _).trans
      (append_heq rfl rfl (by simp [Function.comp_def, FreeMon.flatten_obj, flatMap_flatten_map])
        (by simp [Function.comp_def, FreeMon.flatten_obj, flatMap_flatten_map]) HEq.rfl
        (flat_flat_heq P x.2))
  | [], _ :: _, x => PEmpty.elim x
  | _ :: _, [], x => PEmpty.elim x

theorem zip_hmap_right (P : Profunctor.{u} C D) {Q Q' : Profunctor.{u} D E} (g : Q ⟶ Q') :
    ∀ {cs : List C} {ds : List D} {es : List E} (x : Elts P cs ds) (y : Elts Q ds es),
    zip P Q' x (hmap g y) = hmap (P.whiskerLeft g) (zip P Q x y)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, x, y => Prod.ext rfl (zip_hmap_right P g x.2 y.2)
  | [], _ :: _, _, x, _ => PEmpty.elim x
  | _ :: _, [], _, x, _ => PEmpty.elim x
  | [], [], _ :: _, _, y => PEmpty.elim y
  | _ :: _, _ :: _, [], _, y => PEmpty.elim y

theorem zip_hmap_left {P P' : Profunctor.{u} C D} (f : P ⟶ P') (Q : Profunctor.{u} D E) :
    ∀ {cs : List C} {ds : List D} {es : List E} (x : Elts P cs ds) (y : Elts Q ds es),
    zip P' Q (hmap f x) y = hmap (Profunctor.whiskerRight Q f) (zip P Q x y)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, x, y => Prod.ext rfl (zip_hmap_left f Q x.2 y.2)
  | [], _ :: _, _, x, _ => PEmpty.elim x
  | _ :: _, [], _, x, _ => PEmpty.elim x
  | [], [], _ :: _, _, y => PEmpty.elim y
  | _ :: _, _ :: _, [], _, y => PEmpty.elim y

theorem zip_compRestrict {A₀ B₀ E₀ : Type u} [Category.{u} A₀] [Category.{u} B₀]
    [Category.{u} E₀] (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) (F : A₀ ⥤ C)
    (K : B₀ ⥤ D) (G : E₀ ⥤ E) :
    ∀ {as : List A₀} {bs : List B₀} {es : List E₀} (x : Elts (P.whiskerLeft₂ F K) as bs)
    (y : Elts (Q.whiskerLeft₂ K G) bs es),
    restr (P.comp Q) F G (hmap (compRestrict P Q F K G) (zip _ _ x y)) =
      zip P Q (restr P F K x) (restr Q K G y)
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, x, y => Prod.ext rfl (zip_compRestrict P Q F K G x.2 y.2)
  | [], _ :: _, _, x, _ => PEmpty.elim x
  | _ :: _, [], _, x, _ => PEmpty.elim x
  | [], [], _ :: _, _, y => PEmpty.elim y
  | _ :: _, _ :: _, [], _, y => PEmpty.elim y

theorem zip_assoc {E' : Type u} [Category.{u} E'] (P : Profunctor.{u} C D)
    (Q : Profunctor.{u} D E) (R : Profunctor.{u} E E') :
    ∀ {cs : List C} {ds : List D} {es : List E} {es' : List E'} (x : Elts P cs ds)
    (y : Elts Q ds es) (z : Elts R es es'),
    hmap (associator P Q R).hom (zip _ R (zip P Q x y) z) = zip P _ x (zip Q R y z)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, x, y, z => Prod.ext rfl (zip_assoc P Q R x.2 y.2 z.2)
  | [], _ :: _, _, _, x, _, _ => PEmpty.elim x
  | _ :: _, [], _, _, x, _, _ => PEmpty.elim x
  | [], [], _ :: _, _, _, y, _ => PEmpty.elim y
  | _ :: _, _ :: _, [], _, _, y, _ => PEmpty.elim y
  | [], [], [], _ :: _, _, _, z => PEmpty.elim z
  | _ :: _, _ :: _, _ :: _, [], _, _, z => PEmpty.elim z

theorem zip_ofHom_left (P : Profunctor.{u} C D) :
    ∀ {cs ds : List C} {es : List D} (f : FreeMon.Hom ds cs) (x : Elts P ds es),
    hmap (leftUnitor P).hom (zip _ P (ofHom f) x) = mapL P f x
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, f, x => Prod.ext rfl (zip_ofHom_left P f.2 x.2)
  | [], _ :: _, _, f, _ => PEmpty.elim f
  | _ :: _, [], _, f, _ => PEmpty.elim f
  | [], [], _ :: _, _, x => PEmpty.elim x
  | _ :: _, _ :: _, [], _, x => PEmpty.elim x

theorem zip_ofHom_right (P : Profunctor.{u} C D) :
    ∀ {cs : List C} {ds es : List D} (x : Elts P cs ds) (g : FreeMon.Hom es ds),
    hmap (rightUnitor P).hom (zip P _ x (ofHom g)) = mapR P g x
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, x, g => Prod.ext rfl (zip_ofHom_right P x.2 g.2)
  | [], _ :: _, _, x, _ => PEmpty.elim x
  | _ :: _, [], _, x, _ => PEmpty.elim x
  | _, [], _ :: _, _, g => PEmpty.elim g
  | _, _ :: _, [], _, g => PEmpty.elim g

theorem ofHom_idRestrict (K : A ⥤ C) : ∀ {as bs : List A} (f : FreeMon.Hom bs as),
    restr _ K K (hmap (idRestrict K) (ofHom f)) =
      ofHom ((FreeMon.map K).map (X := .mk bs) (Y := .mk as) f)
  | [], [], _ => rfl
  | _ :: _, _ :: _, f => Prod.ext rfl (ofHom_idRestrict K f.2)
  | [], _ :: _, f => PEmpty.elim f
  | _ :: _, [], f => PEmpty.elim f

theorem zip_append (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) :
    ∀ {cs : List C} {ds : List D} {es : List E} {cs' : List C} {ds' : List D} {es' : List E}
    (x : Elts P cs ds) (y : Elts Q ds es) (x' : Elts P cs' ds') (y' : Elts Q ds' es'),
    zip P Q (append P x x') (append Q y y') = append _ (zip P Q x y) (zip P Q x' y')
  | [], [], [], _, _, _, _, _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _, _, _, x, y, x', y' =>
    Prod.ext rfl (zip_append P Q x.2 y.2 x' y')
  | [], _ :: _, _, _, _, _, x, _, _, _ => PEmpty.elim x
  | _ :: _, [], _, _, _, _, x, _, _, _ => PEmpty.elim x
  | [], [], _ :: _, _, _, _, _, y, _, _ => PEmpty.elim y
  | _ :: _, _ :: _, [], _, _, _, _, y, _, _ => PEmpty.elim y

theorem zip_flat (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) :
    ∀ {As : List (FreeMon C)} {Bs : List (FreeMon D)} {Cs : List (FreeMon E)}
    (x : Elts (obj P) As Bs) (y : Elts (obj Q) Bs Cs),
    zip P Q (flat P x) (flat Q y) = flat _ (hmap (mapComp P Q) (zip _ _ x y))
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, x, y =>
    (zip_append P Q x.1 y.1 _ _).trans
      (congrArg (append (P.comp Q) (zip P Q x.1 y.1)) (zip_flat P Q x.2 y.2))
  | [], _ :: _, _, x, _ => PEmpty.elim x
  | _ :: _, [], _, x, _ => PEmpty.elim x
  | [], [], _ :: _, _, y => PEmpty.elim y
  | _ :: _, _ :: _, [], _, y => PEmpty.elim y

theorem ofHom_append : ∀ {cs ds cs' ds' : List C} (f : FreeMon.mk ds ⟶ FreeMon.mk cs)
    (f' : FreeMon.mk ds' ⟶ FreeMon.mk cs'),
    ofHom (FreeMon.append f f') = append _ (ofHom f) (ofHom f')
  | [], [], _, _, _, _ => rfl
  | _ :: _, _ :: _, _, _, f, f' => Prod.ext rfl (ofHom_append f.2 f')
  | [], _ :: _, _, _, f, _ => PEmpty.elim f
  | _ :: _, [], _, _, f, _ => PEmpty.elim f

theorem ofHom_flatten : ∀ {As Bs : List (FreeMon C)} (f : FreeMon.mk Bs ⟶ FreeMon.mk As),
    ofHom ((FreeMon.flatten C).map f) = flat _ (hmap mapId (ofHom f))
  | [], [], _ => rfl
  | _ :: _, _ :: _, f =>
    (ofHom_append f.1 _).trans (congrArg (append _ _) (ofHom_flatten (As := _) (Bs := _) f.2))
  | [], _ :: _, f => PEmpty.elim f
  | _ :: _, [], f => PEmpty.elim f

end Laws

/-- The free strict monoidal category monad acts on profunctors. -/
instance : ProfMonad Cat.freeMon.{u, u} where
  mapProf {C D} := mapProf C D
  mapRestrict F G :=
    { app P := restrNat P F.toFunctor G.toFunctor
      naturality _ _ α := by ext _ _ x; exact restr_hmap _ _ α x }
  mapComp P Q := mapComp P Q
  mapId _ := mapId
  η :=
    { app P := ηApp P
      naturality _ _ _ := by ext; rfl }
  μ :=
    { app P := μApp P
      naturality _ _ α := by ext _ _ x; exact (hmap_flat α x).symm }
  mapRestrict_id _ _ P := by
    ext A B x
    exact eq_of_heq ((restr_id_heq P x).trans (eqToHom_app_app_heq _ _ _ _).symm)
  mapRestrict_comp F' G' F G P := by
    -- TODO: `restr_comp_heq` closes it elementwise; the `eqToHom` component did not unify.
    sorry
  mapComp_whiskerLeft P _ _ g := by
    ext A B ⟨_, x, y⟩
    exact zip_hmap_right P g x y
  mapComp_whiskerRight f Q := by
    ext A B ⟨_, x, y⟩
    exact zip_hmap_left f Q x y
  mapComp_compRestrict P Q _ _ _ := by
    ext A B ⟨_, x, y⟩
    exact zip_compRestrict P Q _ _ _ x y
  mapComp_assoc P Q R := by
    ext A B ⟨_, ⟨_, x, y⟩, z⟩
    exact zip_assoc P Q R x y z
  mapComp_leftUnitor P := by
    ext A B ⟨_, f, x⟩
    exact zip_ofHom_left P f x
  mapComp_rightUnitor P := by
    ext A B ⟨_, x, g⟩
    exact zip_ofHom_right P x g
  mapId_idRestrict K := by
    ext A B f
    exact ofHom_idRestrict K.toFunctor f
  η_restrict _ _ _ := by
    ext
    rfl
  η_comp _ _ := by
    ext _ _ ⟨_, _, _⟩
    rfl
  η_id _ := by
    ext
    rfl
  μ_restrict _ _ P := by
    ext A B x
    exact eq_of_heq ((eqToHom_app_app_heq _ _ _ _).trans (restr_flat_heq P _ _ x))
  μ_comp P Q := by
    ext A B ⟨_, x, y⟩
    exact zip_flat P Q x y
  μ_id _ := by
    ext A B f
    exact ofHom_flatten f
  left_unit P := by
    ext A B x
    exact eq_of_heq ((eqToHom_app_app_heq _ _ _ _).trans (append_nil_heq x))
  right_unit P := by
    ext A B x
    exact eq_of_heq ((eqToHom_app_app_heq _ _ _ _).trans (flat_restr_hmap_η_heq P x))
  assoc {C D} P := by
    ext A B x
    exact eq_of_heq ((eqToHom_app_app_heq _ _ _ _).trans (flat_flat_heq P x))

end CategoryTheory.Native.FreeMonProf
