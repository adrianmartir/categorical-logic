/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/
import Mathlib

/-!
# The Bicategory of Spans

Given a category C with pullbacks, we construct the bicategory Span(C) of spans in C.

## Main definitions

* `CategoryTheory.WithPullbacks` — A class that provides a chosen pullback for every cospan.
* `CategoryTheory.SpanCat` — The type of objects in the span bicategory (wraps objects of C).
* `CategoryTheory.Span` — A span from c to d: an object e with arrows e ⟶ c and e ⟶ d.
* `CategoryTheory.SpanHom` — A 2-cell between spans: a morphism between the apices
  compatible with the legs.
* `CategoryTheory.SpanCat.instBicategory` — The bicategory instance on `SpanCat C`.

## Construction

* Objects are objects of C.
* 1-cells from c to d are spans (e, f : e ⟶ c, g : e ⟶ d).
* 2-cells from (e, f, g) to (e', f', g') are morphisms h : e ⟶ e' such that f' ∘ h = f
  and g' ∘ h = g.
* Composition of spans uses pullbacks.
* The identity span on c is (c, 𝟙 c, 𝟙 c).
-/

namespace CategoryTheory

open Limits

universe v u

variable (C : Type u) [Category.{v} C]

/-! ## WithPullbacks class -/

/-- A class providing chosen pullbacks for every cospan in C. -/
class WithPullbacks where
  /-- The chosen pullback cone for arrows `f : X ⟶ Z` and `g : Y ⟶ Z`. -/
  pullbackCone : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), PullbackCone f g
  /-- The chosen pullback cone is a limit. -/
  isLimit : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), IsLimit (pullbackCone f g)

variable {C}

namespace WithPullbacks

variable [WithPullbacks C]

/-- The pullback object for a cospan `f : X ⟶ Z` and `g : Y ⟶ Z`. -/
def pb {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : C :=
  (pullbackCone f g).pt

/-- The first projection from the pullback. -/
def pbFst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : pb f g ⟶ X :=
  (pullbackCone f g).fst

/-- The second projection from the pullback. -/
def pbSnd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : pb f g ⟶ Y :=
  (pullbackCone f g).snd

/-- The pullback condition. -/
theorem pbCond {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    pbFst f g ≫ f = pbSnd f g ≫ g :=
  (pullbackCone f g).condition

/-- The universal property lift. -/
def pbLift {X Y Z W : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    (p : W ⟶ X) (q : W ⟶ Y) (h : p ≫ f = q ≫ g) : W ⟶ pb f g :=
  (isLimit f g).lift (PullbackCone.mk p q h)

@[reassoc (attr := simp)]
theorem pbLift_fst {X Y Z W : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    (p : W ⟶ X) (q : W ⟶ Y) (h : p ≫ f = q ≫ g) :
    pbLift f g p q h ≫ pbFst f g = p :=
  (isLimit f g).fac (PullbackCone.mk p q h) WalkingCospan.left

@[reassoc (attr := simp)]
theorem pbLift_snd {X Y Z W : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    (p : W ⟶ X) (q : W ⟶ Y) (h : p ≫ f = q ≫ g) :
    pbLift f g p q h ≫ pbSnd f g = q :=
  (isLimit f g).fac (PullbackCone.mk p q h) WalkingCospan.right

/-- Two morphisms into a pullback are equal if they agree on both projections. -/
theorem pb_hom_ext {X Y Z W : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    {k l : W ⟶ pb f g}
    (h1 : k ≫ pbFst f g = l ≫ pbFst f g)
    (h2 : k ≫ pbSnd f g = l ≫ pbSnd f g) : k = l :=
  PullbackCone.IsLimit.hom_ext (isLimit f g) h1 h2

end WithPullbacks

/-! ## Spans and 2-cells -/

variable [WithPullbacks C]

/-- A span from `c` to `d`. -/
structure Span (c d : C) where
  apex : C
  left : apex ⟶ c
  right : apex ⟶ d

/-- A 2-cell between spans. -/
@[ext]
structure SpanHom {c d : C} (s t : Span c d) where
  hom : s.apex ⟶ t.apex
  left_comm : hom ≫ t.left = s.left
  right_comm : hom ≫ t.right = s.right

attribute [reassoc (attr := simp)] SpanHom.left_comm SpanHom.right_comm

/-- Category instance on spans between fixed endpoints. -/
instance spanHomCategory (c d : C) : Category (Span c d) where
  Hom := SpanHom
  id s := ⟨𝟙 s.apex, Category.id_comp _, Category.id_comp _⟩
  comp α β := ⟨α.hom ≫ β.hom,
    by rw [Category.assoc, β.left_comm, α.left_comm],
    by rw [Category.assoc, β.right_comm, α.right_comm]⟩
  id_comp f := SpanHom.ext (Category.id_comp _)
  comp_id f := SpanHom.ext (Category.comp_id _)
  assoc f g h := SpanHom.ext (Category.assoc _ _ _)

omit [WithPullbacks C] in
@[simp]
lemma SpanHom_id_hom {c d : C} (s : Span c d) :
    (𝟙 s : s ⟶ s).hom = 𝟙 s.apex := rfl

omit [WithPullbacks C] in
@[simp]
lemma SpanHom_comp_hom {c d : C} {s t u : Span c d}
    (α : s ⟶ t) (β : t ⟶ u) : (α ≫ β).hom = α.hom ≫ β.hom := rfl

/-! ## Composition and identity spans -/

open WithPullbacks

/-- Compose two spans using the pullback. -/
def Span.comp {a b c : C} (s : Span a b) (t : Span b c) :
    Span a c where
  apex := pb s.right t.left
  left := pbFst s.right t.left ≫ s.left
  right := pbSnd s.right t.left ≫ t.right

/-- The identity span. -/
def Span.idSpan (c : C) : Span c c where
  apex := c
  left := 𝟙 c
  right := 𝟙 c

/-! ## Whiskering -/

/-
Given a span s and a 2-cell α between spans, compose s with α.
-/
def spanWhiskerLeft {a b c : C} (s : Span a b)
    {t₁ t₂ : Span b c} (α : t₁ ⟶ t₂) :
    s.comp t₁ ⟶ s.comp t₂ :=
  ⟨pbLift s.right t₂.left
    (pbFst s.right t₁.left)
    (pbSnd s.right t₁.left ≫ α.hom)
    (by rw [Category.assoc, α.left_comm]; exact pbCond s.right t₁.left),
   by

     simp [Span.comp], by
       simp [Span.comp]⟩

/-
Right whiskering: given a 2-cell α and a span t, compose α with t.
-/
def spanWhiskerRight {a b c : C}
    {s₁ s₂ : Span a b} (α : s₁ ⟶ s₂) (t : Span b c) :
    s₁.comp t ⟶ s₂.comp t :=
  ⟨pbLift s₂.right t.left
    (pbFst s₁.right t.left ≫ α.hom)
    (pbSnd s₁.right t.left)
    (by rw [Category.assoc, α.right_comm]; exact pbCond s₁.right t.left),
   by
     unfold Span.comp; simp +decide [ Category.assoc ] ;, by
       simp +decide [ Span.comp ]⟩

/-! ## Unitors -/

/-
The left unitor: `idSpan a ⬝ s ≅ s`.
-/
def spanLeftUnitor {a b : C} (s : Span a b) :
    (Span.idSpan a).comp s ≅ s where
  hom := ⟨pbSnd (𝟙 a) s.left, by
    have := @WithPullbacks.pbCond C ‹_› ‹_›;
    convert this ( 𝟙 a ) s.left |> Eq.symm using 1, rfl⟩
  inv := ⟨pbLift (𝟙 a) s.left s.left (𝟙 s.apex) (by simp [Span.idSpan]),
    by

      simp [Span.comp, Span.idSpan] at *, by
        unfold Span.comp; simp +decide [ pbLift_snd, Category.assoc ] ;
        simp +decide [ pbLift_snd, Span.idSpan ]⟩
  hom_inv_id := by
    apply SpanHom.ext
    generalize_proofs at *;
    rename_i h₁ h₂ h₃ h₄ h₅;
    rename_i h₆;
    cases h₆;
    simp +decide [ Span.comp, Span.idSpan ];
    rename_i h₆ h₇;
    apply (h₇ _ _).hom_ext;
    intro j; fin_cases j <;> simp +decide [ ← Category.assoc, h₄, h₅ ] ;
    · grind +locals;
    · grind +locals;
    · simp +decide [ Category.assoc, pbSnd, pbLift ]
  inv_hom_id := by
    apply SpanHom.ext;
    simp +zetaDelta at *

/-
The right unitor: `s ⬝ idSpan b ≅ s`.
-/
def spanRightUnitor {a b : C} (s : Span a b) :
    s.comp (Span.idSpan b) ≅ s where
  hom := ⟨pbFst s.right (𝟙 b), rfl, by
    unfold Span.comp; simp +decide [ pbCond ] ;
    exact Eq.symm ( Category.comp_id _ )⟩
  inv := ⟨pbLift s.right (𝟙 b) (𝟙 s.apex) s.right (by simp [Span.idSpan]),
    by
      unfold Span.comp Span.idSpan; simp +decide [ pbLift_fst, pbLift_snd, Category.assoc ] ;, by
        unfold Span.comp Span.idSpan; simp +decide [ pbLift_snd, Category.assoc ] ;⟩
  hom_inv_id := by
    generalize_proofs at *;
    rename_i h₁ h₂ h₃ h₄ h₅;
    apply SpanHom.ext;
    have := @WithPullbacks.pb_hom_ext C ‹_› ‹_›;
    apply this;
    · simp +decide [ Span.comp, Span.idSpan ];
    · simp +decide [ Span.comp, Span.idSpan ];
      simp +decide [ Span.comp, Span.idSpan ] at h₂ ⊢;
      exact h₂
  inv_hom_id := by
    apply SpanHom.ext;
    simp +zetaDelta at *

/-! ## Associator -/

/-
Forward direction of the associator.
-/
def spanAssociatorHom {a b c d : C}
    (s : Span a b) (t : Span b c) (u : Span c d) :
    (s.comp t).comp u ⟶ s.comp (t.comp u) :=
  ⟨pbLift s.right (t.comp u).left
    (pbFst (s.comp t).right u.left ≫ pbFst s.right t.left)
    (pbLift t.right u.left
      (pbFst (s.comp t).right u.left ≫ pbSnd s.right t.left)
      (pbSnd (s.comp t).right u.left)
      (by
      have := @WithPullbacks.pbCond C ‹_› ‹_›;
      rw [ ← this, Category.assoc ];
      exact rfl =≫ pbSnd s.right t.left ≫ t.right))
    (by
    simp +decide [ ← Category.assoc, pbLift_fst, Span.comp ];
    simp +decide [ Category.assoc, pbCond ]),
   by
     simp +decide [ Span.comp, Category.assoc ] at *, by
       simp +decide [ Span.comp, Category.assoc, pbLift_snd ]⟩

/-
Inverse direction of the associator.
-/
def spanAssociatorInv {a b c d : C}
    (s : Span a b) (t : Span b c) (u : Span c d) :
    s.comp (t.comp u) ⟶ (s.comp t).comp u :=
  ⟨pbLift (s.comp t).right u.left
    (pbLift s.right t.left
      (pbFst s.right (t.comp u).left)
      (pbSnd s.right (t.comp u).left ≫ pbFst t.right u.left)
      (by
      have := @WithPullbacks.pbCond C ‹_› ‹_›; aesop;))
    (pbSnd s.right (t.comp u).left ≫ pbSnd t.right u.left)
    (by
    have := @WithPullbacks.pbCond C ‹_› ‹_›;
    simp_all +decide [ Category.assoc, Span.comp ] ;),
   by
     simp +decide [ Span.comp, Category.assoc, pbLift_fst, pbLift_snd ] at *, by
       simp +decide [ Span.comp, Category.assoc ]⟩

/-
The associator isomorphism.
-/
def spanAssociator {a b c d : C}
    (s : Span a b) (t : Span b c) (u : Span c d) :
    (s.comp t).comp u ≅ s.comp (t.comp u) where
  hom := spanAssociatorHom s t u
  inv := spanAssociatorInv s t u
  hom_inv_id := by
    have := @WithPullbacks.pb_hom_ext C ‹_› ‹_›;
    apply_rules [ SpanHom.ext ];
    any_goals apply this;
    all_goals simp +decide [ SpanHom.ext_iff, Span.comp ];
    all_goals unfold spanAssociatorHom spanAssociatorInv; simp +decide [ Span.comp ] ;
  inv_hom_id := by
    apply SpanHom.ext;
    rename_i h₁ h₂;
    apply h₂.pb_hom_ext;
    · simp +decide [ spanAssociatorInv, spanAssociatorHom ];
    · apply h₂.pb_hom_ext;
      · simp +decide [ Category.assoc, spanAssociatorInv, spanAssociatorHom ];
      · simp +decide [ spanAssociatorInv, spanAssociatorHom ]

/-! ## SpanCat and Bicategory instance -/

/-- The type of objects in the span bicategory. -/
structure SpanCat (C : Type u) [Category.{v} C] [WithPullbacks C] where
  obj : C

instance SpanCat.instCategoryStruct : CategoryStruct (SpanCat C) where
  Hom a b := Span (C := C) a.obj b.obj
  id a := Span.idSpan a.obj
  comp s t := s.comp t

instance SpanCat.instHomCategory (a b : SpanCat C) : Category (a ⟶ b) :=
  spanHomCategory a.obj b.obj

/-
Coherence lemmas
-/
lemma spanWhiskerLeft_id {a b c : C} (s : Span a b) (t : Span b c) :
    spanWhiskerLeft s (𝟙 t) = 𝟙 (s.comp t) := by
      unfold spanWhiskerLeft;
      apply_rules [ SpanHom.ext ];
      have := @WithPullbacks.pb_hom_ext C ‹_› ‹_›;
      apply_rules [ SpanHom.ext ];
      all_goals simp +decide [SpanHom.ext_iff, Span.comp, Span.idSpan,
        CategoryTheory.CategoryStruct.id] ;

lemma spanWhiskerLeft_comp {a b c : C} (s : Span a b)
    {t₁ t₂ t₃ : Span b c} (α : t₁ ⟶ t₂) (β : t₂ ⟶ t₃) :
    spanWhiskerLeft s (α ≫ β) = spanWhiskerLeft s α ≫ spanWhiskerLeft s β := by
      unfold spanWhiskerLeft;
      have := @WithPullbacks.pb_hom_ext C ‹_› ‹_›;
      apply_rules [ SpanHom.ext, this ] ; simp +decide [ SpanHom_comp_hom ] ;
      all_goals repeat' erw [ Category.assoc ] ; repeat' erw [ pbLift_snd ];
      all_goals simp +decide [ pbLift_fst, pbLift_snd, SpanHom_comp_hom ] at *;

lemma spanId_whiskerLeft {a b : C} {f g : Span a b} (η : f ⟶ g) :
    spanWhiskerLeft (Span.idSpan a) η =
      (spanLeftUnitor f).hom ≫ η ≫ (spanLeftUnitor g).inv := by
        apply SpanHom.ext;
        have := @WithPullbacks.pb_hom_ext C ‹_› ‹_›; (
        apply this (𝟙 a) g.left;
        · simp +decide [ spanWhiskerLeft, spanLeftUnitor ];
          simp +decide [ Span.idSpan, Span.comp ];
          exact ( ‹WithPullbacks C›.pbCond ( 𝟙 a ) f.left ) ▸ by simp +decide [ Category.id_comp ] ;
        · simp +decide [ spanWhiskerLeft, spanLeftUnitor ];
          unfold Span.idSpan; aesop;)

lemma spanComp_whiskerLeft {a b c d : C}
    (f : Span a b) (g : Span b c) {h h' : Span c d} (η : h ⟶ h') :
    spanWhiskerLeft (f.comp g) η =
      (spanAssociator f g h).hom ≫
        spanWhiskerLeft f (spanWhiskerLeft g η) ≫ (spanAssociator f g h').inv := by
          have := @WithPullbacks.pb_hom_ext C ‹_› ‹_›;
          apply SpanHom.ext
          apply this;
          · simp +decide [ spanWhiskerLeft, spanAssociator, spanAssociatorHom, spanAssociatorInv ];
            apply this;
            · simp +decide [ Category.assoc, pbLift_fst, pbLift_snd ];
            · simp +decide [ Category.assoc, pbLift_fst, pbLift_snd, Span.comp ];
          · simp +decide [ spanWhiskerLeft, spanAssociator ];
            simp +decide [ spanAssociatorHom, spanAssociatorInv ]

/-
PROVIDED SOLUTION
Same approach as spanWhiskerLeft_id that worked: unfold spanWhiskerRight, apply_rules [SpanHom.ext], simp with all the CategoryStruct.comp and CategoryStruct.id and SpanHom.ext_iff and Span.comp and Span.idSpan.
-/
lemma spanId_whiskerRight {a b c : C} (s : Span a b) (t : Span b c) :
    spanWhiskerRight (𝟙 s) t = 𝟙 (s.comp t) := by
      unfold spanWhiskerRight;
      have := @pb_hom_ext C ‹_› ‹_›;
      apply_rules [ SpanHom.ext ];
      all_goals simp +decide [ CategoryTheory.CategoryStruct.id ] ;

/-
PROVIDED SOLUTION
Apply SpanHom.ext. Simp [spanWhiskerRight]. Apply pb_hom_ext s₃.right t.left. For pbFst: LHS = (pbFst ≫ α.hom) ≫ β.hom by pbLift_fst. RHS similarly by pbLift_fst and assoc. For pbSnd: both sides = pbSnd by pbLift_snd.
-/
lemma spanComp_whiskerRight {a b c : C}
    {s₁ s₂ s₃ : Span a b} (α : s₁ ⟶ s₂) (β : s₂ ⟶ s₃)
    (t : Span b c) :
    spanWhiskerRight (α ≫ β) t = spanWhiskerRight α t ≫ spanWhiskerRight β t := by
      -- By the associativity of the spanWhiskerRight operation, we can rewrite the left-hand side as the right-hand side.
      apply Eq.symm; exact (by
        apply SpanHom.ext
        simp [spanWhiskerRight]
        apply Eq.symm; exact (by
          have := @WithPullbacks.pb_hom_ext C ‹_› ‹_›;
          apply this
          all_goals generalize_proofs at *;
          · erw [ Category.assoc ] ; aesop;
          · erw [ Category.assoc ] ; aesop;
        ))

lemma spanWhiskerRight_id {a b : C} {f g : Span a b} (η : f ⟶ g) :
    spanWhiskerRight η (Span.idSpan b) =
      (spanRightUnitor f).hom ≫ η ≫ (spanRightUnitor g).inv := by
        -- By definition of spanWhiskerRight and spanRightUnitor, we know that they are equal when applied to the same span and 2-cell.
        apply SpanHom.ext; simp [spanWhiskerRight, spanRightUnitor] at *; (
        have := @WithPullbacks.pb_hom_ext C ‹_› ‹_›; apply this; simp +decide [ Span.comp, Span.idSpan ] ;
        simp +decide [ Category.assoc, pbLift_snd, Span.idSpan ];
        have := @WithPullbacks.pbCond C ‹_› ‹_›; aesop;)

lemma spanWhiskerRight_comp {a b c d : C}
    {f f' : Span a b} (η : f ⟶ f') (g : Span b c) (h : Span c d) :
    spanWhiskerRight η (g.comp h) =
      (spanAssociator f g h).inv ≫
        spanWhiskerRight (spanWhiskerRight η g) h ≫ (spanAssociator f' g h).hom := by
          apply SpanHom.ext;
          nontriviality;
          have := @WithPullbacks.pb_hom_ext C ‹_› ‹_›;
          apply this;
          · simp +decide [ spanWhiskerRight, spanAssociator, spanAssociatorHom, spanAssociatorInv ];
          · simp +decide [ spanWhiskerRight, spanAssociator ];
            apply this;
            · simp +decide [ spanAssociatorInv, spanAssociatorHom ];
            · simp +decide [ spanAssociatorInv, spanAssociatorHom ]

lemma spanWhisker_assoc {a b c d : C}
    (f : Span a b) {g g' : Span b c} (η : g ⟶ g') (h : Span c d) :
    spanWhiskerRight (spanWhiskerLeft f η) h =
      (spanAssociator f g h).hom ≫
        spanWhiskerLeft f (spanWhiskerRight η h) ≫ (spanAssociator f g' h).inv := by
          have := @WithPullbacks.pb_hom_ext C ‹_› ‹_›;
          contrapose! this;
          cases' ‹WithPullbacks C› with _ _;
          rename_i h₁ h₂;
          contrapose! this;
          apply_rules [ SpanHom.ext ];
          all_goals simp +decide [ spanWhiskerRight, spanWhiskerLeft, spanAssociator, spanAssociatorHom, spanAssociatorInv ];
          apply this;
          · simp +decide [ Category.assoc, pbLift_fst, pbLift_snd, Span.comp ];
          · simp +decide [ Category.assoc, pbLift_fst, pbLift_snd ]

/-
PROVIDED SOLUTION
Apply SpanHom.ext, simp [spanWhiskerLeft, spanWhiskerRight, SpanHom_comp_hom], apply pb_hom_ext g.right i.left (or whatever the appropriate pullback is), then for each branch simp with pbLift_fst, pbLift_snd, Category.assoc.
-/
lemma spanWhisker_exchange {a b c : C}
    {f g : Span a b} {h i : Span b c}
    (η : f ⟶ g) (θ : h ⟶ i) :
    spanWhiskerLeft f θ ≫ spanWhiskerRight η i =
      spanWhiskerRight η h ≫ spanWhiskerLeft g θ := by
        have := @WithPullbacks.pb_hom_ext C ‹_› ‹_›;
        apply_rules [ SpanHom.ext ];
        all_goals unfold spanWhiskerLeft spanWhiskerRight; simp +decide [ Span.comp, Category.assoc, pbLift_fst, pbLift_snd ]

lemma spanPentagon {a b c d e : C}
    (f : Span a b) (g : Span b c) (h : Span c d) (i : Span d e) :
    spanWhiskerRight (spanAssociator f g h).hom i ≫
      (spanAssociator f (g.comp h) i).hom ≫
        spanWhiskerLeft f (spanAssociator g h i).hom =
    (spanAssociator (f.comp g) h i).hom ≫ (spanAssociator f g (h.comp i)).hom := by
      have := @WithPullbacks.pb_hom_ext C ‹_› ‹_›;
      refine' SpanHom.ext _;
      apply this;
      · simp +decide [ Category.assoc, spanWhiskerRight, spanWhiskerLeft, spanAssociator ];
        simp +decide [ Category.assoc, spanAssociatorHom ];
      · simp +decide [ spanWhiskerRight, spanWhiskerLeft, spanAssociator ];
        apply this;
        · simp +decide [ spanAssociatorHom, Category.assoc ];
        · simp +decide [ spanAssociatorHom, Category.assoc ];
          apply this;
          · simp +decide [ Category.assoc, pbLift_fst, pbLift_snd ];
          · simp +decide [ Category.assoc, pbLift_snd ]

lemma spanTriangle {a b c : C}
    (f : Span a b) (g : Span b c) :
    (spanAssociator f (Span.idSpan b) g).hom ≫
      spanWhiskerLeft f (spanLeftUnitor g).hom =
    spanWhiskerRight (spanRightUnitor f).hom g := by
      unfold spanWhiskerLeft spanWhiskerRight;
      nontriviality;
      rename_i h;
      obtain ⟨ x, y, hxy ⟩ := h;
      have := @WithPullbacks.pb_hom_ext C ‹_› ‹_›;
      apply_rules [ SpanHom.ext, this ];
      all_goals simp +decide [ spanAssociator, spanLeftUnitor, spanRightUnitor, Span.comp ];
      all_goals simp +decide [ spanAssociatorHom, Span.comp, Span.idSpan ]

/-- The bicategory structure on `SpanCat C`. -/
instance SpanCat.instBicategory : Bicategory.{v, max u v, u} (SpanCat C) where
  homCategory a b := SpanCat.instHomCategory a b
  whiskerLeft := @fun _ _ _ s _ _ α => spanWhiskerLeft s α
  whiskerRight := @fun _ _ _ _ _ α t => spanWhiskerRight α t
  associator := @fun _ _ _ _ s t u => spanAssociator s t u
  leftUnitor := @fun _ _ s => spanLeftUnitor s
  rightUnitor := @fun _ _ s => spanRightUnitor s
  whiskerLeft_id := @fun _ _ _ s t => spanWhiskerLeft_id s t
  whiskerLeft_comp := @fun _ _ _ s _ _ _ α β => spanWhiskerLeft_comp s α β
  id_whiskerLeft := @fun _ _ _ _ η => spanId_whiskerLeft η
  comp_whiskerLeft := @fun _ _ _ _ f g _ _ η => spanComp_whiskerLeft f g η
  id_whiskerRight := @fun _ _ _ s t => spanId_whiskerRight s t
  comp_whiskerRight := @fun _ _ _ _ _ _ α β t => spanComp_whiskerRight α β t
  whiskerRight_id := @fun _ _ _ _ η => spanWhiskerRight_id η
  whiskerRight_comp := @fun _ _ _ _ _ _ η g h => spanWhiskerRight_comp η g h
  whisker_assoc := @fun _ _ _ _ f _ _ η h => spanWhisker_assoc f η h
  whisker_exchange := @fun _ _ _ _ _ _ _ η θ => spanWhisker_exchange η θ
  pentagon := @fun _ _ _ _ _ f g h i => spanPentagon f g h i
  triangle := @fun _ _ _ f g => spanTriangle f g

end CategoryTheory
