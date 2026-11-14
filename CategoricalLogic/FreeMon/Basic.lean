/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import Mathlib.CategoryTheory.Category.Cat

/-!
# The free strict monoidal category monad on `Cat`

For a category `X`, `FreeMon X` is the free strict monoidal category on `X`: its objects are
lists of objects of `X` and its morphisms are lists of morphisms of `X`, matched up positionwise.
This is the monad on `Cat` whose algebras are strict monoidal categories, and whose generalized
multicategories are the (planar) multicategories.

## Main definitions

* `FreeMon X`: a one-field structure around `List X` (constructor `FreeMon.mk`, field
  `FreeMon.as`), so that the category instance does not leak onto `List`.
* `FreeMon.Hom xs ys`: the morphisms, by recursion on both lists (`PUnit`, `×`, `PEmpty`).
  An inductive family would live in `Type (max u v)` because of its index arguments; this
  recursive definition lives in `Type v`, so `FreeMon X : Type u` is a `Category.{v}`.
* `FreeMon.nil`, `FreeMon.cons`, `FreeMon.head`, `FreeMon.tail`: the API for morphisms. The
  eliminators `FreeMon.homRec` (use `induction f using FreeMon.homRec`) and `FreeMon.casesCons`
  hide the representation.
* `FreeMon.append`: concatenation of morphisms (the tensor product of morphisms).
* `FreeMon.map F`, `FreeMon.unit X`, `FreeMon.flatten X`: the functor, unit and multiplication.

## Definitional behaviour on objects

With `xs : List X`, `A : FreeMon X`, `As : List (FreeMon X)`:

| equality | status |
|---|---|
| `(map F).obj A = mk (A.as.map F.obj)` | `rfl` |
| `(unit X).obj x = mk [x]` | `rfl` |
| `(flatten X).obj A = mk (A.as.flatMap as)` | `rfl` |
| `(map F).obj (mk (x :: xs)) = mk (F.obj x :: ((map F).obj (mk xs)).as)` | `rfl` |
| `(flatten X).obj (mk (A :: As)) = mk (A.as ++ ((flatten X).obj (mk As)).as)` | `rfl` |
| `F ⋙ unit Y = unit X ⋙ map F` (naturality of the unit, as functors) | `rfl` |
| `(flatten X).obj ((unit _).obj A) = mk (A.as ++ [])` | `rfl` |
| `(flatten X).obj ((unit _).obj A) = A` (left unit) | propositional |
| `(flatten X).obj ((map (unit X)).obj A) = A` (right unit) | propositional |
| `(map (𝟭 X)).obj A = A`, `(map (F ⋙ G)).obj A = (map G).obj ((map F).obj A)` | propositional |
| naturality of `flatten`, associativity | propositional |

All of these are `rfl` when `A` is a literal list, e.g. `mk [x, y]`. The propositional ones are
`map_id_obj`, `map_comp_obj`, `unit_flatten_obj`, `map_unit_flatten_obj`,
`flatten_naturality_obj` and `map_flatten_flatten_obj`.

## Transports

The simp normal form never unfolds `(map F).obj A` or `(flatten X).obj A` for a variable `A`
(`map_obj` and `flatten_obj` are not simp lemmas): otherwise the objects would disagree, up to
unfolding `map`, with the types of morphisms `(map F).map f`. Only applications to literal
`mk []` and `mk (x :: xs)` are unfolded (`map_obj_cons`, ...), consistently with `map_map_cons`.

`eqToHom_cons` splits a transport between nonempty lists, but only fires when the equation is
syntactically between lists `mk (_ :: _)`. The robust way to prove equalities of morphisms up to
transport is through `HEq`: `conj_eqToHom_iff_heq` reduces them to `HEq`, which is proved with
the congruences `cons_heq_cons` and `append_heq_append`, the `HEq` lemmas `append_nil_heq`,
`append_assoc_heq`, `map_map_append_heq`, `flatten_map_append_heq`, and
`induction f using FreeMon.homRec`. The `eqToHom` forms (`append_nil`, `append_assoc`,
`map_map_append`, `flatten_map_append`) are derived from these.
-/

@[expose] public section

namespace CategoryTheory

universe w v u v' u' v'' u''

/-- The free strict monoidal category on a category `X`: its objects are lists of objects of
`X`, its morphisms are lists of morphisms of `X` matched up positionwise. -/
@[ext]
structure FreeMon (X : Type u) where
  /-- An object of `FreeMon X` given by a list of objects of `X`. -/
  mk ::
  /-- The underlying list of an object of `FreeMon X`. -/
  as : List X

namespace FreeMon

section Category

variable {X : Type u} [Category.{v} X]

/-- The morphisms of `FreeMon X` between the underlying lists. They are defined by recursion on
both lists (rather than as an inductive family) so that they live in `Type v`. -/
def Hom : List X → List X → Type v
  | [], [] => PUnit
  | x :: xs, y :: ys => (x ⟶ y) × Hom xs ys
  | [], _ :: _ => PEmpty
  | _ :: _, [] => PEmpty

/-- The identity morphism. -/
def Hom.id : ∀ xs : List X, Hom xs xs
  | [] => PUnit.unit
  | x :: xs => (𝟙 x, Hom.id xs)

/-- Composition of morphisms, positionwise. -/
def Hom.comp : ∀ {xs ys zs : List X}, Hom xs ys → Hom ys zs → Hom xs zs
  | [], [], [], _, _ => PUnit.unit
  | _ :: _, _ :: _, _ :: _, f, g => (f.1 ≫ g.1, Hom.comp f.2 g.2)
  | [], _ :: _, _, f, _ => PEmpty.elim f
  | _ :: _, [], _, f, _ => PEmpty.elim f
  | [], [], _ :: _, _, g => PEmpty.elim g
  | _ :: _, _ :: _, [], _, g => PEmpty.elim g

theorem Hom.id_comp : ∀ {xs ys : List X} (f : Hom xs ys), Hom.comp (Hom.id xs) f = f
  | [], [], _ => rfl
  | _ :: _, _ :: _, f => Prod.ext (Category.id_comp f.1) (Hom.id_comp f.2)
  | [], _ :: _, f => PEmpty.elim f
  | _ :: _, [], f => PEmpty.elim f

theorem Hom.comp_id : ∀ {xs ys : List X} (f : Hom xs ys), Hom.comp f (Hom.id ys) = f
  | [], [], _ => rfl
  | _ :: _, _ :: _, f => Prod.ext (Category.comp_id f.1) (Hom.comp_id f.2)
  | [], _ :: _, f => PEmpty.elim f
  | _ :: _, [], f => PEmpty.elim f

theorem Hom.assoc : ∀ {xs ys zs ws : List X} (f : Hom xs ys) (g : Hom ys zs) (h : Hom zs ws),
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h)
  | [], [], [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, f, g, h =>
    Prod.ext (Category.assoc f.1 g.1 h.1) (Hom.assoc f.2 g.2 h.2)
  | [], _ :: _, _, _, f, _, _ => PEmpty.elim f
  | _ :: _, [], _, _, f, _, _ => PEmpty.elim f
  | [], [], _ :: _, _, _, g, _ => PEmpty.elim g
  | _ :: _, _ :: _, [], _, _, g, _ => PEmpty.elim g
  | [], [], [], _ :: _, _, _, h => PEmpty.elim h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => PEmpty.elim h

/-- The first component of a morphism between nonempty lists. -/
def Hom.head {x y : X} {xs ys : List X} (f : Hom (x :: xs) (y :: ys)) : x ⟶ y := f.1

/-- The remaining components of a morphism between nonempty lists. -/
def Hom.tail {x y : X} {xs ys : List X} (f : Hom (x :: xs) (y :: ys)) : Hom xs ys := f.2

instance category : Category.{v} (FreeMon X) where
  Hom A B := Hom A.as B.as
  id A := Hom.id A.as
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

omit [Category.{v} X] in
@[simp] theorem mk_as (A : FreeMon X) : mk A.as = A := rfl

variable {x y z : X} {xs ys : List X} {A B C : FreeMon X}

/-- The empty list of morphisms. -/
def nil : mk ([] : List X) ⟶ mk [] := PUnit.unit

/-- Prepend a morphism to a list of morphisms. -/
def cons (f : x ⟶ y) (fs : A ⟶ B) : mk (x :: A.as) ⟶ mk (y :: B.as) := (f, fs)

/-- The first morphism of a list of morphisms between nonempty lists. -/
def head (f : mk (x :: xs) ⟶ mk (y :: ys)) : x ⟶ y := Hom.head f

/-- All but the first morphism of a list of morphisms between nonempty lists. -/
def tail (f : mk (x :: xs) ⟶ mk (y :: ys)) : mk xs ⟶ mk ys := Hom.tail f

@[simp] theorem head_cons (f : x ⟶ y) (fs : A ⟶ B) : head (cons f fs) = f := rfl

@[simp] theorem tail_cons (f : x ⟶ y) (fs : A ⟶ B) : tail (cons f fs) = fs := rfl

@[simp] theorem cons_head_tail (f : mk (x :: xs) ⟶ mk (y :: ys)) : cons (head f) (tail f) = f :=
  rfl

theorem hom_ext_nil (f g : mk ([] : List X) ⟶ mk []) : f = g := rfl

theorem hom_ext_cons {f g : mk (x :: xs) ⟶ mk (y :: ys)} (h₁ : head f = head g)
    (h₂ : tail f = tail g) : f = g :=
  Prod.ext h₁ h₂

@[simp] theorem cons_inj {f f' : x ⟶ y} {fs fs' : A ⟶ B} :
    cons f fs = cons f' fs' ↔ f = f' ∧ fs = fs' :=
  Prod.mk_inj

instance : Unique (mk ([] : List X) ⟶ mk []) where
  default := nil
  uniq _ := rfl

instance : IsEmpty (mk ([] : List X) ⟶ mk (y :: ys)) := ⟨fun f => PEmpty.elim f⟩

instance : IsEmpty (mk (x :: xs) ⟶ mk ([] : List X)) := ⟨fun f => PEmpty.elim f⟩

/-- Case analysis on a morphism between nonempty lists. -/
@[elab_as_elim]
def casesCons {motive : (mk (x :: xs) ⟶ mk (y :: ys)) → Sort w}
    (cons : ∀ (f : x ⟶ y) (fs : mk xs ⟶ mk ys), motive (cons f fs))
    (f : mk (x :: xs) ⟶ mk (y :: ys)) : motive f :=
  cons (head f) (tail f)

/-- Implementation of `homRec`, by recursion on the underlying lists. -/
def homRecAux {motive : ∀ A B : FreeMon X, (A ⟶ B) → Sort w}
    (nil : motive (mk []) (mk []) nil)
    (cons : ∀ {x y : X} {A B : FreeMon X} (f : x ⟶ y) (fs : A ⟶ B),
      motive A B fs → motive (mk (x :: A.as)) (mk (y :: B.as)) (cons f fs)) :
    ∀ {xs ys : List X} (f : mk xs ⟶ mk ys), motive (mk xs) (mk ys) f
  | [], [], _ => nil
  | _ :: _, _ :: _, f => cons (head f) (tail f) (homRecAux nil cons (tail f))
  | [], _ :: _, f => isEmptyElim f
  | _ :: _, [], f => isEmptyElim f

/-- Induction on morphisms of `FreeMon X`: every morphism is built from `nil` and `cons`.
Use it as `induction f using FreeMon.homRec`. -/
@[elab_as_elim]
def homRec {motive : ∀ A B : FreeMon X, (A ⟶ B) → Sort w}
    (nil : motive (mk []) (mk []) nil)
    (cons : ∀ {x y : X} {A B : FreeMon X} (f : x ⟶ y) (fs : A ⟶ B),
      motive A B fs → motive (mk (x :: A.as)) (mk (y :: B.as)) (cons f fs))
    {A B : FreeMon X} (f : A ⟶ B) : motive A B f :=
  homRecAux (motive := motive) nil cons (xs := A.as) (ys := B.as) f

@[simp] theorem homRec_nil {motive : ∀ A B : FreeMon X, (A ⟶ B) → Sort w}
    (nil' : motive (mk []) (mk []) nil)
    (cons' : ∀ {x y : X} {A B : FreeMon X} (f : x ⟶ y) (fs : A ⟶ B),
      motive A B fs → motive (mk (x :: A.as)) (mk (y :: B.as)) (cons f fs)) :
    homRec (motive := motive) nil' cons' nil = nil' := rfl

@[simp] theorem homRec_cons {motive : ∀ A B : FreeMon X, (A ⟶ B) → Sort w}
    (nil' : motive (mk []) (mk []) nil)
    (cons' : ∀ {x y : X} {A B : FreeMon X} (f : x ⟶ y) (fs : A ⟶ B),
      motive A B fs → motive (mk (x :: A.as)) (mk (y :: B.as)) (cons f fs))
    (f : x ⟶ y) (fs : A ⟶ B) :
    homRec (motive := motive) nil' cons' (cons f fs) =
      cons' f fs (homRec (motive := motive) nil' cons' fs) := rfl

@[simp] theorem id_nil : 𝟙 (mk ([] : List X)) = nil := rfl

@[simp] theorem id_cons : 𝟙 (mk (x :: xs)) = cons (𝟙 x) (𝟙 (mk xs)) := rfl

@[simp] theorem nil_comp_nil : nil ≫ nil = (nil : mk ([] : List X) ⟶ mk []) := rfl

@[simp] theorem cons_comp_cons (f : x ⟶ y) (fs : A ⟶ B) (g : y ⟶ z) (gs : B ⟶ C) :
    cons f fs ≫ cons g gs = cons (f ≫ g) (fs ≫ gs) := rfl

theorem head_comp (f : mk (x :: xs) ⟶ mk (y :: ys)) (g : mk (y :: ys) ⟶ mk (z :: C.as)) :
    head (f ≫ g) = head f ≫ head g := rfl

theorem tail_comp (f : mk (x :: xs) ⟶ mk (y :: ys)) (g : mk (y :: ys) ⟶ mk (z :: C.as)) :
    tail (f ≫ g) = tail f ≫ tail g := rfl

omit [Category.{v} X] in
theorem mk_cons_eq_mk_cons_iff : mk (x :: xs) = mk (y :: ys) ↔ x = y ∧ mk xs = mk ys := by
  simp

/-- A transport between nonempty lists is a list of transports. -/
@[simp] theorem eqToHom_cons (h : mk (x :: xs) = mk (y :: ys)) :
    eqToHom h = cons (eqToHom (mk_cons_eq_mk_cons_iff.mp h).1)
      (eqToHom (mk_cons_eq_mk_cons_iff.mp h).2) := by
  obtain ⟨rfl, h'⟩ := mk_cons_eq_mk_cons_iff.mp h
  cases h'
  rfl

/-! ### Concatenation of morphisms -/

/-- Concatenation of lists of morphisms: the tensor product of morphisms of the strict monoidal
category `FreeMon X`. -/
def append {A B A' B' : FreeMon X} (f : A ⟶ B) (g : A' ⟶ B') :
    mk (A.as ++ A'.as) ⟶ mk (B.as ++ B'.as) :=
  homRec (motive := fun A B _ => mk (A.as ++ A'.as) ⟶ mk (B.as ++ B'.as)) g
    (fun f _ fgs => cons f fgs) f

variable {A' B' C' A'' B'' : FreeMon X}

@[simp] theorem nil_append (g : A' ⟶ B') : append nil g = g := rfl

@[simp] theorem cons_append (f : x ⟶ y) (fs : A ⟶ B) (g : A' ⟶ B') :
    append (cons f fs) g = cons f (append fs g) := rfl

@[simp] theorem append_id (A A' : FreeMon X) : append (𝟙 A) (𝟙 A') = 𝟙 _ := by
  obtain ⟨xs⟩ := A
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem append_comp (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C') :
    append (f ≫ g) (f' ≫ g') = append f f' ≫ append g g' := by
  induction f using homRec generalizing C with
  | nil => obtain ⟨_ | _⟩ := C <;> first | rfl | exact isEmptyElim g
  | cons f fs ih =>
    obtain ⟨_ | ⟨z, zs⟩⟩ := C
    · exact isEmptyElim g
    · induction g using casesCons with
      | cons g gs => simp [ih]

@[simp] theorem eqToHom_append (h : A = B) (h' : A' = B') :
    append (eqToHom h) (eqToHom h') = eqToHom (by rw [h, h']) := by
  cases h; cases h'; simp

@[simp] theorem append_eqToHom_comp (h : A = B) (f : B ⟶ C) (g : A' ⟶ B') :
    append (eqToHom h ≫ f) g = eqToHom (by rw [h]) ≫ append f g := by
  cases h; simp

@[simp] theorem append_comp_eqToHom (f : A ⟶ B) (h : B = C) (g : A' ⟶ B') :
    append (f ≫ eqToHom h) g = append f g ≫ eqToHom (by rw [h]) := by
  cases h; simp

@[simp] theorem append_eqToHom_comp' (f : A ⟶ B) (h : A' = B') (g : B' ⟶ C') :
    append f (eqToHom h ≫ g) = eqToHom (by rw [h]) ≫ append f g := by
  cases h; simp

@[simp] theorem append_comp_eqToHom' (f : A ⟶ B) (g : A' ⟶ B') (h : B' = C') :
    append f (g ≫ eqToHom h) = append f g ≫ eqToHom (by rw [h]) := by
  cases h; simp

/-- Congruence for `cons` along equalities of the boundary objects. -/
theorem cons_heq_cons {x x' y y' : X} {A A' B B' : FreeMon X} {f : x ⟶ y} {f' : x' ⟶ y'}
    {fs : A ⟶ B} {fs' : A' ⟶ B'} (hx : x = x') (hy : y = y') (hA : A = A') (hB : B = B')
    (hf : f ≍ f') (hfs : fs ≍ fs') : cons f fs ≍ cons f' fs' := by
  subst hx hy hA hB
  cases hf
  cases hfs
  rfl

/-- Congruence for `append` along equalities of the boundary objects. -/
theorem append_heq_append {A₁ A₂ B₁ B₂ A₁' A₂' B₁' B₂' : FreeMon X} {f₁ : A₁ ⟶ B₁}
    {f₂ : A₂ ⟶ B₂} {g₁ : A₁' ⟶ B₁'} {g₂ : A₂' ⟶ B₂'} (hA : A₁ = A₂) (hB : B₁ = B₂)
    (hA' : A₁' = A₂') (hB' : B₁' = B₂') (hf : f₁ ≍ f₂) (hg : g₁ ≍ g₂) :
    append f₁ g₁ ≍ append f₂ g₂ := by
  subst hA hB hA' hB'
  cases hf
  cases hg
  rfl

omit [Category.{v} X] in
theorem mk_append_nil (A : FreeMon X) : mk (A.as ++ []) = A := by simp

omit [Category.{v} X] in
theorem mk_append_assoc (A A' A'' : FreeMon X) :
    mk ((mk (A.as ++ A'.as)).as ++ A''.as) = mk (A.as ++ (mk (A'.as ++ A''.as)).as) := by simp

theorem append_nil_heq (f : A ⟶ B) : append f nil ≍ f := by
  induction f using homRec with
  | nil => rfl
  | cons f fs ih =>
    exact cons_heq_cons rfl rfl (mk_append_nil _) (mk_append_nil _) HEq.rfl ih

theorem append_nil (f : A ⟶ B) :
    append f nil = eqToHom (mk_append_nil A) ≫ f ≫ eqToHom (mk_append_nil B).symm :=
  (conj_eqToHom_iff_heq _ _ (mk_append_nil A) (mk_append_nil B)).2 (append_nil_heq f)

theorem append_assoc_heq (f : A ⟶ B) (f' : A' ⟶ B') (f'' : A'' ⟶ B'') :
    append (append f f') f'' ≍ append f (append f' f'') := by
  induction f using homRec with
  | nil => rfl
  | cons f fs ih =>
    exact cons_heq_cons rfl rfl (mk_append_assoc _ _ _) (mk_append_assoc _ _ _) HEq.rfl ih

theorem append_assoc (f : A ⟶ B) (f' : A' ⟶ B') (f'' : A'' ⟶ B'') :
    append (append f f') f'' = eqToHom (mk_append_assoc A A' A'') ≫
      append f (append f' f'') ≫ eqToHom (mk_append_assoc B B' B'').symm :=
  (conj_eqToHom_iff_heq _ _ (mk_append_assoc A A' A'') (mk_append_assoc B B' B'')).2
    (append_assoc_heq f f' f'')

end Category

/-! ### Functoriality -/

section Functor

variable {X : Type u} [Category.{v} X] {Y : Type u'} [Category.{v'} Y]
  {Z : Type u''} [Category.{v''} Z]

variable {x y : X} {xs : List X} {A B : FreeMon X}

/-- The action of `map F` on morphisms. Use `(map F).map` instead. -/
def mapHom (F : X ⥤ Y) {A B : FreeMon X} (f : A ⟶ B) :
    mk (A.as.map F.obj) ⟶ mk (B.as.map F.obj) :=
  homRec (motive := fun A B _ => mk (A.as.map F.obj) ⟶ mk (B.as.map F.obj)) nil
    (fun f _ gs => cons (F.map f) gs) f

theorem mapHom_id (F : X ⥤ Y) (A : FreeMon X) : mapHom F (𝟙 A) = 𝟙 _ := by
  obtain ⟨xs⟩ := A
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change cons (F.map (𝟙 x)) (mapHom F (𝟙 (mk xs))) = cons (𝟙 (F.obj x)) (𝟙 _)
    rw [ih, F.map_id]

theorem mapHom_comp (F : X ⥤ Y) {A B C : FreeMon X} (f : A ⟶ B) (g : B ⟶ C) :
    mapHom F (f ≫ g) = mapHom F f ≫ mapHom F g := by
  induction f using homRec generalizing C with
  | nil => obtain ⟨_ | _⟩ := C <;> first | rfl | exact isEmptyElim g
  | cons f fs ih =>
    obtain ⟨_ | ⟨z, zs⟩⟩ := C
    · exact isEmptyElim g
    · induction g using casesCons with
      | cons g gs =>
        change cons (F.map (f ≫ g)) (mapHom F (fs ≫ gs)) =
          cons (F.map f ≫ F.map g) (mapHom F fs ≫ mapHom F gs)
        rw [ih, F.map_comp]

/-- The free strict monoidal category construction is functorial. -/
def map (F : X ⥤ Y) : FreeMon X ⥤ FreeMon Y where
  obj A := mk (A.as.map F.obj)
  map := mapHom F
  map_id := mapHom_id F
  map_comp := mapHom_comp F

/-- Not a simp lemma: rewriting `(map F).obj A` for a variable `A` would make the objects
disagree (up to unfolding `map`) with the types of morphisms `(map F).map f`. -/
theorem map_obj (F : X ⥤ Y) (A : FreeMon X) : (map F).obj A = mk (A.as.map F.obj) := rfl

/-- Not a simp lemma, see `map_obj`. -/
theorem map_obj_as (F : X ⥤ Y) (A : FreeMon X) : ((map F).obj A).as = A.as.map F.obj := rfl

@[simp] theorem map_obj_nil (F : X ⥤ Y) : (map F).obj (mk []) = mk [] := rfl

@[simp] theorem map_obj_cons (F : X ⥤ Y) (x : X) (xs : List X) :
    (map F).obj (mk (x :: xs)) = mk (F.obj x :: ((map F).obj (mk xs)).as) := rfl

@[simp] theorem map_map_nil (F : X ⥤ Y) : (map F).map (nil : mk ([] : List X) ⟶ mk []) = nil :=
  rfl

@[simp] theorem map_map_cons (F : X ⥤ Y) (f : x ⟶ y) (fs : A ⟶ B) :
    (map F).map (cons f fs) = cons (F.map f) ((map F).map fs) := rfl

theorem map_obj_append (F : X ⥤ Y) (A A' : FreeMon X) :
    (map F).obj (mk (A.as ++ A'.as)) = mk (((map F).obj A).as ++ ((map F).obj A').as) := by
  simp [map_obj]

theorem map_map_append_heq (F : X ⥤ Y) {A B A' B' : FreeMon X} (f : A ⟶ B) (g : A' ⟶ B') :
    (map F).map (append f g) ≍ append ((map F).map f) ((map F).map g) := by
  induction f using homRec with
  | nil => rfl
  | cons f fs ih =>
    exact cons_heq_cons rfl rfl (map_obj_append F _ _) (map_obj_append F _ _) HEq.rfl ih

theorem map_map_append (F : X ⥤ Y) {A B A' B' : FreeMon X} (f : A ⟶ B) (g : A' ⟶ B') :
    (map F).map (append f g) = eqToHom (map_obj_append F A A') ≫
      append ((map F).map f) ((map F).map g) ≫ eqToHom (map_obj_append F B B').symm :=
  (conj_eqToHom_iff_heq _ _ (map_obj_append F A A') (map_obj_append F B B')).2
    (map_map_append_heq F f g)

variable (X) in
theorem map_id_obj (A : FreeMon X) : (map (𝟭 X)).obj A = A := FreeMon.ext (List.map_id A.as)

variable (X) in
theorem map_id : map (𝟭 X) = 𝟭 (FreeMon X) := by
  refine Functor.hext (map_id_obj X) fun A B f => ?_
  induction f using homRec with
  | nil => rfl
  | cons f fs ih =>
    exact cons_heq_cons rfl rfl (map_id_obj X _) (map_id_obj X _) HEq.rfl ih

theorem map_comp_obj (F : X ⥤ Y) (G : Y ⥤ Z) (A : FreeMon X) :
    (map (F ⋙ G)).obj A = (map G).obj ((map F).obj A) :=
  FreeMon.ext (List.map_map (l := A.as) (f := F.obj) (g := G.obj)).symm

theorem map_comp (F : X ⥤ Y) (G : Y ⥤ Z) : map (F ⋙ G) = map F ⋙ map G := by
  refine Functor.hext (map_comp_obj F G) fun A B f => ?_
  induction f using homRec with
  | nil => rfl
  | cons f fs ih =>
    exact cons_heq_cons rfl rfl (map_comp_obj F G _) (map_comp_obj F G _) HEq.rfl ih

end Functor

/-! ### The unit -/

section Unit

variable (X : Type u) [Category.{v} X] {Y : Type u'} [Category.{v'} Y]

/-- The unit of the monad: an object is sent to the singleton list. -/
def unit : X ⥤ FreeMon X where
  obj x := mk [x]
  map f := cons f nil
  map_id _ := rfl
  map_comp _ _ := rfl

variable {X}

@[simp] theorem unit_obj (x : X) : (unit X).obj x = mk [x] := rfl

@[simp] theorem unit_map {x y : X} (f : x ⟶ y) : (unit X).map f = cons f nil := rfl

theorem unit_naturality (F : X ⥤ Y) : F ⋙ unit Y = unit X ⋙ map F := rfl

end Unit

/-! ### The multiplication -/

section Flatten

variable {X : Type u} [Category.{v} X] {Y : Type u'} [Category.{v'} Y]

variable {x y : FreeMon X} {xs : List (FreeMon X)} {A B : FreeMon (FreeMon X)}

/-- The action of `flatten X` on morphisms. Use `(flatten X).map` instead. -/
def flattenHom {A B : FreeMon (FreeMon X)} (f : A ⟶ B) :
    mk (A.as.flatMap as) ⟶ mk (B.as.flatMap as) :=
  homRec (motive := fun A B _ => mk (A.as.flatMap as) ⟶ mk (B.as.flatMap as)) nil
    (fun f _ gs => append f gs) f

theorem flattenHom_id (A : FreeMon (FreeMon X)) : flattenHom (𝟙 A) = 𝟙 _ := by
  obtain ⟨xs⟩ := A
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change append (𝟙 x) (flattenHom (𝟙 (mk xs))) = 𝟙 _
    rw [ih, append_id]

theorem flattenHom_comp {A B C : FreeMon (FreeMon X)} (f : A ⟶ B) (g : B ⟶ C) :
    flattenHom (f ≫ g) = flattenHom f ≫ flattenHom g := by
  induction f using homRec generalizing C with
  | nil => obtain ⟨_ | _⟩ := C <;> first | rfl | exact isEmptyElim g
  | cons f fs ih =>
    obtain ⟨_ | ⟨z, zs⟩⟩ := C
    · exact isEmptyElim g
    · induction g using casesCons with
      | cons g gs =>
        change append (f ≫ g) (flattenHom (fs ≫ gs)) =
          append f (flattenHom fs) ≫ append g (flattenHom gs)
        rw [ih, append_comp]

variable (X) in
/-- The multiplication of the monad: a list of lists is sent to its concatenation. -/
def flatten : FreeMon (FreeMon X) ⥤ FreeMon X where
  obj A := mk (A.as.flatMap as)
  map := flattenHom
  map_id := flattenHom_id
  map_comp := flattenHom_comp

/-- Not a simp lemma, see `map_obj`. -/
theorem flatten_obj (A : FreeMon (FreeMon X)) : (flatten X).obj A = mk (A.as.flatMap as) := rfl

/-- Not a simp lemma, see `map_obj`. -/
theorem flatten_obj_as (A : FreeMon (FreeMon X)) :
    ((flatten X).obj A).as = A.as.flatMap as := rfl

@[simp] theorem flatten_obj_nil : (flatten X).obj (mk []) = mk [] := rfl

@[simp] theorem flatten_obj_cons (x : FreeMon X) (xs : List (FreeMon X)) :
    (flatten X).obj (mk (x :: xs)) = mk (x.as ++ ((flatten X).obj (mk xs)).as) := rfl

@[simp] theorem flatten_map_nil :
    (flatten X).map (nil : mk ([] : List (FreeMon X)) ⟶ mk []) = nil := rfl

@[simp] theorem flatten_map_cons (f : x ⟶ y) (fs : A ⟶ B) :
    (flatten X).map (cons f fs) = append f ((flatten X).map fs) := rfl

theorem flatten_obj_append (A A' : FreeMon (FreeMon X)) :
    (flatten X).obj (mk (A.as ++ A'.as)) =
      mk (((flatten X).obj A).as ++ ((flatten X).obj A').as) := by
  simp [flatten_obj]

theorem flatten_map_append_heq {A B A' B' : FreeMon (FreeMon X)} (f : A ⟶ B) (g : A' ⟶ B') :
    (flatten X).map (append f g) ≍ append ((flatten X).map f) ((flatten X).map g) := by
  induction f using homRec with
  | nil => rfl
  | cons f fs ih =>
    exact (append_heq_append rfl rfl (flatten_obj_append _ _) (flatten_obj_append _ _) HEq.rfl
      ih).trans (append_assoc_heq _ _ _).symm

theorem flatten_map_append {A B A' B' : FreeMon (FreeMon X)} (f : A ⟶ B) (g : A' ⟶ B') :
    (flatten X).map (append f g) = eqToHom (flatten_obj_append A A') ≫
      append ((flatten X).map f) ((flatten X).map g) ≫ eqToHom (flatten_obj_append B B').symm :=
  (conj_eqToHom_iff_heq _ _ (flatten_obj_append A A') (flatten_obj_append B B')).2
    (flatten_map_append_heq f g)

theorem flatten_naturality_obj (F : X ⥤ Y) (A : FreeMon (FreeMon X)) :
    (flatten Y).obj ((map (map F)).obj A) = (map F).obj ((flatten X).obj A) := by
  simp [map_obj, flatten_obj, List.map_flatMap, List.flatMap_map]

theorem flatten_naturality (F : X ⥤ Y) : map (map F) ⋙ flatten Y = flatten X ⋙ map F := by
  refine Functor.hext (flatten_naturality_obj F) fun A B f => ?_
  induction f using homRec with
  | nil => rfl
  | cons f fs ih =>
    exact (append_heq_append rfl rfl (flatten_naturality_obj F _) (flatten_naturality_obj F _)
      HEq.rfl ih).trans (map_map_append_heq F _ _).symm

variable (X)

theorem unit_flatten_obj (A : FreeMon X) : (flatten X).obj ((unit (FreeMon X)).obj A) = A := by
  simp [flatten_obj]

theorem unit_flatten : unit (FreeMon X) ⋙ flatten X = 𝟭 (FreeMon X) :=
  Functor.hext (unit_flatten_obj X) fun _ _ f => append_nil_heq f

theorem map_unit_flatten_obj (A : FreeMon X) : (flatten X).obj ((map (unit X)).obj A) = A := by
  simp [map_obj, flatten_obj, List.flatMap_map]

theorem map_unit_flatten : map (unit X) ⋙ flatten X = 𝟭 (FreeMon X) := by
  refine Functor.hext (map_unit_flatten_obj X) fun A B f => ?_
  induction f using homRec with
  | nil => rfl
  | cons f fs ih =>
    exact cons_heq_cons rfl rfl (map_unit_flatten_obj X _) (map_unit_flatten_obj X _) HEq.rfl ih

theorem map_flatten_flatten_obj (A : FreeMon (FreeMon (FreeMon X))) :
    (flatten X).obj ((map (flatten X)).obj A) = (flatten X).obj ((flatten (FreeMon X)).obj A) := by
  simp [map_obj, flatten_obj, List.flatMap_map, List.flatMap_assoc]

theorem map_flatten_flatten :
    map (flatten X) ⋙ flatten X = flatten (FreeMon X) ⋙ flatten X := by
  refine Functor.hext (map_flatten_flatten_obj X) fun A B f => ?_
  induction f using homRec with
  | nil => rfl
  | cons f fs ih =>
    exact (append_heq_append rfl rfl (map_flatten_flatten_obj X _) (map_flatten_flatten_obj X _)
      HEq.rfl ih).trans (flatten_map_append_heq _ _).symm

end Flatten

end FreeMon

end CategoryTheory
