/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Designs.Wiring.Prof

/-!
# Operads with structural rules `W`

A `W`-operad on a category `X` is a `FreeW W`-monoid in the sense of Cruttwell–Shulman: a
profunctor `hom : X ⇸ FreeW W X` of operations, a nullary identity cell and a binary composition
cell, subject to unit and associativity laws. For `W = planar` these are (non-symmetric)
multicategories over `X`, for `W = cartesian` cartesian multicategories over `X`.

The laws are stated elementwise with the concrete action of `FreeW W` on cells
(`FreeW.ηCell`, `FreeW.mapNullary`, `FreeW.mapBinary`, `FreeW.μCell`). The monad laws for lists
hold only propositionally, so each law has one transport `mpRight` along a list equation.

## Main definitions

* `WOperad W X`: a `W`-operad on `X`.
* `WOperad.Hom M N`: morphisms of `W`-operads, with `Hom.id` and `Hom.comp`.
-/

@[expose] public section

namespace CategoryTheory

open Profunctor FreeW

universe u v v' v'' w w' w''

namespace FreeW

variable {W : WiringClass.{u}} {C : Type u} [Category.{v} C] {D : Type u} [Category.{v'} D]
  {E : Type u} [Category.{v''} E]

/-! ### The monad laws on objects -/

theorem flatten_unit (b : FreeW W C) : (flatten (W := W)).obj ((unit (W := W)).obj b) = b :=
  FreeW.ext (by simp)

theorem flatten_map_unit (b : FreeW W C) :
    (flatten (W := W)).obj ((map (unit (W := W))).obj b) = b :=
  FreeW.ext (by simp [List.flatMap_map])

theorem flatten_flatten (d : FreeW W (FreeW W (FreeW W C))) :
    (flatten (W := W)).obj ((flatten (W := W)).obj d) =
      (flatten (W := W)).obj ((map (flatten (W := W))).obj d) :=
  FreeW.ext (by simp [List.flatMap_assoc, List.flatMap_map])

theorem map_flatten (F : C ⥤ D) (c : FreeW W (FreeW W C)) :
    (map F).obj ((flatten (W := W)).obj c) = (flatten (W := W)).obj ((map (map F)).obj c) :=
  FreeW.ext (by simp [List.map_flatMap, List.flatMap_map])

theorem map_id_obj (b : FreeW W C) : (map (𝟭 C)).obj b = b :=
  FreeW.ext (List.map_id' b.as)

theorem map_comp_obj (F : C ⥤ D) (G : D ⥤ E) (b : FreeW W C) :
    (map (F ⋙ G)).obj b = (map G).obj ((map F).obj b) :=
  FreeW.ext (by simp)

/-- `eqToHom` in `FreeW W X` reads every variable from the position with the same index. -/
theorem eqToHom_assign_eq {xs ys : FreeW W C} (h : xs = ys) {y : C} (k : Var ys.as y)
    (v : Var xs.as y) (hv : v.idx = k.idx) : assign (eqToHom h) k = ⟨y, v, 𝟙 y⟩ := by
  rw [eqToHom_assign]
  congr
  subst h
  exact Var.ext_idx _ _ hv.symm

end FreeW

variable (W : WiringClass.{u}) (X : Type u) [Category.{v} X]

/-- A `W`-operad on `X`: operations `hom.app a b` with output `a : X` and inputs `b`, a list of
objects of `X`, acted on by the structural rules of `W`; identities and composition. -/
structure WOperad where
  /-- The operations. -/
  hom : Profunctor.{w} X (FreeW W X)
  /-- The identity operation on `a`, with inputs `[a]`. -/
  id : NullaryCell hom (𝟭 X) unit
  /-- Composition of an operation `g` with inputs `b` and a `b`-indexed family `f` of
  operations whose inputs are the blocks of `c`: the result has inputs `c` flattened. -/
  comp : BinaryCell hom (prof W hom) hom (𝟭 X) flatten
  /-- Composing the identity with the singleton family `[f]` is `f`. -/
  comp_id {a : X} {b : FreeW W X} (f : hom.app a b) :
    comp.app (id.app a) ((ηCell hom).app f) = hom.mpRight f (flatten_unit b)
  /-- Composing `f` with the family of identities is `f`. -/
  id_comp {a : X} {b : FreeW W X} (f : hom.app a b) :
    comp.app f ((mapNullary id).app b) = hom.mpRight f (flatten_map_unit b)
  /-- Associativity. -/
  comp_assoc {a : X} {b : FreeW W X} {c : FreeW W (FreeW W X)}
      {d : FreeW W (FreeW W (FreeW W X))} (h : hom.app a b) (g : (prof W hom).app b c)
      (f : (prof W (prof W hom)).app c d) :
    comp.app (comp.app h g) ((μCell hom).app f) =
      hom.mpRight (comp.app h ((mapBinary comp).app g f)) (flatten_flatten d)

namespace WOperad

variable {W X} {Y : Type u} [Category.{v'} Y] {Z : Type u} [Category.{v''} Z]

/-- A morphism of `W`-operads: a functor on objects and a map of operations preserving
identities and composition. -/
structure Hom (M : WOperad.{u, v, w} W X) (N : WOperad.{u, v', w'} W Y) where
  /-- The action on objects. -/
  functor : X ⥤ Y
  /-- The action on operations. -/
  map : Square M.hom N.hom functor (FreeW.map functor)
  /-- Identities are preserved. -/
  map_id (a : X) : map.app (M.id.app a) = N.id.app (functor.obj a)
  /-- Composition is preserved. -/
  map_comp {a : X} {b : FreeW W X} {c : FreeW W (FreeW W X)} (g : M.hom.app a b)
      (f : (prof W M.hom).app b c) :
    map.app (M.comp.app g f) =
      N.hom.mpRight (N.comp.app (map.app g) ((mapSquare map).app f)) (map_flatten functor c)

end WOperad

namespace FreeW

variable {W : WiringClass.{u}} {C : Type u} [Category.{v} C]

theorem eqToHom_comp_map_id {b b' : FreeW W C} (β : b ⟶ b') :
    eqToHom (map_id_obj b) ≫ β = (map (𝟭 C)).map β ≫ eqToHom (map_id_obj b') := by
  refine hom_ext fun y k ↦ ?_
  dsimp only [comp_assign]
  rw [eqToHom_assign_eq (map_id_obj b) (assign β k).2.1 ((assign β k).2.1.map (𝟭 C).obj)
    (Var.idx_map _ _), eqToHom_assign_eq (map_id_obj b') k (k.map (𝟭 C).obj) (Var.idx_map _ _),
    map_assign_map]
  simp

/-- The canonical morphism `(map (map 𝟭)).obj c ⟶ c`, with `eqToHom` components. -/
def mapMapIdHom (c : FreeW W (FreeW W C)) : (map (map (𝟭 C))).obj c ⟶ c :=
  Wired.mapSrc (map (𝟭 C)).obj (fun _ _ σ ↦ σ)
    (Wired.refl (R := fun c c' : FreeW W C ↦ (map (𝟭 C)).obj c ⟶ c')
      (fun c ↦ eqToHom (map_id_obj c)) (as := c.as))

theorem idx_join_map {D : Type u} [Category.{v'} D] (F : C ⥤ D) {c : List (FreeW W C)}
    {cs : FreeW W C} {y : C} (i : Var c cs) (v : Var cs.as y) :
    (Var.join FreeW.as (i.map (map F).obj) (v.map F.obj)).idx = (Var.join FreeW.as i v).idx := by
  induction i with
  | zero => simp [Var.join, Var.map]
  | succ i ih => simp [Var.join, Var.map, ih]

theorem idx_join_map_map_id {c : List (FreeW W C)} {cs : FreeW W C} {y : C}
    (i : Var c cs) (v : Var cs.as y) :
    (Var.join FreeW.as (i.map (map (𝟭 C)).obj) (v.map (𝟭 C).obj)).idx =
      (Var.join FreeW.as i v).idx :=
  idx_join_map (𝟭 C) i v

theorem eqToHom_map_id_flatten (c : FreeW W (FreeW W C)) :
    eqToHom (map_id_obj ((flatten (W := W)).obj c)) =
      eqToHom (map_flatten (𝟭 C) c) ≫ (flatten (W := W)).map (mapMapIdHom c) := by
  refine hom_ext fun y k ↦ ?_
  induction k using Var.flatMap_induction with
  | h i v =>
    dsimp only [comp_assign]
    rw [flatten_assign_join]
    dsimp only [mapMapIdHom, Wired.mapSrc_assign, Assign.mapSrc, Wired.refl_assign, Assign.refl]
    rw [eqToHom_assign_eq (map_id_obj _) v (v.map (𝟭 C).obj) (Var.idx_map _ _),
      eqToHom_assign_eq _ _ ((Var.join FreeW.as i v).map (𝟭 C).obj) (Var.idx_map _ _),
      eqToHom_assign_eq _ _ ((Var.join FreeW.as i v).map (𝟭 C).obj) (by
        rw [Var.idx_map]; exact (idx_join_map_map_id i v).symm)]
    simp

end FreeW

namespace WOperad

variable {W : WiringClass.{u}} {X : Type u} [Category.{v} X]

/-- The square of the identity morphism of operads. -/
def Hom.idSquare (M : WOperad.{u, v, w} W X) : Square M.hom M.hom (𝟭 X) (FreeW.map (𝟭 X)) where
  app f := M.hom.mpRight f (map_id_obj _)
  natL α f := M.hom.mpRight_mapL α f _
  natR f β := by
    simp only [Profunctor.mpRight]
    rw [← mapR_comp, ← mapR_comp, eqToHom_comp_map_id]

theorem Hom.mpLeft_mapSquare_idSquare (M : WOperad.{u, v, w} W X) {b : FreeW W X}
    {c : FreeW W (FreeW W X)} (f : (prof W M.hom).app b c) :
    (prof W M.hom).mpLeft (map_id_obj b) ((mapSquare (Hom.idSquare M)).app f) =
      (prof W M.hom).mapR (mapMapIdHom c) f := by
  refine prof_ext fun x k ↦ ?_
  simp only [Profunctor.mpLeft]
  rw [prof_mapL_assign, prof_mapR_assign,
    eqToHom_assign_eq (map_id_obj b) k (k.map (𝟭 X).obj) (Var.idx_map _ _)]
  dsimp only
  rw [mapSquare_assign_map]
  simp only [mapL_id]
  rfl

/-- The identity morphism of `W`-operads. -/
def Hom.id (M : WOperad.{u, v, w} W X) : Hom M M where
  functor := 𝟭 X
  map := Hom.idSquare M
  map_id a := M.hom.mpRight_rfl (M.id.app a)
  map_comp g f := by
    change M.hom.mpRight _ _ = M.hom.mpRight (M.comp.app (M.hom.mpRight g _) _) _
    rw [BinaryCell.mpRight_app, Hom.mpLeft_mapSquare_idSquare, M.comp.natR]
    simp only [Profunctor.mpRight]
    rw [← mapR_comp]
    exact congrArg (fun m ↦ M.hom.mapR m _) (eqToHom_map_id_flatten _)

end WOperad


namespace FreeW

variable {W : WiringClass.{u}} {C : Type u} [Category.{v} C] {D : Type u} [Category.{v'} D]
  {E : Type u} [Category.{v''} E]

theorem eqToHom_comp_map_comp (F : C ⥤ D) (G : D ⥤ E) {b b' : FreeW W C} (β : b ⟶ b') :
    eqToHom (map_comp_obj F G b) ≫ (map G).map ((map F).map β) =
      (map (F ⋙ G)).map β ≫ eqToHom (map_comp_obj F G b') := by
  refine hom_ext fun y k ↦ ?_
  induction k using Var.map_induction with
  | h j =>
    induction j using Var.map_induction with
    | h j =>
      dsimp only [comp_assign]
      rw [map_assign_map, map_assign_map,
        eqToHom_assign_eq (map_comp_obj F G b) _ ((assign β j).2.1.map (F ⋙ G).obj)
          (by simp only [Var.idx_map]),
        eqToHom_assign_eq (map_comp_obj F G b') _ (j.map (F ⋙ G).obj) (by simp only [Var.idx_map]),
        map_assign_map]
      simp

/-- The canonical morphism `(map (map (F ⋙ G))).obj c ⟶ (map (map G)).obj ((map (map F)).obj c)`,
with `eqToHom` components. -/
def mapMapCompHom (F : C ⥤ D) (G : D ⥤ E) (c : FreeW W (FreeW W C)) :
    (map (map (F ⋙ G))).obj c ⟶ (map (map G)).obj ((map (map F)).obj c) :=
  Wired.mapSrc (map (F ⋙ G)).obj (fun _ _ σ ↦ σ)
    (Wired.mapTgt (map G).obj (fun _ _ σ ↦ σ)
      (Wired.mapTgt (map F).obj (fun _ _ σ ↦ σ)
        (Wired.refl (R := fun c c' : FreeW W C ↦ (map (F ⋙ G)).obj c ⟶ (map G).obj ((map F).obj c'))
          (fun c ↦ eqToHom (map_comp_obj F G c)) (as := c.as))))

theorem mapMapCompHom_assign (F : C ⥤ D) (G : D ⥤ E) (c : FreeW W (FreeW W C))
    {cs : FreeW W C} (i : Var c.as cs) :
    assign (mapMapCompHom F G c) ((i.map (map F).obj).map (map G).obj) =
      ⟨(map (F ⋙ G)).obj cs, i.map (map (F ⋙ G)).obj, eqToHom (map_comp_obj F G cs)⟩ := by
  dsimp only [mapMapCompHom, Wired.mapSrc_assign, Assign.mapSrc, Wired.mapTgt_assign]
  rw [Assign.mapTgt_map, Assign.mapTgt_map]
  rfl

theorem eqToHom_map_comp_flatten (F : C ⥤ D) (G : D ⥤ E) (c : FreeW W (FreeW W C))
    (h : (map (F ⋙ G)).obj ((flatten (W := W)).obj c) =
      (flatten (W := W)).obj ((map (map G)).obj ((map (map F)).obj c))) :
    eqToHom h = eqToHom (map_flatten (F ⋙ G) c) ≫ (flatten (W := W)).map (mapMapCompHom F G c) := by
  refine hom_ext fun y k ↦ ?_
  induction k using Var.flatMap_induction with
  | h i v =>
    induction i using Var.map_induction with
    | h i =>
      induction i using Var.map_induction with
      | h i =>
        induction v using Var.map_induction with
        | h v =>
          induction v using Var.map_induction with
          | h v =>
            dsimp only [comp_assign]
            rw [flatten_assign_join, mapMapCompHom_assign]
            dsimp only
            rw [eqToHom_assign_eq (map_comp_obj F G _) _ (v.map (F ⋙ G).obj)
                (by simp only [Var.idx_map]),
              eqToHom_assign_eq h _ ((Var.join FreeW.as i v).map (F ⋙ G).obj)
                (by rw [Var.idx_map]; exact ((idx_join_map G _ _).trans
                  (idx_join_map F i v)).symm),
              eqToHom_assign_eq _ _ ((Var.join FreeW.as i v).map (F ⋙ G).obj)
                (by rw [Var.idx_map]; exact (idx_join_map (F ⋙ G) i v).symm)]
            simp

end FreeW

namespace WOperad

variable {W : WiringClass.{u}} {X : Type u} [Category.{v} X] {Y : Type u} [Category.{v'} Y]
  {Z : Type u} [Category.{v''} Z] {L : WOperad.{u, v, w} W X} {M : WOperad.{u, v', w'} W Y}
  {N : WOperad.{u, v'', w''} W Z}

/-- The square of a composite morphism of operads. -/
def Hom.compSquare (φ : Hom L M) (ψ : Hom M N) :
    Square L.hom N.hom (φ.functor ⋙ ψ.functor) (FreeW.map (φ.functor ⋙ ψ.functor)) where
  app f := N.hom.mpRight (ψ.map.app (φ.map.app f)) (map_comp_obj φ.functor ψ.functor _)
  natL α f := by
    rw [φ.map.natL, ψ.map.natL]
    exact N.hom.mpRight_mapL _ _ _
  natR f β := by
    rw [φ.map.natR, ψ.map.natR]
    simp only [Profunctor.mpRight]
    rw [← mapR_comp, ← mapR_comp, eqToHom_comp_map_comp]

theorem Hom.mpLeft_mapSquare_compSquare (φ : Hom L M) (ψ : Hom M N) {b : FreeW W X}
    {c : FreeW W (FreeW W X)} (f : (prof W L.hom).app b c) :
    (prof W N.hom).mpLeft (map_comp_obj φ.functor ψ.functor b)
        ((mapSquare (Hom.compSquare φ ψ)).app f) =
      (prof W N.hom).mapR (mapMapCompHom φ.functor ψ.functor c)
        ((mapSquare ψ.map).app ((mapSquare φ.map).app f)) := by
  refine prof_ext fun x k ↦ ?_
  induction k using Var.map_induction with
  | h j =>
    induction j using Var.map_induction with
    | h j =>
      simp only [Profunctor.mpLeft]
      rw [prof_mapL_assign, prof_mapR_assign,
        eqToHom_assign_eq _ _ (j.map (φ.functor ⋙ ψ.functor).obj) (by simp only [Var.idx_map])]
      dsimp only
      rw [mapSquare_assign_map, mapSquare_assign_map, mapSquare_assign_map,
        mapMapCompHom_assign]
      simp only [mapL_id]
      rfl

/-- The composite of morphisms of `W`-operads. -/
def Hom.comp (φ : Hom L M) (ψ : Hom M N) : Hom L N where
  functor := φ.functor ⋙ ψ.functor
  map := Hom.compSquare φ ψ
  map_id a := by
    change N.hom.mpRight (ψ.map.app (φ.map.app (L.id.app a))) _ = _
    rw [φ.map_id, ψ.map_id]
    exact N.hom.mpRight_rfl _
  map_comp g f := by
    change N.hom.mpRight (ψ.map.app (φ.map.app _)) _ =
      N.hom.mpRight (N.comp.app (N.hom.mpRight (ψ.map.app (φ.map.app g)) _) _) _
    rw [φ.map_comp, Square.app_mpRight, ψ.map_comp, BinaryCell.mpRight_app,
      Hom.mpLeft_mapSquare_compSquare, N.comp.natR]
    simp only [Profunctor.mpRight_mpRight]
    simp only [Profunctor.mpRight]
    rw [← mapR_comp]
    exact congrArg (fun m ↦ N.hom.mapR m _) (eqToHom_map_comp_flatten _ _ _ _)

end WOperad

end CategoryTheory
