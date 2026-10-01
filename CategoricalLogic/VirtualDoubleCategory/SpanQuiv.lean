/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/

module

public import CategoricalLogic.VirtualDoubleCategory.Basic

/-!
# The virtual double category of quiver spans

Quivers, prefunctors and quiver spans form a virtual double category. Its arrows from `r` to
`q` are the prefunctors `r ⥤q q`, composition of arrows is diagrammatic composition of
prefunctors, its cells with source a path `p` of spans and target a span `A` are the
multisquares `MultiSquare p A`, the identity cell on a span is the left unitor, and
substitution is n-ary horizontal composition (`SpanQuiv.hCompPath`) followed by vertical
composition. It lands one universe up.

## Main definitions

* `SpanQuiv.hom`, `SpanQuiv.id`, `SpanQuiv.comp`: the data.
* `SpanQuiv.virtualDoubleCategory`: the virtual double category.

## Implementation notes

The monoid laws are checked elementwise. The unit laws reduce to `hCompPath` of identity cells
being the identity (`SpanQuiv.hCompPath_mapHom_id`) and to splitting off an empty path
(`SpanQuiv.composePathCompInv_nil_leftUnitor`). Associativity reduces to `hCompPath` taking
concatenation of chains to binary horizontal composition (`SpanQuiv.hCompPath_comp`), which
rests on the coherence of splitting with the associator (`SpanQuiv.composePathCompInv_assoc`).
Sources of cells agree only up to equations of paths such as `Quiver.Path.comp_assoc`, so cells
are compared with heterogeneous equality.
-/

@[expose] public section

namespace CategoryTheory

universe u v

open QuiverSpan hiding Square
open KleisliSpan

namespace SpanQuiv

/-- The vertices of `Paths SpanQuiv` are those of `SpanQuiv`, so they are quivers too. Instance
resolution does not see through `Paths` on its own. -/
instance (C : Paths SpanQuiv.{u, v}) : Quiver.{max u v} C.α := SpanQuiv.str' C

/-- The Kleisli span of the virtual double category of quivers, prefunctors and quiver spans.
Its arrows from `r` to `q` are the prefunctors `r ⥤q q`, and its cells with source a path `p`
of spans and target a span `A` are the multisquares `MultiSquare p A`. -/
def hom : KleisliSpan SpanQuiv.{u, v} SpanQuiv.{u, v} where
  arr q r := r.α ⥤q q.α
  square A p f f' := MultiSquare p A f f'

/-- n-ary horizontal composition of cells. A chain of multisquares, whose targets spell out the
path `n` of spans and whose sources spell out the path of paths `m`, composes to one square from
the composite of the concatenation of `m` to the composite of `n`. -/
def hCompPath {q : SpanQuiv.{u, v}} {r : Paths SpanQuiv.{u, v}} {F : hom.arr q r} :
    {q' : SpanQuiv.{u, v}} → {r' : Paths SpanQuiv.{u, v}} →
    {n : Quiver.Path q q'} → {m : @Quiver.Path (Paths SpanQuiv.{u, v}) _ r r'} →
    {G : hom.arr q' r'} →
    PathSquare hom F n m G →
      QuiverSpan.Square (composePath ((Paths.flatten SpanQuiv.{u, v}).map m)) (composePath n) F G
  | _, _, _, _, _, .nil => QuiverSpan.Square.hId F
  | _, _, _, _, _, .cons c t =>
      QuiverSpan.Square.vComp (composePathCompInv _ _) (QuiverSpan.Square.hComp (hCompPath c) t)

/-- Composition in the virtual double category of spans: prefunctors compose on arrows, and a
chain of multisquares is substituted into a multisquare by n-ary horizontal composition
followed by vertical composition. -/
def comp : KleisliSpan.BinaryCell hom.{u, v} hom.{u, v} hom.{u, v} where
  map_arr | ⟨_, ⟨_, F, G⟩, ⟨⟨rfl⟩⟩⟩ => G ⋙q F
  map_square {_ _ _ _ _ _ a b} := fun s =>
    match a, b, s with
    | ⟨_, ⟨_, _, _⟩, ⟨⟨rfl⟩⟩⟩, ⟨_, ⟨_, _, _⟩, ⟨⟨rfl⟩⟩⟩, ⟨_, ⟨_, α, β⟩, ⟨⟨h⟩⟩⟩ =>
      h ▸ QuiverSpan.Square.vComp (hCompPath β) α

/-- Identities in the virtual double category of spans: identity prefunctors on arrows, and the
n-ary composite of a one-element path as the identity cell on a span. -/
def id : KleisliSpan.NullaryCell hom.{u, v} where
  map_arr {_ y} a :=
    match y, a with
    | _, ⟨⟨rfl⟩⟩ => 𝟭q _
  map_square {_ _ y y' A p a b} := fun s =>
    match y, y', p, a, b, s with
    | _, _, _, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩ => composePathToPath A

/-! ### Laws -/

open QuiverSpan.Square (vComp hComp)

theorem flatten_map_comp {r r' r'' : Paths SpanQuiv.{u, v}} (m₁ : Quiver.Path r r')
    (m₂ : Quiver.Path r' r'') :
    (Paths.flatten SpanQuiv.{u, v}).map (m₁.comp m₂) =
      ((Paths.flatten SpanQuiv.{u, v}).map m₁).comp ((Paths.flatten SpanQuiv.{u, v}).map m₂) :=
  CategoryTheory.composePath_comp m₁ m₂

/-- n-ary horizontal composition takes concatenation of chains to binary horizontal
composition. -/
theorem hCompPath_comp {q q' : SpanQuiv.{u, v}} {r r' : Paths SpanQuiv.{u, v}}
    {F : hom.arr q r} {G : hom.arr q' r'} {n₁ : Quiver.Path q q'}
    {m₁ : Quiver.Path r r'} (c : PathSquare hom F n₁ m₁ G) :
    {q'' : SpanQuiv.{u, v}} → {r'' : Paths SpanQuiv.{u, v}} → {H : hom.arr q'' r''} →
    {n₂ : Quiver.Path q' q''} → {m₂ : Quiver.Path r' r''} →
    (d : PathSquare hom G n₂ m₂ H) →
      vComp (hCompPath (c.comp d)) (composePathCompInv n₁ n₂) ≍
        vComp (composePathCompInv ((Paths.flatten _).map m₁) ((Paths.flatten _).map m₂))
          (hComp (hCompPath c) (hCompPath d))
  | _, _, _, _, _, .nil => HEq.rfl
  | _, _, _, _, _, .cons (p := n₂) (q := m₂) (f := P) d s =>
    (QuiverSpan.heq_dcongr
      (fun (Z : Quiver.Path (V := SpanQuiv.{u, v}) r _) (K : QuiverSpan.Square (composePath Z)
          (QuiverSpan.comp (composePath n₁) (composePath n₂)) F _) =>
        vComp (composePathCompInv Z P) (vComp (hComp K s) (QuiverSpan.associator _ _ _)))
      (flatten_map_comp m₁ m₂) (hCompPath_comp c d)).trans
    (QuiverSpan.heq_dcongr
      (fun (Z : Quiver.Path (V := SpanQuiv.{u, v}) r _) (K : QuiverSpan.Hom (composePath Z)
          (QuiverSpan.comp (composePath ((Paths.flatten _).map m₁))
            (QuiverSpan.comp (composePath ((Paths.flatten _).map m₂)) (composePath P)))) =>
        vComp K (hComp (hCompPath c) (hComp (hCompPath d) s)))
      (Quiver.Path.comp_assoc _ _ P) (composePathCompInv_assoc _ _ P))

/-- Substituting along a chain of composites is substituting twice. -/
theorem hCompPath_mapHom_comp {q q' : SpanQuiv.{u, v}} {r r' : Paths SpanQuiv.{u, v}}
    {a : (hom.comp hom).arr q r} {b : (hom.comp hom).arr q' r'} {n : Quiver.Path q q'}
    {L : Quiver.Path r r'} (βγ : PathSquare (hom.comp hom) a n L b) :
    hCompPath (βγ.mapHom comp) ≍
      vComp (hCompPath (PathSquare.unzip (PathSquare.unzip βγ).2.1).2.2.flatten)
        (hCompPath (PathSquare.unzip (PathSquare.unzip βγ).2.1).2.1) := by
  obtain ⟨_, ⟨_, _, _⟩, ⟨⟨ha⟩⟩⟩ := a
  cases ha
  induction βγ with
  | nil =>
    refine heq_of_eq (QuiverSpan.Square.ext (fun x => ?_) (fun {_ _ _ _ _ _ x y} t => ?_))
    · obtain ⟨⟨rfl⟩⟩ := x
      rfl
    · obtain ⟨⟨rfl⟩⟩ := x
      obtain ⟨⟨rfl⟩⟩ := y
      obtain ⟨⟨rfl⟩⟩ := t
      rfl
  | cons βγ t ih =>
    rename_i b c
    obtain ⟨_, ⟨_, _, _⟩, ⟨⟨hb⟩⟩⟩ := b
    cases hb
    obtain ⟨_, ⟨_, _, _⟩, ⟨⟨hc⟩⟩⟩ := c
    cases hc
    obtain ⟨M, ⟨p, β, γ⟩, ⟨⟨ht⟩⟩⟩ := t
    cases ht
    have hL := eq_of_heq (PathSquare.mapPath_heq_of_restrict_id _ (PathSquare.unzip βγ).2.2)
    have hZ := (congrArg (Paths.flatten SpanQuiv.{u, v}).map hL.symm).trans
      (Paths.flatten_assoc _).symm
    exact (composePathCompInv_hComp_heq hZ _ ih _).trans
      (QuiverSpan.Square.vComp_heq_vComp (congrArg composePath (flatten_map_comp _ M))
        (hCompPath_comp (PathSquare.unzip (PathSquare.unzip βγ).2.1).2.2.flatten γ)
        (hComp (hCompPath (PathSquare.unzip (PathSquare.unzip βγ).2.1).2.1) β)).symm

/-- Substituting identity cells along a path is the identity. -/
theorem hCompPath_mapHom_id {q q' : SpanQuiv.{u, v}} {r r' : Paths SpanQuiv.{u, v}}
    {a : (KleisliSpan.id SpanQuiv.{u, v}).arr q r} {b : (KleisliSpan.id SpanQuiv.{u, v}).arr q' r'}
    {n : Quiver.Path q q'} {L : Quiver.Path r r'}
    (c : PathSquare (KleisliSpan.id SpanQuiv.{u, v}) a n L b) :
    hCompPath (c.mapHom id) ≍ QuiverSpan.Square.id (composePath n) := by
  obtain ⟨⟨ha⟩⟩ := a
  cases ha
  induction c with
  | nil =>
    refine heq_of_eq (QuiverSpan.Square.ext (fun x => ?_) (fun {_ _ _ _ _ _ x y} t => ?_))
    · obtain ⟨⟨rfl⟩⟩ := x
      rfl
    · obtain ⟨⟨rfl⟩⟩ := x
      obtain ⟨⟨rfl⟩⟩ := y
      obtain ⟨⟨rfl⟩⟩ := t
      rfl
  | cons c t ih =>
    rename_i b d
    obtain ⟨⟨hb⟩⟩ := b
    cases hb
    obtain ⟨⟨hd⟩⟩ := d
    cases hd
    obtain ⟨⟨ht⟩⟩ := t
    cases ht
    have hL := eq_of_heq (PathSquare.mapPath_heq_of_restrict_id _ c)
    have hZ := (congrArg (Paths.flatten SpanQuiv.{u, v}).map hL.symm).trans
      (Paths.flatten_map_mapPath_of _)
    exact composePathCompInv_hComp_heq hZ _ ih _

/-- `comp` on an explicit element: substitution. -/
theorem comp_map_square_heq {x x' : SpanQuiv.{u, v}} {y y' : Paths SpanQuiv.{u, v}}
    {z z' : Paths (Paths SpanQuiv.{u, v})} {e : x ⟶ x'} {n : y ⟶ y'} {m : z ⟶ z'}
    {e' : Quiver.Path (V := SpanQuiv.{u, v}) z z'} {F : hom.arr x y} {F' : hom.arr x' y'}
    {G : hom.arr y z} {G' : hom.arr y' z'}
    (α : hom.square e n F F') (β : PathSquare hom G n m G')
    (h : (Paths.flatten SpanQuiv.{u, v}).map m = e') :
    comp.map_square (a := ⟨z, ⟨y, F, G⟩, ⟨⟨rfl⟩⟩⟩) (b := ⟨z', ⟨y', F', G'⟩, ⟨⟨rfl⟩⟩⟩)
      ⟨m, ⟨n, α, β⟩, ⟨⟨h⟩⟩⟩ ≍ vComp (hCompPath β) α := by
  subst h
  rfl

theorem one_mul : (whiskerRight id hom).comp comp = KleisliSpan.leftUnitor hom.{u, v} := by
  refine QuiverSpan.Square.ext (fun a => ?_) (fun {_ _ _ _ _ _ a b} u => ?_)
  · obtain ⟨_, ⟨_, ⟨⟨ha⟩⟩, _⟩, ⟨⟨ha'⟩⟩⟩ := a
    cases ha
    cases ha'
    rfl
  · obtain ⟨_, ⟨_, ⟨⟨ha⟩⟩, _⟩, ⟨⟨ha'⟩⟩⟩ := a
    cases ha
    cases ha'
    obtain ⟨_, ⟨_, ⟨⟨hb⟩⟩, _⟩, ⟨⟨hb'⟩⟩⟩ := b
    cases hb
    cases hb'
    obtain ⟨_, ⟨_, ⟨⟨hn⟩⟩, c⟩, ⟨⟨h⟩⟩⟩ := u
    cases hn
    obtain _ | ⟨c, t⟩ := c
    obtain _ | _ := c
    refine (comp_map_square_heq _ _ h).trans ?_
    refine HEq.trans ?_
      (hom.castSquare_heq ((Paths.flatten_map_of _).symm.trans h) rfl rfl t).symm
    refine (heq_of_eq (congrArg (vComp (composePathCompInv .nil _))
      (QuiverSpan.leftUnitor_naturality t))).trans ?_
    exact QuiverSpan.Square.vComp_heq_vComp (congrArg composePath (Quiver.Path.nil_comp _))
      (composePathCompInv_nil_leftUnitor _) t

theorem mul_one : (whiskerLeft hom id).comp comp = KleisliSpan.rightUnitor hom.{u, v} := by
  refine QuiverSpan.Square.ext (fun a => ?_) (fun {_ _ _ _ _ _ a b} u => ?_)
  · obtain ⟨_, ⟨_, _, ⟨⟨ha⟩⟩⟩, ⟨⟨ha'⟩⟩⟩ := a
    cases ha
    cases ha'
    rfl
  · obtain ⟨_, ⟨_, _, ⟨⟨ha⟩⟩⟩, ⟨⟨ha'⟩⟩⟩ := a
    cases ha
    cases ha'
    obtain ⟨_, ⟨_, _, ⟨⟨hb⟩⟩⟩, ⟨⟨hb'⟩⟩⟩ := b
    cases hb
    cases hb'
    obtain ⟨L, ⟨n, α, c⟩, ⟨⟨h⟩⟩⟩ := u
    have hL := eq_of_heq (PathSquare.mapPath_heq_of_restrict_id _ c)
    have hZ := (congrArg (Paths.flatten SpanQuiv.{u, v}).map hL.symm).trans
      (Paths.flatten_map_mapPath_of n)
    refine (comp_map_square_heq _ _ h).trans ?_
    refine HEq.trans ?_ (hom.castSquare_heq (hZ.symm.trans h) rfl rfl α).symm
    exact QuiverSpan.Square.vComp_heq_vComp (congrArg composePath hZ) (hCompPath_mapHom_id c) α

theorem mul_assoc :
    (associatorInv hom hom hom).comp ((whiskerRight comp hom).comp comp) =
      (whiskerLeft hom comp).comp comp.{u, v} := by
  refine QuiverSpan.Square.ext (fun a => ?_) (fun {_ _ _ _ _ _ a b} u => ?_)
  · obtain ⟨_, ⟨_, _, ⟨_, ⟨_, _, _⟩, ⟨⟨ha⟩⟩⟩⟩, ⟨⟨ha'⟩⟩⟩ := a
    cases ha
    cases ha'
    rfl
  · obtain ⟨_, ⟨_, F₁, ⟨_, ⟨_, G₁, _⟩, ⟨⟨ha⟩⟩⟩⟩, ⟨⟨ha'⟩⟩⟩ := a
    cases ha
    cases ha'
    obtain ⟨_, ⟨_, F₂, ⟨_, ⟨_, G₂, _⟩, ⟨⟨hb⟩⟩⟩⟩, ⟨⟨hb'⟩⟩⟩ := b
    cases hb
    cases hb'
    obtain ⟨L, ⟨n, α, βγ⟩, ⟨⟨h⟩⟩⟩ := u
    cases h
    have hL := eq_of_heq (PathSquare.mapPath_heq_of_restrict_id (Paths.flatten SpanQuiv.{u, v})
      (PathSquare.unzip βγ).2.2)
    have hZ := (Paths.flatten_assoc _).trans
      (congrArg (Paths.flatten SpanQuiv.{u, v}).map hL)
    refine (comp_map_square_heq
      (comp.map_square (a := ⟨_, ⟨_, F₁, G₁⟩, ⟨⟨rfl⟩⟩⟩) (b := ⟨_, ⟨_, F₂, G₂⟩, ⟨⟨rfl⟩⟩⟩)
        ⟨_, ⟨n, α, (PathSquare.unzip (PathSquare.unzip βγ).2.1).2.1⟩, ⟨⟨rfl⟩⟩⟩)
      (PathSquare.unzip (PathSquare.unzip βγ).2.1).2.2.flatten hZ).trans ?_
    refine HEq.trans ?_ (comp_map_square_heq α (βγ.mapHom comp) rfl).symm
    exact QuiverSpan.Square.vComp_heq_vComp (congrArg composePath hZ)
      (hCompPath_mapHom_comp βγ).symm α

/-- Quivers, prefunctors and quiver spans form a virtual double category. -/
def virtualDoubleCategory : VirtualDoubleCategory SpanQuiv.{u, v} where
  hom := hom
  id := id
  mul := comp
  one_mul := one_mul
  mul_one := mul_one
  mul_assoc := mul_assoc

end SpanQuiv

end CategoryTheory
