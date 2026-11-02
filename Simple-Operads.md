# Simple operads: T-operads in profunctors without virtual double categories

Status: proposal, awaiting decisions on the open questions in §10.
Step numbers follow the original request (steps 1–7; there is no step 5).

**Conventions.** Everything follows the orientation of `QuiverSpan`, which agrees with mathlib and
with Cruttwell–Shulman (CS):

* `Profunctor.{w} C D` (mathlib, `C ⥤ Dᵒᵖ ⥤ Type w`) is the proarrow `C ⇸ D`. Its elements
  `(P.obj x).obj (op y)` are heteromorphisms from `y : D` to `x : C`, covariant in `x` and
  contravariant in `y`.
* `QuiverSpan C D` has `arr x y` = arrows from `y` to `x`, the same orientation.
* A T-operad on `C` has `hom : Profunctor C (T.obj C)`. `hom x s` holds the operations with output
  `x` and input `s`. This is CS's `A₀ ⇸ T A₀`.

Lean snippets marked **(checked)** were typechecked against the current tree (Lean v4.35.0-rc2,
mathlib v4.35.0-rc2). Everything else is a sketch, so its names and signatures may change.

---

## 0. Summary

1. **A profunctor is a quiver span whose squares are propositions** (commuting squares). Cells of
   the VDC Prof, of any arity, are `QuiverSpan` squares out of the *unquotiented*
   `QuiverSpan.comp` of the profunctor spans. A square of the composite carries the middle
   morphisms, so preserving squares *is* naturality plus the wedge (dinaturality) condition, all
   at once. No `PathProd`, `WedgeRel`, `TensorProd`, `Cell`, quotient or new square type is
   needed. Checked: a binary cell built from the three elementwise conditions is a four-line
   term (§2).
2. **The "real" monad on Prof** acts on cells of every arity and preserves substitution. Stating
   that needs the n-ary `SpanQuiv` machinery (`composePath`, `hCompPath`, …), which is exactly
   the layer we want to keep out. Recommendation: a `Prof.Monad` that carries the full structure
   on cells of arity ≤ 2, since a T-operad never sees more. The complete notion is
   `VirtualDoubleCategory.Monad` on the Prof VDC from the sanity file. (§3, open question Q1.)
3. **No Kleisli VDC instance.** T-operads need only nullary, unary and binary Kleisli cells, just
   as `VirtualDoubleCategory` needed only `NullaryCell` and `BinaryCell`.
4. **Replace "the planar monad and the symmetric monad" with one family `T_W`.** Here `W` is a
   class of wirings: planar, symmetric, affine, relevant or cartesian. One set of proofs covers
   all of them, and step 7 needs the cartesian case anyway (Q2).
5. **Free operads: path products are the wrong shape.** `Term.lean`'s `Preterm` cannot express
   `f(x, g(y))`, a tree whose leaves sit at different depths. A *generic* T cannot carry a free
   construction (no positivity). For `T_W` and a signature over a type of sorts, the free
   T-operad is ordinary first-order terms plus a `W`-condition on how variables are used. These
   terms are canonical and computable, with decidable equality, and no structural quotient is
   needed. The only quotient is by the theory (Q4).
6. **Step 6c:** the word problem is undecidable in general (it already is for finitely presented
   groups). "Computable" therefore means a sound rewriting and normalisation engine, plus
   decision procedures for particular theories that are proved complete (§8).
7. **Step 7 as stated does not typecheck mathematically.** Distributivity duplicates a variable
   and `0·x = 0` deletes one, so R-algebras are not a symmetric-operad theory. Use the cartesian
   `T_W`. Also, mathlib's `MvPolynomial` is noncomputable (§9, Q5).

---

## 1. Feedback on the outlined steps

### Step 1 (the Prof ingredients)

* **Reusing `QuiverSpan` for bookkeeping is the key idea, and it goes further than "bookkeeping".**
  Define `P.span : QuiverSpan C D` with `square e e' a b := PLift (e·a = b·e')`. Then:
  * a `QuiverSpan.Square P.span Q.span F G` is a natural transformation `P ⇒ Q(F, G)` (the
    square condition *is* naturality);
  * a `QuiverSpan.Square (QuiverSpan.comp P.span Q.span) R.span F H` is a binatural
    transformation. A square of `comp` is `⟨m, s, t⟩` with a middle morphism `m`. With
    `e = 𝟙, e' = 𝟙` it says `(a·m, b) ↦ (a, m·b)`, which is the wedge condition, and with
    `m = 𝟙` it is naturality on either side;
  * a square out of `QuiverSpan.id C` is a natural family of elements (a nullary cell);
  * substitution of cells is `hComp` followed by `vComp`, both already in `QuiverSpan.lean`.

  So Prof is the full sub-VDC of `SpanQuiv` on the spans of profunctors. Its cells and their
  composition are literally those of `SpanQuiv`, so the sanity-file VDC instance can *inherit*
  its laws rather than reprove them (§2).
* **Don't define a new square type.** `Prof.Square P Q F G` should be an `abbrev` for
  `QuiverSpan.Square P.span Q.span F G`. Then `vComp`, `hComp`, `ext`, unitors and the
  associator come for free (the interchange law between `vComp` and `hComp` is `rfl`, checked).
* **Horizontal composition of profunctors is never formed** as a profunctor. The composite is a
  `QuiverSpan` and is only ever the *source* of a cell. This is what removes every quotient from
  the core.
* **No n-ary `MultiSquare` in the main code.** The main code needs arities 0, 1, 2 (and 3 only as
  the source of the associativity law). The n-ary `MultiSquare` and its composition belong in
  the sanity file, where they are `SpanQuiv.MultiSquare` of the image path.
* **What to extract from `Profunctor/`:** only the elementwise API of `Basic.lean` (left and right
  actions, their `id`/`comp`/commutation lemmas, transport along `eqToHom`). Rewrite it in span
  order (target first): the old `app X Y` puts the *source* first. Also, morphisms in `Type` are
  now `ConcreteCategory.hom`-wrapped, so thin wrappers keep `simp` usable. `Product.lean` and
  `Cells.lean` are superseded. `Discrete.lean` contains `sorry`s and is not needed: we use
  mathlib's `Discrete` and build profunctors by hand.
* **Renaming.** `Operad.lean` and `Term.lean` import `Profunctor.Basic`, so they have to move to
  `ProfunctorOld/` too (or to `Deprecated/`). `Deprecated/Prof.lean` defines
  `CategoryTheory.Prof`, which would clash with the `Prof` namespace below if it is ever imported.
  Delete it or rename it.

### Step 2 (the monad interface)

* "The actual real definition" of a monad on Prof is a functor of VDCs (acting on cells of
  *every* arity and preserving substitution), two transformations and the monad laws. In our
  encoding that means stating "T commutes with substitution" for chains of multisquares. That is
  `SpanQuiv.hCompPath` with all its coherence (`composePathCompInv_assoc`, …), and every instance
  would have to prove it. This is precisely the VDC layer we are trying not to depend on.
* There are two honest options:
  * **(A, recommended)** `Prof.Monad`: the vertical part is mathlib's `Monad Cat` (strict, as in
    CS). The horizontal part is `T` on profunctors and on cells of arity 0, 1, 2, the cell
    components `ηCell` and `μCell`, and *all* the laws among them that stay within arity ≤ 2
    (sources of arity ≤ 3). This is the real structure restricted to what T-operads and their
    morphisms can see, not a weakened version of it. Prof has composites (coends), and by CS's
    remark functors of VDCs between VDCs with composites are lax functors, determined by data in
    arity ≤ 2 with coherence in arity 3. So nothing essential is lost; we just never name it.
  * **(B)** Put the Prof VDC (sanity file) into the main code and use the existing
    `VirtualDoubleCategory.Monad`. It is principled and short to *state*, but every elementwise
    computation and every instance would go through `PathSquare`, `hCompPath` and casts along
    `Paths.flatten_*`.
* **Transport is unavoidable.** For any monad on `Cat` built from lists, `μ ∘ η = 𝟭` and
  `T 𝟭 = 𝟭` are propositional (`[s].flatten = s ++ []`). Laws therefore compare cells over
  functors that are only propositionally equal. Use the mathlib idiom: a transport cell
  `Prof.eqToSquare` built from `eqToHom`, so that laws are honest `=` of cells. This is the
  analogue of `KleisliSpan.Square.id` transporting along `Prefunctor.mapPath_id`. Avoid `HEq` in
  statements.
* **Normality is a separate concern.** Step 4a needs `T(U_C) ≅ U_{TC}` (CS assume "normal"
  there). Make it a mixin `[T.Normal]`. It holds definitionally for `T_W`.

### Step 3 (Kleisli arrows)

* **No full VDC instance for the Kleisli construction.** Its associativity is the biggest proof
  in CS ("too large a diagram to show here"), it needs T on n-ary cells, and nothing downstream
  consumes it. What we need is a vocabulary of Kleisli cells (unary `KlSquare`, nullary over
  `(𝟭, η)`, binary over `(𝟭, μ)`) and Kleisli horizontal composition of *unary* cells
  (`φ ⊙ Tψ`), which T-operad morphisms use.
* Use plain `Square`s over `η` and `μ` rather than `Hom`s out of restricted companions.
  `PathsKleisli` needed the companion trick because `Paths.map (𝟭q _)` is not `𝟭q _`. Here the
  vertical sides are functors, and the targets are profunctors whose squares are propositions,
  so the simpler form costs nothing.
* **3a, algebras:** mathlib already has them. The Eilenberg–Moore algebras of the vertical monad,
  `T.toMonad.Algebra`, are exactly the strict T-algebras in `Cat`. This is free.
* **3b:** see summary item 4 and §5. One family `T_W` instead of two monads, with planar and
  symmetric as instances (cartesian is needed for step 7).
* **3c:** strict algebras of `T_planar` are *strict* monoidal categories. Mathlib's
  `MonoidalCategory` is weak and has no strictness class. The direction algebra → monoidal
  category (or → symmetric monoidal category) is easy: the structure isomorphisms are `eqToIso`,
  and the braiding is `a` applied to the swap. The converse is easy for the planar case under
  strictness hypotheses, but **hard for the symmetric case**: a T_sym-algebra structure on a
  symmetric monoidal category needs the symmetric coherence theorem (the morphism induced by a
  permutation is well defined), which mathlib does not have. Pseudo-algebras (all monoidal
  categories) need 2-monad machinery and coherence, so out of scope for now (Q3).

### Step 4 (T-operads)

* This step is straightforward in the new setting: a T-operad is `(hom, one, mul)` plus three
  laws, all plain functions and propositions, so computability is automatic.
* Add **`Operad.comap`** (restriction along a functor `D ⥤ C`). Endomorphism operads, sub-operads
  on chosen objects and the comparison in step 7 are all restrictions.
* **4a** is CS's theorem `oplax-alg` in the strict case: `hom x s := (a s ⟶ x)`. It needs
  `[T.Normal]`. Payoff: endomorphism operads, hence *models* of theories, as T-operad maps (§7).

### Step 6 (free operads, terms, deduction)

* **Path products give uniform-depth trees.** A depth-n element of the n-fold Kleisli composite
  applies an operation to *every* input at every layer. The free monoid in `Kl(T)` is *not*
  `Σₙ A^{⊙n}`, because `T` does not preserve coproducts of profunctors (a list of mixed elements
  is not a sum of lists). It is the initial algebra of `X ↦ U_K ⊕ (Σ ⊙_K X)`, so trees with a
  variable constructor. `Term.lean`'s `Preterm` (layers of `T S`) has exactly this defect.
* For a *generic* `T` that inductive type cannot be written (Lean cannot see that `T` is
  positive), and the ω-colimit alternative is neither computable nor short. So the free
  construction should be for `T_W`.
* For `T_W` and a signature `Σ₀ : S → List S → Type` over a type of sorts, the free
  `T_W`-operad is: terms in context with variables at the leaves, subject to "the leaf → variable
  map lies in `W`". Planar: every variable used once, in order. Symmetric: every variable once.
  Affine: at most once. Relevant: at least once. Cartesian: no condition, so ordinary
  first-order terms. This representation is *canonical*, so the "structural relations" are
  trivial and no quotient is needed. If profunctor signatures with non-trivial actions are
  wanted later, their free operad is a quotient of this one, and that quotient is the only
  non-computable part (Q4).
* **6a:** an equation is a context, a sort and two terms in it. A theory is a `Set` of equations.
  Terms modulo a theory form the smallest operadic congruence containing it, and the quotient is
  again a `T_W`-operad: the operad presented by `(Σ₀, E)`. Its universal property is "models of
  `E`".
* **6b:** without equations, the free operad *is* the term operad, so the universal property is
  proved directly by recursion on terms. With equations, the quotient has the expected universal
  property relative to `E`.
* **6c:** see summary item 6 and §8. Note which theories live where. Monoids are planar (all
  axioms are order-preserving and linear) and commutative monoids are symmetric. Groups, rings
  and R-algebras are cartesian: `x⁻¹·x = e` uses `x` twice on the left and not at all on the
  right.

### Step 7 (R-algebras)

* As noted, the R-algebra axioms are not linear, so this is a **cartesian** theory (a clone or
  Lawvere theory), not a symmetric operad.
* "The symmetric monoidal category of polynomial R-algebras with ⊗": for *commutative* algebras
  ⊗ is the coproduct, so this category is cocartesian, and its opposite is the Lawvere theory of
  commutative R-algebras. The operad attached to it is the co-endomorphism operad of `R[x]`,
  `n ↦ Hom(R[x], R[x]^{⊗n}) = R[x₁,…,xₙ]`, with substitution as composition. That is the clone of
  polynomials. Via 4a it is the restriction to `1` of the `T_cart`-operad of the Lawvere theory
  `L_R`, a strict `T_cart`-algebra: objects `ℕ`, `n × m = n + m`, and morphisms `n → m` are
  `m`-tuples of polynomials in `n` variables. `L_R` is the opposite of the category of polynomial
  algebras, and it has to be this side because `T_cart`-algebras have finite *products*.
* Computability: `MvPolynomial` is `noncomputable`. The comparison theorem can use it, but the
  measuring computations (7a) need a computable polynomial normal form: our own sparse
  representation, or Lean core's `Lean.Grind.CommRing.Poly` (ℤ coefficients, computable
  `Expr.toPoly` with soundness `Expr.denote_toPoly`).

---

## 2. Stage 1: Prof without composites (`CategoricalLogic/Prof/Basic.lean`)

Target: about 150 lines.

```lean
/-- A profunctor `P : C ⇸ D` as a quiver span from `C` to `D`. Its arrows from `y` to `x` are
the elements of `P` at `x` and `y`, and its squares are the commuting squares, which are
propositions. -/
def Profunctor.span (P : Profunctor.{w} C D) : QuiverSpan C D where       -- (checked)
  arr x y := (P.obj x).obj (op y)
  square e e' a b := PLift ((P.map e).app (op _) a = (P.obj _).map e'.op b)

namespace Prof

/-- Cells with unary source: natural transformations `P ⇒ Q(F, G)`. -/
abbrev Square (P : Profunctor.{w} C D) (Q : Profunctor.{w} C' D') (F : C ⥤ C') (G : D ⥤ D') :=
  QuiverSpan.Square P.span Q.span F.toPrefunctor G.toPrefunctor          -- (checked)

/-- Cells with nullary source on `C`: natural families of elements `Q(F x, G x)`. -/
abbrev NullaryCell (Q : Profunctor.{w} D D') (F : C ⥤ D) (G : C ⥤ D') :=
  QuiverSpan.Square (QuiverSpan.id C) Q.span F.toPrefunctor G.toPrefunctor  -- (checked)

/-- Cells with binary source: binatural transformations. -/
abbrev BinaryCell (P : Profunctor.{w} C D) (Q : Profunctor.{w} D E) (R : Profunctor.{w} C' E')
    (F : C ⥤ C') (H : E ⥤ E') :=
  QuiverSpan.Square (QuiverSpan.comp P.span Q.span) R.span F.toPrefunctor H.toPrefunctor  -- (checked)
```

Constructors from elementwise data are the user-facing API. A binary cell over identity functors
**(checked)**:

```lean
def BinaryCell.mk' {P : Profunctor.{w} C D} {Q : Profunctor.{w} D E} {R : Profunctor.{w} C E}
    (app : ∀ {x y z}, (P.obj x).obj (op y) → (Q.obj y).obj (op z) → (R.obj x).obj (op z))
    (natL : ∀ {x x' y z} (f : x ⟶ x') a (b : (Q.obj y).obj (op z)),
      app ((P.map f).app _ a) b = (R.map f).app _ (app a b))
    (wedge : ∀ {x y y' z} (g : y ⟶ y') (a : (P.obj x).obj (op y')) (b : (Q.obj y).obj (op z)),
      app ((P.obj x).map g.op a) b = app a ((Q.map g).app _ b))
    (natR : ∀ {x y z z'} (h : z ⟶ z') (a : (P.obj x).obj (op y)) b,
      app a ((Q.obj y).map h.op b) = (R.obj x).map h.op (app a b)) :
    QuiverSpan.Hom (QuiverSpan.comp P.span Q.span) R.span where
  map_arr a := app a.2.1 a.2.2
  map_square {x x' z z' e e' a b} s := by
    obtain ⟨y, a₁, a₂⟩ := a
    obtain ⟨y', b₁, b₂⟩ := b
    obtain ⟨m, ⟨s₁⟩, ⟨s₂⟩⟩ := s
    exact ⟨(natL e a₁ a₂).symm.trans <| (congrArg (app · a₂) s₁).trans <|
      (wedge m b₁ a₂).trans <| (congrArg (app b₁) s₂).trans (natR e' b₁ b₂)⟩
```

(The final version generalises this to sides `F` and `H`, and the proof will be a term, per the
style guide.) The rest of the file:

```lean
/-- Cells into a profunctor are determined by their action on arrows: squares are propositions. -/
theorem ext {K : QuiverSpan C D} {s t : QuiverSpan.Square K Q.span F G}
    (h : ∀ {x y} (a : K.arr x y), s.map_arr a = t.map_arr a) : s = t

/-- The identity cell of `P`, transported along equalities of functors. Laws of monads and of
T-operads compare cells over functors that are only propositionally equal; this is the only
transport we use. -/
def eqToSquare (P : Profunctor.{w} C D) {F : C ⥤ C} {G : D ⥤ D}
    (hF : 𝟭 C = F) (hG : 𝟭 D = G) : Square P P F G

/-- Elementwise accessors (`Square.app`, `NullaryCell.app`, `BinaryCell.app`) and their
naturality lemmas, `NullaryCell.mk'`, `Square.mk'`. -/
```

Also extracted from `ProfunctorOld/Basic.lean`, in span order: `Profunctor.lmap`/`rmap` (the
two actions on elements), `lmap_id`, `lmap_comp`, `lmap_rmap`, `lmap_eqToHom` (transport as a
cast), plus the hom profunctor `Profunctor.id C` (mathlib's `yoneda`) with its identity
`NullaryCell` and composition `BinaryCell`. The latter two are needed for normality and 4a.

### The sanity file (`Sanity/ProfVDC.lean`, separate `lean_lib`, not a default target)

```lean
/-- Bundled categories, with profunctors as edges. -/
structure ProfCat where
  α : Type u
  [str : Category.{u} α]

instance : Quiver ProfCat.{u} where Hom C D := Profunctor.{u} C.α D.α

/-- Underlying quivers and spans. `SpanQuiv` puts apices one universe above edges, hence
`Profunctor.ulift` (mathlib). -/
def ProfCat.toSpanQuiv : ProfCat.{u} ⥤q SpanQuiv.{u+1, u}

/-- n-ary cells are the multisquares of the image path. Their composition is that of `SpanQuiv`. -/
abbrev MultiSquare (p : Quiver.Path C D) (Q : C ⟶ D) F G :=
  SpanQuiv.MultiSquare (ProfCat.toSpanQuiv.mapPath p) (ProfCat.toSpanQuiv.map Q) F G

/-- General construction (could live in `VirtualDoubleCategory/`): restrict a VDC along a
prefunctor of its proarrow quiver. Cells between images are all cells of `V`, so the laws are
inherited. -/
def VirtualDoubleCategory.comap (V : VirtualDoubleCategory Q) (ι : R ⥤q Q) :
    VirtualDoubleCategory R

/-- Categories, prefunctors and profunctors: the full sub-VDC of `SpanQuiv` on profunctor spans. -/
def Prof.virtualDoubleCategory := SpanQuiv.virtualDoubleCategory.comap ProfCat.toSpanQuiv

/-- Optional: the wide sub-VDC on functors (arrows restricted by a predicate closed under
identities and composition). -/
def VirtualDoubleCategory.wide ...

/-- Check that `Prof.BinaryCell` agrees with 2-ary multisquares. -/
def binaryCellEquiv : Prof.BinaryCell P Q R F H ≃ MultiSquare [P, Q] R F H
```

The universe catch: `Profunctor.span` must allow its square universe to be chosen
(`ULift (PLift _)`) so that the lifted spans land in `SpanQuiv`'s pinned universe. Main code
uses universe 0 for squares.

---

## 3. Stage 2: the monad (`CategoricalLogic/Prof/Monad.lean`)

Recommendation (A). Data skeleton **(checked)**, laws sketched:

```lean
/-- A monad on the virtual double category of categories, functors and profunctors, on cells
of arity at most two. A T-operad sees nothing else. The vertical part is mathlib's monad on
`Cat`. -/
structure Prof.Monad extends CategoryTheory.Monad Cat.{u, u} where
  /-- `T` on profunctors. -/
  prof {C D : Cat.{u, u}} : Profunctor.{u} C D → Profunctor.{u} (obj C) (obj D)
  /-- `T` on cells. -/
  mapSquare {P Q} {F : C ⟶ C'} {G : D ⟶ D'} :
    Square P Q F.toFunctor G.toFunctor → Square (prof P) (prof Q) (map F).toFunctor (map G).toFunctor
  mapNullary {Q} {F : C ⟶ D} {G : C ⟶ D'} :
    NullaryCell Q F.toFunctor G.toFunctor →
      NullaryCell (prof Q) (map F).toFunctor (map G).toFunctor
  mapBinary {P Q R} {F : C ⟶ C'} {H : E ⟶ E'} :
    BinaryCell P Q R F.toFunctor H.toFunctor →
      BinaryCell (prof P) (prof Q) (prof R) (map F).toFunctor (map H).toFunctor
  /-- The cell components of `η` and `μ`. -/
  ηCell (P : Profunctor.{u} C D) : Square P (prof P) (η.app C).toFunctor (η.app D).toFunctor
  μCell (P : Profunctor.{u} C D) :
    Square (prof (prof P)) (prof P) (μ.app C).toFunctor (μ.app D).toFunctor
  -- Laws. `⟦_⟧` denotes transport by `eqToSquare` along the named law of `Monad Cat`.
  -- (F) functoriality (uses `map_id`, `map_comp`):
  mapSquare_id      : mapSquare (Square.id P) = ⟦⟧ (eqToSquare (prof P) …)
  mapSquare_vComp   : mapSquare (s.vComp t) = ⟦⟧ ((mapSquare s).vComp (mapSquare t))
  mapNullary_vComp  : mapNullary (ν.vComp t) = ⟦⟧ ((mapNullary ν).vComp (mapSquare t))
  mapBinary_vComp   : mapBinary (β.vComp t) = ⟦⟧ ((mapBinary β).vComp (mapSquare t))
  mapBinary_hComp   : mapBinary ((s.hComp s').vComp β)
                        = ⟦⟧ (((mapSquare s).hComp (mapSquare s')).vComp (mapBinary β))
  -- (N) naturality of `ηCell` and `μCell` with respect to unary, nullary and binary cells
  --     (uses `η.naturality`, `μ.naturality`):
  ηCell_natural     : s.vComp (ηCell Q) = ⟦⟧ ((ηCell P).vComp (mapSquare s))
  ηCell_nullary     : ν.vComp (ηCell Q) = ⟦⟧ (mapNullary ν)    -- after `hId`
  ηCell_binary      : β.vComp (ηCell R) = ⟦⟧ (((ηCell P).hComp (ηCell Q)).vComp (mapBinary β))
  μCell_natural, μCell_nullary, μCell_binary : …
  -- (M) monad laws on cells (uses `left_unit`, `right_unit`, `assoc`):
  ηCell_μCell       : (ηCell (prof P)).vComp (μCell P) = eqToSquare (prof P) …
  mapSquare_ηCell_μCell : (mapSquare (ηCell P)).vComp (μCell P) = eqToSquare (prof P) …
  μCell_assoc       : (μCell (prof P)).vComp (μCell P) = ⟦⟧ ((mapSquare (μCell P)).vComp (μCell P))
```

Where each group is used:

| laws | used by |
|---|---|
| (F) `mapSquare_id`, `mapSquare_vComp` | the category of T-operads (identity and composition of morphisms) |
| (F) the rest, (N), `Normal` | 4a (algebra → operad) |
| (M) | 4a, and the free-operad comparison maps |

Add a law only when a proof needs it, and keep this table current.

```lean
/-- `T` preserves hom profunctors: `T(U_C) ≅ U_{TC}`, compatibly with identities, composition,
`T` on functors, `η` and `μ`. Every example in this project satisfies this by definition. -/
class Prof.Monad.Normal (T : Prof.Monad) where
  norm (C : Cat) : Square (T.prof (Profunctor.id C)) (Profunctor.id (T.obj C)) (𝟭 _) (𝟭 _)
  normInv (C : Cat) : …
  norm_idCell, norm_compCell, norm_fmap, norm_ηCell, norm_μCell : …
```

Universes: start with everything at one universe `u` (`Cat.{u, u}`, `Profunctor.{u}`), as
`SpanQuiv` does. Normality needs the profunctor universe to equal the hom universe anyway.
Generalise later if a use appears.

Helper abbreviations: `T.fmap F := (T.map F).toFunctor`, `T.η' C := (T.η.app C).toFunctor`,
`T.μ' C := (T.μ.app C).toFunctor`. Also derived maps that absorb the transport
`T.fmap (𝟙 C) = 𝟭`, for cells whose left side is `𝟭` (as in every T-operad):
`mapBinaryId : BinaryCell P Q R (𝟭 C) H → BinaryCell (prof P) (prof Q) (prof R) (𝟭 _) (T.fmap H)`.

---

## 4. Stage 3: Kleisli cells and algebras (`CategoricalLogic/Prof/Kleisli.lean`, `Algebra.lean`)

Kleisli proarrows need no new type: `Profunctor C (T.obj D)`.

```lean
/-- Unary Kleisli cells: squares whose right side is `T` of a functor. -/
abbrev KlSquare (M : Profunctor C (T.obj D)) (N : Profunctor C' (T.obj D')) (F : C ⟶ C')
    (G : D ⟶ D') := Square M N F.toFunctor (T.fmap G)

/-- Kleisli horizontal composition of unary cells: `φ ⊙ Tψ`, as a cell between binary sources. -/
def KlSquare.hCompKl (φ : KlSquare M N F G) (ψ : KlSquare M' N' G H) :
    QuiverSpan.Square (M.span.comp (T.prof M').span) (N.span.comp (T.prof N').span) F (T.fmap (T.fmap H))
  := φ.hComp (T.mapSquare ψ)
```

The nullary and binary Kleisli cells *are* `NullaryCell M (𝟭 C) (T.η' C)` and
`BinaryCell M (T.prof N) K (𝟭 C) (T.μ' E)`. They get no new names unless the T-operad file
reads better with them.

**3a.** `abbrev Prof.Monad.Algebra (T : Prof.Monad) := T.toMonad.Algebra` (mathlib), with
mathlib's morphisms.

---

## 5. Stage 3b: the free `W`-monoidal category monads (`CategoricalLogic/FreeMonoidal/`)

One construction parametrised by a class of wirings. A morphism `ys ⟶ xs` of `T_W C` assigns to
every entry of `xs` an entry of `ys` and a morphism between them; `W` says which assignments are
allowed. This is the "free category with strictly associative finite products" (CS, example
`free-safp`) cut down to the wirings in `W`. Planar: only identity wirings, giving the free
strict monoidal category. Symmetric: bijections. Cartesian: all functions.

The design uses de Bruijn style variables, so `T_W` on functors (`List.map`), `μ` (`List.flatten`)
and composition are all *structural*, with no index casts. Core definitions **(checked, including
an `#eval`)**:

```lean
/-- A variable of sort `a` in the context `l`: de Bruijn indices as data. -/
inductive Var {α : Type u} : List α → α → Type u
  | zero {a : α} {l : List α} : Var (a :: l) a
  | succ {a b : α} {l : List α} : Var l a → Var (b :: l) a

/-- Dependent tuples over a list. (`List.TProd` is a `def` by `foldr`, so it cannot host the
nested inductive of terms in §8.) -/
inductive Tup {α : Type u} (R : α → Type v) : List α → Type (max u v)
  | nil : Tup R []
  | cons {a : α} {l : List α} : R a → Tup R l → Tup R (a :: l)

/-- Raw heteromorphisms from `ys` to `xs`: every entry of `xs` picks an entry of `ys` and an
element of `P` between them. -/
abbrev RawHet (P : C → D → Type w) (xs : List C) (ys : List D) :=
  Tup (fun x => Σ y, Var ys y × P x y) xs

/-- Composition along a binary cell, structurally. -/
def RawHet.comp (β : ∀ {x y z}, P x y → Q y z → R x z)
    (f : RawHet P xs ys) (g : RawHet Q ys zs) : RawHet R xs zs :=
  f.map fun ⟨_, v, p⟩ => let ⟨z, v', q⟩ := g.get v; ⟨z, v', β p q⟩

/-- A class of wirings, with closure properties. -/
structure Wiring where
  Allowed : ∀ {m n : ℕ}, (Fin m → Fin n) → Prop
  id_mem (n : ℕ) : Allowed (id : Fin n → Fin n)
  comp_mem {f : Fin l → Fin m} {g : Fin m → Fin n} : Allowed f → Allowed g → Allowed (g ∘ f)
  -- to add: closure under block substitution (needed for `μ`), stated through
  -- `finSigmaFinEquiv`, and decidability `[∀ f, Decidable (Allowed f)]` (needed in §8).

def Wiring.planar : Wiring where
  Allowed {m n} f := ∃ h : m = n, f = Fin.cast h
  …
def Wiring.symmetric : Wiring where Allowed f := Function.Bijective f; …
def Wiring.cartesian : Wiring where Allowed _ := True; …
-- also `affine` (injective) and `relevant` (surjective).
```

Then, sketched:

```lean
/-- Heteromorphisms with an allowed wiring. -/
def Het (W : Wiring) (P : C → D → Type w) (xs ys) := { f : RawHet P xs ys // W.Allowed f.wiring }

/-- The free `W`-monoidal category on `C`. Objects are lists, and morphisms `ys ⟶ xs` are
heteromorphisms of the hom family. Its homs are *definitionally* `T_W` of the hom profunctor,
which makes `T_W` normal by `rfl`. -/
def FreeW (W : Wiring) (C : Type u) := List C
instance : Category (FreeW W C) where
  Hom ys xs := Het W (fun x y => y ⟶ x) xs ys
  comp g f := Het.comp (fun p q => q ≫ p) f g
  …

/-- `T_W` on a profunctor: heteromorphisms of its elements, acted on by composition. -/
def Profunctor.freeW (P : Profunctor C D) : Profunctor (FreeW W C) (FreeW W D)

/-- `T_W` on a binary cell is `Het.comp` along it; on unary cells `Het.map`; on nullary cells
the identity tuple; `μ` is `Het.flatten`; `η` is the one-entry tuple. -/
def Prof.Monad.freeW (W : Wiring) : Prof.Monad
instance : (Prof.Monad.freeW W).Normal
```

All laws come from a handful of `RawHet` lemmas: associativity and unitality of `comp` relative
to the cells, `comp` against `map`, `flatten` against `comp`, and the wiring of each. The
category structure, the profunctor actions and *every* `Prof.Monad` law are instances of these.

The known pain point is the `Cat`-level equalities with lists. `T_W (F ⋙ G) = T_W F ⋙ T_W G`
and `μ ∘ η = 𝟭` hold on objects only propositionally (`List.map_map`, `List.flatten_singleton`
and so on), so they are `Functor.ext` proofs with `eqToHom`. This is a one-time cost; hand it to
Aristotle if it fights back. (Fin-tuple objects make functoriality definitional but the monad
laws far worse, so lists win.)

---

## 6. Stage 3c: algebras are (symmetric) strict monoidal categories (`FreeMonoidal/Monoidal.lean`)

```lean
/-- A strict `T_planar`-algebra is a monoidal category: `x ⊗ y := a [x, y]`, `f ⊗ g := a.map [f, g]`,
with associator and unitors `eqToIso` (algebra laws, plus `a [z] = z` from the unit law). -/
def Prof.Monad.Algebra.monoidalCategory (A : (freeW .planar).Algebra) : MonoidalCategory A.A

theorem … : α_ x y z = eqToIso _      -- strictness, stated as the structure isomorphisms being `eqToIso`

/-- For `T_sym`, `β_ x y := a (swap)`; symmetry and the hexagons follow from functoriality of `a`. -/
def … (A : (freeW .symmetric).Algebra) : SymmetricCategory A.A

/-- Converse for the planar case: a monoidal category whose associator and unitors are `eqToIso`
gives a strict `T_planar`-algebra. -/
def MonoidalCategory.toPlanarAlgebra … (h : strictness) : (freeW .planar).Algebra
```

The symmetric converse needs symmetric coherence and is postponed (Q3).

---

## 7. Stage 4: T-operads (`CategoricalLogic/Prof/Operad.lean`, `AlgebraOperad.lean`)

Data skeleton **(checked)**, laws sketched:

```lean
/-- A T-operad (CS: a T-monoid) on the category `C`: a monoid in the Kleisli double category. -/
structure Prof.Monad.Operad (T : Prof.Monad) (C : Cat.{u, u}) where
  /-- `hom x s`: operations with output `x` and input `s`. -/
  hom : Profunctor.{u} C (T.obj C)
  /-- The identity operations. -/
  one : NullaryCell hom (𝟭 C) (T.η' C)
  /-- Substitution. -/
  mul : BinaryCell hom (T.prof hom) hom (𝟭 C) (T.μ' C)
  one_mul : (one.hComp (T.ηCell hom)).vComp mul
              = (QuiverSpan.leftUnitor hom.span).vComp (eqToSquare hom rfl (T.left_unit' C))
  mul_one : (QuiverSpan.rightUnitorInv hom.span).vComp
              (((Square.id hom).hComp (T.mapNullaryId one)).vComp mul) = eqToSquare hom rfl …
  mul_assoc : (QuiverSpan.associator _ _ _).vComp (((Square.id hom).hComp (T.mapBinaryId mul)).vComp mul)
              = ⟦T.assoc⟧ ((mul.hComp (T.μCell hom)).vComp mul)

/-- Elementwise: `M.unit x`, `M.comp f g`, and lemmas `comp_unit`, `unit_comp`, `comp_assoc`
with `eqToHom` actions. These are what the term calculus is written against. -/

/-- Morphisms of T-operads (CS: T-monoid homomorphisms). -/
structure Operad.Hom (M : T.Operad C) (N : T.Operad D) where
  functor : C ⟶ D
  map : Square M.hom N.hom functor.toFunctor (T.fmap functor)
  map_one : M.one.vComp map = ⟦T.η.naturality⟧ ((QuiverSpan.Square.hId _).vComp N.one)
  map_mul : M.mul.vComp map = ⟦T.μ.naturality⟧ ((map.hComp (T.mapSquare map)).vComp N.mul)

/-- Identity and composition. Uses only (F) of `Prof.Monad`. -/
instance : Category (Σ C, T.Operad C)      -- or a bundled `OperadCat T`

/-- Restriction along a functor: `(M.comap F).hom x s := M.hom (F x) (T F s)`. -/
def Operad.comap (M : T.Operad C) (F : D ⟶ C) : T.Operad D
```

**4a**, sketched:

```lean
/-- CS, theorem `oplax-alg`, strict case: an algebra `a : T A ⥤ A` gives the T-operad
`hom x s := (a s ⟶ x)`, with unit `eqToHom (a (η x) = x)` and `mul f g := a.map (norm (T r g)) ≫ f`,
where `r` is the restriction cell `hom ⇒ U_A` over `(𝟭, a)`. -/
def Prof.Monad.Algebra.toOperad [T.Normal] (A : T.Algebra) : T.Operad A.A

/-- Algebra morphisms give T-operad morphisms (functoriality of 4a). -/
def Prof.Monad.Algebra.Hom.toOperadHom …

/-- The endomorphism T-operad of a family of types `X : S → Type u`. The strict
`T_W`-algebra is the category with objects `List S` and morphisms `Γ ⟶ Δ` the functions
`Tup X Γ → Tup X Δ` (strict finite products by concatenation, so it is an algebra for every `W`).
Restricting along `x ↦ [x]` gives `hom x Γ ≅ (Tup X Γ → X x)`. Models of a theory are T-operad
morphisms into it. -/
def endOperad (X : S → Type u) : (freeW W).Operad (Cat.of (Discrete S))
```

---

## 8. Stage 6: terms, theories, deduction (`CategoricalLogic/Term/`)

### 6. Signatures, terms, free operads

```lean
/-- A signature over a type of sorts: operation symbols with an output sort and a list of input
sorts. The "certain profunctors" of the project brief are the free profunctors on these. -/
abbrev Signature (S : Type u) := S → List S → Type u

/-- First-order terms in the context `Γ`. Nested through `Tup`; if Lean refuses, use a mutual
`Term`/`Terms`. -/
inductive Term (Σ₀ : Signature S) (Γ : List S) : S → Type u
  | var {x} (v : Var Γ x) : Term Σ₀ Γ x
  | app {x s} (σ : Σ₀ x s) (args : Tup (Term Σ₀ Γ) s) : Term Σ₀ Γ x
  deriving DecidableEq   -- given decidable equality on `Σ₀`

/-- The variables at the leaves, from left to right. -/
def Term.leaves : Term Σ₀ Γ x → List (Fin Γ.length)

/-- The free `T_W`-operad on `Σ₀`: terms whose variable usage is a `W`-wiring. -/
def FreeOp (W : Wiring) (Σ₀ : Signature S) (x : S) (Γ : List S) :=
  { t : Term Σ₀ Γ x // W.Allowed t.leafMap }

def Term.subst (t : Term Σ₀ Γ x) (σ : Tup (Term Σ₀ Δ) Γ) : Term Σ₀ Δ x
def Term.rename (t : Term Σ₀ Γ x) (ρ : Tup (Var Δ) Γ) : Term Σ₀ Δ x

/-- `FreeOp` as a `T_W`-operad on the discrete category of sorts: renaming along `T_W`-morphisms
is the profunctor action, `var` is the unit, and substitution, after weakening each argument
into its block of the flattened context, is `mul`. The laws are `subst_var`, `var_subst` and
`subst_subst`, plus closure of `W`. -/
def FreeOp.operad (W) (Σ₀) : (freeW W).Operad (Cat.of (Discrete S))

/-- 6b: the universal property. -/
def FreeOp.lift (M : (freeW W).Operad (Cat.of (Discrete S)))
    (φ : ∀ {x s}, Σ₀ x s → M.hom ⟨x⟩ (s.map Discrete.mk)) : Operad.Hom (FreeOp.operad W Σ₀) M
theorem FreeOp.lift_unique …
def FreeOp.liftEquiv : Operad.Hom (FreeOp.operad W Σ₀) M ≃ (signature maps Σ₀ → M)
```

(Sorts live in `Discrete S` on the operad side. Provide `Discrete`-free elementwise accessors
so that the term calculus can speak about `List S`.)

### 6a. Equations and theories

```lean
structure Equation (W : Wiring) (Σ₀ : Signature S) where
  ctx : List S
  sort : S
  lhs : FreeOp W Σ₀ sort ctx
  rhs : FreeOp W Σ₀ sort ctx

abbrev Theory (W) (Σ₀ : Signature S) := Set (Equation W Σ₀)

/-- The smallest operadic congruence containing the theory. -/
inductive Derives (E : Theory W Σ₀) : FreeOp W Σ₀ x Γ → FreeOp W Σ₀ x Γ → Prop
  | ax (e : Equation W Σ₀) (h : e ∈ E) : Derives E e.lhs e.rhs
  | refl t | symm … | trans …
  | subst (h : Derives E t t') (σ) : Derives E (t.subst σ) (t'.subst σ)   -- instances and renamings
  | cong (t) (h : ∀ v, Derives E (σ.get v) (σ'.get v)) : Derives E (t.subst σ) (t.subst σ')

/-- Terms modulo the theory, again a `T_W`-operad: the operad presented by `(Σ₀, E)`. -/
def Theory.operad (E : Theory W Σ₀) : (freeW W).Operad (Cat.of (Discrete S))

/-- Its universal property: morphisms out of it are signature maps that satisfy `E`. -/
def Theory.liftEquiv …

/-- Models of a theory in a family of types, through the endomorphism operad of §7. -/
abbrev Theory.Model (E) (X : S → Type u) := Operad.Hom E.operad (endOperad X)
```

### 6c. Computing with the deduction system (`Term/Rewrite.lean`)

```lean
/-- First-order matching of a pattern against a term. -/
def Term.match (pat : Term Σ₀ Γ x) (t : Term Σ₀ Δ x) : Option (Tup (Term Σ₀ Δ) Γ)

/-- One rewrite step with oriented equations, leftmost-outermost. -/
def Term.step (R : List (Equation W Σ₀)) (t : FreeOp W Σ₀ x Δ) : Option (FreeOp W Σ₀ x Δ)

/-- Normalisation with fuel. -/
def Term.normalize (R) (fuel : ℕ) (t) : FreeOp W Σ₀ x Δ

theorem step_sound (hR : ∀ e ∈ R, e ∈ E) : t.step R = some t' → Derives E t t'

/-- A sound semi-decision procedure. -/
theorem derives_of_normalize_eq (hR : …) :
    normalize R n t = normalize R n u → Derives E t u
```

* The measure of success: `#eval` and `decide` on concrete examples in a test file
  `CategoricalLogic/Examples/Eval.lean` that is built in CI. Examples: the word problem for free
  monoids (planar; a convergent system), commutative monoids (symmetric; normal form by sorting),
  and groups (cartesian; Knuth–Bendix's 10-rule system as given rewrite rules).
* Out of scope: completion (Knuth–Bendix) and AC-rewriting. Commutativity cannot be oriented,
  so symmetric or cartesian theories with commutative operations get *theory-specific* normal
  forms that are proved complete (§9).

---

## 9. Stage 7: commutative R-algebras (`CategoricalLogic/Examples/RAlgebra.lean`)

```lean
/-- One sort; `0, 1 : []`, `+, · : [⋆, ⋆]`, `-` unary, a constant `c r` for every `r : R`. -/
def ralgSig (R : Type u) : Signature Unit
/-- The commutative R-algebra axioms, plus `c (r + s) = c r + c s`, `c (r * s) = c r * c s`,
`c 0 = 0`, `c 1 = 1`. Infinitely many, as a `Set`. -/
def ralgTheory (R) [CommRing R] : Theory .cartesian (ralgSig R)

/-- The clone of polynomials: `hom ⋆ Γ := MvPolynomial (Fin Γ.length) R`, with substitution by
`bind₁` and the operad laws from `bind₁_bind₁`, `bind₁_X_right`, `bind₁_X_left`. -/
noncomputable def polyOperad (R) [CommRing R] : (freeW .cartesian).Operad (Cat.of (Discrete Unit))

/-- Step 7: the theory presents the clone of polynomials. -/
noncomputable def ralgIso : (ralgTheory R).operad ≅ polyOperad R
```

Proof plan for `ralgIso`:

1. The map is `liftEquiv` of the evaluation map; the axioms hold in `MvPolynomial` (`ring`).
2. Surjectivity: `MvPolynomial.induction_on`.
3. Injectivity is completeness. Define a computable normal form `nf : Term → CPoly` (sorted
   sparse polynomials) and `reflect : CPoly → Term`, and prove (a) `Derives E t (reflect (nf t))`
   and (b) `toMvPolynomial ∘ nf = eval`, with `toMvPolynomial` injective on normal forms.
   (a) is the substantial lemma, essentially the completeness of `ring` normalisation, and a
   good Aristotle target.
4. Connection to the symmetric monoidal category: the Lawvere theory `L_R` (objects `ℕ`,
   `n × m = n + m`, morphisms `n → m` = `m`-tuples of polynomials in `n` variables; the opposite
   of polynomial algebras with `⊗`) is a strict `T_cart`-algebra. It gives a `T_cart`-operad by
   4a, and `polyOperad R ≅ (toOperad L_R).comap (object 1)`, since
   `L_R(n, 1) = R[x₁,…,xₙ]`.

7a: for `R = ℤ` (or ℚ with decidable equality), `nf` decides `Derives (ralgTheory R)`. Examples:
`(x + y)² = x² + 2xy + y²`, `(x - y)(x + y) = x² - y²`, and an identity with constants. All are
checked by `decide` or `rfl` on `nf`, then turned into derivations by (a). Lean core's
`Lean.Grind.CommRing.Poly` is a computable ℤ-normaliser with a soundness theorem; reuse it or
model ours on it.

---

## 10. Open questions (my recommendation first)

* **Q1, step 2.** (A) `Prof.Monad` on cells of arity ≤ 2 with the laws of §3, or (B) the full
  definition as `VirtualDoubleCategory.Monad` on the Prof VDC, which then has to move into the
  main code? I recommend A.
* **Q2, step 3b.** One family `T_W` (planar, symmetric, affine, relevant, cartesian), or
  separate planar and symmetric monads? I recommend `T_W`: one set of proofs, and step 7 needs
  the cartesian case.
* **Q3, steps 3c and 4a.** Strict algebras only (generic and easy), with non-strict examples
  handled by strict replacements as in §7 and §9? Or should pseudo-algebras and genuine mathlib
  `MonoidalCategory` be in scope (coherence, much more work)? And is the symmetric converse in
  3c needed (symmetric coherence)? I recommend strict only for now.
* **Q4, step 6.** Signatures as families over a type of sorts (computable, no structural
  quotient), or arbitrary Kleisli profunctors (needs coend-style quotients)? I recommend
  families, with profunctor signatures added later as a quotient if needed.
* **Q5, step 7.** Confirm the target: *commutative* R-algebras, *cartesian*, and
  "`(Σ_R, E_R)` presents the clone `n ↦ R[x₁,…,xₙ]`", plus its relation via 4a to the Lawvere
  theory `L_R` (the opposite of polynomial algebras with `⊗`). Or did you mean something else by
  "symmetric"?
* **Q6, step 6c.** Is "sound rewriting engine + complete theory-specific normalisers" the right
  reading of "a general working algorithm"?

---

## 11. Module layout, order of work, commits

```
CategoricalLogic/
  ProfunctorOld/         (renamed Profunctor/, plus Operad.lean and Term.lean, which depend on it)
  Prof/
    Basic.lean           Stage 1    span, Square, NullaryCell, BinaryCell, mk', ext, eqToSquare,
                                    elementwise actions, the hom profunctor's identity and composition
    Monad.lean           Stage 2    Prof.Monad, Normal, helper abbreviations
    Kleisli.lean         Stage 3    KlSquare, hCompKl, Algebra
    Operad.lean          Stage 4    Operad, Hom, category, comap, elementwise API
    AlgebraOperad.lean   Stage 4a   Algebra.toOperad, endOperad
  FreeMonoidal/
    Tuple.lean           Var, Tup, RawHet and their lemmas
    Wiring.lean          Wiring and its five instances
    Basic.lean           FreeW W C, Profunctor.freeW, Prof.Monad.freeW, Normal
    Monoidal.lean        Stage 3c
  Term/
    Basic.lean           Signature, Term, leaves, subst, rename, FreeOp
    Free.lean            FreeOp.operad, lift, universal property     (6, 6b)
    Theory.lean          Equation, Theory, Derives, Theory.operad, Model   (6a)
    Rewrite.lean         match, step, normalize, soundness          (6c)
  Examples/
    Monoid.lean, CommMonoid.lean, Group.lean, RAlgebra.lean, Eval.lean
Sanity/
  ProfVDC.lean           comap, Prof.virtualDoubleCategory, binaryCellEquiv (own lean_lib)
```

Commits, one per line, each building on its own:

1. Rename `Profunctor/` to `ProfunctorOld/` and move `Operad.lean` and `Term.lean` with it.
2. `Prof/Basic.lean`.
3. `Sanity/ProfVDC.lean` and its `lean_lib` (the step 1 criterion).
4. `Prof/Monad.lean`, `Prof/Kleisli.lean`.
5. `FreeMonoidal/Tuple.lean`, `Wiring.lean`.
6. `FreeMonoidal/Basic.lean`: `T_W` as a `Prof.Monad`. This is the hardest of the early commits;
   use Aristotle for the `Cat`-level equalities if needed.
7. `Prof/Operad.lean`.
8. `Prof/AlgebraOperad.lean`, `FreeMonoidal/Monoidal.lean`.
9. `Term/Basic.lean`, `Term/Free.lean`.
10. `Term/Theory.lean`, `Term/Rewrite.lean`, `Examples/Monoid.lean`, `Group.lean`, `Eval.lean`.
11. `Examples/RAlgebra.lean`.

Size targets, to keep us honest: `Prof/Basic` ≤ 200 lines, `Prof/Monad` ≤ 150, `Prof/Operad`
≤ 200, `FreeMonoidal/*` ≤ 600 in total, `Sanity/ProfVDC` ≤ 250.

## 12. Risks

* **Casts along list equalities** in the `Cat`-level laws of `T_W`. Mitigation: structural
  `Var`/`Tup` definitions keep casts out of the data, and only object equalities remain, handled
  with `eqToHom` and `simp`. Aristotle as a fallback.
* **The law list of `Prof.Monad` drifts.** Mitigation: the usage table in §3; a law is added only
  together with the proof that needs it.
* **Nested inductive `Term` through `Tup`.** Mitigation: a mutual `Term`/`Terms` with the same
  API.
* **Completeness for R-algebras (7, step 3a)** is a real theorem. Mitigation: isolate it as one
  lemma and send it to Aristotle early.
* **Performance of `decide`** on terms. Mitigation: prefer `#eval` plus `rfl` on normal forms, and
  derive `DecidableEq` rather than writing it by hand.
