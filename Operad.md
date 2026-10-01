This file should not contain any references to old identifiers or old states. Remove old references if you see them.

We will define virtual double categories and T-operads for a monad T on a virtual double category in multiple layers.

These are five modules in the `CategoricalLogic/VirtualDoubleCategory` directory, each
importing the previous one: `QuiverSpan.lean`, `Paths.lean`, `PathsKleisli.lean`, `Basic.lean`
(virtual double categories) and `SpanQuiv.lean` (the example of quiver spans). One section
below per module.

### Quiver spans

A quiver span is a span $Q \leftarrow A \rightarrow R$ between two quivers, but axiomatized
via its fibers.

We will think of vertices as objects, of edges in the two quivers as proarrows and of the
cells as filling a square of arrows and proarrows.

**Definition.**  A quiver span between quivers $Q$ and $R$ consists of the following data: First, a type $A(x,y)$ of arrows for each vertex $x$ in $Q$ and for each vertex $y$ in $R$. Then, for each pair of edges $e : x \to x'$ and $e' : y \to y'$ in $Q$ and $R$, respectively and for arrows $f \in A(x,y)$ and $f' \in A(x',y')$, a type of squares $A(e,e',f,f')$.

**Orientation.** We follow Cruttwell–Shulman throughout: in a span $Q \leftarrow A \rightarrow R$ the left leg carries *targets* and the right leg carries *sources*, for arrows and for squares alike. So an element $f \in A(x,y)$ is an arrow from $y$ to $x$, and a square in $A(e,e',f,f')$ has source $e'$, target $e$, and sides $f$ and $f'$:

```
y --e'--> y'
|f        |f'
v         v
x --e-->  x'
```

Reading $A(x,y)$ right to left is the price of matching the paper; it is what makes the Kleisli span of a virtual double category carry the n-ary *sources* of its cells on the right, in `Paths`. In the ambient double category the same convention says that a square of prefunctors and quiver spans goes from its first span (its source) to its second (its target), with the prefunctors running from the feet of the source to the feet of the target. A cell with n-ary source is therefore a square *out of* an n-ary horizontal composite.

The module `QuiverSpan.lean` should contain a construction of quiver spans together with a comprehensive API for how the double category of quivers, prefunctors and quiver spans behaves.

This does not mean that we will formalize some sort of instance for a double category (which will later be defined in terms of quiver spans themselves), but that this will be our guiding principle for organizing the file.

Composition of prefunctors is already defined, so we only need

**Spans, squares and vertical composition.**

* A definition for quiver spans
* A definition of squares of two prefunctors and two quiver spans
* A morphism of quiver spans, as the special case where both prefunctors are identities
  (`Hom`). Most of the file is stated in terms of it.
* An identity square
* Binary vertical composition of squares `vComp`
* Restriction of a span along prefunctors into its feet (`restrict`). The Kleisli identity
  and the Kleisli composition are both built from restrictions, so this is not optional.
* Associativity and identity law for squares (we will do this later)

**Horizontal composition.** When all the above is done, we move onto horizontal composition.

* Horizontal identity, and the square that a prefunctor induces between two horizontal
  identities (`Square.hId`)
* Binary horizontal composition, of spans and of squares (`QuiverSpan.comp` and
  `Square.hComp`)
* Unitors and the associator, as cells (`leftUnitor`, `rightUnitor`, `rightUnitorInv`,
  `associator`). These are data and the n-ary API below is built from them; they are not the
  coherence laws.
* Coherence laws (only if needed somewhere else)
* n-ary horizontal composition of spans (`SpanQuiv.composePath`, after mathlib's
  `composePath`)
* Splitting an n-ary composite over a concatenation of two paths (`composePathCompInv`), in
  the direction *out of* the concatenated path, which is the one that substitution of cells
  consumes. Also the unary case, comparing a
  single span with the n-ary composite of the one-element path on it (`composePathToPath`,
  which is the left unitor).
* n-ary horizontal composition of squares. It needs the chains of squares of `Paths.lean`, so
  it lives with the example in `SpanQuiv.lean` (`SpanQuiv.hCompPath`).

**Cells with n-ary source.**

* A definition for `MultiSquare`, which takes a target quiver span `A`, a composable chain of source quiver spans `p` and two vertical arrows connecting the corners and is defined by `QuiverSpan.Square (composePath p) A f f'`, a square out of the composite of the sources into the target. It is the only notion of a cell with n-ary source; special cases should be abbreviations of it.

All definitions should facilitate an easy definition of a Kleisli span together with a composition operation at the end. They have to be reusable for this purpose.

Note that `composePath` and `MultiSquare` are the n-ary structure of the *ambient* double
category. Defining a virtual double category and a functor between them does not use them
(see the last section); they are what exhibits quivers, prefunctors and spans as an example
of a virtual double category, and what the operad work will be phrased in.

Use the naming conventions for `Bicategory` that are in mathlib whenever you're not sure. Naming conventions should follow the imaginary double category structure that we're working with here.

### The Paths monad

The `Paths.lean` module should contain all the necessary monad structure on the `Paths`
monad. To be precise, `Paths` should be thought of as a monad on the virtual double
category of quivers, prefunctors and quiver spans.

As in the previous module this is a guiding principle and not an instance: we never say what
a monad on a virtual double category is. Instead every definition carries a docstring naming
the piece of monad structure it is, so that the shape stays legible from the code.

Here `Paths` is bookkeeping for n-ary sources. Everything mentioned below is needed unless it
is marked "(not needed)", and the standard for that is whether the Kleisli virtual double
category for `Paths`, or the laws of virtual double categories, use it. Reuse mathlib wherever it applies.

The free category monad on quivers is already in mathlib, so we only need

**The vertical direction.** Objects are quivers and vertical arrows are prefunctors, so this
layer is the ordinary free category monad on quivers.
* `Paths Q` and its unit `Paths.of`, both from mathlib
* `Paths` on a prefunctor (`Paths.map`), from mathlib's `Cat.freeMap`. A Kleisli cell over
  prefunctors `f` and `g` has `Paths g` as its right boundary.
* The multiplication, flattening a path of paths (`Paths.flatten`). It is mathlib's
  `pathComposition` for the path category, so on edges it is `composePath`, which reduces
  definitionally on `nil` and `cons`.
* Functoriality, `Paths 𝟭q = 𝟭q` and `Paths (F ⋙q G) = Paths F ⋙q Paths G` (mathlib
  `mapPath_id` and `mapPath_comp_apply`; on paths of paths `Paths.mapPath_map_id` and
  `Paths.mapPath_map_comp`). Neither is `rfl`, which is why the two
  forms of `Paths` on cells below cannot be collapsed into one. The identity and composite
  functors of virtual double categories use them.
* Naturality of the unit and of the multiplication in prefunctors (mathlib `mapPath_toPath`)
  (not needed)
* The monad laws (`Paths.flatten_map_of`, `Paths.flatten_map_mapPath_of`,
  `Paths.flatten_assoc`) and naturality of the multiplication (`Paths.flatten_naturality`).
  The laws of virtual double categories and of their functors transport cells along them.

**The horizontal direction.** Horizontal arrows are quiver spans.
* `Paths` on a span (`QuiverSpan.PathSquare` and `QuiverSpan.paths`). A cell of `Paths A`
  over two paths is a chain of cells of `A`, indexed by the two paths rather than cut out of a
  larger type; that indexing is what makes `Paths` lift to spans at all, and it forces the
  two paths to have the same length. As for `Quiver.Path`, the start of a chain is a
  parameter rather than an index, which is what makes recursion on chains structural, so
  that it reduces definitionally.
* Concatenation of chains (`PathSquare.comp`), and the unit and the multiplication on spans,
  elementwise (`PathSquare.single` and `PathSquare.flatten`). Kleisli composition uses the
  multiplication only in the vertical direction; the multiplication on spans enters through
  the associativity law of virtual double categories.
* Unzipping a chain of a binary horizontal composite into a chain of each factor
  (`PathSquare.unzip`): the comparison cell for binary horizontal composition, elementwise.
  The inverse associator of Kleisli composition uses it.
* The other comparison cells, and their inverses (not needed). They are what associativity and unitality of Kleisli
  composition will need.

**Cells.**
* `Paths` on a morphism of spans (`PathSquare.mapHom` and `Hom.paths`), used by
  functoriality of Kleisli composition in both arguments
* `Paths` on a square over arbitrary prefunctors, landing on `Paths f` and `Paths g`
  (`PathSquare.map` and `Square.paths`), used by functors of virtual double categories. Both forms have to exist, since `Paths 𝟭q = 𝟭q` is
  not `rfl`.
* Functoriality on cells, the naturality axioms and the monad laws in this direction
  (not needed)

**Universes.** `Paths` raises the edge universe and is idempotent after one application, so
`SpanQuiv` carries a `Quiver.{max u v}` on `Type v`: with an unconstrained pair of universes
`Paths` would not act on it at all. It is its own two-field structure rather than a synonym of
mathlib's `Quiv`, which keeps the universe linter satisfied without switching it off. The apex universes then look after themselves.

Everything above is data or a short induction. Hand any proof that turns out to be hard to
Aristotle rather than letting the file grow around it.

### The Kleisli virtual double category

The `PathsKleisli.lean` module should contain the Kleisli virtual double category for
`Paths`. Virtual double categories are the monoids there, but they get their own module.

**Kleisli spans and their composition.**
* A Kleisli span from `Q` to `R` is a quiver span from `Q` to `Paths R` (`KleisliSpan`).
* The Kleisli identity (`KleisliSpan.id`): the restriction of the horizontal identity on
  `Paths Q` along `Paths.of Q`, which makes the unit of the monad visible in the definition
  instead of buried in it. Its arrows are equations `(Paths.of Q).obj x = (𝟭q _).obj y`, so
  matching on them with `rfl` needs the endpoint `y` generalized into the `match`.
* Binary Kleisli composition (`KleisliSpan.comp`): the horizontal composite of `A`, of
  `Paths B`, and of the horizontal identity restricted along `Paths.flatten`. The docstring
  names those three factors, since that is where the multiplication of the monad enters.
* Functoriality of Kleisli composition in both arguments (`KleisliSpan.hComp`). Used by
  functors of virtual double categories.
* Kleisli cells (`KleisliSpan.Square`). A cell from `A` to `B` over prefunctors `f` and `g` is
  a square from `A` to `B` over `f` and `Paths g`. This is the reason `Paths.lean` has to keep `Paths` on
  prefunctors and `Paths` on squares over arbitrary prefunctors.
* Kleisli cells with nullary and binary source, as abbreviations for cells out of the
  Kleisli identity and out of a binary Kleisli composite (`KleisliSpan.NullaryCell` and
  `KleisliSpan.BinaryCell`).
* n-ary Kleisli composition (not needed). A monoid only ever uses the nullary and the binary
  case, and so does a morphism of monoids.

### Virtual double categories

The `Basic.lean` module should contain virtual double categories, their
functors, transformations between functors, and monads on a virtual double category. A
virtual double category is a monoid in the Kleisli virtual double category of the previous
section, so the module is that definition unfolded and then built upon.

**Virtual double categories.**
* A virtual double category is a quiver `Q` together with a Kleisli span `A : Q ⇸ Q`, a
  nullary cell into it and a binary cell into it. It is a single structure
  `VirtualDoubleCategory` holding the data and the monoid laws.
* The dictionary is worth a docstring: vertices of `Q` are objects, edges of `Q` are
  proarrows, `A.arr x y` are the arrows from `y` to `x`, and `A.square e p a b` is a cell with
  n-ary source `p`, unary target `e`, and side arrows `a` from the start of `p` to the start
  of `e` and `b` from the end of `p` to the end of `e`. The path `p` is exactly where the
  n-ary source comes from.
* Elementwise accessors for the two cells: identity arrow and identity cell from the nullary
  one, composition of arrows and substitution of cells from the binary one (`idArr`,
  `idCell`, `compArr`, `subst`). `compArr` is in diagrammatic order. The cell halves are
  what the term calculus will actually be written against.
* Axioms: the monoid laws `one_mul`, `mul_one` and `mul_assoc`, as equations between
  morphisms of Kleisli spans, built from whiskering (`KleisliSpan.whiskerLeft`,
  `KleisliSpan.whiskerRight`), the unitors (`KleisliSpan.leftUnitor`,
  `KleisliSpan.rightUnitor`) and the inverse of the associator (`KleisliSpan.associatorInv`).
  Only the inverse of the associator is needed, and it only concatenates chains. Evaluated at
  an element, the laws are the unit and associativity laws of arrows and cells; the ones for
  arrows and `idCell_subst` are derived.
* All of this is a single structure `VirtualDoubleCategory`; there is no separate structure
  for the data.
* The accessors are the elementwise accessors of nullary and binary Kleisli cells
  (`KleisliSpan.NullaryCell.arr`, `.square` and `KleisliSpan.BinaryCell.arr`, `.square`).

**Functors.** A functor from `(Q, A)` to `(R, B)` is a morphism of monoids: a prefunctor
`f : Q ⥤q R` together with a Kleisli cell from `A` to `B` over `f` and `f` (a square from `A`
to `B` over `f` and `Paths f`), preserving the unit and the multiplication:
`id ≫ F = idMap f ≫ id` and `mul ≫ F = (F ⊙ F) ≫ mul`. It is one structure,
`VirtualDoubleCategory.Functor`. This needs, in `PathsKleisli.lean`, the Kleisli identity on a
prefunctor (`KleisliSpan.idMap`) and horizontal composition of Kleisli cells over prefunctors
(`KleisliSpan.Square.hComp`), which uses naturality of `Paths.flatten` as a square
(`KleisliSpan.flattenMap`).
* The identity functor and composition of functors, built on `KleisliSpan.Square.id` and
  `KleisliSpan.Square.vComp`. These transport cells along `Prefunctor.mapPath_id` and
  `Prefunctor.mapPath_comp_apply`, so their laws are proved elementwise, with `Square.ext`, the
  interchange law `KleisliSpan.Square.hComp_vComp_map_square_heq` and heterogeneous congruence
  lemmas.

**Transformations.** A transformation from `F = (f, _)` to `G = (g, _)` is a Kleisli cell `θ`
from the Kleisli identity on `Q` to `B` over `g` and `f`. Its components are an arrow
`θ x : B.arr (g x) (f x)` for each object and a cell with source `f e` and target `g e` for each
proarrow. Naturality is one equation of cells out of `A`:
`λ⁻¹ ≫ (θ ⊙ F) ≫ mul = ρ⁻¹ ≫ (G ⊙ θ) ≫ mul`, with the inverse unitors of Kleisli composition.
Elementwise it is naturality in arrows and the paper's `θ_q (Fα) = (Gα)(θ_{p₁} ⊡ ⋯ ⊡ θ_{pₙ})`.
* The components of identity transformations and of vertical composites, as cells
  (`VirtualDoubleCategory.unitCell`, `VirtualDoubleCategory.compCell`).
* Identity transformations, vertical composition and whiskering as transformations, with
  their naturality proofs (not done yet).

**Monads.** A monad on a virtual double category `X` consists of
* an endofunctor `T` of `X`;
* a transformation `η` from the identity functor to `T`;
* a transformation `μ` from `T ∘ T` to `T`;
* the unit laws `μ ∘ ηT = id` and `μ ∘ Tη = id`, and associativity `μ ∘ Tμ = μ ∘ μT`, as
  equations between the component cells. Whiskering is vertical composition of Kleisli cells
  (`KleisliSpan.Square.vComp`) with `KleisliSpan.idMap T` or with the cell of `T`, and the
  composites are `compCell`. Stated on the component cells, the laws need no comparison of
  transformations between functors that are only propositionally equal, such as `T ∘ 1` and
  `T`.

**Example.** Quivers, prefunctors and quiver spans form a virtual double category, whose data
is `SpanQuiv.hom`, `SpanQuiv.id` and `SpanQuiv.comp` (the monoid laws are not proved yet). Its arrows from `r` to `q` are the prefunctors
`r ⥤q q`, composition of arrows is diagrammatic composition of prefunctors, the identity cell
on a span is the left unitor, and substitution is n-ary horizontal composition
(`SpanQuiv.hCompPath`) followed by vertical composition. It lands one universe up.

`Paths` is a monad on this virtual double category, but we cannot say so in this module: that
needs the axioms above and the span-level unit and multiplication of `Paths.lean`. So
`Paths.lean` and `PathsKleisli.lean` stay independent of this module, and the definition
above is there for the monads whose operads we want later.
