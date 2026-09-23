
This file should not contain any references to old identifiers or old states. Remove old references if you see them.

We will define virtual double categories and T-operads for a monad T on a virtual double category in multiple layers.

### Quiver spans

A quiver span $R$ is a span $Q \xrightarrow{} R \xleftarrow{} S$ between two quivers, but axiomatized via its fibers.

We will think of vertices as objects, of edges in the two quivers as proarrows and of the cells as filling a square of arrows and proarrows.

**Definition.**  A quiver span between quivers $Q$ and $R$ consists of the following data: First, a type $R(x,y)$ of arrows for each vertex $x$ in $Q$ and for each vertex $y$ in $R$. Then, for each pair of edges $e : x \to x'$ and $e' : y \to y'$ in $Q$ and $R$, respectively and for arrows $f \in R(x,y)$ and $f' \in R(x',y')$, a type of squares $R(e,e',f,f')$.

The module `QuiverSpan.lean` should contain a construction of quiver spans together with a comprehensive API for how the double category of quivers, prefunctors and quiver spans behaves.

This does not mean that we will formalize some sort of instance for a double category (which will later be defined in terms of quiver spans themselves), but that this will be our guiding principle for organizing the file.

Composition of prefunctors is already defined, so we only need
* A definition for quiver spans
* A definition of squares of two prefunctors and two quiver spans
* An identity square
* Binary vertical composition of squares `vComp`
* Associativity and identity law for squares (we will do this later)
* When all the above is done, we move onto horizontal composition.
    * Horizontal identity
    * Binary horizontal composition
    * Coherence laws (only if needed somewhere else)
    * n-ary horizontal composition of spans (currently named `pathProd`, but the name should reflect that this is ordinary horizontal composition)
    * If needed, n-ary horizontal composition of squares
* A definition for `MultiSquare`, which takes a target quiver span `A`, a composable chain of source quiver spans `p` and two vertical arrows connecting the corners and is defined by `QuiverSpan.Square A (pathProd p) f f'`. This replaces and generalizes all former notions of `MultiHom`, `BiHom` and `Unit`. If you need those concepts later, redefine them as an abbrev here.

All definitions should facilitate an easy definition of a quiver T-span together with a composition operation at the end. They have to be reusable for this purpose.

Use the naming conventions for `Bicategory` that are in mathlib whenever you're not sure. Naming conventions should follow the imaginary double category structure that we're working with here.

### The Paths monad

The `Paths.lean` module should contain all the necessary monad structure on the `Paths`
monad. To be precise, `Paths` should be thought of as a monad on the virtual double
category of quivers, prefunctors and quiver spans.

Here `Paths` is bookkeeping for n-ary sources: the source of a cell is a path of composable
spans. We are not building `Paths`-monoids yet, so anything that only serves that goal stays
out. The criterion for including a definition or a law is whether the **Kleisli virtual
double category for `Paths`** uses it; that is the only thing we build in the first pass,
and each item below says whether it is used.

Reuse mathlib and what is already in `VirtualDoubleCategory/Paths.lean` and
`VirtualDoubleCategory/Basic.lean`; the latter will need a heavy refactor, and the old names
below are there to be moved or dropped. We never state "monad on a virtual double category"
abstractly, so each definition should carry a docstring naming the piece of monad structure
it is (unit or multiplication, on objects or on spans, comparison cell, monad law). That
comment is the whole point of the organizing principle.

#### On objects and prefunctors

* `Paths Q` and `Paths.of` (mathlib): the underlying functor and the unit on objects. Used.
* `flattenPath` and `pathsJoin` in `Paths.lean`: the multiplication on objects. Used —
  `QuiverTSpan.comp` restricts an identity span along `pathsJoin`, and
  `SpanQuiv.pathSquareComp` lands on `pathProd (flattenPath _)`.
* `Paths` on a prefunctor, i.e. `Prefunctor.mapPath` (mathlib bundles it as `Cat.freeMap`).
  Currently `QuiverTSpan.pathComp`, in the wrong namespace and unused. Keep it: a Kleisli
  cell over prefunctors `f`, `g` has `Paths g` as its right boundary, so it is needed as
  soon as cells have non-identity vertical boundaries.
* `flattenPath_mapPath_of` in `Paths.lean`: a monad law on objects. Already proved, not yet
  used. Keep, it is one line.
* Functoriality (`Prefunctor.mapPath_id`, `mapPath_comp_apply`, both mathlib): not used.
  Worth knowing only because neither is `rfl`, which is why the two forms of `Paths` on
  cells below cannot be collapsed into one.

#### On spans and cells

* `QuiverSpan.PathSquare` and `QuiverSpan.paths`: `Paths` on a span. A cell of `paths A`
  over two paths is a chain of cells of `A`, indexed by the two paths rather than cut out of
  a larger type — that indexing is what makes `Paths` lift to spans at all, and it forces
  the two paths to have the same length. Used by `QuiverTSpan.comp`.
* `PathSquare.map` and `QuiverSpan.pathsMap`: `Paths` on a morphism of spans. Used by
  `QuiverTSpan.mapComp`.
* The same for a square over arbitrary prefunctors, landing on `Paths f` and `Paths g`. Both
  forms have to exist, since `Paths (𝟭q Q) = 𝟭q (Paths Q)` is not `rfl`. Used exactly when
  the previous prefunctor item is.
* `PathSquare.comp`: concatenation of chains, currently unused. It exists only to define the
  multiplication on spans, so it goes out with it.

#### Not needed in the first pass

The unit and multiplication on spans (`pathsUnit`, `PathSquare.flatten`, `pathsMul`, all
currently commented out in `Basic.lean`), the comparison cells
`paths A ⊙ paths B ⟶ paths (A ⊙ B)` and `id (Paths Q) ⟶ paths (id Q)`, and the monad laws
and naturality axioms on spans. `QuiverTSpan.comp` uses the multiplication only on objects,
so none of these has a consumer yet. They are what would let us say the construction really
is the horizontal Kleisli one, and they are what associativity and unitality of Kleisli
composition will need, so say so in a comment where the object-level versions are defined.

#### Universes

`Paths` raises the edge universe — for `Q : Type u` with `Quiver.{v} Q`, `Paths Q` is
`Type u` with `Quiver.{max u v}` — and is idempotent after one application. Elementwise this
is harmless. But `SpanQuiv` has to be a quiver for n-ary sources to be paths of spans, and
`Paths` acts on it only if its edge universe already absorbs its vertex universe:
`SpanQuiv := Quiv.{u, v}` has to become `Quiv.{max u v, v}`. With that one change the apex
universes look after themselves, since `Paths` of a span whose apex universes are `max u v`
keeps them there.

Everything above is data or a short induction. Hand any proof that turns out to be hard to
Aristotle rather than letting the file grow around it.
