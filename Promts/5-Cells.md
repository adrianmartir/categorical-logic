I want to build an API for cells of profunctors in 'CategoricalLogic/Profunctor/Cells.lean'. Specifically:
* A functor 'Paths' that sends a quiver Q to a new quiver whose edges from v to w are paths in Q from v to w (use 'Quiver.Path' for this).
* A monad instance for 'Paths'
* A type alias 'Prof' that is the same as the category of categories, only that we provide a quiver instance on it, where an edge from C to D is a profunctor from C to D.
* Given a pair of categories 'C' and 'D' and a path H_1,...,H_n in 'Prof' from 'C' to 'D' (source) and another profunctor K from 'C' to 'D' (target), define the set of cells to be the following family of maps: Given any objects c_0, ..., c_n in each of the categories included in the path, a map
    H_1(c_0,c_1) × H_2(c_1,c_2) × ... × H_n(c_{n-1},c_n) -> K(c_0,c_n)
satisfying a naturality property in c_0 and in c_n and moreover a wedge property for each c_i and c_{i + 1}. Take 'BiNatTrans' in 'CategoricalLogic/Operad.lean' as a template for this, it is the case for two paths.
* Finally (this is optional!), define a composition operation for these paths.

Note: Form submitted, but without output review.
5f6c68dd-5e33-4a21-99e1-8bde87430b03