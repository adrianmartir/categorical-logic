Refactor 'CategoricalLogic/Profunctor/Cells.lean':
* Make it use 'CategoricalLogic/Profunctor/Basic.lean' instead of 'CategoricalLogic/Prof.lean'? Note that this changes the order of the arguments every time we apply the profunctor. Also swap the order of the arguments in 'PathProd'.
* Move all the 'PathProd' code to 'CategoricalLogic/Profunctor/Product.lean'.
* Instead of using 'AllWedges', add an inductive type in 'CategoricalLogic/Profunctor/Product.lean' that generates a relation on 'PathProd P' identifying two n-tuples if they can be identified by a wedge condition. This means that it doesn't matter whether we act on the ith member of the tuple on one side or on the (i+1)st member of the tuple on the other side. Make this a setoid instance.
* Back in 'CategoricalLogic/Profunctor/Cell.lean', define a Cell to be a map out of 'PathProd P' preserving this relation and satisfying a naturality condition. This is the same condition as the one that is currently in the 'CategoricalLogic/Profunctor/Cells.lean' file.
* Define the functor tensor product by quotienting out this setoid relation. Give a profunctor structure to the functor tensor product along a path. If possible, inherit this profunctor structure from a profunctor structure on 'PathProd'.

e0b22767-3025-4129-a83c-8d61d1a141f4