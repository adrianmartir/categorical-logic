This project aims to give clear categorical definitions for virtual double categories, monads on them, the Kleisli category of a monad on a virtual double category and T-operads for T an operad on a virtual double category.

Later, we will want to use T-operads as a way of modelling terms for algebraic theories. We will develop the concept of a signature of an algebraic theory by using certain profunctors. We will define an operation that makes these profunctors into T-operads, which will correspond to a construction of the T-operad of preterms over a signature. Then we will quotient out certain relations out of the preterms so that they're actually a completion of the original signature (there is a universal property). In addition, we will define theories to be sets of pairs of preterms, that will also be quotiented out.

All these relations that will be quotiented out will form a deduction system. In time, we will want to define computational procedures for these deduction systems. This is why we have to take care that all the constructions that are relevant to this are computable.

We will support all of this by a series of examples of theories. Monoids, groups, rings, etc. will all have their own T-operads for suitable T. We hope that this will provide a good ground for generalizing concepts that are already in mathlib.

The priority should always be to assist the user in finding the correct categorical definitions (at the right level of generality) and developing an API that helps satisfy the broader aims outlined here. The aim is never to simply provide a proof of a certain theorem or to give a definition for a certain object. That is not worth much. Conceptual clarity and conciseness are much more important. We're building a delicate core API that might eventually get into mathlib.

Getting definitions right might require multiple iterations of trial and error and refinement. Also, when you see that a definition that has already been done makes it hard to continue with it, and you think that there is a better way to structure things, prompt the user with a suggestion.

The main source for our formalization of operads is in the folder `GeneralizedMulticategories/`, though keep in mind that we do not follow the source strictly and will choose ourselves at which generality we want to state the concepts. When not sure about the generality, prompt the user.

`USING_ARISTOTLE.md` contains instructions on how to use the external AI-agent prover Aristotle.

Don't use tactics in term mode.

