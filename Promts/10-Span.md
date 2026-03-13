We will construct the bicategory of spans in 'CategoricalLogic/Profunctor/Span.lean' in the folowing steps:

First, define a class 'WithPullbacks' on categories that has a field that computes the pullback of two arrows and a proof that this pullback cone is actually a limit. This is to allow specific, possibly computable, choices of pullbacks.

Based on this, construct the category of spans:

Given a category C with pullbacks, define the bicategory Span(C) of spans in C to have
* Objects as in C
* Morphisms Hom(c,d) consist of an object e and a pair of arrows e -> c and e -> d (these are spans)
* A 2-cell from a span (e,f,g) to (e',f',g') consists of a morphism h : e -> e' such that f' ∘ h = f and g' ∘ h = g
* The composition (e'',f'',g'') of two spans (e,f,g) and (e',f',g') is constructed by using the pullback of e and e' along g and f' (this is e''). Then f'' and g'' are given by composing the two pullback projection maps with f and g'.

Finally, give a bicategory instance using this data and appropriate unitors and associators. Fill as many sorries as you can.

d483948b-67c5-49db-9a1e-ea1a7bf390fa