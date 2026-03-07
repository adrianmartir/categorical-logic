In the file 'CategoricalLogic/Profunctor.lean', add definitions 'Profunctor.actLeft' and 'Profunctor.addRight' that compose a functor F with a profunctor H by computing x, y ↦ H(F(x),y) and x, y ↦ H(x,F(y)) respectively.
* Add a lemma actLeft_obj, that shows how to compute actLeft on objects (similar for actRight)
* Add a similar lemmas for morphisms (in both arguments of the profunctor), with Profunctor.map and also variations with Profunctor.mapL
* Add a lemma that computes a natural transformations 'h ⟶ k.actLeft f' on objects (same for actRight).
* Add any obvious missing API for 'actLeft' and 'actRight'
* Now at the categorical level: Show that 'actRight' and 'actLeft' do nothing when we use the identity functor (identity property). Show that 'actRight' and 'actLeft', when applied twice, do yield the same result that we would get when we compose the two functors first (associativity property).

f9e78d57-6327-4f05-828a-3b060158ddfd