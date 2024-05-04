
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.ChosenFiniteProducts

import LeanProject.Syntax

/- Interpretation & normalization
We want to
* Make interpretation of formulas in categories easy (seemless substitution by pullback!). Explore strictness issues and solutions.
* Explore normal forms in this context (& categorical enhancements thereof)
* Facilitate deduction in this context
-/

open CategoryTheory


-- We require actual choices of finite limits, since we might want to try to compute things
class FiniteLimits (C: Type u) [Category C] where
limit (J: Type) [SmallCategory J] [FinCategory J] (F: Functor J C) : Limits.LimitCone F

def List.toFn {α: Type u} (x: List α) (n: Fin x.length) : α := x[n.val]

def asFunctor (C: Type u) [Category C] (x: List C) : Functor (Discrete (Fin x.length)) C :=
  Discrete.functor (List.toFn x)

-- How do we construct discrete categories in a way that is computable?
-- In essence, decidable equality should be the missing link.
instance finCategoryDiscreteOfFintype' (J : Type v) [Fintype J] [DecidableEq J] : FinCategory (Discrete J) where
  fintypeObj := by infer_instance
  fintypeHom := by
    intro j j'
    simp only [Quiver.Hom]
    apply ULift.fintype

def powLim {C: Type u} [Category C] [FiniteLimits C] (x: List C) :=
  FiniteLimits.limit (Discrete (Fin x.length)) (asFunctor C x)

def pow {C: Type u} [Category C] [FiniteLimits C] x := (powLim (C:=C) x).cone.pt

structure Structure (l: Language) (C: Type u) [Category C] [FiniteLimits C] where
  objects : l.sort → C
  functions : (a: List l.sort) → (b: l.sort) → (f: l.function_symbol a b) → (pow (a.map objects)) ⟶ (objects b)
