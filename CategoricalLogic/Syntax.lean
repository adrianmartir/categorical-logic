

structure Language where
sort : Type u
-- Given n inputs, one output we have a type of 'function symbols'
-- This reminds of a 'multicategory', where we have no composition operation yet.
-- We use lists since checking termination is easier
function_symbol : List sort → sort → Type u
-- relation : (n: ℕ) → (Fin n → sort) → Type u



-- No bound variables for now
inductive Term (l: Language) (vars: Type u)
| fvar: vars → l.sort → Term l vars
-- Careful: Inputs may not have the correct sorts!
| apply : (a: List l.sort) → (b: l.sort) → (f: l.function_symbol a b) → (List (Term l vars)) → Term l vars

inductive Formula (l: Language) (vars: Type u)
| equal : Term l vars → Term l vars → Formula l vars
| conj : List (Formula l vars) → Formula l vars


variable {l: Language} {vars: Type u}

def fvars : Term l vars → List vars
| Term.apply a b f (List.cons head tail) => (fvars head) ++ (fvars (Term.apply a b f tail))
| Term.apply _ _ _ [] => []
| Term.fvar x _  => [x]

def sort : Term l vars → l.sort
| Term.fvar _ s => s
| Term.apply _ b _ _ => b

def HasSort : Term l vars → l.sort → Prop
| Term.fvar _ a, s => a = s
| Term.apply a b _ x, s => (b = s) ∧ HasSortHelper a x
where
  HasSortHelper : List l.sort → List (Term l vars) → Prop
  | List.cons ha ta, List.cons h t => HasSort h ha ∧ HasSortHelper ta t
  | [], [] => True
  | _, _ => False

class SortChecks (t: Term l vars) where
  proof: HasSort t (sort t)

declare_syntax_cat absFormula
declare_syntax_cat absTerm

--Application of nterms?
syntax term " ( " absTerm,+ " ) " : absTerm
syntax absTerm "=" absTerm: absFormula
syntax " ⟦ " absFormula " ⟧ " : term
syntax " < " absTerm " > " : term


def arrayToSyntax (x: Array (Lean.TSyntax `term)) : Lean.MacroM (Lean.TSyntax `term) := do
  let empty <- `([])
  x.foldlM (fun acc next => do
    `(List.cons $acc $next)
    ) empty

#check `str
macro_rules
  | `(term|⟦ $s:absTerm = $t:absTerm ⟧) => `(Formula.equal <$s> <$t>)
  | `(term| <$t:term( $xs:absTerm,* ) >) => do
      let s <- xs.getElems.mapM (fun x => `(<$x>))
      -- Want to construct a term of `sorts`
      let a <- s.mapM (fun x => `(sort $x))

      let s <- arrayToSyntax s
      let a <- arrayToSyntax a
      `(Term.apply $a _ $t $s)

-- Free variable syntax category?
-- We use terms (of type `vars`) to construct free variables
-- How do you do binders? Look at implemetation of `fun x => ...`
