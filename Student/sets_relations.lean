import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic

/-!
binary relation on a type, α
- reflexive : everything related to itself
- symmetric
- transitive : if a is related to b and b is related to c, a is related to c
- equivalence (Core.lean)
- asymmetric : has self loops
- antisymmetric
- closures
- inverse

- empty relation : r: α → α → Prop := λ a b => False
- complete relation : everything related to everything : λ a b => True
- subrelation

binary relation from α → β, etc
- compose
- join

inverse image

total order
partial order or poset- it must be reflexive and transitive, not symmetric, it is anti-symmetric (if set a is contained in b and set b is contained in a then a=b)

-/
inductive Person : Type
| lu
| mary
| jane

open Person

def Likes : Person → Person → Prop :=
λ p1 p2 =>
  (p1 = lu ∧ p2 = mary) ∨
  (p2 = lu ∧ p1 = mary)

#reduce Likes lu mary

#reduce Likes lu jane

example : Likes lu mary := Or.inl ⟨ rfl, rfl ⟩  --reflexive relation

-- example : ¬ Likes lu jane :=
--   λ h : Likes lu jane => by
--     cases h with
--     nomatch h.2

example : ¬ Likes lu jane :=
  λ h : Likes lu jane => by
    unfold Likes at h
    cases h
    Or.inl l => nomatch l.2
    Or.inl r => nomatch r.1
/-
order relations
- partial order: reflexive, antisymmetric, transitive
- poset: a set α along with a partial order on α
- total order: partial order ∧ ∀ a b, a < b ∨ b < a
-/

/-
functions
- a single-valued relation is a function

- domain of definition
- codomain - set of possible outputs
- domain - input
- range
- partial
- total - if and only if every value a in the domain there exists a value b in the codomain such that r a b where r is a relation

- identity function -- See Mathlib.Logic.Function.Basic

- one-to-one (vs many-to-one, injective)
- onto (surjective) - iff ∀ b ε f.codomain, ∃ a ε f.domain r a b
- bijective - both injective and surjective

- composition
- inverse
- etc
-/
