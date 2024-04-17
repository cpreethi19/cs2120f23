import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic
import Mathlib.LinearAlgebra.AffineSpace.Basic

/-!
binary relation on a type, α
- reflexive : everything related to itself
- symmetric : if x = y then y = x
- transitive : if a is related to b and b is related to c, a is related to c
- equivalence : needs to reflexive, symmetric, transitive (Core.lean)
- asymmetric : has self loops
- antisymmetric : if x < y then y < x then x = y
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

/-
In Lean, we will often represent a set, S, of elements of type
α as a membership predicate, mem: α → Prop.
-/

def a_set : Set Nat := {1, 2, 3 }
def b_set : Set Nat := {3, 4, 5}

def a_set' : Set Nat := { n : Nat | n = 1 ∨ n = 2 ∨ n = 3}

example : 1 ∈ a_set := by
  show a_set 1
  unfold a_set
  show 1=1 ∨ 1=2 ∨ 1=3
  exact Or.inl rfl

example : 3 ∈ a_set ∩ b_set := by
  show 3 ∈ a_set ∧ 3 ∈ b_set
  exact ⟨ Or.inr (Or.inr rfl) , Or.inl rfl ⟩

example : 2 ∈ a_set ∪ b_set := by
  show 2 ∈ a_set ∨ 2 ∈ b_set
  exact Or.inl (Or.inr (Or.inl rfl))

example : 2 ∈ a_set \ b_set :=
  show 2 ∈ a_set ∧ 2 ∉ b_set
  exact ⟨ Or.inr (Or.inl rfl) , λ h => nomatch h ⟩

example : 3 ∉ a_set \ b_set := _

/-
Properties of Relations
-/

#reduce Reflexive (@Eq Nat)

lemma eq_nat_is_refl : Reflexive (@Eq Nat) := by
  unfold Reflexive
  intro x
  exact rfl

lemma eq_nat_is_symm : Symmetric (@Eq Nat) := by
  unfold Symmetric
  intro x y
  intro hxy
  rw [hxy]

#reduce eq_nat_is_symm

lemma eq_nat_is_trans : Transitive (@Eq Nat) := by
  unfold Transitive
  intro x y z
  intro hxy hyz
  rw [hxy]
  rw [hyz]

theorem eq_nat_is_equiv : Equivalence (@Eq Nat) :=
  Equivalence.mk @eq_nat_is_refl @eq_nat_is_symm @eq_nat_is_trans

def cong_mod_n : Nat → Nat → Nat → Prop := λ n a b => a%n = b%n

theorem cong_mod_n_equiv': ∀ n, Equivalence (cong_mod_n n) :=
  by
    intro n
    exact Equivalence.mk _ _ _

lemma cong_mod_n_rfl : ∀ (n: Nat), Reflexive (cong_mod_n n) := by
  intro n
  unfold cong_mod_n
  unfold Reflexive
  intro a
  exact rfl

lemma cong_mod_n_symm : ∀ (n: Nat), Symmetric (cong_mod_n n) := by
  intro n
  unfold Symmetric
  intro x y
  intro hxy
  unfold cong_mod_n
  unfold cong_mod_n at hxy
  rw [hxy]

lemma cong_mod_n_trans : ∀ (n : Nat), Transitive (cong_mod_n n) := by
  intro n a b c hab hbc
  unfold cong_mod_n
  unfold cong_mod_n at hab hbc
  rw [hab, hbc]

theorem cong_mod_n_equiv : ∀ (n: Nat), Equivalence (cong_mod_n n) :=
  by
    intro n
    unfold cong_mod_n
    exact Equivalence.mk
      (by intro x; rfl)
      (by intro x y h; rw [h])
      (by intros x y z hxy hyz; rw [hxy, hyz])
