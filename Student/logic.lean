/-!
### Predicates

A predicate is paramterized proposition. Applying a predicate to argument
(of the right type) yields a proposition.

Here's an example: this function returns an equality proposition
-/

def isEven(n : Nat): Prop := n % 2 = 0

#check isEven 0
#check isEven 1

#reduce isEven 0
#reduce isEven 1
#reduce isEven 2
#reduce isEven 3

/-!
### For All (∀)

In classical logic, the form of a universally quantified proposition is
∀ (p : P), Q. This says that for any (p : P) you can pick, Q is true.

That said, the more usual form of ∀ in practicals is ∀ (p : P), Q p, with
Q not being a predicate with argument p. the (Q p) is a proposition about p.
-/

example : ∀ (n : Nat), isEven n := _ --not true

def zornz : ∀ (n : Nat), n = 0 ∨ n ≠ 0 :=
  λ n => match n with
  | 0 => (Or.inl (Eq.refl 0))
  | (_ + 1) => (Or.inr (λ h => nomatch h))

#reduce zornz 3

/-!
### Elimination

-/

variable
  (P : Type)
  (Q: P → Prop)
  (R : Prop)
  (t : P)

#check P --type
#check Q --predicate
#check Q t --proposition
#check ∀ (p : P), Q p --propostion, pronounce it like: every p has property Q

#check ∀ (x : P), R

--degenerate example type of return value does not depend on arguments, this is just an ordinary function

/-
### Exists
-/

--general form introduction rule
example : ∃ (p : P), Q p := _ --there is some p that has property Q

example : ∃ (n : Nat), n ≠ 0 := (5, _)

def exists_even_nat : ∃ (n : Nat), isEven n := ( 2, rfl )

--elimination rule

def foo : (∃ (n : Nat), isEven n) → True
| ( n', pf ) => _

/-
Equality
-/

#check 1 = 0
#check Eq 1 0

#check Eq.refl 1

example: 1 + 1 = 2 := rfl

inductive IsEven : nat → Prop
| zero_is_even : IsEven 0
| even_plus_2_even : ∀ (n : Nat), IsEven n → isEven (n + 2)

Open IsEven
example : IsEven 0 := zero_is_even

example : IsEven 4 := even_plus_2_even 2 (even_plus_2_even 0)
