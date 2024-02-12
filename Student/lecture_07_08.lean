structure my_monoid' (α : Type) where
(op : α → α → α)
(id : α)

-- define general foldr function for my_monoid

def foldr' {α : Type} : my_monoid' α → List α → α
| m, [] => m.id
| m, h::t => m.op h (foldr' m t)

#eval foldr' (my_monoid'.mk Nat.add 0) [1, 2, 3, 4, 5]
#eval foldr' (my_monoid'.mk Nat.mul 1) [1, 2, 3, 4]
#eval foldr' (my_monoid'.mk String.append "") ["Hello", " my ", "name", " is ", "Preethi"]

def nary_add := foldr' (my_monoid'.mk Nat.add 0)
#eval nary_add [1, 2, 3, 4, 5]

/-
What does a moniod do? It extends a binary operator to be a n-ary operator
-/

structure my_monoid (α : Type) where
(op : α → α → α)
(id : α)
(left_id : ∀ a, op id a = a)
(right_id : ∀ a, op a id = a)
(op_assoc: ∀ a b c, op a (op b c) = op (op a b) c)

def nat_add_monoid : my_monoid Nat :=
  my_monoid.mk Nat.add 0 sorry sorry sorry

def foldr {α : Type}: my_monoid α → List α → α
| m, [] => m.id
| m, h::t => m.op h (foldr m t)

#eval foldr nat_add_monoid [1, 2, 3, 4, 5]

/-
Let's try to write out the proofs for the monoid now

to define constructor use backslash less than ⟨ and ⟩

by is a keyword that starts a tactic script, which is an automated proof construction algorithm

this proof: λ a => by simp (Nat.add)
for any arbitraty a will follow the rule for Nat.add

we define it this way so that if you accidentally write a 1 for the identity element, the proof checker will fail
-/
def nat_add_monoid' : my_monoid Nat :=
  ⟨ Nat.add,
    0,
    λ a => by simp (Nat.add),
    λ a => by simp (Nat.add),
    _
  ⟩

def nat_mul_monoid' : my_monoid Nat :=
  ⟨ Nat.mul,
    1,
    λ a => by simp (Nat.mul),
    λ a => by simp (Nat.mul),
    sorry
  ⟩

def nary_mul' : List Nat → Nat := foldr (my_monoid.mk Nat.mul 1 sorry sorry sorry)

/-
map function maps a list of one type to a list of another type
compare list and option data types
option has none, list has the empty list
can you imagine a defintion of map that takes option instead of list?
-/

#check (@Option)

def pred : Nat → Option Nat
| Nat.zero => Option.none
| (Nat.succ n') => n'

#reduce pred 3
#reduce pred 0

/-
define option map for square
-/

def option_map {α β: Type} : (α → β) → Option α → Option β
| f, Option.none => Option.none
| f, Option.some a => some (f a)
