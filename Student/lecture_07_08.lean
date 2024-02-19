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

def list_map {α β : Type} : (α → β) → List α → List β
| _, List.nil => List.nil
| f, h::t => f h::list_map f t

def option_map {α β : Type} : (α → β) → Option α → Option β
| _, Option.none => Option.none
| f, Option.some a => some (f a)

inductive Tree (α : Type) : Type
| empty
-- | node : α → Tree α → Tree α → Tree α
| node (a : α) (l r : Tree α) : Tree α

def tree_map {α β : Type} : (α → β) → Tree α → Tree β
| _, Tree.empty => Tree.empty
| f, (Tree.node a l r) => Tree.node (f a) (tree_map f l) (tree_map f r)

#reduce tree_map Nat.succ Tree.empty

def a_tree :=
  Tree.node
    1
    (Tree.node
      2
      Tree.empty
      Tree.empty
    )
    (Tree.node
      3
      Tree.empty
      Tree.empty
    )

#reduce tree_map Nat.succ a_tree


/-!
-/

structure functor {α β : Type} (c : Type → Type) : Type where
map (f : α → β) (ic : c α) : c β

def list_functor {α β : Type} : @functor α β List := functor.mk list_map
#check @list_functor
def option_functor {α β : Type} : @functor α β Option := functor.mk option_map

def convert {α β : Type} (c : Type → Type) (m : @functor α β c) : (f : α → β) → c α → c β
| f, c => m.map f c

#reduce convert List list_functor Nat.succ [1, 2, 3, 4, 5]
#reduce convert Option option_functor Nat.succ (Option.some 3)

inductive Box (α : Type)
| contents (a : α)

#reduce convert Box _ Nat.succ (Box.contents 3)
