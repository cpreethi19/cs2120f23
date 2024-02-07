-- 2/5
-- [1, 2] is really 1::(2::nil)

-- sum an entire list (or do some other operation)
def foldr''' : (Nat → Nat → Nat) → List Nat → Nat
| _, List.nil => 0
| op, h::t => op h (foldr''' op t)

-- id is the identity element for op
-- 0 for addition, 1 for multuplication, true for and

def foldr'' : (Nat → Nat → Nat) → Nat → List Nat → Nat
| _, id, [] => id
| op, id, h::t => op h (foldr'' op id t)

#reduce foldr''' Nat.add [1, 2, 3, 4, 5]
#reduce foldr''' Nat.mul [1, 2, 3, 4, 5] -- unexpected 0 result, because the base case is 0

#reduce foldr'' Nat.mul 1 [1, 2, 3, 4, 5] -- fixes the multiplication result by changing the identity function
#reduce foldr'' Nat.sub 0 [5, 3, 1]

/-!
Write a function that takes a list of strings and returns a single string
in which all the given strings are appended using List.append
-/
def foldStr : (List String) → String
| List.nil => ""
| (h::t) => String.append h (foldStr t)

#eval foldStr ["Hello", "World!"]
-- Note: if you get 'recursion limit exceeded' with reduce, try eval

-- abstract version of our earlier function
def foldr' {α : Type }: (α → α → α) → α → List α → α
| _, id, [] => id
| op, id, h::t => op h (foldr' op id t)

#eval foldr' String.append "" ["Hello", "World"]

def isEvenLen : String → Bool := λ s => s.length % 2 == 0

-- homework: write a function 'combine' that takes a string at the head of the list, a bool, and returns a bool
def combine : String → Bool → Bool := λ s b => isEvenLen s && b

-- return true if all strings in the list have even length
def foldr { α β : Type } : (α → β → β) → β → List α → β
| _, id, List.nil => id
| op, id, (h::t) => op h (foldr op id t)

/-
2/7
structure is a key word in lean for introducing a data type
mk is the default constructor for structure
you can represent logical propositions as types
in this definition, left_id and right_id are both propositions
-/

structure my_monoid (α : Type) where
(op : α → α → α)
(id : α)
(left_id : ∀ (a : α), op id a = a)
(right_id : ∀ (a : α), op a id = a)

/-
rewrite my_monoid using inductive
structure is basically an inductively defeined data type, useful when there is just one constructor
-/

inductive my_monoid' (α : Type) where
| mk : (op : α → α → α) →
(id : α) →
(left_id : ∀ (a : α), op id a = a) →
(right_id : ∀ (a : α), op a id = a) → my_monoid' α

-- sorry key word denotes that we don't know how to provide the proof necessary for this structure

def a_monoid : my_monoid Nat := my_monoid.mk Nat.add 0 sorry sorry
