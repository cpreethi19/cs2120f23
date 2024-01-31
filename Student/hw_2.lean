/-
(1) Write a function called add that takes two natural numbers, a and b,
and returns their sum, a + b. Don't just look up the answer. Figure it out on your own.
Hint: do case analysis on the second argument (a Nat can be either Nat.zero or (Nat.succ n')
and use the fact that n + (1 + m) = 1 + (n + m).

(2) Write a function called append, polymorphic in a type, T, that takes two lists values,
n and m of type List T and that returns the result of appending the two lists.
For example, append [1,2,3] [4,5,6], should return [1,2,3,4,5,6].
Hint: It's very much list Nat addition.
-/

def sum : Nat → Nat → Nat
| a, Nat.zero => a
| a, Nat.succ b' => Nat.succ (sum a b')

#reduce sum 2 3

def mul : Nat → Nat → Nat
| n, 0 => 0
| n, Nat.succ m' => sum n (mul n m')

#eval mul 5 4

def exp : Nat → Nat → Nat
| n, 0 => 1
| n, Nat.succ m' => mul n (exp n m')

#eval exp 2 5

def append {α : Type}: List α → List α → List α
| List.nil, b => b
| List.cons a l, b => List.cons a (append l b)

#reduce append [1, 2, 3] [4, 5, 6]


/-
Now let's introduce a range of fundamental data types along with functions involving values of these types
-/

#check Bool

/-
inductive Bool : Type where
| false : Bool
| true : Bool
-/

#check Unit
/-
inductive PUnit : Sort u where
| unit : PUnit
-/

#check Empty
/-
inductive Empty : Type
-/

/-
function of empty to empty cannot be called but can be implemented
-/
def e2e : Empty → Empty
| e => e

#eval e2e _

/-
function of nat to empty cannot be implemented
-/
def n2e : Nat → Empty
| n=> e
