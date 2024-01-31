/-
Review of how to write function comp
-/
def comp {α β γ : Type}: (β → γ) → (α → β) → (α → γ)
| g, f => λ a => g (f a)

/-
Function composition: compose 4 times
-/

def comp4 {α : Type} : (α → α) → (α → α)
| f => fun a => (f ∘ f ∘ f ∘ f) a

def square (n: Nat) : Nat := n^2
def inc (n : Nat) := Nat.succ n

/-
First case Nat.zero, meaning the function is applied 0 times to argument
Nat.zero, f => λ a => a
that's the base case, now you can recur
-/
def compn' {α : Type} : Nat → (α → α) → (α → α)
| Nat.zero, f => fun a => a
| (Nat.succ n'), f => f ∘ (compn' n' f)

/-
use the composition function instead
-/
def compn {α : Type} : Nat → (α → α) → (α → α)
| Nat.zero, f => fun a => a
| (Nat.succ n'), f => λ a => (f ∘ compn n' f) a

#reduce compn 3 inc 1
def sq(n : Nat) := n * n
#eval compn 5 sq 2

#check (@List)

/-
Inductive List (α : Type u) where
| nil : List a
| cons (head : α) (tail : List α) : List α
-/

def e : List Nat := List.nil
def e' : List Nat := []

def l1 : List Nat := List.cons 1 e
def l1' : List Nat := 1::e
def l1'' : List Nat := [1]

def l2 : List Nat := List.cons 0 l1
#reduce l2
/-
list.cons 0 (list.cons 1 empty list)
head of the list followed by smaller list
-/

def list_len{α : Type} : List α → Nat
| List.nil => 0
| (List.cons _ t) => 1 + list_len t
