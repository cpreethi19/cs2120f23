#check Bool.rec
#check Nat.rec
#check List.rec

inductive Tree (α : Type) where
| empty : Tree α
| node (a : α) (l r : Tree α  )


#check Tree.rec

example : (∀ (b : Bool), !!b = b) :=
by
  intros b
  induction b
  repeat {rfl}


example : (∀ (b : Bool), !!b = b) :=
by
  intros b
  cases b
  repeat {rfl}


def fact_0 := 1
def fact_succ_n : (n : Nat) → (fact_n : Nat) → Nat :=
  λ n fact_n => (n + 1) * fact_n

def fact : Nat → Nat
| 0 => fact_0
| Nat.succ n => fact_succ_n n (fact n)

#reduce fact 5

-- def fact : Nat → Nat := Nat

/-
Nat.rec.{u}
  {motive : Nat → Sort u}
  (zero : motive Nat.zero)
  (succ : (n : Nat) → motive n → motive (Nat.succ n))
  (t : Nat) : motive t
-/

#check List.rec


/-
List.rec.{u_1, u}
  {α : Type u}
  {motive : List α → Sort u_1}
  (nil : motive [])
  (cons : (head : α) → (tail : List α) → motive tail → motive (head :: tail))
  (t : List α) :
  motive t
-/

def list_empty_len := 0
-- def list_step {α : Type} : α → List α → Nat → Nat :=
