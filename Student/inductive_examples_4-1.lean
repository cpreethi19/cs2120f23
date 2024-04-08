/-
inductive Person

def Loves := Person → Person → Prop

def els : Prop := ∀ (p : Person), ∃ (q : Person), Loves

-/
example :
  ∀ (Person : Type)
    (Loves : Person → Person → Prop)
    (p q : Person),
    (∃ (q : Person), ∀ (p : Person), Loves p q) →
    (∀ (p : Person), ∃ (q : Person), Loves p q) :=
  λ Person Loves p q sel k => match sel with
  | ⟨joe, everyone_loves_joe ⟩ => ⟨joe, everyone_loves_joe k ⟩


variable
  (Ball : Type)
  (Heavy : Ball → Prop)
  (Red : Ball → Prop)

example : (∃ (b : Ball), Red b ∧ Heavy b) → (∃ (b : Ball), Red b ∨ Heavy b) :=
λ h => match h with
| ⟨ ball, redandheavy ⟩ => ⟨ball, Or.inr redandheavy.2⟩

example :(∃ (b : Ball), ¬(Red b))  → (¬ ∀ (b : Ball), Red b) :=
λ nonred => match nonred with
| ⟨nrb, pfnrb⟩ => λ h =>
  let rb := (h nrb)
  -- by contradiction
  False.elim (pfnrb rb)
