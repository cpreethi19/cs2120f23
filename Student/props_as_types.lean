/-
What is a proposition? It's an assertion that some fact is true
Supposed Q and P are propositions
Then we can write
P && Q    P and Q       (p, q)
P V Q     P or Q        (p, _) or (_, q)
P -> Q    P implies     if I have a function : P -> Q, then we know P -> Q is True
~P        not P

Truth table for implies
p     q       p->q
True  True    True
True  False   False
False True    True
False False   True
-/

#check Empty

/-
If I assume there is a value of type Empty, then I can return a value of type Empty
This is essentially False implies False
-/
def e2e : Empty → Empty
| e => e


/-
We are not able to build a function that returns an empty given a nat
This demonstrates that True implies False is False
-/
def n2e : Nat → Empty
| n => _

/-
Think of the proposition BobStudiesAtUVA as a type and its values as proofs
-/
inductive BobStudiesAtUVA
| attendsClasses
| paidTuition

inductive MaryStudiesAtUVA
| attendsClasses
| paidTuition

inductive MarkoStudiesAtUVA

def neg (α : Type) := α → Empty

example : neg MarkoStudiesAtUVA :=
λ m : MarkoStudiesAtUVA => nomatch m

/-
We basically encoded an and of operations to prove that Bob and Mary study at UVA
-/

inductive BobStudiesAtUVAAndMaryStudiesAtUVA
| and (b : BobStudiesAtUVA) (m : MaryStudiesAtUVA)

def b : BobStudiesAtUVA := BobStudiesAtUVA.paidTuition
def m : MaryStudiesAtUVA := MaryStudiesAtUVA.paidTuition
example : BobStudiesAtUVAAndMaryStudiesAtUVA :=
  BobStudiesAtUVAAndMaryStudiesAtUVA.and b m

inductive BobStudiesAtUVAOrMaryStudiesAtUVA
| left (b : BobStudiesAtUVA)
| right (m : MaryStudiesAtUVA)

example : BobStudiesAtUVAOrMaryStudiesAtUVA :=
  BobStudiesAtUVAOrMaryStudiesAtUVA.left b

inductive MyAnd (α β : Type)
| mk (a : α) (b : β)

example : MyAnd BobStudiesAtUVA MaryStudiesAtUVA := MyAnd.mk b m

inductive MyOr (α β : Type)
| inl (a : α)
| inr (b : β)

example : MyOr BobStudiesAtUVA MaryStudiesAtUVA := MyOr.inl b

example : MyOr BobStudiesAtUVA MaryStudiesAtUVA := MyOr.inr m

def MyNot (α : Type) := α → Empty

example : MyNot BobStudiesAtUVA := λ b => _ --Nope

example : MyNot MarkoStudiesAtUVA := λ m => nomatch m

inductive B : Prop
| paid
| classes

inductive M : Prop
| paid
| classes

inductive K : Prop

-- And ∧
-- intro: construct a pair of proofs
-- elim: show (P ∨ Q → R) by case analysis on proof od P ∨ Q

example : And B M := And.intro B.paid M.classes
def b_and_m_true : B ∧ M := And.intro B.paid M.classes
theorem b_and_m_true' : B ∧ M := And.intro B.paid M.classes
example : B ∧ M := ( B.paid, M.classes )

--elim


-- Or

--intro
example : B ∨ K := Or.inl B.paid

--elim
example : B ∨ K → B :=
λ bork => match bork with
| Or.inl b => b
| Or.inr k => nomatch k

example : ∀ (Raining Sprinkling Wt : Prop),
  (Raining ∨ Sprinkling) →
  (Raining → Wet) →
  (Sprinkling → Wet) →
  Wet :=
λ _ _ _ rors rw sp =>
match rors with
| Or.inl r => rw r
| Or.inr s => sp s

-- Not
-- intro: Prove ¬ P by proving P → False
-- elim: as with any function, elimination is by apply

--intro example
def notK : ¬K := λ k => nomatch k

--elim example (law of no contradiction)
example (P : Prop) : ¬P → P → False :=
λ np p => np p

example (P : prop) : ¬¬P → P
| nnp => _ --stuck

example (P : Prop) : (P ∨ ¬P) → (¬¬ P → P)
| pornp => match pornp with
  | Or.inl p => λ nnp => p
  | Or.inr np => λ nnp => nomatch (nnp np)

-- law of excluded middles: for any prop p you can for free have a proof of

-- ∀ (P : Prop), P ∨ ¬P
