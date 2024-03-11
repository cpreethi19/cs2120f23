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
