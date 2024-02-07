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
