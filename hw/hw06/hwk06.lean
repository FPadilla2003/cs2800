-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2023, HOMEWORK 6

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: ...
-/

/-
Technical instructions: same as in the last homework. 
-/


/-
NOTE: most of the LEAN proofs in this homework set require the _have_ tactic which we haven't learned yet at the time this homework is given. we will discuss _have_ on monday 16 october's lecture: see 15-code.lean posted on canvas. 

in short, you can use _have_ as an implementation of the modus ponens proof rule. if i have in my hypotheses

h1 : A -> B
and
h2 : A

then i can derive new hypothesis h3 : B by using

have h3 := h1 h2,

in my proof (between the _begin ... end_). 

for more details, see 15-code.lean posted on canvas. 
-/


import .mylibrary09
import .mylibrary14


/- HWK06-01: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
theorem implies_transitive1: forall A B C : Prop, (A -> B) -> (B -> C) -> (A -> C)
-- ANSWER:
 ... 



/- HWK06-02: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
theorem implies_transitive2: ∀ A B C : Prop, ((A → B) ∧ (B → C)) → (A → C)
-- ANSWER:
 ... 



/- HWK06-03: 
consider the two propositional logic formulas (1) and (2) given below:
  (1) A -> (B -> C)
  and
  (2) (A ∧ B) -> C
-/


/- HWK06-03-1: 
are formulas (1) and (2) equivalent? if not, exhibit a counterexample
-/
-- ANSWER:
/-
... 
-/


/- HWK06-03-2: 
can you build a formal proof by hand of the implication (1) -> (2) with the proof rules that we have defined so far?
(see list of proof rules in slide "cheat sheet" in our lecture slides.) 
if so, provide such a proof. 
-/
-- ANSWER:
/-
... 
-/


/- HWK06-03-3: 
can you build a formal proof by hand of the implication (2) -> (1) with the proof rules that we have defined so far?
(see list of proof rules in slide "cheat sheet" in our lecture slides.) 
if so, provide such a proof. 
if not, design a sound proof rule so that you can complete the proof, and complete the rule with your new rule. 
make sure your rule is _sound_, meaning it cannot be used to prove "false" from nothing!
-/
-- ANSWER:
/-
... 
-/





/- HWK06-04:

suppose that in addition to the proof rules in our cheat sheet (see lecture slides) we have the following two rules to deal with negation (these rules go from down to up, like the rules shown in the slides):

    Hyps ⊢ (G -> false)
  ----------------------- NotGoal
    Hyps ⊢ ¬G 


    Hyps, (P -> false) ⊢ G
  --------------------------- NotHyps
    Hyps, ¬P ⊢ G 

so these rules transform ¬A into (A -> false), in the goal and in the hypotheses, respectively. 

can you use these two rules, as well as any of the other rules in our cheat sheet, to prove the tautology P ∨ ¬P ? 
-/
-- ANSWER:
/-
... 
-/



/- HWK06-05: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
lemma redundant_and: ∀ p q : Prop, ((p ∨ q) ∧ (p ∨ ¬ q)) ↔ p 
-- ANSWER: 
 ... 


/- HWK06-06: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
theorem p_and_not_p_eq_false: ∀ p : Prop, (p ∧ ¬ p) ↔ false 
-- ANSWER: 
 ... 



/- HWK06-07: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
theorem and_elim: ∀ p q r : Prop, (p ∧ q) → (p → q → r) → r 
-- ANSWER:
 ... 


/- HWK06-08: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
theorem or_elim: ∀ p q r : Prop, (p ∨ q) → (p → r) → (q → r) → r 
-- ANSWER:
 ... 




/- HWK06-09: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
theorem not_p_not_q_iff: ∀ P Q : Prop, ¬P → (¬Q → (P ↔ Q)) 
-- ANSWER:
 ... 



/- HWK06-10: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
theorem mp_eq: ∀ P Q : Prop, ((P → Q) ∧ P) ↔ (P ∧ Q) 
-- ANSWER:
 ... 


/- HWK06-11: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
theorem contraposition: ∀ P Q : Prop, (P → Q) → (¬Q → ¬P) 
-- ANSWER:
 ... 



/- HWK06-12: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
theorem iff_and: ∀ P Q : Prop, (P ↔ Q) ↔ ((P → Q) ∧ (Q → P))
-- ANSWER:
 ... 


/- HWK06-13: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
theorem exportation: ∀ A B C : Prop, (A → B → C) ↔ (A ∧ B → C) 
-- ANSWER:
 ... 



/- HWK06-14: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
theorem xor_xor_iff: forall A B C : Prop, (and (xor A B) (xor B C)) -> (A <-> C)
 ... 


/- HWK06-15: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
theorem p_xor_true: ∀ P : Prop, (xor P true) ↔ ¬ P 
-- ANSWER:
 ... 





/- HWK06-16: 
let's continue formalizing the correctness of sorting programs like isort from your hwk01. in HWK04 we asked you to define functions leq and sortedb. correct implementations of those are given below: 
-/

def leq : nat -> nat -> bool 
  | 0 y := tt 
  | (nat.succ x) 0 := ff 
  | (nat.succ x) (nat.succ y) := leq x y 
--

def sortedb : list nat -> bool 
  | [] := tt 
  | [_] := tt 
  | (x :: (y :: L)) := andb (leq x y) (sortedb (y :: L)) 
--

/- HWK06-16-1:
claiming that a sorting program f : list ℕ → list ℕ always produces sorted lists is not enough to show that f is a correct sorting program. for example: (1) the program that always returns the empty list always produces sorted lists: prove that in LEAN. (2) the program that always returns the list [1,2,3] also always produces sorted lists: prove that too. 
-/

def fsrtempty: list ℕ → list ℕ := λ L, [] 
def fsrt123: list ℕ → list ℕ := λ L, [1,2,3] 

theorem fsrtempty_sorted: ∀ L : list ℕ, sortedb (fsrtempty L) = tt  
:= begin
-- ANSWER:
   ... 
end

theorem fsrt123_sorted: ∀ L : list ℕ, sortedb (fsrt123 L) = tt  
:= begin
-- ANSWER:
   ... 
end

/- HWK06-16-2:
now we know that producing sorted lists is not enough to make a sorting program correct. what other properties should a sorting program f satisfy then? the answer is, that (f L) should be a "permutation" of L, for any input list L. we will formalize permutation in two steps. 

define a function occurno : ℕ → list ℕ → ℕ  which takes a nat x and a list of nats L, and returns the number of times x occurs in L. as usual, all tests below must pass. 
-/

-- ANSWER:
def occurno : ℕ → list ℕ → ℕ  
   ... 

-- DO NOT DELETE:
example: occurno 0 [] = 0 := begin refl, end 
example: occurno 0 [1] = 0 := begin refl, end 
example: occurno 0 [1,2] = 0 := begin refl, end 
example: occurno 0 [1,2,3] = 0 := begin refl, end 
example: occurno 0 [0] = 1 := begin refl, end 
example: occurno 0 [0,1] = 1 := begin refl, end 
example: occurno 0 [0,0] = 2 := begin refl, end 
example: occurno 1 [1,0] = 1 := begin refl, end 
example: occurno 10 [10,0,10,10,10] = 4 := begin refl, end 

/- HWK06-16-3:
define a function permutation : list ℕ → list ℕ → Prop which takes two lists of nats L1 and L2, and returns the proposition "the number of occurrences of x in L1 is equal to those in L2, for any nat x".  
-/

-- ANSWER:
def permutation ... 

#check permutation 

/- HWK06-16-4:
now we can formalize the complete notion of correctness of a sorting program mysort: mysort must have two properties: it must produce sorted lists. but it must also produce output lists that have some relation to the input list (hint: permutation).  

state that mysort has these two properties as a LEAN theorem. 
you do NOT have to prove the theorem, just state it. 
-/
section hwk06_16 

variable mysort : list nat -> list nat 

-- ANSWER:
theorem mysort_correct: 
     ... 
:= begin
    sorry,
end


end hwk06_16



/- HWK06-17: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
theorem not_p_or_q_implies_p_implies_q: 
    ∀ p q : Prop, (¬p ∨ q) → (p → q)
-- ANSWER:  
  ... 



/- HWK06-18: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
lemma and_absorb_or_and: ∀ p q : Prop, (p ∧ (¬p ∨ q)) ↔ (p ∧ q) 
-- ANSWER: 
   .... 



/- HWK06-19: 
the famous _De Morgan's laws_ of propositional logic state that:

  1. ¬ (p ∨ q) is equivalent to (¬ p) ∧ (¬ q) 
  2. ¬ (p ∧ q) is equivalent to (¬ p) ∨ (¬ q) 

thou shalt (you shall) try to prove these laws. we will first split each equivalence into two implications, so you will have 4 separate lemmas to prove. try to prove as many of those 4 as you can in LEAN, using the tactics that you know. how many and which ones did you manage to prove completely? 

show all proofs (complete or not). end any incomplete proofs with sorry. 
-/

lemma deMorgan1: ∀ (p q : Prop), (¬ p ∧ ¬ q) → ¬ (p ∨ q) 
:= begin
-- ANSWER:
  ... 
end


lemma deMorgan2: ∀ (p q : Prop), (¬ p ∨ ¬ q) → ¬ (p ∧ q) 
:= begin
-- ANSWER:
  ... 
end


lemma deMorgan3: ∀ (p q : Prop), ¬ (p ∨ q) → (¬ p ∧ ¬ q) 
:= begin
-- ANSWER:
  ... 
end


lemma deMorgan4: ∀ (p q : Prop), ¬ (p ∧ q) → (¬ p ∨ ¬ q) 
:= begin
-- ANSWER:
   .... 
end

