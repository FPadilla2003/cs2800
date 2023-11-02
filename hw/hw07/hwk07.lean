-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2023, HOMEWORK 7


/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: Artur Efremenko, Felipe Padilla
-/


/-
Technical instructions: same as in the last homework
-/

/- ADDITIONAL INSTRUCTIONS:

Just like you are welcome to use any function defined in class or in previous homeworks or in the current homework, you are also welcome to use any lemma/theorem/example proved in class or in previous homeworks or in the current homework. 

You are also allowed to define and use your own helper functions and you are also allowed to define and use/call your own lemmas/theorems, in order to prove other theorems. 

in this homework we sometimes ask "did you have to use classical.em?"  you should first try to do your proof without classical.em or classical.by_contradiction. only use those when necessary. 
WE WILL CUT POINTS OFF IF YOU USE classical.em or classical.by_contradiction UNNECESSARILY.  

in this homework we sometimes ask "is your proof constructive?". a proof is constructive if it does NOT rely on classical axioms classical.em or classical.by_contradiction. write your answer as a LEAN comment. 

write any counterexamples also as LEAN comments. 

-/


import .mylibrary09 
import .mylibrary14



/- HWK07-01:
the lemma nat.zero_lt_succ is defined (proven) in the LEAN library. you don't have to know how it's proven. you only need to be able to understand (1) what it says, and (2) how to use/call it. 
-/

#check nat.zero_lt_succ   -- move your cursor here to see what this lemma states 

/- HWK07-01 continued:
prove that 0 < 2 by using the "have" tactic to call lemma nat.zero_lt_succ 
-/
example: 0 < 2  
:= begin
-- ANSWER:
  have h1 : 0 < 2 := nat.zero_lt_succ (nat.succ 0),
  exact h1,
end




/- HWK07-02:
we will prove that plus x 0 = x, with a little help from our friends, the lemmas. 
-/

/- HWK07-02-1:
prove the lemma plusind0:
-/
lemma plusind0: plus 0 0 = 0 
:= begin 
-- ANSWER:
  refl,
end

#check plus

/- HWK07-02-2:
prove the lemma plusind1:
-/
lemma plusind1: ∀ (x : ℕ), plus x 0 = x → plus (nat.succ x) 0 = nat.succ x
:= begin
-- ANSWER:
  intro h1,
  intro h2,
  cases h1 with h3 h4,
  split,


end

/-
suppose the lemma plusind2 is given to you. you do NOT have to prove it. ignore the fact that the proof below is empty ("sorry"). you can still call the lemma plusind2. 
-/
lemma plusind2: 
    plus 0 0 = 0 → 
    (∀ x : ℕ, plus x 0 = x → plus (nat.succ x) 0 = nat.succ x) → 
    (∀ x : ℕ, plus x 0 = x)
:= sorry -- leave this here 

/- HWK07-02-3:
use the above three lemmas, and the "have" tactic, in order to prove the theorem plus_x_0. you can also use any other tactics that we have learned. 
-/
theorem plus_x_0: ∀ x : ℕ, plus x 0 = x 
:= begin
-- ANSWER:
  ... 
end






/- HWK07-03-1:
prove the following directly, without calling any other lemmas/theorems. 
-/
example: ∀ x : nat, x = 0 ∧ x ≠ 0 → x > 10 
:= begin
-- ANSWER: direct proof:
   ... 
end

/- HWK07-03-2:
prove the same result by calling a lemma/theorem that we proved already in class. you must find which lemma or theorem you want to use among those that we proved in class already. read the lecture code and decide. copy the lemma/theorem that you chose here, and then use it. 
-/
-- ANSWER: proof using the following result proven in class:
 ... 

example: ∀ x : nat, x = 0 ∧ x ≠ 0 → x > 10 
:= begin
-- ANSWER: 
  ... 
end






/- HWK07-04:
the theorems "le_transitive" and "lt_implies_le" below are given to you. you don't need to know how they have been proven. consider them part of some "black-box" library. you can call stuff from that library, but you don't need to know how they are implemented. 

use these theorems to prove theorem hwk07_04.  
-/

theorem le_transitive: ∀ x y z : ℕ, x ≤ y → y ≤ z → x ≤ z 
:= begin
    intro,
    intro,
    intro,
    intro h1,
    intro h2,
    apply nat.le_trans h1 h2,
end

theorem lt_implies_le: ∀ x y : ℕ, x < y → x ≤ y 
:= begin
    intro,
    intro,
    intro h,
    apply le_of_lt h,
end

theorem hwk07_04: ∀ a b c : ℕ, (a < b ∧ b < c) → a ≤ c 
:= begin
-- ANSWER:
   ... 
end







/- HWK07-05:
is the following claim true? if so prove it and answer the question: is your proof constructive? if you believe the claim is not true, exhibit a counterexample. 
-/
theorem p_xor_not_p: ∀ P : Prop, xor P ¬P 
-- ANSWER: 
... 




/- HWK07-06: 
is the following claim true? if so prove it and answer the question: is your proof constructive? if you believe the claim is not true, exhibit a counterexample. 
-/
theorem p_iff_false: ∀ P : Prop, (P ↔ false) ↔ ¬ P 
-- ANSWER: 
... 




/- HWK07-07: 
is the following claim true? if so prove it and answer the question: is your proof constructive? if you believe the claim is not true, exhibit a counterexample. 
-/
lemma or_absorb_and_or: ∀ p q : Prop, p ∨ (¬ p ∧ q) ↔ (p ∨ q) 
-- ANSWER: 
... 



/- HWK07-08: 
is the following claim true? if so prove it and answer the question: is your proof constructive? if you believe the claim is not true, exhibit a counterexample. 
-/
lemma not_p_implies_p: ∀ P : Prop, (¬ P → P) ↔ P 
-- ANSWER: 
... 



/- HWK07-09: 
is the following claim true? if so prove it and answer the question: is your proof constructive? if you believe the claim is not true, exhibit a counterexample. 
-/
lemma or_if: ∀ (P Q : Prop), P ∨ Q ↔ (¬ P → Q) 
-- ANSWER: 
... 




/- HWK07-10: 
consider the following formulas:
(1) (A → B) ∧ (¬A → C)  
(2) (A ∧ B) ∨ (¬A ∧ C) 
are they equivalent? or is one stronger than the other? which one?

if you think they are equivalent, prove it, using Props. is your proof constructive?

if you think one is strictly stronger than the other, prove the implication that holds, and provide counterexample for the implication that does not hold. 
-/
-- ANSWER: 
... 



/- HWK07-11: 
you can now prove all four De Morgan's laws. do that below, and state which proofs are constructive. 
you may copy the proofs you already did in hwk06. 
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
... 
end




/- HWK07-12: 
use the 4 lemmas deMorgan1, deMorgan2, deMorgan3, deMorgan4 to prove the two deMorgan theorems below (in this problem we are not asking you to re-do the proofs by copy-pasting the lemma proofs you wrote above, but instead to **call** the above lemmas at the appropriate places in your proof):
-/
theorem deMorgan_or: ∀ p q : Prop, ¬ (p ∨ q) ↔ (¬p ∧ ¬q)
:= begin
-- ANSWER:
  ... 
end


theorem deMorgan_and: ∀ p q : Prop, ¬ (p ∧ q) ↔ (¬p ∨ ¬q) 
:= begin
-- ANSWER:
  ... 
end



/- HWK07-13:
use some theorems we proved in class to prove theorem not_p_or_q_iff_p_implies_q given below. again, you should not copy-paste the proofs we did in class, but you should call the right theorems. feel free to copy-paste these theorems from the lecture notes. 
-/
-- ANSWER:
... 

theorem not_p_or_q_iff_p_implies_q: 
    ∀ p q : Prop, (¬p ∨ q) ↔ (p → q)
:= begin
  ... 
end



/- HWK07-14: 
you will now prove the law of excluded middle assuming the law of contradiction.

note: this is a more challenging problem than usual. this is intentional. 
-/

def contra              := ( ∀ p : Prop, ¬¬p → p )
def law_excluded_middle := ( ∀ p : Prop, p ∨ ¬ p )

/- HWK07-14-1: 

prove the theorem "contra_implies_em" given below. 

you are NOT allowed to use neither classical.em, nor classical.by_contradiction! 

you are allowed to use any of the previously proven lemmas/theorems, AS LONG AS THEY THEMSELVES DON'T RELY ON either classical.em, nor classical.by_contradiction! 
-/

theorem contra_implies_em: contra → law_excluded_middle
:= begin 
-- ANSWER:
   ... 
end




/- HWK07-14-2: 
can you prove theorem not_not_p_implies_p_implies_p_or_not_p below constructively?

theorem not_not_p_implies_p_implies_p_or_not_p: 
  ∀ p : Prop, (¬ ¬ p → p) → (p ∨ ¬ p)

explain the difference between not_not_p_implies_p_implies_p_or_not_p and contra_implies_em.
-/
-- ANSWER:
... 




/- HWK07-15: 
use _rewrite_ to prove the following. 

NOTE: for this problem we want you to learn to use the _rewrite_ tactic. there is a very short proof (4 lines!) using _rewrite_ and other tactics that we learned. there are also longer proofs. try to find the short one. we will cut points off for too long proofs.  
-/
theorem iff_trans: ∀ A B C : Prop, (A ↔ B) ∧ (B ↔ C) → (A ↔ C) 
:= begin
-- ANSWER:
   ... 
end


/- HWK07-16: 
prove the following theorem:
-/

theorem and_distrib_or: ∀ A B C : Prop, A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) 
:= begin
-- ANSWER:
   ... 
end




/- HWK07-17-1: 

prove theorem  not_xor given below. 

for this problem, you can prove the result in any way you want. in particular, you can use any of the theorems listed above. 
-/

theorem not_xor: ∀ (p q : Prop), (¬ xor p q) ↔ ((p ∧ q) ∨ (¬ p ∧ ¬ q))
:= begin
-- ANSWER:
 ... 
end



/- HWK07-17-2:
prove the same result, by completing the proof below, using ONLY the rw (rewrite) tactic! 

for this problem, you can also use any of the LEAN library theorems listed below. 
NOTES:
  - as always, you are allowed to use ANY previously proven result in class, in given libraries, in previous homeworks, or in the same homework. in particular, you ARE allowed to use De Morgan's laws and any of the theorems listed above. 

  - you may have to do a lot of rewrites. this is normal. in my proof i used rw 17 times, but there might be shorter proofs. 

  - for proofs like this one, it might be a good idea to FIRST WORK OUT THE PROOF ON PAPER AND PENCIL. see how you would prove this using the logical equivalences you know (de Morgan, etc). then try to re-do the same proof in LEAN. 
-/

-- for this problem, you can also use any of these LEAN library theorems: 
#check and_self
#check or_self
#check and_comm 
#check or_comm 
#check and_assoc
#check or_assoc 
#check or_false 
#check false_or 
#check or_true 
#check true_or 
#check and_true
#check true_and 
#check and_false 
#check false_and


theorem not_xor_rw: ∀ (p q : Prop), (¬ xor p q) ↔ ((p ∧ q) ∨ (¬ p ∧ ¬ q))  
:= begin
  intro,
  intro,
  unfold xor,
-- use only the "rw" tactic (as many times as you want) in the rest of the proof. 
-- ANSWER: 
  ... 
end




/- HWK07-18: 
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
example: ∀ x y : ℕ, x = y+1 → x > 0 → (x > 0 ∧ y+1 > 0) 
-- ANSWER: 
 ... 



/- HWK07-19: 
consider the following functions:
-/

def app : list nat -> list nat -> list nat 
  | [] L := L 
  | (a :: L1) L2 := a :: (app L1 L2)
--

def tail: list nat -> list nat 
  | [] := []
  | (x :: L) := L
--

def minus1: nat -> nat 
    | 0 := 0 
    | (nat.succ x) := x 
--



/- HWK07-19-1:
write the LEAN theorem "len_tail_or" stating that for any list of nats L, either L is empty and the length of the tail of L is zero, or the length of the tail of L is one less than the length of L. use the "minus1" function above to express "one less". use "or" (and not "xor") to combine the two parts. 

then prove the theorem "len_tail_or". (hint: you can do cases on lists) 
-/
-- ANSWER:
theorem len_tail_or:  ... 


/- HWK07-19-2:
does the statetement hold if we use "xor" instead of "or"? if yes, prove it also with "xor". if not, provide a counterexample. 
-/
-- ANSWER:
... 
