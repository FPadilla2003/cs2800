-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2023, HOMEWORK 4

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

do NOT use LEAN's predefined functions on bools, nor their corresponding infix operators &&, ||, etc. instead, use our own negb, andb, orb, functions, provided in the library imported below.

as always, you may also use any of the functions you already defined in this homework for subsequent problems in the homework. e.g., you may use leq in your definition of sortedb below. 

Replace "..." below with the names of the people in your group.

Names of ALL group members: ...
-/

/-
Technical instructions: same as in the last homework. 

ADDITIONAL INSTRUCTIONS FOR FORMAL PROOFS BY HAND: in several problems in this homework we ask you to do formal proofs "by hand". we will NOT accept LEAN proofs (if you already know how to do these proofs in LEAN it's great! but we want to make sure you also know how to do them "by hand" without the help of LEAN). you can type your formal proofs as LEAN comments following the style in our lecture slides 10-formal-proofs.pdf. or you can write them on a piece of paper, and scan that into a PDF. or you can write them using another software (e.g., latex) and the compile into a PDF. then you will submit the PDF together with this .lean file as a .zip file in bottlenose. if you submit a PDF, make it VERY CLEAN which page of the PDF solves which homework problem! 
-/


/- THIS HOMEWORK GOALS:

- write formal specifications as LEAN propositions (Props)
- understand whether a formal specification is "complete"
- understand forall vs exists quantifiers 
- appreciate the difference between claims written in English vs formally
- review of propositional logic: truth tables, satisfiability, validity, strong/weak formulas, ... 
- start doing formal proofs by hand

-/


-- DO NOT DELETE:
import .mylibrary09

-- these functions are defined in the library; you can use them
#check plus
#check len 
#check negb 
#check andb 
#check orb 


/- HWK04-01:

let's start formalizing the correctness of sorting programs like isort from your hwk01.

define the function leq : nat -> nat -> bool such that (leq x y) = tt if x is less or equal to y, and ff otherwise. 

do NOT use any of LEAN's predefined operators (e.g., <=, ≤, or anything else). define leq from scratch, using recursion and pattern matching. 

make sure your function passes all tests provided below.  
-/

-- ANSWER:
def leq : nat -> nat -> bool 
  | 0 0 := tt
  | 0 y := tt
  | x 0 := ff
  | x y := if (x <= y) then tt else ff
--

-- DO NOT DELETE:
example: leq 0 0 = tt := begin refl, end 
example: leq 0 1 = tt := begin refl, end 
example: leq 0 2 = tt := begin refl, end 
example: leq 0 10 = tt := begin refl, end 
example: leq 1 0 = ff := begin refl, end 
example: leq 1 1 = tt := begin refl, end 
example: leq 10 0 = ff := begin refl, end 
example: leq 10 10 = tt := begin refl, end 
example: leq 1 2 = tt := begin refl, end 
example: leq 10 0 = ff := begin refl, end 
example: leq 10 1 = ff := begin refl, end 
example: leq 10 2 = ff := begin refl, end 


/- HWK04-02:

define a function sortedb : list nat -> bool which returns tt if the input list is sorted in increasing order, and ff otherwise. 

define sorted from scratch. you can use the leq function you defined above. you can also use our library operators on bools: negb, andb, etc. nothing else.  

all tests provided below must pass. 
-/
-- ANSWER:
def sortedb : list nat -> bool 
  | [] := 
  | (_ :: _) := 
--

-- DO NOT DELETE:
example: sortedb [] = tt := begin refl, end 
example: sortedb [1] = tt := begin refl, end 
example: sortedb [0,0,0,0] = tt := begin refl, end 
example: sortedb [1,2,3] = tt := begin refl, end 
example: sortedb [1,1,2,3,3,4,10,1000,1000,10000] = tt := begin refl, end 
example: sortedb [3,2,1,0] = ff := begin refl, end 
example: sortedb [2,3,1] = ff := begin refl, end 
example: sortedb [1,2,3,2,3] = ff := begin refl, end 




/- HWK04-03:

we want to formalize the proposition that a sorting program outputs sorted lists. we don't really care what the sorting program does. let's assume that we have a sorting program called mysort:
-/
-- this basically says "let mysort be some function from list nat to list nat" : 
section hwk04_3 -- it's good to enclose "variable" declarations like the one below within a "section" scope

variable mysort : list nat -> list nat 

/- HWK04-03-1:

write as a formal LEAN specification the property "mysort always produces sorted lists":
-/
-- ANSWER:
#check ... put your formal spec here ... 

end hwk04_3




/- HWK04-03-2:

is the above specification enough to specify that mysort is correct? that is, is the above specification complete, or is it missing some additional properties that mysort must have in order to be correct?

if you answer "NO" then provide a buggy implementation of mysort, called buggysort. buggysort must satisfy the above specification, that is, it must produce sorted lists:  prove that it does. 

however, buggysort must be incorrect in another way. explain why. 
-/
-- ANSWER:
... 




/- HWK04-04-1:

If A is some set, then x ∈ A denotes that x is a member (or element) of A. Sometimes people write things like ∀ x ∈ A, x ≥ 0. What does this claim mean? (choose one of the options below as your answer)

  - ∀ x, x ∈ A ∧ x ≥ 0
  - ∀ x, x ∈ A ∨ x ≥ 0
  - ∀ x, x ∈ A → x ≥ 0  

-/
-- ANSWER:
-- ... copy here one of the 3 options above ... 



/- HWK04-04-2:

Sometimes people write things like ∃ x ∈ A, x ≥ 0. What does this claim mean? (choose one of the options below as your answer)

  - ∃ x, x ∈ A ∧ x ≥ 0
  - ∃ x, x ∈ A ∨ x ≥ 0
  - ∃ x, x ∈ A → x ≥ 0  

-/
-- ANSWER:
-- ... copy here one of the 3 options above ... 







/- HWK04-05-1:

write down as a formal LEAN specification the following property: "for any even natural number x, x modulo 2 is zero." you can assume there is a function even with the type below that checks whether a given nat x is even (even x = tt) or odd (even x = ff). you can also assume there is a function modulo that returns the remainder of x divided by y. 

make sure that your specification is of type Prop (#check must confirm that). 
-/
section hwk04_5

variable even : nat -> bool  
variable modulo : nat -> nat -> nat 

-- ANSWER:
#check ... your answer here ... 


/- HWK04-05-2:

write down as a formal LEAN specification the following property: "for any integer number x, there is an even natural number y that is greater or equal to the absolute value of x." you can assume there is a function abs that returns the absolute value of an int. you can use the leq function that you defined above to express the "greater or equal" part. 

make sure that your specification is of type Prop (#check must confirm that). 
-/

variable abs : int -> nat 


-- ANSWER:
#check ... your answer here ... 

end hwk04_5




/- HWK04-06-1:

suppose people are identified by nats, and there is a predicate Loves with the type given below and the intended meaning that (Loves x y) is true if x loves y. 

write down as a formal LEAN specification the claim (a) below: 

(a) There is someone who loves everyone.

-/

section hwk04_6

def person := nat 
variable Loves : person -> person -> Prop 

-- ANSWER:
#check ... your answer here ... 


/- HWK04-06-2:

write down as a formal LEAN specification the claim (b) below: 

(b) There is someone whom no one loves.

-/

-- ANSWER:
#check ... your answer here ... 


/- HWK04-06-3:

Are the two claims (a) and (b) consistent with each other? (I.e., is their conjunction satisfiable?) Justify/argue informally your yes/no answer. 
-/
-- ANSWER:
/-
...
-/

end hwk04_6


/- UNGRADED -- for your own practice and fun 

suppose humans are identified by nats, time is also a nat, and there is a predicate CanBeFooled with the type given below and the intended meaning that (CanBeFooled x t) is true if person x can be fooled at time t. 

express in LEAN (as Props) the following claims:

(a) You can fool some people sometimes.
(b) You can fool some of the people all of the time.
(c) You can fool some people sometimes but you can't fool all the people all the time [Bob
Marley].
(d) You can fool some of the people all of the time, and all of the people some of the time,
but you can not fool all of the people all of the time [Abraham Lincoln].

explain informally the difference between all these claims. 
-/

section hwk04_fool 

def time := nat 
variable CanBeFooled : person -> person -> Prop 

-- ANSWERS:
-- you don't need to submit anything here and we won't grade it, but we'd be happy to discuss it in class or during office hours. 

end hwk04_fool 







/- HWK04-07:
recall the function list1toN requested in HWK02. a correct implementation of list1toN is provided below. write a theorem stating that the length of the list produced by the call (list1toN n) should be n. leave the proof of your theorem unfinished with := begin sorry, end. 
-/


def list1toNhelp : ℕ → ℕ → list ℕ 
  | 0 _ := []
  | (n+1) x := (x-n) :: (list1toNhelp n x)

def list1toN (n : nat) : list nat := list1toNhelp n n 
--

-- ANSWER:
theorem list1toN_n_len_n: ... your answer here ... 
:= begin
    sorry,
end




/- HWK04-08:
consider the functions exponent and myexp given below. write a LEAN theorem stating that the two functions are "almost" equivalent, meaning that they are equivalent except when both inputs are 0. as usual complete your theorem with the proof := begin sorry, end. 
-/

def mult : ℕ → ℕ → ℕ 
  | nat.zero _ := nat.zero 
  | (nat.succ x) y := plus y (mult x y)  
--

def exponent : nat -> nat -> nat 
  | x 0 := 1 
  | x (e+1) := mult x (exponent x e)
--

def myexp : ℕ → ℕ → ℕ 
  | 0 _ := 0
  | (nat.succ x) 0 := 1
  | (nat.succ x) (nat.succ n) := mult (nat.succ x) (myexp (nat.succ x) n) 
--

#eval exponent 0 0 
#eval myexp 0 0 
#eval exponent 2 3 
#eval myexp 2 3 


-- ANSWER:
theorem myexp_almost_equiv_to_exponent: ... your answer here ... 
:= begin
    sorry,
end




/- HWK04-09:
recall the function rl from HWK03. state as a LEAN theorem the property that "for any list of nats L, if we pass to rl L and the length of L, then rl will return the same list L". 
-/


def rl : list ℕ → ℕ → list ℕ 
 | [] _ := []
 | (x :: L) 0 := (x :: L)
 | (x :: L) (nat.succ n) := rl (L ++ [x]) n 
--

-- ANSWER:
theorem rl_L_len_L: ... your answer here ... 
:= begin
    sorry,
end


/- HWK04-10:
recall the function apply from HWK03. find a function f such that the following property is true: "for any list of nats L, if we pass L and f to apply, then apply will return the same list L". Then state this property as a LEAN theorem. 
-/

def apply : list ℕ → (ℕ → ℕ) → list ℕ 
    | [] _ := []
    | (x :: L) f := (f x) :: (apply L f)
--

-- ANSWER:

theorem map_identity: ... your answer here ... 
:= begin
    sorry,
end



/- HWK04-11:
suppose we have written a function F : (list nat) -> (list nat). formalize the claim "every list produced by F contains at least one element which is 0". write this claim as a forall-specification in LEAN. complete the LEAN theorem given below, but don't prove it. 

NOTE: you should NOT use ∃ (exists) quantifiers in your theorem. instead, you can define a helper function which captures for a given list L the property "L contains at least one element which is 0". then you can use this helper function in your forall-specification. 
-/

section hwk04_11 

-- we suppose F exists, we don't care how it's defined 
variable F : (list nat) -> (list nat) 

-- ANSWER:
... 

theorem everyoutputofFcontainsatleastone0:
   ... your answer here ... 
:= begin sorry, end 

end hwk04_11




/- HWK04-12:
consider the inductive data type below:
-/

inductive foo : Type 
  | bar : foo 
  | ber : ℕ → foo → foo 
  | bor : foo → bool → foo → foo 

/- HWK04-12-1:
is foo a finite or is it an infinite type? why?
-/
-- ANSWER:
-- ... your answer here ... 

/- HWK04-12-2:
provide at least 3 distinct elements of foo, using ALL its constructors:
-/
-- ANSWER:
#check ... 
#check ... 
#check ... 





/- HWK04-13: 
A. Construct the truth table for each of the following propositional logic formulas.
   Use alphabetical order for the variables in the formula, and create
   columns for all variables occurring in the formula AND for all
   intermediate subexpressions. For example, if your formula is

   (p → q) ∨ r

   your table should have 5 columns: for p, q, r, p → q, and (p → q) ∨ r .

   You can use 0 and 1, or F and T for false and true in your truth table. 

For each formula, you also have to:

B. Indicate if is satisfiable, unsatisfiable, valid, or falsifiable (exactly two of these characterizations will hold for each formula!).

C. Indicate how many assignments satisfy the formula (i.e., make the formula true).

D. If the formula is valid, submit a formal proof of this fact.  
-/

/-
Example: p ∧ (q ∨ ¬q)

ANSWER:

A: (Notice that we place T's and F's under the operator associated with the
   column, e.g., in the final column, we are taking a conjunction.)

p | q | ¬q | q ∨ ¬q | p ∧ (q ∨ ¬q)
-----------------------------
T | T | F  |   T    |   T
T | F | T  |   T    |   T
F | T | F  |   T    |   F
F | F | T  |   T    |   F

B: satisfiable and falsifiable

C: 2

D: formula is not valid, therefore i don't have to submit any proof. 
-/


/- HWK04-13 continued:

Do the above A,B,C steps for each of the following formulas:
1. x → (y → x)
2. x → (y → z)
3. (x → y) → z  
4. (p → (q ∧ r)) ∧ (r → ¬q)

-/
-- ANSWERS:
/- 1. ... 
-/

/- 2. ... 
-/

/- 3. ... 
-/

/- 4. ... 
-/




/- HWK04-14:
is the propositional formula below valid? if yes provide a formal proof by hand. if not provide a counterexample, i.e., an assignment that makes the formula false. 

(P ∧ Q) → Q 
-/
-- ANSWER:
/-
... 
-/



/- HWK04-15:
is the propositional formula below valid? if yes provide a formal proof by hand. if not provide a counterexample, i.e., an assignment that makes the formula false. 

(P ∧ Q) → (Q ∧ P)
-/
-- ANSWER:
/-
... 
-/



/- HWK04-16:
is the propositional formula below valid? if yes provide a formal proof by hand. if not provide a counterexample, i.e., an assignment that makes the formula false. 

(P ∧ Q) → (Q ∨ P) 
-/
-- ANSWER:
/-
... 
-/



/- HWK04-17:
is the propositional formula below valid? if yes provide a formal proof by hand. if not provide a counterexample, i.e., an assignment that makes the formula false. 

(P ∨ Q) → (Q ∨ P)
-/
-- ANSWER:
/-
... 
-/



/- HWK04-18:
is the propositional formula below valid? if yes provide a formal proof by hand. if not provide a counterexample, i.e., an assignment that makes the formula false. 

(P ∨ Q) → (Q ∧ P) 
-/
-- ANSWER:
/-
... 
-/




/- HWK04-19:
is the propositional formula below valid? if yes provide a formal proof by hand. if not provide a counterexample, i.e., an assignment that makes the formula false. 

(P ↔ Q) ↔ (Q ↔ P) 
-/
-- ANSWER:
/-
... 
-/





/- HWK04-20:
is the propositional formula below valid? if yes provide a formal proof by hand. if not provide a counterexample, i.e., an assignment that makes the formula false. 

(A ∨ (B ∨ C)) ↔ ((A ∨ B) ∨ C)
-/
-- ANSWER:
/-
... 
-/




/- HWK04-21:
is the propositional formula below valid? if yes provide a formal proof by hand. if not provide a counterexample, i.e., an assignment that makes the formula false. 

(P ∧ (P ∨ Q)) ↔ P 
-/
-- ANSWER:
/-
... 
-/




/- HWK04-22:
in class we claimed that IMPLICATION is the most important logical operator, in the sense that all other logical operators can be defined in terms of implication. show this. use your knowledge of propositional equivalences, e.g., implies in terms of or, de Morgan's laws, double negation, etc. 

in particular:
-/

/- HWK04-22-1:

express ¬P (not P) in terms of implies. 

that is, find a boolean expression E that uses only ->, P, true, false (it doesn't have to use all of these, and it can use the same thing multiple times), such that E is equivalent to ¬P. 

then prove that E is equivalent to ¬P, that is, prove that ¬P <-> E is valid: use the truth table method for that. 
-/
-- ANSWER:
/-
... 
-/



/- HWK04-22-2:

express P ∨ Q (or P Q) in terms of implies. 

that is, find a boolean expression E that uses only ->, P, Q, true, false (it doesn't have to use all of these, and it can use the same thing multiple times), such that E is equivalent to P ∨ Q.

then prove that E is equivalent to P ∨ Q, that is, prove that (P ∨ Q) <-> E is valid: use the truth table method for that. 
-/
-- ANSWER:
/-
... 
-/

/- HWK04-22-3:

express P ∧ Q (and P Q) in terms of implies. 

that is, find a boolean expression E that uses only ->, P, Q, true, false (it doesn't have to use all of these, and it can use the same thing multiple times), such that E is equivalent to P ∧ Q.

then prove that E is equivalent to P ∧ Q, that is, prove that (P ∧ Q) <-> E is valid: use the truth table method for that. 
-/
-- ANSWER:
/-
... 
-/

