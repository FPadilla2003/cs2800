-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- lecture code 2023-10-11


import .mylibrary09
import .mylibrary14   -- NEW LIBRARY FILE POSTED ON CANVAS REQUIRED FOR THE EXAM!

#check plus
#check len 
#check negb 
#check orb 
#check andb 

#check mult 
#check exponent 
#check evenb 



/-
REMINDERS: 

  TOMORROW WE HAVE OUR EXAM 1 !!!
  
  IN CLASS, IN PERSON, NO REMOTE OPTION

  TAKE THE PRACTICE EXAM ON GRADESCOPE

  DOWNLOAD THE NEW LIBRARY FILE FROM CANVAS TO HAVE IT READY BEFORE THE EXAM: mylibrary14.lean 

-/



/-
    RECAP: WHERE WE STAND

At a minimum, you should be able to:

- write functions with types in LEAN (including recursive functions using pattern matching)

- recognize the type of a function, well-typed, and ill-typed (type error!) expressions

- write and prove examples-tests with refl

- write forall specifications, which include functions, =, and any of the logical connectives (→ , ¬ , ∧ , ∨ , ↔ , ...) 

- build truth tables and understand the concepts of SAT/UNSAT, valid, stronger, weaker, equivalent formulas

- do formal LEAN proofs by cases on finite types (bool, weekday, ...) 

- be able to do manual formal proofs (by hand) for formulas in propositional logic 

- be able to do formal proofs in LEAN for formulas in propositional logic 


If any of the above sounds strange, weird, never-heard-of, etc, COME TO OFFICE HOURS RIGHT AWAY!

consult the lecture notes regularly, especially sections 7 and 8:
    https://course.ccs.neu.edu/cs2800f23/lecture-notes.pdf
-/



-- TIME FOR SOME PRACTICE!!! 

-- ERASE ALL PROOFS AND TRY THEM ON YOUR OWN!

-- practice is the way to learn!


-- let's apply all the stuff we have learned so far:

lemma p_and_true: ∀ P : Prop, (P ∧ true) ↔ P 
:= begin
  intros p,
  split,
  {
    intro h,
    cases h with h1 h2,
    exact h1,
  },
  {
    intro h,
    split,
      assumption,
      trivial,
  },
end



lemma p_or_true: ∀ P : Prop, (P ∨ true) ↔ true 
:= begin
  intro,
  split,
  {
    intro h,
    trivial,
  },
  {
    intro h,
    right,
    trivial,
  },
end


theorem p_and_q_implies_q_and_p: ∀ p q : Prop, (p ∧ q) → (q ∧ p) 
:= begin
  intros p q,
  intro h,
  cases h with h1 h2,
  split,
  {
    exact h2,
  },
  {
    exact h1,
  },
end







/-
QUIZZES: EXAM PRACTICE!
-/



/-
Qz10a: I was able to finish the LEAN proof given in class:

theorem and_associative: forall A B C : Prop, 
    (and A (and B C)) <-> (and (and A B) C)

ANSWERS: YES/NO  (BOTH ANSWERS ARE CORRECT = EARN YOU SAME POINTS)

-- respond at: https://pollev.com/tripakis

-/


theorem and_associative: forall A B C : Prop, 
    (and A (and B C)) <-> (and (and A B) C)
:= begin
  intro,
  intro,
  intro,
  split,
  {
    intro h,
    cases h with h1 h2,
    cases h2 with h2 h3,
    split,
    {
      split,
      {
        exact h1,
      },
      exact h2,
    },
    exact h3,
  },
  {
    intro h,
    cases h,
    cases h_left,
    split,
    assumption,
    split,
    assumption,
    assumption,
  },
end









/-
Qz10b: I was able to reply to the quiz given in class:

is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:

theorem or_absorb_and: ∀ P Q : Prop, (P ∨ (P ∧ Q)) ↔ P 

ANSWERS: YES/NO  (BOTH ANSWERS ARE CORRECT = EARN YOU SAME POINTS)

-- respond at: https://pollev.com/tripakis

-/


theorem or_absorb_and: ∀ P Q : Prop, (P ∨ (P ∧ Q)) ↔ P 
:= begin
  intro,
  intro,
  split,
  {
    intro h,
    cases h,
    {
      exact h,
    },
    {
      cases h with h1 h2,
      exact h1,
    }
  },
  {
    intro h,
    left,
    assumption,
  },
end











/-
REVIEW: any homework problems you want to go over?  this includes homework 05  
-/



open weekday


theorem next_workday_not_weekend: 
    ∀ d : weekday, next_workday d ≠ sunday ∧ next_workday d ≠ saturday 
:= begin
  intro,
  split,
  repeat {
    intro h,
    cases d,
    repeat {
      contradiction,
    },
  },
end





/- HWK05-13: 
is the claim below true? if so prove it in LEAN, if not, exhibit a counterexample:
-/
theorem p_implies_xor: ∀ p q : Prop, p → ((xor p q) ↔ ¬q)
:= begin
    intros p q h1,
    split,
    {
        intro h2,
        cases h2,
        {
            cases h2 with h3 h4,
            exact h4,
        },
        {
          cases h2 with h3 h4,
          contradiction, -- we'll see why this works soon 
        }
    },
    {
        intro h2,
        left,
        split,
        assumption,
        assumption,
    },
end


