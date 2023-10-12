-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- lecture code 2023-10-05

import .mylibrary09


-------------------------------------------------------
-- FORMAL PROOFS IN LEAN, continued 
-------------------------------------------------------


---------------------------------------------------------
-- implication continued 
---------------------------------------------------------

-- just like in types, the implications A → B → C are interpreted as A → (B → C), that is, "A implies (B implies C)", or in other words, "if A holds, then if B holds then C must hold". so, in the case of P → P → P, this gives "if P holds, then if P holds then P must hold", which is true: 
theorem p_implies__p_implies_p: ∀ P : Prop, P → (P → P)
:= begin
    intro,
    intro h1,
    intro h2,
    exact h1, -- or exact h2  
end

-- but this doesn't hold:
theorem p__implies_p_implies_p: ∀ P : Prop, (P → P) → P    -- NOT VALID !!!  (e.g., when P is false)
:= begin
    intro,
    intro h,
    try {assumption, },  -- "P → P" is not the same as "P" !!!
    try { exact h,},     -- "P → P" is not the same as "P" !!!
    sorry ,
end



----------------------------------------------------
-- true is implied by anything: trivial 
----------------------------------------------------

#check true     -- this is _not_ the same as tt 

/- we have already said that "true" is the proposition taken for granted to be true. but can we prove that? which tactic should we use when our goal is "true"? we can use "trivial":
-/

theorem true_trivially_holds: true
:= begin
    trivial, -- trivial recognizes true in the goal
end

theorem anything_implies_true: ∀ p : Prop, p → true
:= begin
    intro,
    intro h, 
    trivial, 
end 




----------------------------------------------------
-- false cannot be proven 
----------------------------------------------------

#check false    -- this is _not_ the same as ff 


/- "false" is the proposition which is taken for granted to be false. we cannot prove false. false should be unprovable in any sound system. if you manage to prove false (without any assumptions) in LEAN, you have found a LEAN bug. i will then give you automatically an A, and you can probably graduate and go work for the LEAN team. 
-/


theorem false_by_itself_cannot_be_proven: false 
:= begin
    sorry,
end



/- SOUNDNESS and COMPLETENESS

we should be glad we are not able to prove false. if we were able to do that, then our proof system would be _unsound_. in general, a logic / proof system is _sound_ if it is only able to prove statements that are (semantically) valid. meaning, if it can prove a statement φ, then φ is valid, i.e., φ is indeed true. the reverse is called _completeness_: a logic / proof system is _complete_ if it is able to prove all (semantically) valid statements. meaning, if φ is valid, then φ can be proven in that system. we always want soundness, but completeness is sometimes too much to ask. many systems are sound but incomplete. we will talk about this a bit later. 


now, false cannot be proven, but starting from false you can prove anything you want! so false → P is true for any P : Prop!

(politicians know that starting from false premises you can prove anything you want, and they exploit this marvellously.)  
-/


--------------------------------------------------------
-- false implies anything: the tactic "contradiction"
--------------------------------------------------------

-- which tactic should we use when one of our assumptions is "false"? 

theorem false_implies_anything: ∀ P : Prop, false → P
:= begin
    intro,
    intro h,
    contradiction, 
end

theorem false_implies_false: false → false
:= begin
    intro h,
    contradiction, -- assumption or exact also work here 
end

/-
it should be clear that false is NOT the same claim as (false -> false). we can prove the latter, but we cannot prove the former! if this is not clear, ask!
-/

-- sometimes contradiction also works for "obviously false" hypotheses:
theorem one_equals_zero_implies_anything: ∀ P : Prop, 1 = 0 → P 
:= begin
    intro,
    intro h,
    contradiction,
end

-- but "obviously false" is not always so "obvious" to LEAN:
example: ∀ P : Prop, 1 = 2 → P 
:= begin
    intro,
    intro h,
    try {contradiction,}, -- doesn't work!
    sorry,
end

-- the "cases" tactic to the rescue!
theorem one_equals_two_implies_anything: ∀ P : Prop, 1 = 2 → P 
:= begin
    intro,
    intro h,
    cases h, -- don't ask "why" this works 
end


/-
now let's see how to deal with the rest of the logical connectives: or, and, not, iff, xor. 

we have to know how to handle each of those when we encounter it: either in the goal; or in one of our hypotheses. 
-/

----------------------------------------------------
-- disjunction in the goal 
----------------------------------------------------

-- which tactic should we use when our goal is an "or" (i.e., a disjunction)?

----------------------------------------------------
-- left, right
----------------------------------------------------

theorem disjunction_left: ∀ P Q : Prop, P → (P ∨ Q)
:= begin
    intro,
    intro,
    intro h,
    left,       -- we choose to prove the left part of the disjunction
    exact h,
end

theorem disjunction_right: ∀ P Q : Prop, Q → (P ∨ Q) 
:= begin
    intro,
    intro,
    intro h,
    right,      -- we choose to prove the right part of the disjunction
    exact h,
end



/- tactics = moves

a legal move (tactic that applies) is NOT always a good move!
-/

/- NOTE: tactics are _local_ in the sense that whether or not they apply only depends on _the current proof state_! meaning the current goal, and the current set of hypotheses. a tactic is just one step in a proof. a tactic does not have a "global view" of neither what we are trying to prove, nor how we go about proving it. applying a tactic is like making a legal move in a game of chess. when a tactic applies, it means that the rules of chess are followed. when a tactic gives an error, it means that i tried to do something that violates the rules of the game. LEAN won't let me do that. but the fact that i make a move that doesn't break the rules of chess does not necessarily mean that this is a smart move to make! it doesn't necessarily mean that i will end up winning the game! it only means that i have made one move. same thing when proving in LEAN. applying a tactic does not necessarily mean it's the right tactic to apply, and that it will necessarily lead us to completing the proof. 

one or more tactics may apply, and yet lead to a dead-end, where we cannot complete the proof (either because the proof cannot be completed because the result is false, or simply because we didn't take the right steps / choose the right tactics). 

as an example, consider the left / right tactics that we learned. they apply but might lead to a dead-end:
-/

theorem true_theorem_but_bad_choice_tactic: ∀ p q : Prop, p → (p ∨ q) 
:= begin
    intros p q h,
    right, -- bad choice, now the theorem cannot be proven anymore ... 
    sorry,
end

theorem false_theorem_but_i_can_still_go_ahead_several_steps_in_the_proof: ∀ p q r : Prop, p → (q ∨ r ∨ q ∨ r) 
:= begin
    intros p q r h,
    -- from now on, i could follow many paths, but none of them leads anywhere ... 
    right,
    right,
    left,
    sorry,
end





----------------------------------------------------
-- conjunction in the goal 
----------------------------------------------------

-- which tactic should we use when our goal is a conjunction?

----------------------------------------------------
-- split
----------------------------------------------------

theorem p_implies_q_implies_q_and_p: ∀ p q : Prop, p → ( q → (p ∧ q) )
:= begin
    intro,
    intro,
    intro h1,
    intro h2,
    split,  -- when the goal is of the form P ∧ Q, _split_ splits the proof in two, one where the goal is P and another where the goal is Q
    {
        exact h1,
    },
    {
        exact h2,
    }
end



----------------------------------------------------
-- disjunction in the hypotheses 
----------------------------------------------------

-- which tactic should we use when one of our _hypotheses_ is a disjunction?

----------------------------------------------------
-- cases, again
----------------------------------------------------

theorem p_or_q_implies_q_or_p: ∀ P Q : Prop, (P ∨ Q) → (Q ∨ P) 
:= begin
    intro,
    intro,
    intro h,
    try {assumption}, -- does nothing 
    cases h,  -- when _h_ is an assumption of the form P ∨ Q, _cases h_ splits the goal into two subgoals, one where we assume P and another where we assume Q
    -- we can also use "cases h with ... ..." to rename the hypotheses 
    {
        right,
        exact h,
    },
    {
        left,
        exact h,
    }
end


----------------------------------------------------
-- conjunction in the hypotheses 
----------------------------------------------------

-- which tactic should we use when one of our hypotheses is a conjunction?

----------------------------------------------------
-- cases, again
----------------------------------------------------

theorem p_and_q_implies_p: ∀ p q : Prop, (p ∧ q) → p 
:= begin
    intro,
    intro,
    intro h,
    cases h, -- when _h_ is an assumption of the form P ∧ Q, _cases h_ "splits" _h_ into two separate hypotheses, one for P and one for Q 
    assumption, 
end

-- better solution: we should use "cases ... with ..." to rename the hypotheses:
theorem p_and_q_implies_p_with: ∀ p q : Prop, (p ∧ q) → p 
:= begin
    intro,
    intro,
    intro h,
    cases h with h1 h2,
    exact h1, -- portable solution because we used "with" above 
end


----------------------------------------------------
-- NEGATION: not ¬ 
----------------------------------------------------

/- what is negation? it is fascinating that it can be defined not as a primitive, but in terms of implication, namely: ¬ P := (P → false).  read: "not P" is the same as "if P then false". 

if you are unsure why this definition makes sense, try to build the truth tables for ¬p and for (p → false). you will see that the column for ¬p and (p → false) are identical! 
-/
#check not  -- you can CTRL-click on "not" to see how it's defined

/- 
so not is really implication!!! since we know how to treat implication, we can use this fact to prove stuff involving not:
-/

theorem not_false_: ¬ false 
:= begin
    -- ¬ is an implication, so _intro_ should apply:
    intro h,
    contradiction, 
end

-- so, ¬ false and false → false are the same thing!
theorem false_implies_false_: false → false 
:= begin
    intro,
    contradiction,
end

-- ¬ is implication independently of the Prop it is applied to:

theorem thm3: ∀ x : nat, ¬ (x = x+1) 
:= begin
    intro,
    intro h,
    sorry,
end

-- ≠ is the same as ¬ ( ... = ... )  
theorem thm4: ∀ x : nat,  (x  ≠  x+1) 
:= begin
    intro,
    intro h,
    sorry,
end





----------------------------------------------------
-- iff (if and only if)
----------------------------------------------------

-- P ↔ Q is equivalent to (P → Q) ∧ (Q → P). so we treat it just like a conjunction:

theorem p_iff_p: ∀ P : Prop, P ↔ P 
:= begin
    intro,
    split, -- from A ↔ B it generates two goals: A → B and B → A
    {
        intro h,
        exact h,
    },
    {
        intro h,
        exact h,
    }
end




theorem p_iff_p_with_repeat: ∀ P : Prop, P ↔ P 
:= begin
    intro,
    split, 
    repeat {
        intro h,
        exact h,
    },
end



----------------------------------------------------
-- xor 
----------------------------------------------------

-- (xor P Q) is equivalent to (P ∧ ¬ Q) ∨ (Q ∧ ¬ P). so we treat it just like a disjunction:

theorem not_xor_p_p: ∀ P : Prop, ¬ (xor P P) 
:= begin
    intro,
    intro h,
    -- xor is really a disjunction:
    cases h,
    {
        cases h with h1 h2,
        -- now what? could we deal with this in our formal proofs by hand? how?
        -- in LEAN we don't know how to deal with this yet. so we give up for now:
        sorry,
    },
    {
        cases h with h1 h2,
        sorry,
    }
end


------------------------------------------
-- equality vs iff in propositional logic
------------------------------------------

-- LEAN let's us write this:
example: ∀ p : Prop, p = p 
:= begin
    intro,
    refl,
end

-- but the equals symbol "=" is not really part of propositional logic, so we insist on writing this instead:
example: ∀ p : Prop, p ↔ p 
:= begin
    intro,
    refl,
end

-- similarly, LEAN let's us write this:
example: ∀ p : Prop, ¬ (p ≠ p) 
:= begin
    intro,
    intro h,
    contradiction,
end

-- but we will insist on writing this instead:
example: ∀ p : Prop, ¬ ¬ (p ↔ p) 
:= begin
    intro,
    intro h,
    contradiction,
end




/-
SUMMARY: 

- which tactic to use when the goal is of the form A = A ?
    refl

- which tactic to use when the goal is of the form ∀ x ... ?
    intro

- which tactic to use when the goal is of the form A → B ?
    intro

- which tactic to use when the goal is the Prop true?
    trivial

- which tactic to use when a hypothesis is the Prop false?
    contradiction

- which tactic to use when a hypothesis H is identical to the goal?
    exact H

- which tactic to use when the goal is of the form A ∨ B ?
    left or right, depending whether we want to continue with A or B

- which tactic to use when the goal is of the form A ∧ B ?
    split

- which tactic to use when a hypothesis is of the form H : A ∨ B ?
    cases H [with ...]

- which tactic to use when a hypothesis is of the form H : A ∧ B ?
    cases H [with ...]

- which tactic to use when the goal is of the form ¬ A ?
    intro 

- which tactic to use when the goal is of the form A ↔ B ?
    split  (or rw, as we will see later), since iff is really a conjunction 

- which tactic to use when a hypothesis is of the form H : A ↔ B ?
    cases H, since iff is really a conjunction 

- which tactic to use when the goal is of the form (xor A B) ?
    left or right, since xor is really a disjunction 

- which tactic to use when a hypothesis is of the form H : xor A B ?
    cases H, since xor is really a disjunction 

-/


-- TIME FOR SOME PRACTICE!!! 

-- ERASE ALL PROOFS AND TRY THEM ON YOUR OWN!

-- practice is the way to learn!


-- let's apply all the stuff we have learned so far:

lemma p_and_true: ∀ P : Prop, (P ∧ true) ↔ P 
:= begin
end



lemma p_or_true: ∀ P : Prop, (P ∨ true) ↔ true 
:= begin
end


theorem p_and_q_implies_q_and_p: ∀ p q : Prop, (p ∧ q) → (q ∧ p) 
:= begin
end





/-
    RECAP: WHERE WE STAND

At a minimum, you should be able to:

- write functions with types in LEAN (including recursive functions using pattern matching)

- write and prove examples-tests with refl

- write forall specifications, which include functions, =, and any of the logical connectives (→ , ¬ , ∧ , ∨ , ↔ , ...) 

- be able to do manual formal proofs (by hand) for formulas in propositional logic 

- be able to do formal proofs in LEAN for formulas in propositional logic 


If any of the above sounds strange, weird, never-heard-of, etc, COME TO OFFICE HOURS RIGHT AWAY!

consult the lecture notes regularly, especially sections 7 and 8:
    https://course.ccs.neu.edu/cs2800f23/lecture-notes.pdf
-/



