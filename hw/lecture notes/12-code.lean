-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- lecture code 2023-10-04

import .mylibrary09




/-

1st EXAM DATE: MARK YOUR CALENDARS!

EXAM 1: Thu 12 Oct 

In class. 

Material: everything up to and including the material for homework 05. 

We will use gradescope. You have been added to the CS2800 course on gradescope for Fall 2023 (you should have received notification, if not, let me know). Also have a piece of paper with you to possibly write and submit formal proofs by hand. Further instructions to follow. 

-/




-------------------------------------------------------
-- PROVING TAUTOLOGIES on bools continued
-------------------------------------------------------


-------------------------------------------------------
-- PROOF BY CASES continued
-------------------------------------------------------


theorem negb_involutive : ∀ x : bool, negb (negb x) = x 
:= begin
  intro,
  cases x, 
  { -- we begin the first subgoal
    refl,
  }, -- first subgoal done!
  { -- we begin the second subgoal
    refl,
  } -- second subgoal done! proof complete!
end


/-
      NESTED CASES
-/

-- this is the tautology x ∧ y ↔ y ∧ x written with bools:
theorem andb_commutative: forall x y : bool, andb x y = andb y x 
:= begin
  intro,
  intro,
  cases x,
  {
    cases y,
    {
      refl,
    },
    {
      refl,
    }
  },
  {
    cases y,
    {
      refl,
    },
    {
      refl,
    }
  },
end



----------------------------------------------------
-- repeat
----------------------------------------------------

-- can we shorten the proof?
theorem andb_commutative_with_repeat: forall x y : bool, andb x y = andb y x 
:= begin
  intro,
  intro,
  cases x,
  -- we can use _repeat_ to keep applying a block of tactics as many times as they can be applied:
  repeat {   -- repeat whatever is between { ... } 
    cases y,
    {
      refl,
    },
    {
      refl,
    }
  },
end


-- we can we shorten it even more:
theorem andb_commutative_with_repeats: forall x y : bool, andb x y = andb y x 
:= begin
  intro,
  intro,
  cases x,
  repeat {
    cases y,
    repeat {
      refl,
    },
  },
end


----------------------------------------------------
-- intros
----------------------------------------------------

-- the _intros_ tactic applies the _intro_ tactic repeatedly:
theorem andb_commutative_with_intros: forall x y : bool, andb x y = andb y x 
:= begin
  intros,
  cases x,
  repeat {
    cases y,
    repeat {
      refl,
    },
  },
end


-- you can also rename the variables if you like:
theorem andb_commutative_with_renaming: forall x y : bool, andb x y = andb y x 
:= begin
  intros a b,
  cases a,
  repeat {
    cases b,
    repeat {
      refl,
    },
  },
end






----------------------------------------------------
-- cases applies to ANY inductive data type
----------------------------------------------------


/-
the cases tactic applies to any inductive data type, not just bools.  
-/

open weekday

theorem next_workday_not_weekend: 
    ∀ x : weekday, next_workday x ≠ sunday 
:= begin
    intro,
    cases x,
    repeat {
      try {refl}, -- doesn't work ... :( 
      sorry,
    },
end

/-
cases applies to any inductive data type, including infinite types like nat: 
-/

def silly (x : nat) : nat := if (x = 0) then 0 else 0 

theorem silly_is_silly: ∀ x : ℕ, silly x = 0
:= begin
  intro,
  try {refl,}, 
  cases x with y, -- remove "with y" to see what happens!
  {
    refl, -- expected
  },
  {
    refl, -- wow! how come refl can do this? we'll return to this later. 
  },
end


--------------------------------------------
-- tactics = implementations of proof rules
-- when a tactic _applies_ to a proof state
--------------------------------------------

/-
the "commands" that we put inside LEAN's begin ... end proofs are called "tactics". what are these tactics really? you can think of them as implementing proof rules, like the ones that we saw in our slides on formal proofs by hand. 

and just like we must learn when does a certain proof rule apply to a certain proof state, we must also learn whether a given tactic applies to a given proof state. it's the same concept: we will say that a tactic _applies_ to a certain proof state if we can issue that tactic successfully at that proof state, i.e., without a LEAN error. for example:
-/

lemma silly_of_nonzero_is_0: ∀ x : nat, silly (nat.succ x) = 0 
:= begin
    -- the refl tactic does not apply here:
    -- refl, -- if we try it we get an error 
    -- "cases x"  does not apply here either:
    -- cases x, -- if we try it we get an error
    -- the intro tactic applies here:
    intro,
    -- intro does not apply here:
    -- intro, -- if we try it we get an error 
    -- "cases x" applies here:
    -- cases x, -- OK! 
    -- refl also applies here (and in fact finishes the proof!):
    refl,
end

/-
when we say that a tactic _applies_ we do NOT necessarily mean that it's the right thing to do. we do NOT necessarily mean that by applying this tactic we will make progress towards proving our goal. all we are saying is that it is OK to issue this tactic in that particular proof state, and the tactic will do something in that proof state. whether this is a good idea or not is a whole different story. in fact, there are cases where the goal may not be provable at all, because it's wrong! still, some tactics apply, until we reach a deadlock. sometimes, no matter what we do, we reach a deadlock, because there's no way to complete the proof, because what we are trying to prove is wrong, for example. at other times, we may take a wrong direction, and reach a deadlock. then we have to go back at an earlier point in the proof, and try another path, and we may succeed. 

here's an example of a wrong claim, but where a tactic still applies:
-/

example: ∀ x : nat, x = 0 := begin
    -- the intro tactic applies here:
    intro,
    -- in class ungraded quiz: does intro apply here? 
    -- in class ungraded quiz: does refl apply here? 
end

/-
we will later see examples of claims which are true and provable, but where if we issue the wrong tactic we will reach a deadlock and not be able to continue our proof. in such cases we need to backtrack and try something else. this is not easy to do on paper, but easy to do on LEAN!
-/




--------------------------------------
-- are "try" and "sorry" tactics?
--------------------------------------

/-
let's not consider "try" and "sorry" to be tactics. sorry always "applies" to any proof state, and "aborts" trying to prove the corresponding goal. try also always "succeeds" in the sense that if the attempted tactic(s) fail(s) then "trying" them simply does nothing. 
-/




-------------------------------------------------------
-- PROVING PROPOSITIONAL LOGIC TAUTOLOGIES on Props 
-------------------------------------------------------

/-
we have seen how to prove propositional logic tautologies on bools. now we will see how to do that with Props. this is useful, because Props are much more general. so if we know how to deal, for example, with → (implies) on Props, we know how to deal with P → Q where P and Q can be ANY Prop (including Props on nats, lists of nats, functions, etc). 

for example, we can prove P → P once and for all for any Prop P, instead of separately proving x = 1 → x = 1, x = 2 → x = 2, x+1>0 → x+1>0, len [x,y,z] = 3 → len [x,y,z] = 3, etc. 


this is more powerful than it seems, because it allows us to deal with the basic logical connectives in any context: the tactics that we introduce below apply not just on abstract Props like P, Q, etc; they apply to any Prop.

this will be very useful later on, because concrete theorems about programs often have a _propositional skeleton_ which maps to basic propositional logic. for example, the statement "∀ x : ℕ, x = 0 ∨ x ≠ 0" maps to the purely logical statement "∀ p : Prop, p ∨ ¬ p". so if we know how to prove the latter, we can use the exact same proof to prove the former. 
-/

---------------------------------------------------------
-- PROOF TACTICS TO DEAL WITH BASIC LOGICAL CONNECTIVES
---------------------------------------------------------

-- logical connectives:

#check implies -- implication, → 
#check and -- conjunction, ∧ 
#check or -- disjunction, ∨ 
#check not -- negation, ¬ 
#check iff -- logical equivalence, ↔ 
#check xor -- exclusive or



-----------------------------------------------
-- eliminating implication in the goal: intro
-----------------------------------------------

/-
we have already seen the tactic intro for eliminating ∀. as it turns out, intro also eliminates implication in the goal (like the ImpIntro rule we saw in our formal proofs by hand): 
-/

theorem p_implies_p_try1: forall P : Prop, P -> P 
:= begin
  intro, -- eliminates the forall
  intro h, -- eliminates the implication in the goal and introduces hypothesis h
  sorry,
end



/-

!!! ADDITIONAL INSTRUCTIONS: !!!

-- WE WILL INSIST ON YOU TRYING TO MAKE YOUR PROOFS CHARACTER-SET INDEPENDENT!

when you have a goal of the form A -> B, don't just do "intro". this creates a new hypothesis x : A, but LEAN chooses what it wants "x" to be, and this is different from one installation to the other, which means that your proof is not portable. instead, do "intro h" (you can choose whatever you want "h" to be), "intro h1", "intro h13", etc. 
-/





/- if we already have the goal in our list of hypotheses, we can use one of these tactics:
-/

----------------------------------------------------
--  assumption, exact
----------------------------------------------------


theorem p_implies_p_with_assumption: ∀ P : Prop, P → P
:= begin
    intro,
    intro h,
    assumption, 
end


theorem p_implies_p_with_exact: ∀ P : Prop, P → P
:= begin
    intro,
    intro h,
    exact h,
end


/-
but notice that P → P holds for _any_ Prop P! so we can prove also things like that: 
-/

example: ∀ x : ℕ, x ≠ 0 → x ≠ 0 
:= begin
    intro,
    intro h,
    exact h,
end

section arbitrary_function  -- this encloses the "variable" declaration below in scope so that f doesn't clash with any other f in our file
variable f : nat -> nat  -- this says "let f be an arbitrary function from nat to nat"

example: ∀ x : ℕ, f x = 0 → f x = 0  
:= begin
    intro,
    intro h,
    exact h,
end

end arbitrary_function



---------------------------------------------------------
-- implication continued 
---------------------------------------------------------

-- just like in types, the implications A → B → C are interpreted as A → (B → C), that is, "A implies (B implies C)", or in other words, "if A holds, then if B holds then C must hold". so, in the case of P → P → P, this gives "if P holds, then if P holds then P must hold", which is true: 
theorem p_implies__p_implies_p: ∀ P : Prop, P → (P → P)
:= begin
    ... PROVE ME!!! ... 
end



-- what about this?  is it true?
theorem p__implies_p_implies_p: ∀ P : Prop, (P → P) → P    
:= begin
    ??? 
end
