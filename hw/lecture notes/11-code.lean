-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!


-- lecture code 2023-10-02




/-

in class we showed formal proofs by hand as trees going UP. for your homeworks, exams, etc, feel free if you'd like to have your trees go DOWN, e.g. as in: 

 ⊢ P → P 
--------- ImpIntro
 P ⊢ P
-------- Assumption    
  DONE

in general, in this class we care more about concepts and less about style. we also want to treat you as adults. as a result, we are OK with you taking initiative and proposing or doing new things, as long as they are reasonable. 

-/


/-

SLIDES: read 11-proof-rules.pdf 

-/


-----------------------------------
-- PROOF ASSISTANTS
-----------------------------------

/- doing formal proofs by hand is painful: even very simple propositional logic tautologies (a tautology is a valid formula) might result in a long proof! and writing those down on paper is unmanageable!

doing formal proofs by hand not only painful, it is also error-prone. who says we didn't make a mistake in our proof? who says we didn't forget a proof obligation? who says we didn't use a rule that didn't apply to a certain proof state? imagine yourself grading your friend's formal proof. how do you check that they didn't make any of these or other mistakes?

for the above reasons, we would like to have _proof assistants_. LEAN is a proof assistant. it's a program that helps us in at least two ways:
  1. it allows us to write formal proofs in code, and it does all the book-keeping for us, so that we don't have to do it ourselves. 
  2. even more importantly, it CHECKS our proof! a proof assistant like LEAN makes sure we haven't forgotten a proof obligation, for instance: if we do, it will our proof as incomplete. a proof assistant like LEAN also makes sure that whenever we try to apply a proof rule, that rule is indeed applicable. so unless LEAN has bugs, we can be confident that when we complete a proof, our theorem is indeed proven. 

wouldn't it be great to have tools that do proofs FULLY AUTOMATICALLY so that we don't have to do anything by hand!? yes, that would be ideal, but unfortunately, fundamental obstacles like intractability (truth tables becoming too large) and undecidability (we will talk about it later) prevent us from ever completely achieving this ideal. having said that, there's a lot of tools out there which try to overcome these obstacles and automate proofs as much as possible. we will see some of these tools later. 
-/


-----------------------------------
-- FORMAL PROOFS IN LEAN
-----------------------------------

/- we have learned how to do formal proofs by hand: you should know how to do this, as you will be tested in quizzes and exams!

but for the reasons mentioned above, we would rather do formal proofs using a proof assistant like LEAN. we already started doing such proofs using example: ... := begin refl, end. we now continue with more interesting proofs. 
-/

import .mylibrary09


-------------------------------------------------------
-- EXPRESSING TAUTOLOGIES on Props vs bools
-------------------------------------------------------
/-
let's say we want to prove that a propositional logic formula like 
    p ∨ ¬p  
is valid (i.e., a tautology, i.e., "always true"). 

we can show this using the truth table method:

TRUTH TABLE FOR p ∨ ¬p  :

    +---+----+-------------+
    | p | ¬p |    p ∨ ¬p   |
    +---+----+-------------+
    | T |  F |      T      |
    | F |  T |      T      |
    +---+----+-------------+

since the column for p ∨ ¬p only has Ts, the formula is valid. 

in LEAN we can prove this tautology in two ways: either treating p as a Prop, or treating p as a bool: 
-/

-- if we treat p as a Prop, we can express this validity in this way:
theorem p_or_not_p_Prop: ∀ p : Prop, p ∨ ¬p
:= begin
    sorry, -- we will see how to prove things on Props later 
end

 

-- if we treat p as a bool, we can express this validity in this way:
theorem p_or_not_p_bool: ∀ p : bool, orb p (negb p) = tt 
:= begin
    sorry, -- we will see how to prove things on bools next 
end




-- bool and Prop are different:
#check bool 
#check Prop 

#check tt 
#check true 
#check ff 
#check false  

#check ff && tt 
#check false ∧ true

#eval ff && tt 
#eval false ∧ true -- can't do
#reduce false ∧ true -- nothing useful happens 

#check and false true 
#check xor false true 


#check false ∨ tt   -- horrible type coercion! avoid at all costs! 





-------------------------------------------------------
-- PROVING TAUTOLOGIES on bools 
-------------------------------------------------------



----------------------------------------------------
-- try
----------------------------------------------------

-- so how do we prove this? we can try refl, but it won't work:
theorem x_or_not_x_bool_try1: forall x : bool, orb x (negb x) = tt 
:= begin
    try {refl}, -- "try" attempts to apply a tactic but doesn't fail if that tactic fails
    -- the proof state hasn't changed, which means that the tactic refl failed to do anything useful. since that's the only tactic we have learned so far, we give up:
    sorry,  
end



----------------------------------------------------
-- intro
----------------------------------------------------

theorem x_or_not_x_bool_try2: forall x : bool, orb x (negb x) = tt 
:= begin
  intro, -- eliminates the forall quantifier and introduces x in the hypotheses

  try {refl}, -- still doesn't work
  sorry,  
end



-------------------------------------------------------
-- PROOF BY CASES 
-------------------------------------------------------

----------------------------------------------------
-- cases
----------------------------------------------------

theorem x_or_not_x_bool: forall x : bool, orb x (negb x) = tt 
:= begin
  intro, -- eliminates the forall quantifier and introduces x in the hypotheses

  cases x, -- generates two cases (subgoals, or proof obligations) one for x=tt and another for x=ff 
  { -- we begin the first subgoal
    refl, -- now refl works!
  }, -- first subgoal done!
  { -- we begin the second subgoal
    refl, -- now refl works!
  } -- second subgoal done! proof complete!
end

/- NICE! now proofs on bools become easy! we just have to unfold and refl all possible cases!
-/
