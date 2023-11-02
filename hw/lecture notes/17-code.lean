-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- lecture code 2023-10-19

import .mylibrary09

/-

using chatGPT, GitHub copilot, OR ANYTHING ELSE, is NOT ALLOWED!
you have signed a contract stating that you will not use them. 
using them amounts to cheating. 

- the first time we detect this in homeworks, we give you 0 to the entire homework 

- the second time we detect this in homeworks, we report you for an academic integrity violation 

- if you do it in an exam, we report you for an academic integrity violation

-/








--------------------------------------------------
-- CLASSIC LOGIC vs. CONSTRUCTIVE LOGIC continued
--------------------------------------------------


/-
there are things that we can prove without the law of excluded middle. you have already done many many proofs (e.g., homework 06) that don't need classical.em. but there are also things that we cannot prove without this law!  (or another law that we will learn below)

for example, we know that this is a propositional logic tautology:

    (A → B) ↔ (¬A ∨ B)

can we prove this for Props? do we need classical.em? let's try each implication separately:
-/


theorem not_or_implies: forall A B : Prop,   (¬A ∨ B) -> (A -> B)
:= begin
    intro,
    intro,
    intro h1,
    intro h2,
    cases h1,
        {
            have h3 := h1 h2,
            contradiction,
        },
        {
            exact h1,
        },
    -- DONE! we didn't have to use classical.em 
end


theorem implies_not_or: forall A B : Prop,   (A -> B) -> (¬A ∨ B)
:= begin
    intro,
    intro,
    intro h1,
    -- now what? seem stuck... 
    -- need to use classical.em 
    cases classical.em A,
    {
        have h2 := h1 h,
        right,
        exact h2,
    },
    {
        left,
        exact h,
    },
end



------------------------------------------------------------
-- HOW DO I KNOW WHETHER I HAVE TO USE classical.em ?
------------------------------------------------------------

/- 
many facts can be proven in both classic logic and constructive logic. we have been proving many things already, without the need for classical.em. but there are some tautologies that need classical.em. in fact, there are cases where some statement (a) may look very similar to another statement (b), while in fact (a) does not need classical.em but (b) does. 

how do we know whether or not we have to use classical.em? 

you will learn this by practice. in general you will:
(1) start trying to do the proof using the tactics that we learned. try to finish the proof without using classical.em. 
(2) what if you get stuck? first, try to see whether what you are trying to prove is valid to begin with! here, you can try to do some boolean reasoning: "either p will be true, or p will be false. if p is true then .... if p is false then  .... "
(3) if you find that what you are trying to prove is NOT true, then: either the entire theorem that you are trying to prove is false, or you took a wrong turn somewhere before. in the first case you provide a counterexample. in the second case you backtrack! 
(4) if you are convinced that what you are trying to prove is indeed true (your boolean reasoning didn't reveal a counterexample) then you can formalize your boolean reasoning using classical.em, e.g., as in: 
    have h := classical.em p,
then you can do cases h and try to continue your proof for both the cases when p is true and when ¬ p is true (i.e., p is false). 

let us now look at some examples of this method:
-/

-- let's try to prove this:
theorem p_implies_not_not_p: ∀ P : Prop, P → (¬ ¬ P) 
:= begin
    intro,
    intro h1,
    intro h2,
    have h := h2 h1,
    trivial,
    -- we succeeded without using classical.em !
end

-- now let's try to prove this:
theorem not_not_p_implies_p_1st_try: ∀ P : Prop, (¬ ¬ P) → P 
:= begin
    intro,
    intro h1,
    -- recall that ¬ ¬ P is the same as (¬ P) → false, which is the same as (P → false) → false:
    dunfold not at h1, -- not needed, here just to unfold ¬ 
    -- but how to proceed from here? we are stuck!
    try {cases h1, }, -- does nothing, h1 is not an ∨ or an ∧ !
    try {cases P,}, -- does nothing, cases doesn't work on Props!
    sorry,
end

/-
at this point, we have to stop and think. is what i am trying to prove really true? we can do boolean reasoning: 
    - either P will be true, in which case the implication (¬¬P) → P will be trivially true;
    - or P will be false, in which case ¬P will be true, and therefore ¬¬P will be false, so the implication (¬¬P) → P will be true again. 
so we are convinced that what we are trying to prove is indeed true. we can then try the proof one more time, this time using classical.em: 
-/
theorem not_not_p_implies_p_using_em: ∀ P : Prop, (¬ ¬ P) → P 
:= begin
    intro,
    intro h1,
    have h2 := classical.em P, -- we are "calling" classical.em with argument P
    cases h2,
    {
        assumption,
    },
    {
        have h3 := h1 h2,
        trivial,
    }
end


/-
it's interesting that although (P → ¬¬P) and (¬¬P → P) look similar, one of them needs classical.em while the other one does not! 
-/




----------------------------------------------
-- classical.by_contradiction
----------------------------------------------

/- as it turns out, ¬¬P → P is also an axiom of classic logic. it is the rule of "proof by contradiction". it says: "in order to prove P, I will assume ¬P, and I will reach a contradiction (i.e., false)". in other words, "if I can prove (¬P → false) then I have proven P". but (¬P → false) is exactly ¬¬P ! the proof by contradiction rule is also an axiom in LEAN:
-/

#check classical.by_contradiction   
#check classical.em 

/-
note that the type of classical.by_contradiction looks different from the type of classical.em. the latter has a (∀ p : Prop) in the front, which means it takes a Prop as input. but  classical.by_contradiction  does not take a Prop as input. it takes as input a proof of ¬¬P, for some (any) Prop P, and it returns a proof of P: 
-/

example: ∀ x : ℕ, ¬ (x ≠ 0) → x = 0 
:= begin
  intro,
  intro h1,
  have h2 := classical.by_contradiction h1,
  assumption,
end



/- do we need both axioms classical.em and classical.by_contradiction? no we don't. as we saw just above, if we have classical.em, then we can prove classical.by_contradiction: we did that in the theorem "not_not_p_implies_p_using_em". conversely, if we have classical.by_contradiction, then we can prove classical.em (this will be in your homework). so only one of them is really needed. but LEAN provides both for convenience, so that users don't have to re-prove them. 
-/



-------------------------------------
-- PROOF BY SIMPLIFICATION 
-------------------------------------

/-
very often our goal is of the form A = B, but we know that we can reduce it to B = B, or A = A, or even C = C, by 'simplifying' A or B (or both). in the Software Foundations series, this is called "proof by simplification":
https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html
("simplification", "reduction", "equational reasoning", "unfolding", ... are other terms that you might see used for the same concept.)

we have already implicitly done proof by simplification using _refl_. recall:
-/

example: plus 0 3 = 3
:= begin
  refl,
end

example: forall x : nat, len [x] = 1
:= begin
  intro,
  refl, 
end


/-
the tactic _refl_ works for the above (and many other) goals, even though these goals are **not** of the form A = A. why? because _refl_ simplifies the left- or right-hand side of goals such as A = B "under the hood". 

we want to be able to see explicitly how these "under the hood" simplifications are done. for this, we can use the tactic _rewrite_, also abbreviated as _rw_: 
-/



----------------------------------------------------
-- rewrite, rw
----------------------------------------------------


example: plus 0 3 = 3
:= begin
  rewrite plus, -- actually rewrite does the job and completes the entire proof so we don't have to do refl!
end

example: plus 3 1 = 4 
:= begin
    rw plus,
    rw plus,
    rw plus,  -- you can use rw for step-by-step debugging!
    rw plus,
end

example: forall x : nat, len [x] = 1
:= begin
  intro,
  rewrite len,
  rewrite len, -- again, rewrite completes the proof
end

example: len [1,2,3] = 3 
:= begin
  rw len,
  rw len,
  rw len,
  rw len,
end



----------------------------------------------------
-- dunfold, unfold
----------------------------------------------------


/-
other simplication tactics in LEAN are dunfold and unfold:
-/

example: plus 0 3 = 3
:= begin
  dunfold plus,
  refl,
end

example: forall x : nat, len [x] = 1
:= begin
  intro,
  dunfold len,
  refl,
end

example: len [1,2,3] = 3 
:= begin
  dunfold len,
  refl,
end


example: plus 0 3 = 3
:= begin
  unfold plus,
end

example: forall x : nat, len [x] = 1
:= begin
  intro,
  unfold len,
end

example: len [1,2,3] = 3 
:= begin
  unfold len,
end


/-
these simplification tactics can sometimes exhibit weird (and annoying) behavior. for example:
-/

-- this is the standard way to define append on lists:
def app: list ℕ -> list ℕ -> list ℕ
  | [] L := L 
  | (x :: L1) L2 := list.cons x (app L1 L2)
--

-- but let's suppose we defined list append like this instead:
def appred: list ℕ -> list ℕ -> list ℕ
  | [] [] := []
  | [] (y :: L) := list.cons y (appred [] L)
  | (x :: L1) L2 := list.cons x (appred L1 L2)

-- the definition of appred is unorthodox, but the cases are non-overlapping and the function works correctly:
#reduce appred [1, 2, 3] [4, 5, 6] 

-- and yet refl and dunfold don't work!
example: appred [1, 2, 3] [4, 5, 6] = [1,2,3,4,5,6] 
:= begin
  try { refl }, 
  try { dunfold appred, },
  sorry,
end 

-- in fact it's even more embarrassing! 
example: appred [] [] = [] 
:= begin
  try { refl }, 
  try { dunfold appred, },
  sorry,
end

-- i have no idea why this happens! LEAN mystery ... 

-- but unfold and rewrite work:

example: appred [] [] = [] 
:= begin
  rw appred,  -- unfold also works
end

example: appred [1, 2, 3] [4, 5, 6] = [1,2,3,4,5,6] 
:= begin
  -- unfold appred, -- finishes the goal in one step
  rw appred,
  rw appred,
  rw appred,
  rw appred,
  rw appred,
  rw appred, -- it's long, but you can use it for step-by-step debugging!
  rw appred,
end 



/- 
in this course, you can use _any_ of these tactics (refl, rw, dunfold, unfold) to discharge goals of the form A = B. we will not penalize you for using one vs the other, unless we explicitly ask you to use a particular one for training purposes. 

we will also not insist on manual equational reasoning in this course, since it is something that theorem provers can help us with pretty well, so that we don't have to do it "by hand". but we need to know what it is, because in principle we should be able to do everything by hand, even if we didn't have LEAN! indeed, LEAN is just a proof _assistant_ which makes our lives easier so that we don't have to write stuff down, remember all the goals that we have to prove, do the simple reductions, etc. but in principle we could do all these things ourselves with paper and pencil. it would just be tedious. to see this, let's do a few examples:
-/

/- reducing the expression "len []":

len []
= by definition of len, 1st case
0
-/

/- reducing the expression "len [1]":

len [1] 
= by definition of notation "[1]"
len (1 :: [])
= by definition of len, 2nd case
1 + (len [])
= by definition of len, 1st case
1 + 0
= "arithmetic"  (this is actually a bit misleading, because "arithmetic" already hides a lot of stuff! e.g., how is + defined?) 
1
-/

/- reducing the expression "len [x]":

len [x] 
= by definition of notation [x] 
len (x :: [])   -- or len (list.cons x [])   or len (list.cons x list.nil) 
= by definition of len, 2nd case
1 + len [] 
= by definition of len, 1st case
1 + 0
= by arithmetic
1

-/

/- #eval vs #reduce:
-/
-- you can think of #reduce as performing the above reductions. you can think of #eval as a more efficient #reduce (never mind how it's implemented):


def exponent : ℕ → ℕ → ℕ  
    | _ nat.zero  := 1
    | x (nat.succ n) := x * (exponent x n) 

-- #reduce exponent 2 15  -- out of time/memory
#eval exponent 2 1000 -- ok 


/- many students ask: what are the differences between refl, rw, dunfold, unfold?

answer: we don't really care how these tactics are implemented in LEAN and how exactly they work. all we need to know is that we can use (any of) them for proofs by simplification. 
-/

example: ∀ x : ℕ, plus 0 x = x 
:= begin
  try { rw plus, }, -- does not work inside the forall
  try { refl, }, -- does not work inside the forall
  dunfold plus, -- works inside the forall!
  intro,
  refl,
end



------------------------------------
-- doing more with rewrite
------------------------------------

/- rw can be used in other situations as well. for example, suppose one of our hypotheses is h : x = 0, meaning that we know that x is 0. then, we can replace x in our goal with 0! rw can be used to do exactly that:
-/

example: ∀ x y : nat, x = 0 → plus x y = y 
:= begin
    intro,  -- introduce x
    intro,  -- introduce y
    intro h,  -- introduce the hypothesis x = 0
    rw h,  -- rewrite x to 0, according to the equality in hypothesis h
    refl,
end

-- by default rw rewrites from left to right. if we want to rewrite in the opposite direction, we can use "rw <-" :
example: ∀ x y : nat, 0 = x → plus x y = y 
:= begin
    intros x y H,  
    rw <- H, -- by default, rewrite rewrites in the left-to-right direction. here we want the opposite direction
    refl,
end

-- now we can prove things like that: 
theorem plus_id: ∀ x y : ℕ, x = y → plus x x = plus y y 
:= begin
    intros x y H,
    rewrite H, 
end

-- in fact this holds for all functions (make sure you are able to "read in english" what the theorem below states!): 
theorem functions_are_functions: 
    ∀ T : Type, ∀ f : T → T, ∀ x y : T, x = y → f x = f y 
:= begin 
    intros T f x y H,
    rw H,
end



-- rw works not just with equalities x = y, but also with equivalences p ↔ q :
theorem iff_rw: ∀ P Q : Prop, (P ↔ Q) → (P → Q) 
:= begin
    intros P Q h1,
    rw h1,
    intro h2,
    exact h2,
end

-- we can use rw to rewrite not just the goal, but also a hypothesis using "rw H1 at H2":
theorem iff_rw_hyp: ∀ P Q : Prop, (P ↔ Q) → (P → Q) 
:= begin
    intro,
    intro,
    intro h1,
    intro h2,
    rw h1 at h2,
    exact h2,
end



