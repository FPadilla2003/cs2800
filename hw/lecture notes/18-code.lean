-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- lecture code 2023-10-23

import .mylibrary09
import .mylibrary14 
import .mylibrary18 -- NEW LIBRARY FILE, AVAILABLE ON CANVAS 




-------------------------------------------------
-- rewriting, unfolding, etc, _at_ hypotheses
-------------------------------------------------


-- we can use rw to rewrite not just the goal, but also a hypothesis using _rw ... at ..._ : 
theorem iff_rw_hyp: ∀ P Q : Prop, (P ↔ Q) → (P → Q) 
:= begin
    intro,
    intro,
    intro h1,
    intro h2,
    rw h1 at h2,
    exact h2,
end


example: ∀ x y z : ℕ, x = y → y = z → x = z 
:= begin
    intros x y z h1 h2,
    rw <- h1 at h2,
    assumption,
end

/-
idem with dunfold, unfold, etc 
-/

example: ∀ x y : ℕ, plus 0 x = y → x = y 
:= begin
    intros x y h,
    dunfold plus at h,
    exact h,
end




--------------------------------
-- the power of rewrite 
--------------------------------

-- this is a theorem we have already proven:
#check plus_0_x  -- it's in mylibrary18.lean, available on canvas

-- suppose we want to prove this:
theorem mult_0_plus_v1: 
    ∀ (x y : nat), mult (plus 0 x) y = mult x y 
:= begin
    intros, 
    -- normally we would prove this by first using have:
    have h := plus_0_x x, 
    -- and then rw:
    rw h,
end

-- but we can also call the theorem directly, omitting the have:
theorem mult_0_plus_v2: 
    ∀ (a b : nat), mult (plus 0 a) b = mult a b 
:= begin
    intros,
    rw (plus_0_x a),  
end

-- we can also let rewrite do the name matching and omit passing the arguments:
-- (NOTE: in tests i will ask you to explicitly put the arguments, so you must know how to do it!)
theorem mult_0_plus_v3: 
    ∀ (a b : nat), mult (plus 0 a) b = mult a b 
:= begin
    intros,
    rw plus_0_x, 
end



/-
using rewrite we can do proofs similar to doing simplifications by hand. for example, suppose we wanted to show that formulas (a) and (b) below are equivalent:

    (a)    x ∧ ((x → z) ∧ true) ∧ y
    (b)     x ∧ y ∧ (¬x ∨ z) 

if we did this by hand, we would start with (a), and keep simplifying it until we get (b):

(a)
=
x ∧ ((x → z) ∧ true) ∧ y
= A ∧ true is equivalent to A, so ((x → z) ∧ true) becomes (x → z)
x ∧ (x → z) ∧ y
= (A ∧ B) ↔ (B ∧ A), so (x → z) ∧ y becomes y ∧ (x → z)
x ∧ y ∧ (x → z) 
= (A → B) ↔ (¬A ∨ B), so (x → z) becomes (¬x ∨ z)
x ∧ y ∧ (¬x ∨ z) 
=
(b)

rw allows us to do exactly that, by rewriting based on theorems we have proved previously:
-/


-- some theorems from mylibrary18.lean: 
#check p_and_true
#check p_and_q_iff_q_and_p
#check implies_iff_not_or 

theorem power_of_rw: 
  ∀ x y z : Prop, (x ∧ (((x → z) ∧ true) ∧ y)) ↔ (x ∧ (y ∧ (¬x ∨ z)))
:= begin
    intros,
    rw (p_and_true (x → z)),  
    rw (p_and_q_iff_q_and_p (x → z) y),
    rw implies_iff_not_or x z,
end



/-
CAREFUL: rewrite does NOT work with implications! indeed, it should NOT!  make sure you understand why!
-/

theorem trying_rw_on_implies:
    ∀ p q : Prop, p -> (p -> q) -> q
:= begin
    intro,
    intro,
    intro h1,
    intro h2,
    try { rw h2 }, -- fails: p cannot be "rewritten" into q based on h2
    try { rw h1 at h2 }, -- fails: p cannot be "rewritten" into q based on h2
    -- instead, we want to use modus ponens:
    have h3 := h2 h1,
    exact h3,
end








----------------------------------
-- The dangers of overlapping
----------------------------------

-- definition of list_delete without overlapping cases:
def ld : list nat -> nat -> list nat
  | [ ] _ := [ ]
  | (x :: L) 0 := L
  | (x :: L) (nat.succ i) := x :: (ld L i)  -- no overlapping
--

example: ld [1,2,3] 2 = [1,2] 
:= begin
  rw ld, -- unnecessary, but does not do any harm
  refl,
end

-- definition of list_delete with overlapping cases:
def ldov : list nat -> nat -> list nat
  | [ ] _ := [ ]
  | (x :: L) 0 := L
  | (x :: L) i := x :: (ldov L (i-1))  -- overlapping!
--

-- this will mess up the rewrite of this function, see below:
example: ldov [1,2,3] 2 = [1,2] 
:= begin
  rw ldov, -- unnecessary, but shouldn't hurt!!! 
  /- ???  how come we got two goals!?  because of overlapping!
  essentially LEAN asks us to also prove that we will skip the 2nd case in the definition of ldov, that is, that i (which is 2 in our case) is not 0. so we have to prove 2 ≠ 0, i.e., ¬ 2 = 0. 
  -/
  refl,
  intro h,
  contradiction, 
end





----------------------------------------------------
-- simplifying equalities that involve constructors 
----------------------------------------------------

-- 1 = 0 implies anything:
example: forall p : Prop, 1 = 0 → p 
:= begin
    intro,
    intro h,
    contradiction,
end

-- 20 = 10 also implies anything, but contradiction doesn't work!
example: forall p : Prop, 20 = 10 → p 
:= begin
    intro,
    intro h,
    try {contradiction},
    sorry,
end

/-
to deal with this type of situations, we will use lemma succeq:
-/

#check succeq 

/-
by definition of inductive data types, two elements x and y of such a type T can only be equal if they are built using the same constructor. for example, nat.zero and (nat.succ x) CANNOT be equal, for any x. and also, (nat.succ x) and (nat.succ y) are equal iff x is equal to y. 

the lemma succeq asserts that. (this lemma is proved in mylibrary18.lean. don't mind how it is proven. you can (and should) use this lemma when needed, but you are NOT ALLOWED to use the tactic _simp_ unless we explicitly allow you to.)
-/


-- now we can prove these:

example: ∀ p : Prop, 100 = 200 → p 
:= begin
    intro,
    intro h,
    rw (succeq 99 199) at h,
    repeat {rw succeq at h},
    contradiction, 
end

example: ∀ x y : nat,  (nat.succ x) = (nat.succ y) → x = y 
:= begin
    intro,
    intro,
    intro h,
    rw (succeq x y) at h,
    exact h,
end




/-
the same principle holds for any inductive data type. for example, [] is not equal to [1], because the former is constructed with list.nil and the latter with list.cons. we can already prove that with contradiction:
-/
example: [] ≠ [1] 
:= begin
    intro h,
    contradiction,
end

/- but [1] is also different from [1,2,3,4] and contradiction doesn't work here:
-/
example: [1] ≠ [1,2,3,4] 
:= begin
    intro h,
    try {contradiction},
    sorry,
end


/-
the lemma listeq allows us to simplify list equalities. it says that two lists are equal iff their heads are equal and their tails are also equal: 
-/

#check listeq  



-- now we can prove this:

example: [1] ≠ [1,2,3,4] 
:= begin
    intro h,
    rw (listeq 1 1 [] [2,3,4]) at h,
    cases h with h1 h2,
    contradiction,
end


-- PRACTICE: PROVE THESE AT HOME!!!

example: ∀ x : ℕ, ∀ L1 L2 : list ℕ, (x :: L1) = (x :: L2) → L1 = L2 
:= begin
    ... 
end

example: ∀ x y : ℕ, ∀ L : list ℕ, (x :: L) = (y :: L) → x = y 
:= begin
    ... 
end

example: ∀ (x y : ℕ) (L : list ℕ) (p : Prop), x :: y :: L = [x] → p 
:= begin
   ... 
end












/- REMINDER: STRONGER, WEAKER, EQUIVALENT FORMULAS

suppose A and B are propositional logic formulas. we say that:

    - _A is stronger than B_ if A → B is valid / a tautology. if A is stronger than B, then whenever A is true, B is also true. in other words, A implies B. 

    - _A is weaker than B_ if B → A is valid / a tautology. in other words, A is weaker than B iff B is stronger than A. 

    - _A is equivalent to B_ if both A → B and B → A are valid, that is, both A is stronger and weaker than B. in other words, A ↔ B is valid. 

the same terminology applies to more general (not just propositional) logic formulas. for example, (x ≥ 10) is stronger than (x ≥ 0). 

-/



-- PRACTICE!

/- let's practice the method we described earlier. consider the formulas (a) and (b) below:

    (a)  p → q 
    (b)  ¬(p ∨ q) 

answer the questions below:

1. are these two formulas equivalent?

2. is (a) stronger than (b)? if it is, prove it. did you have to use classical.em? if (a) is not stronger than (b), find a counterexample. 

3. is (b) stronger than (a)? if it is, prove it. did you have to use classical.em? if (b) is not stronger than (a), find a counterexample. 

-/

-- ANSWERS:
/- the two formulas are not equivalent. ¬(p ∨ q) is strictly stronger (strictly stronger means that it is stronger and not equivalent). we can prove it, without using classical.em:
-/
example: ∀ p q : Prop, ¬(p ∨ q) → (p → q) 
:= begin
    intro,
    intro,
    intro h1,
    intro h2,
    have h : p ∨ q 
    := begin
        left,
        assumption,
    end,
    have h3 := h1 h,
    contradiction,
end

/-
(p → q) is not stronger than ¬(p ∨ q). for example, the assignment p := true and q := true makes (p → q) true, but it makes ¬(p ∨ q) false. 
-/




/- THEOREMS vs FORMULAS
  
    BE CAREFUL!!!  
-/

-- consider theorems thm1 and thm2:

def thm1: ∀ p q : Prop, p -> q -> p 
:= begin intros, assumption, end 

def thm2: ∀ p q : Prop, (p ∧ q) -> (q ∧ p) 
:= begin intros p q h, cases h, split, assumption, assumption, end 

/-
since thm1 and thm2 are both valid, they are both equivalent to Prop true. so they must themselves be equivalent. but we cannot just write
    thm1 <-> thm2
-/

#check (thm1 ↔ thm2)     -- type error!  
/-
THEOREMS ARE FUNCTIONS! in particular, thm1 and thm2 are functions. 
↔ (iff) does NOT operate on functions. it operates on Props! thm1 and thm2 are NOT Props. 
-/

#check thm1                       -- thm1 has type (∀ (p q : Prop), p → q → p) ... 
#check ∀ (p q : Prop), p → q → p  -- ... and (∀ (p q : Prop), p → q → p) has type Prop


/-
this is a good illustration how types are a very useful tool to help us avoid mixing up concepts which are not the same. natural languages like english or greek are very loosely typed (verb, noun, etc.) which often leads to confusion. politicians sow confusion and exploit it deliberately.

now, going back to what we started with: how can we prove that thm1 and thm2 are equivalent?

there are a couple of ways to do that. one is to just copy the claims of the theorems and paste them to the left and right sides of an ↔ : 
-/
example: ( ∀ (p q : Prop), p → q → p )
                ↔ 
        ( ∀ (p q : Prop), p ∧ q → q ∧ p ) 
:= begin
    split,
    {
        intro h1,
        intro,
        intro,
        intro h2,
        cases h2 with h3 h4,
        split,
        assumption,
        assumption,
        -- notice we didn't use h1 at all. why?
    },
    {
        intro h1,
        intro,
        intro,
        intro h2,
        intro h3,
        assumption,
        -- again, we didn't use h1 at all. why?
    },
end

/-
a better way is to give names to each of these statements, so that we don't have to copy the statements themselves, but we can use their names instead: 
-/

def taut1 := ( ∀ (p q : Prop), p → q → p )
def taut2 := ( ∀ (p q : Prop), p ∧ q → q ∧ p ) 

#check taut1   -- taut1 is a Prop
#check taut2   -- taut2 is also a Prop 

/-
notice that taut1 is NOT the same thing as thm1! thm1 has type ( ∀ (p q : Prop), p → q → p ), but taut1 has type Prop! thm1 is a function that receives a bunch of stuff and returns a proof. taut1 is not a function. taut1 is the proposition itself. taut1 is a logical formula, a logical claim. 

idem for thm2 vs taut2. 

now we can state and prove this, in the same way as with the copy-paste example above:
-/

-- taut1 and taut2 are Props, so we can combine them with iff: 
example: taut1 ↔ taut2 
:= begin
    split,
    {
        intro h1,
        intro,
        intro,
        intro h2,
        cases h2 with h3 h4,
        split,
        assumption,
        assumption,
    },
    {
        intro h1,
        intro,
        intro,
        intro h2,
        intro h3,
        assumption,
    },
end

/-
to conclude this discussion, proving taut1 ↔ taut2 is not  interesting, once we have proven that taut1 and taut2 are both tautologies. but in general, we may have two statements formula1 and formula2, which we want to prove equivalent, without knowing whether they are true or not. 
-/

















---------------------------------------------------------
-- TACTICS, DEDUCTION SYSTEMS, AND THE MEANING OF LOGIC 
---------------------------------------------------------

/- 
TACTICS & DEDUCTION SYSTEMS:

tactics are also known as _inference rules, proof rules, or sequents_. all these are also collectively known as _deduction systems_. we have seen many tactics already (refl, intro, cases, split, left, ...). these tactics manipulate the proof state and help us finish our proofs. we have also seen proof rules in our formal proofs by hand.  

but what is the _meaning_ of these tactics? what is the _meaning_ of our proof rules in our proofs by hand? are these things completely arbitrary? if they are, why not introduce a _superduper_ tactic which just completes any proof? well, that wouldn't be valid, because then we would be able to also proof untrue things, so our logic / proof system would be _unsound_! (more on soundness below)

the tactics that we have are sound because they implement basic inference rules of logic. for example, the _left_ tactic implements the proof rule OrLeft, which formalizes the following english statement: "if you want to prove P ∨ Q (i.e., if your goal is P ∨ Q) then it suffices to prove P (i.e., it's OK/sound to change your goal to P)". that's exactly what _left_ does. 

the other tactics are similar. _right_ implements the proof rule OrRight. _cases h_ where h is a hypothesis that starts with or implements OrHyps. _cases h_ where h is a hypothesis that starts with and implements AndHyps. and so on. 


PROVABILITY:

tactics and deduction systems are _formalisms_. they have no "meaning" other than that they _implement_ the meaning of ∨, ∧, ¬, ∀, →, etc. so, in a way, proof rules themselves give meaning to logic. it is more correct to say that **proof rules give meaning to the notion of proof**. they define formally what a (correct) proof is. they also define what it means for a statement to be _provable_: it is provable if and only if it can be proved using the tactics. provability is the one of the two meanings of logic. 


(SEMANTIC) TRUTH: 

provability says that some proposition P can be proved (using the tactics). but does that really mean that P is "true"? in logic we have not only the notion of proof (which is symbolic/syntactic), but also the notion of semantic truth. how is semantic truth defined? that depends on the logic. in propositional logic, it is defined by truth tables, boolean functions, validity, and satisfiability, as we saw (see 07-propositional-logic.pdf). for example, we can say that the formula P → P is "true" because it's valid. 

in other logics, semantic truth is defined more or less similarly, except that things become a bit more complicated, because we cannot build truth tables, because some things are infinite! for example, consider this first-order logic formula:

    ∀ x, P(x) → P(x) 

intuitively, this formula says "for any x, if P(x) holds, then P(x) holds". this sounds true, but we cannot build a truth table to verify it! first, we don't know what x is. it's a variable, but of what type? second, if x is a nat, say, then x can take infinitely many values. so we cannot build a complete truth table. third, we also don't know what P is! it's a _predicate_, meaning it takes some x and returns true or false, but we don't know how it's defined. in order to define the semantics (truth) of first-order logic, we need to define all these things: the domain of x, the meaning of P, etc. these are called _models_ or _interpretations_. once we define those, we realize that the formula ∀ x, P(x) → P(x) is true in all interpretations! so we say that it is _valid_, just like P → P in propositional logic is valid. 


FIRST-ORDER LOGIC:

there are (many!) other valid formulas in first-order logic, for example:

    ¬ (∀ x, P(x)) ↔ (∃ x, ¬ P(x))

the above formula has both the ∀ and ∃ quantifiers. in this class we will not study the ∃ quantifier much, but in your next homework you will get to think about it a little bit. 


PROVABILITY vs. SEMANTIC TRUTH: SOUNDNESS vs COMPLETENESS

when i prove something, can i be sure that what i proved is really (semantically) true? yes, provided that the deduction system you used to prove your claim is _sound_. as we said earlier:

    soundness: provable → true 

LEAN is sound, unless you find a bug in it! let me know if you do!

the other direction is called _completeness_:

    completeness: true → provable 

LEAN is complete for propositional logic: there is a way to prove any valid formula of the form
     ∀ p q r ... : Prop, ... some boolean expression on p q r ... 

what about completeness for other logics? There are fundamental impossibility results that say that we cannot have both soundness and completeness in general for more powerful logics. we may revisit those results later. 


THE "MEANING" OF LEAN:

LEAN is a deduction system. like any other deduction system, it only "understands" symbols and syntax (proofs). LEAN does not understand semantics. semantics is the domain of human interpretation only. 

this shouldn't shock you. we saw it already when we talked about inductive types like ℕ, mynat, and their constructors. the constructor "nat.zero" is just a symbol. we (humans) take it to mean "0". in fact, "0" itself is just a symbol! in our mind, it means "the number zero". 

in fact, every language, written or oral, is based on symbols. the word "chair" is a symbol. to someone who can read english, this symbol invokes meaning: you read "chair" and you form some image of some chair in your brain. "chair" is the symbol, the image in your brain is its "meaning". 
-/



/- some student asked: is there a way to "break up" an assumption h : p → q ?  we learned modus ponens. but for modus ponens to apply, we need to know that p holds. otherwise we cannot derive q. what if we don't have p? would it be legal to have a tactic, say, tactic _rubbish_ which "breaks up" the assumption p → q into two separate assumptions, one for p, and another for q?

no, that wouldn't be legal: such a tactic would lead to UNSOUNDNESS! how?

first, we can already prove false → false:
-/
lemma lem1: false → false := begin intro, trivial, end 

-- now we can easily derive false on its own:
theorem false_using_rubbish: false :=
begin
    have H := lem1, 
    try {/- rubbish H, -/ }, -- if _rubbish_ were a tactic, this would break up hypothesis H into two hypotheses, h1 : false and h2 : false. 
    try {contradiction}, -- then we could just complete the proof with contradiction
    sorry, -- luckily we don't have _rubbish_ 
end



-------------------------------------------------------
-- FORMAL PROOFS BY HAND: DEDUCTION SYSTEMS
-------------------------------------------------------

/- 
Do we need LEAN in order to do formal proofs? – or any other software, or even computers at all!?

As I often claimed in class, we don't need LEAN, or in fact any other software, or even computers at all! We can do formal proofs "by hand". It's tedious, but it's doable in principle. You have already seen that. 

The same holds for any kind of computation, by the way. People did calculations way before computers were invented. Computers "only" made those calculations faster. 

Human "computers" were used by NASA up to at least 1960, c.f. the film: https://en.wikipedia.org/wiki/Hidden_Figures

-/


--------------------------------
-- existential angst
--------------------------------

/-
some of you may be worried about having contradictory hypotheses, e.g.: 
-/

example: ∀ p q : Prop, (p ∧ ¬p) → q 
:= begin
    intros p q h,
    -- OMG! my hypothesis h is p ∧ ¬p, which is false! that can't be right!
    sorry,
end

/-
there is nothing wrong with having contradictory hypotheses! recall the meaning of a proof state:

1 goal
p q : Prop,
h : p ∧ ¬p
⊢ q

what this says is:
"
    - assume p is a Prop
    - assume q is a Prop
    - assume that p ∧ ¬p holds
    - prove q 
"

or in other words:
"
    - if p is a Prop
    - and if q is also a Prop
    - and if p ∧ ¬p holds
    - then q holds
"

which is trivially true, because p ∧ ¬p CANNOT hold! 

so proof states are implications, and hypotheses don't have to be true. only the implication has to be true. if the hypotheses are false, the implication is trivially true, because false implies anything. 

back to our example:
-/


example: ∀ p q : Prop, (p ∧ ¬p) → q 
:= begin
    intros p q h,
    -- great! my hypothesis h is false. this is going to be an easy proof, so i will still have time to play!
    cases h with h1 h2,
    have h3 := h2 h1,
    contradiction,
end
