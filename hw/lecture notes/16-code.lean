-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- lecture code 2023-10-18

import ..hw07.mylibrary09


----------------------------------------------------
-- CALLING LEMMAS & THEOREMS LIKE FUNCTIONS
----------------------------------------------------

/-
we are now able to see how we can use previously proven lemmas or theorems, in order to prove new lemmas or theorems. we can simply "call" those existing (proven) lemmas/theorems like functions (because that's what they are!). we can call them inside the proofs of our new lemmas/theorems using "have": 
-/

-- already saw this:
theorem modus_ponens_with_implications: ∀ P Q : Prop, P → ((P → Q) → Q) 
:= begin
    intro, 
    intro,
    intro h1, 
    intro h2,   
    have h3 := h2 h1,  -- the type Q of H3 can be omitted 
    exact h3,
end

#check modus_ponens_with_implications 
/-
learn to read the type of such a theorem as a function type: what does the function consume? what does it produce?
it consumes:
    - a Prop P
    - another Prop Q
    - a proof of P (i.e., something of type P!)
    - a proof of (P → Q) (i.e., something of type P → Q)
it produces:
    - a proof of Q (i.e., something of type Q)
-/

-- we re-prove ¬(P ∧ ¬P) by "calling" the previously proven theorem "modus_ponens_with_implications":
theorem not_p_and_not_p_bis: ∀ P : Prop, ¬(P ∧ ¬P) 
:= begin
    intro,
    intro h,
    cases h with h1 h2,
    dunfold not at h2, -- not needed, should remember what ¬ is 
    have h3 : false := modus_ponens_with_implications P false h1 h2,
    /- to see what's going on in the above line, remove the ": false" part, and observe what happens as you start with just this:

    have h3 := modus_ponens_with_implications,

    and then keep adding arguments one by one to modus_ponens_with_implications:

    have h3 := modus_ponens_with_implications P,

    have h3 := modus_ponens_with_implications P false,

    have h3 := modus_ponens_with_implications P false h1, 

    have h3 := modus_ponens_with_implications P false h1 h2,
    -/
    contradiction,
end


-- we can also do it in multiple steps:
theorem not_p_and_not_p_tris: ∀ P : Prop, ¬ (P ∧ ¬P) 
:= begin
    intro,
    intro h,
    cases h with h1 h2,
    -- in multiple steps:
    have h3 := modus_ponens_with_implications,
    have h4 := h3 P,
    have h5 := h4 false,
    have h6 := h5 h1,
    have h7 := h6 h2,
    contradiction,
end








-- practice: ERASE ALL PROOFS AND TRY THEM ON YOUR OWN!

theorem thm1: ∀ x y : ℕ, (x > 0 ∧ y > 0) → x > 0 
-- we can prove this directly:
:= begin
    intro,
    intro,
    intro h,
    cases h with h1 h2,
    exact h1,
end

-- we can also prove it using a helper lemma:
lemma p_and_q_implies_p: ∀ p q : Prop, (p ∧ q) → p 
:= begin
    intro,
    intro,
    intro h,
    cases h with h1 h2,
    exact h1,
end

theorem thm2: ∀ x y : ℕ, (x > 0 ∧ y > 0) → x > 0 
-- proof by "calling" lemma p_and_q_implies_p:
:= begin
    intro,
    intro,
    intro h1,
    have h2 := p_and_q_implies_p (x > 0) (y > 0) h1,
    exact h2,
end


theorem thm3: ∀ x y : ℕ, x > 0 ∧ y > 0 → x > 0 
-- same proof but calling happens in multiple steps:
:= begin
    intro,
    intro,
    intro h,
    have h1 := p_and_q_implies_p,
    have h2 := h1 (x > 0),
    have h3 := h2 (y > 0),
    have h4 := h3 h, 
    exact h4,
end



theorem thm4: ∀ x y : ℕ, (x > 0 ∧ y > 0) → x > 0 
:= begin
    intro,
    intro,
    have h := p_and_q_implies_p (x > 0) (y > 0),
    -- but we could also stop here: 
    exact h,
end

-- theorems are functions, so we can also write this:
theorem thm5 (x y : nat) : (x > 0 ∧ y > 0) → x > 0 
  := p_and_q_implies_p (x > 0) (y > 0) -- theorem thm5 is proved!!!

#check thm5 

/-
theorems are functions that consume stuff and produce proofs. thm5 (just like thm4, thm3, ..., thm1) consumes:
  - a nat x
  - a second nat y
  - a proof of the claim (x > 0 ∧ y > 0)
and produces
  - a proof of the claim x > 0

illustration:
-/

/-
nat.lt.base is a lemma from the LEAN library. 
make sure you are able to read its type: what does it consume? what does it produce?
-/
#check nat.lt.base 
















/-
ANSWER: it consumes a nat n. it produces a proof of the claim n < n.succ, that is, a proof of the claim n+1 > n. 

note: x > y is just notation for y < x. 
-/

#check nat.lt.base 0 -- (nat.lt.base 0) is a proof that 1>0 
#check nat.lt.base 1 -- (nat.lt.base 1) is a proof that 2>1 

#check nat.lt_trans 
/-
nat.lt_trans consumes a proof of x < y and a proof of y < z and produces a proof of x < z. 
-/
#check nat.lt_trans (nat.lt.base 0) (nat.lt.base 1) -- what is this?

#check and.intro 
/-
what does and.intro consume? what does it produce?
-/

#check and.intro (nat.lt_trans (nat.lt.base 0) (nat.lt.base 1)) (nat.lt.base 0) -- what is this? 

#check thm5 2 1 (and.intro (nat.lt_trans (nat.lt.base 0) (nat.lt.base 1)) (nat.lt.base 0))  -- wow!







----------------------------------------------
-- CLASSIC LOGIC vs. CONSTRUCTIVE LOGIC
----------------------------------------------

/- 
recall the propositional logic tautology P ∨ ¬P. this tautology is also called the _law of excluded middle_, meaning there's nothing "in between" P and ¬P. so either one or the other must hold. we can prove this easily for bools:
-/
theorem excluded_middle_bool: ∀ x : bool, orb x (negb x) = tt 
:= begin
    intro,
    cases x,
    refl,
    refl,
end

-- but can we prove it for any Prop?  let's see if we can prove it with the tactics that we have learned so far:
theorem excluded_middle_1st_try: ∀ P : Prop, P ∨ ¬ P 
:= begin
    intro,
    -- now what? our goal is a disjunction, so we have to choose "left" or "right". but no matter what we choose, we cannot complete the proof... 
    try {cases P},  -- this doesn't work ... 
    sorry
end

/- in fact, the law of excluded middle is something that cannot be proven for Props with the tactics we have seen so far. in classic logic, this is an _axiom_. an axiom is something that can be taken for granted, without having to be proven. in terms of the discussion about proof rules that we had above, we can write:
    ⊢ P ∨ ¬P 
meaning that starting even with an empty left-hand side to ⊢ (i.e., no hypotheses at all) we can still prove P ∨ ¬P, for any P. 

this is an axiom of _classic_ logic, but it is not an axiom of other logics. in particular, it is not an axiom of so-called _constructive_ or _intuitionistic_ logic, which forms the foundation of the so-called _calculus of constructions_ and tools like Coq. the same logic is behind LEAN, but LEAN includes the law of excluded middle as an axiom in its library. 

You may wonder why on earth would there be a logic like constructive logic which doesn't have the law of excluded middle? Constructive logic, like its name implied, stemmed from a desire for more "constructive" mathematics, where for instance, proofs of existence of something not only proved that this something must exist, but also offered concrete ways to find it. Here's a nice example of this, taken from the _Handbook of Practical Logic and Reasoning_ by Harrison. 

Here's a non-constructive proof of the following theorem: _There exist irrational numbers x and y such that x^y (x to the power y) is rational._ "Proof: Let z denote the square root of 2. Either z^z is rational, or it is irrational. If z^z is rational, then we have found x = y = z (why? because both x and y are irrational, but x^y = z^z is rational). If z^z is irrational, then let x = z^z and y = z. Then x^y = 2 (why? because x^y = (√2^√2)^√2 = √2^(√2⬝√2) = √2^2 = 2), which is rational. QED" Now, you may be satisfied with this proof, but in the end, we don't really know what x and y are. We know that _either_ they are something, _or_ they are something else, but we don't know which. Such proofs displeased the proponents of constructive logic. The above proof is non-constructive, because it uses the axiom "either z^z is rational, or it is not rational", i.e., an instance of P ∨ ¬P (with P in this case being "z^z is rational"). 

We will not delve much into constructive logic, but it is useful to do some exercises in order to understand what can be proven using what. we will also need to be using axioms such as P ∨ ¬P in our proofs, so we will also illustrate how to appeal to those in LEAN. 
-/


-- LEAN already provides the law of excluded middle as an axiom:
#check classical.em 

/-
can we now re-prove the law of excluded middle? yes we can, using classical.em. this is trivial, since classical.em _is_ exactly the law of excluded middle. so we are proving something assuming itself, which is uninteresting. still, we show how this is done for the sake of illustrating also the usage of _have_:
-/

-- "function-oriented" proof:
theorem excluded_middle: ∀ P : Prop, P ∨ ¬ P := classical.em 

-- proof with begin ... end and have:
theorem excluded_middle_have: ∀ P : Prop, P ∨ ¬ P 
:= begin
    intro,
    have h := classical.em P, -- we call classical.em and pass P to it 
    assumption,
end

-- proof with begin ... end and cases:
theorem excluded_middle_cases: ∀ P : Prop, P ∨ ¬ P 
:= begin
    intro,
    cases classical.em P, -- we could also first do have h := classical.em P, and then cases h
    {
        left,
        exact h,
    } ,
    {
        right,
        exact h,
    }
end

#check excluded_middle
#check excluded_middle_have
#check excluded_middle_cases


/-
as with other theorems/functions that take Props as inputs, we can call classical.em with any Prop. for example:
-/

example: ∀ x : ℕ, x = 0 ∨ x ≠ 0 
:= begin
    intro,
    have h := classical.em (x = 0),
    assumption,
end

-- we could also do a more direct proof by simply calling the classical.em function:
example: ∀ x : ℕ, x = 0 ∨ x ≠ 0 := fun x : nat, classical.em ( x = 0 )  -- make sure you understand what's going on here!

