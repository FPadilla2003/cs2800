-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- lecture code 2023-10-25

import .mylibrary18 

/-
make sure you:
    - do the practice problems from 18-code.lean
    - read and understand the entire 18-code.lean -- we won't discuss it in class unless you have questions
-/

------------------------------------------
-- take stock: how good magicians are we?
------------------------------------------

/-
we are almost half-way through the course. 
we have learned many magic spells (=tactics). 
we can do quite a few magic tricks (=proofs). 
but how good magicians are we?
there are still many things we don't know how to prove!

and what's embarrassing is that some of the things we cannot prove seem very simple:
-/


-- plus and mult on nats
#check plus -- imported 
#check mult -- imported


-- we can easily prove this: 
#check plus_0_x -- imported

example: ∀ (x : ℕ), plus 0 x = x
:= begin
    intro,
    refl,
end


-- but what about this?
theorem plus_x_0_try1: forall x : nat, plus x 0 = x 
:= begin
    intro,
    try {refl}, -- it doesn't work! 
    /- but why? why is refl able to prove "plus 0 x = x" but not able to prove "plus x 0 = x" ?
    the reason lies in the definition of the function plus. recall how plus is defined:
    
    def plus : nat -> nat -> nat  
    | nat.zero y := y 
    | (nat.succ x) y := nat.succ (plus x y)

    and recall that nat.zero is the same as 0. therefore, "plus 0 x" matches the first case of the definition of plus (by matching y with x), and refl can simplify it to just "x". then the equality becomes "x = x" and refl concludes the proof. 

    but "plus x 0" does _not_ match the first case of the definition of function plus. and it does not match the second case either. so refl cannot simplify anything in this case, and gives up. 

    we can also see this better if we try to apply rw or a similar tactic:
    -/
    try {rw plus}, -- nothing happens, rw cannot simplify 
    try {dunfold plus},  -- nothing happens, as we should now expect
    try {unfold plus},   -- nothing happens, as we should now expect 
    sorry,
end

/-
so, "plus 0 x" is easy to simplify based on the first case of the definition, but "plus x 0" is not.

now, we could say that plus x 0 = plus 0 x, by commutativity of addition. but we have not yet proved commutativity of addition! (this will also require induction, see below!)
-/



-- but perhaps we can prove it using proof by cases?
theorem plus_x_0_equals_x_try_by_cases: forall x : nat, plus x 0 = x 
:= begin
    intro,
    cases x with y, -- the "with y" renames the variable "x" to "y" in the 2nd case
    {
        refl, -- this was easy!
    },
    { -- but wait, there's one more case ... 
        try {refl}, -- does nothing  
        rw plus,
        try {refl}, -- does nothing
        -- perhaps more cases?
        cases y,
        {
            refl, -- phew ... 
        },
        { -- but wait, there's still one more case ... 
            rw plus,
            try {refl}, -- nothing
            -- i can keep generating cases, but i will never finish! why?
            -- i give up ...
            sorry,
        },
    },
end




-- what about this?
theorem plus_commutative: ∀ (x y : nat), plus x y = plus y x 
:= begin
    intro,
    intro,
  -- x : ℕ     hypothesis 1 
  -- y : ℕ     hypothesis 2 
  -- ⊢ ... goal ... 
    try {refl}, -- merde, alors!
    sorry,
end

-- what about this?
theorem plus_associative: ∀ (x y z : nat), plus (plus x y) z = plus x (plus y z) 
:= begin
    intro,
    intro,
    intro,
    try {refl}, -- !@#$%$#!@#
    sorry,
end



#check app -- imported

/- what about proving things about lists?

just like we can prove plus 0 x = x, we can also prove app [] L = L quite easily:
-/

theorem app_nil_L: ∀ L : list nat, app [] L = L 
:= begin
    intro,
    refl,
end

-- but what about app L [] = L? 
theorem app_L_nil_1st_try: ∀ L : list ℕ, app L [] = L 
:= begin
    intro,
    try {refl}, -- doesn't work
    try {rw app}, -- doesn't work 
    cases L with x L1 ,
    {
        refl,
    },
    {
        rw app,
        rw (listeq x x (app L1 []) L1),
        split,
        refl,
        -- now what? back to square zero!
        sorry,
    }
end




/- it looks like we are not strong enough magicians yet to complete these proofs. as Master Yoda would put it: "much to learn you still have my young apprentice"! not to worry. once we learn induction such proofs will be a piece of cake for us. 
-/






----------------------------------------------------
-- INDUCTION
----------------------------------------------------

/-
the solution is a powerful tool called "induction". you have already seen mathematical induction on natural numbers, in your math courses. in this course, we will learn much more general and powerful induction methods. you will learn induction on ANY inductive data type T (that's why these data types are called "inductive"). in a nutshell, the induction principle is this:

    when trying to prove that some proposition P holds for all objects of type T, i can assume that P already holds for "smaller" objects of type T when trying to prove that it holds for "larger" objects of type T. 
    
this is the _induction hypothesis_ that we make during the _induction step_. we now explain all that in detail. 
-/

/-
let's start with recalling induction on nats:

1. suppose i want to prove that some property P(x) holds for any nat x.  

2. so, i have to prove that P(0) holds, and also that P(1) holds, and also that P(2) holds, and so on. 

3. let me start by proving that P(0) holds. this is the _base case_.

4. now let me prove that, for any nat n, _if P(n) holds then P(n+1) holds_. this is the _induction step_. the part _P(n) holds_ is the _induction hypothesis_. i'm assuming that P holds for the smaller n (induction hypothesis) and i'm proving that P holds for the next larger n+1 (induction step). 

5. if i manage to prove both the base case and the induction step, then i claim that P(x) indeed holds for _any_ nat x. why? well, because i have proven the induction step _for any n_. let me instantiate the induction step with n := 0. then i get:
    _if P(0) holds then P(0+1) holds_, i.e., _if P(0) holds then P(1) holds_
but i know that P(0) holds because i have proven the base case. so i can apply modus ponens and i get that P(1) holds too! now i go on, and instantiate the induction step with n := 1. then i get:
    _if P(1) holds then P(2) holds_
but i know that P(1) holds. so i apply modus ponens and i get that P(2) holds too. i can continue this way for as long as necessary, to prove P(x) for any x. if x is very very large, say 100000000000000, then i have to do many instantiations and modus ponens, but i don't really have to do them. i just know that they can be done! so i can conclude that P(x) indeed holds for any nat x. 

we can express the induction principle for natural numbers in LEAN, as follows:
-/

def nat_induction := ∀ P : ℕ → Prop, -- for any property P of nats 
    (P 0) → -- if the base case holds 
    (∀ n : ℕ, (P n) → (P (nat.succ n))) → -- and if the induction step also holds
    (∀ n : ℕ, P n)  -- then P holds for all nats! 


/- we can use nat_induction to prove stuff, as in the example below. 

NOTE: if the proof that follows is unreadable to you, don't worry! we will NOT do proofs by induction like this! we will use the induction tactic instead. the example that follows is only meant to illustrate how we COULD use the induction axiom to prove stuff. 
-/

example: nat_induction → (∀ x : ℕ, plus x 0 = x)
:= begin
    intro h1,
    dunfold nat_induction at h1,
    have h2 := h1 (λ x : ℕ, plus x 0 = x), -- instantiate P 
    have fun1 : ((λ (x : ℕ), plus x 0 = x) 0) = (plus 0 0 = 0) := begin refl, end,
    rw fun1 at h2, -- compute the lambda 
    have h3 : plus 0 0 = 0 := begin refl, end, -- prove the base case
    have h4 := h2 h3, -- get rid of the base case with modus ponens
    have h5 : (∀ (n : ℕ), (λ (x : ℕ), plus x 0 = x) n → (λ (x : ℕ), plus x 0 = x) (nat.succ n)) := begin
        intro,
        intro g1,
        dunfold plus,
        rw g1,
    end, -- prove the induction step 
    have h6 := h4 h5,  -- get rid of the induction step with modus ponens 
    exact h6, -- DONE!
end

/-
but the above is too complicated, in many ways. 

first, we have to add nat_induction as a hypothesis to every theorem that we want to prove about nats! this would be easy to fix. we could simply define nat_induction as an axiom (like with classical.em). 

second, and more importantly, the proof itself is complex. we have to instantiate nat_induction with the predicate we want to talk about, and there are all these λ's in our proof, and long formulas! can we simplify all that? yes! LEAN provides us with a built-in tactic to do induction:
-/

----------------------------------------------------
-- the _induction_ tactic 
----------------------------------------------------

-- let's prove the above theorem using the _induction_ tactic:
theorem plus_x_zero: ∀ x : ℕ, plus x 0 = x 
:= begin
    intros,
    induction x, -- LEAN automatically generates two goals
    { -- base case: x = 0
        /- the base case goal is generated by replacing x (the variable we induct on) by the base case constructor 0 (nat.zero)-/
        refl,
    },
    { -- induction step: x = nat.succ x_n
        /- the induction step goal is generated by replacing x (the variable we induct on) by the recursive case construction (nat.succ x_n). the inductive hypothesis is generated by replacing x by the "smaller nat" x_n. -/
        rw plus,
        rewrite x_ih, -- x_ih is the "induction hypothesis"
    }
end



-- LEAN automatically chooses names such as x_n, x_ih, etc. if we don't like them, we can change them:
theorem plus_x_zero_alt_names: ∀ x : ℕ, plus x 0 = x 
:= begin
    intros,
    induction x with y ih, -- the "smaller" nat is now called "y" and the induction hypothesis is now called "ih"
    { -- base case: x = 0
        refl,
    },
    { -- induction step: x = nat.succ y
        rw plus,
        rewrite ih, 
    }
end

/- at this point you should stop and compare: (1) the failed proof attempt by cases, and (2) the successful proof by induction. where do the two differ? only in one thing: in the proof by induction, in the case x = nat.succ y, we have an extra hypothesis, the induction hypothesis ih, which we don't have in the proof by cases. it's the induction hypothesis which allows us to "make the jump to infinity"! 

see also:
https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html
-/



/- with induction, we have lift off. we can now pretty much prove everything that can be proven, and fly to the stars!

let's exercise this new power of ours and do more proofs by induction:
-/

theorem mult_x_zero: ∀ x : ℕ, mult x 0 = 0 
:= begin
    intros,
    induction x with y ih,
    {
        refl,
    },
    {
        rw mult,
        rw ih,
        refl,
    }
end

theorem mult_x_one: ∀ x : ℕ, mult x 1 = x 
:= begin
    intros,
    induction x with y ih,
    {
        refl,
    },
    {
        rw mult,
        rw ih,
        rw plus,
        refl,
    }
end



----------------------------------------------------
-- PROOF BY INDUCTION vs PROOF BY CASES 
----------------------------------------------------

/- induction applies to any inductive data type. we have already seen it apply to nats and lists. what if we try induction on a simple enumerative data type like _weekday_? in that case, proof by induction trivially becomes proof by cases, since all the constructors of _weekday_ are "base constructors" in the sense that they are non-recursive. so doing induction on weekday only generates _base cases_:
-/

#check weekday -- imported 
#check next_workday -- imported 

open weekday 

theorem next_workday_not_saturday: ∀ d : weekday, next_workday d ≠ saturday 
:= begin
    intro,
    induction d, -- here has same effect as _cases d_
    -- all the cases are _base cases_ because the data type is a simple enumerative type:
    repeat {
        intro h,
        rw next_workday at h,
        contradiction,
    } 
end





--------------------------------------------
-- INDUCTION is ONLY for INDUCTIVE TYPES!
--------------------------------------------

-- just like we cannot do cases on Props, we CANNOT do induction on non-inductive types, like Prop: 

example: ∀ p : Prop, true 
:= begin
    intro,
    induction p, -- error: "inductive datatype expected"!
end



