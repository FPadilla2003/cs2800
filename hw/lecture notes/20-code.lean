-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- lecture code 2023-10-26

import .mylibrary20  -- NEW LIBRARY FILE AVAILABLE ON CANVAS


----------------------------------------------------
-- SIMPLIFYING if-then-else: itetrue and itefalse
----------------------------------------------------

/- when we know that some Prop p is true, we should be able to simplify (if p then x else y) to x. and if we know that p is false, we should be able to simplify the above if-then-else to y. 

we can use the lemmas itetrue and itefalse to do that: 
-/

#check itetrue 
#check itefalse 

example: ∀ x : ℕ, ∀ s1 s2 : string, 
    (if (x = x) then s1 else s2) = s1 
:= begin
    intros,
    have h1 : x = x := begin refl, end, 
    have h2 := itetrue (x = x) h1 string s1 s2 ,
    exact h2,
end

example: ∀ x y : ℕ, ∀ L : list ℕ, 
    (x ≠ y) → (x :: (if (x = y) then L else [])) = [x]  
:= begin
    intros x y L h1,
    have h2 := itefalse (x = y) h1 (list ℕ) L [] ,
    rw h2,
end








--------------------------------
-- INDUCTION continued
--------------------------------




-----------------------------------------------
-- INDUCTION on ARBITRARY INDUCTIVE TYPES
-----------------------------------------------

/- what does induction on an arbitrary inductive type T look like?

again, the principle is: 
    - we can assume that what we are trying to prove holds for "smaller" elements of T 
    - we prove that it holds for "bigger" elements of T 
where "bigger" means "constructed from the smaller using T's constructors". 

in particular, suppose that x : T (i.e., x is of type T) and that T has **k constructors**.

then, "induction x" will generate **k subgoals, one for each constructor**. these subgoals are also called _proof obligations_. 

suppose constructor i is as follows: 

    | foo : T → T → T → ℕ → bool → T 

meaning that foo consumes 3 elements of type T, one nat, and one bool, and produces a new element of type T. 

then the i-th proof obligation of the induction will look like this:

    - assume that the goal holds for some x1 of type T (induction hypothesis 1)
    - assume that the goal holds for some x2 of type T (induction hypothesis 2)
    - assume that the goal holds for some x3 of type T (induction hypothesis 3)
    - prove that the goal holds for (foo x1 x2 x3 n b), for any n : ℕ, and any b : bool. 

let us look at examples of this below: 
-/




--------------------------------------------------------
-- MULTIPLE INDUCTION HYPOTHESES -- INDUCTION ON TREES
--------------------------------------------------------

/- so far we have talked about the "smaller" element that some element x that we induct on is replaced with in the induction hypothesis. for example, if x is a nat, and x = nat.succ y, then the "smaller" element is y. if x is a list of nats, and x = (a :: L), then the "smaller" element is the list L. if x is a type3, and x = type3.foo z t1, then the "smaller" element is t1. etc. 

but what if x is a tree? recall the type bton: 
-/

inductive bton : Type 
  | leaf : nat -> bton 
  | node : bton -> bton -> bton 


/- what would induction on an element of type bton look like? if t is of type bton, what would be the "smaller" element? to answer this question, we first note that bton has two constructors, so we must consider two cases:

    1. "leaf" is a base case, since constructor _leaf_ doesn't take as input another bton. 

    2. "node" is an inductive case, because constructor _node_ takes as input another bton. in fact, _node_ takes as input _two_ btons. 

because constructor _node_ takes as input two btons, there are _two_ smaller elements. intuitively, each subtree of a binary tree is a "smaller" tree. 

the beauty of induction is that it allows us to assume an induction hypothesis for _every_ "smaller" element. if there's just one smaller element, we have just one induction hypothesis. but if there's more, we have more than one induction hypotheses. in the case of bton, we expect to have _two_ induction hypotheses, one for each subtree. 

let us see this:
-/

-- recall this function:
def bton2natlist: bton -> list nat 
  | (bton.leaf x) := [x] 
  | (bton.node t1 t2) := app (bton2natlist t2) (bton2natlist t1) 


-- this is a simple example that we can prove without induction:
theorem easytree: ∀ x y : ℕ, 
    bton2natlist (bton.node (bton.leaf x) (bton.leaf y)) = [y,x] 
:= begin
    intros,
    rw bton2natlist,
    rw bton2natlist,
    rw bton2natlist,
    rw app,
    rw app,
end

/- now let's look at some theorems which need induction. 

(we will not actually prove these, because we don't know how to reason about LEAN's > relation. but we can see how the induction tactic works on the bton data type.)
-/

theorem inducttree: ∀ t : bton, 
    len (bton2natlist t) > 0 
:= begin
    intro,
    induction t with x t1 t2 ih1 ih2,  
    sorry,
    sorry 
end


theorem inducttree2: ∀ t1 t2 : bton, 
    len (bton2natlist (bton.node t1 t2)) > 0 
:= begin
    intros,
    induction t1 with x t3 t4 ih1 ih2, 
    {
        rw bton2natlist,
        rw bton2natlist,
        sorry,  
    },
    { -- the induction step has two induction hypotheses:
        -- ih1: assume that the result holds for the left subtree t3
        -- ih2: assume that the result holds for the right subtree t4
        -- goal: prove that the result holds for the parent tree (bton.node t3 t4) 
        rw bton2natlist,
        rw bton2natlist,
        sorry,  
    }
end


--------------------------------------------------------
-- MULTIPLE BASE CASES AND MULTIPLE INDUCTION STEPS 
--------------------------------------------------------

/- just like in a proof by cases we can have multiple cases/subgoals to prove, in a proof by induction, we might have multiple base cases and multiple induction steps. suppose we have a data type with two base cases and two inductive cases:
-/

inductive type3 : Type 
    | bla : type3                           -- 1st base case
    | blu : nat -> type3                    -- 2nd base case
    | foo : nat -> type3 -> type3           -- 1st inductive case
    | bar : bool -> type3 -> type3          -- 2nd inductive case
    | bor : nat -> type3 -> bool -> type3   -- 3rd inductive case

/- what does induction on an element of type3 look like? well, we would have to prove 5 cases, corresponding to the 5 constructors: _bla_, _blu_, _foo_, _bar_ and _bor_. _bla_ and _blu_ are both base cases because their constructors do not take another element of type3 as input, but _foo_, _bar_ and _bor_ are inductive cases. so in this case, we expect to have _two_ base cases and _three_ induction steps! indeed:
-/



constant f1 : type3 -> type3 -- let f1 be some function from type3 to type3
constant f2 : type3 -> type3 -- let f2 be some function from type3 to type3 

-- never mind what the theorem below states, it's just for illustration:
theorem illustration_many_induction_steps: 
    ∀ t : type3, f1 t = f2 t 
:= begin
    intro,
    /- stop and think: **how many subgoals do i expect if i do induction t ?** -/
    /- stop and think: **what will each subgoal look like?** (generate the subgoals by hand!) -/





























































    induction t with x y t1 ih1 b t2 ih2 z t3 c ih3, -- generates 5 subgoals
    { -- base case: t = type3.bla 
        sorry,
    },
    { -- 2nd base case: t = type3.blu x, for some x : ℕ 
        sorry,
    },
    { -- induction step: t = type3.foo y t1, for some y : ℕ and some t1 : type3
        sorry,
    },
    { -- induction step: t = type3.bar b t2, for some b : bool and some t2 : type3
        sorry,
    },
    { -- induction step: t = type3.bor z t3 c, for some z : ℕ and some t3 : type3 and some c : bool  
        sorry,
    }
end




-- here's another data type whose last constructor "bor" generates multiple induction hypotheses:
inductive type4 : Type 
    | bla : type4   
    | blu : nat -> type4   
    | foo : nat -> type4 -> type4       
    | bar : bool -> type4 -> type4      
    | bor : nat -> type4 -> bool -> type4 -> type4 

/- the difference with type3 is constructor bor:

    | bor : nat -> type3 -> bool -> type3   

type3.bor takes only one element of type3. type4.bor takes two elements of type4. therefore, when we are trying to prove something by induction on type4, we shoule expect the 5th subgoal (3rd induction step) to have _two_ induction hypotheses:
-/

variable g1 : type4 -> type4 
variable g2 : type4 -> type4 

theorem many_induction_steps_many_induction_hypotheses: 
    ∀ t : type4, g1 t = g2 t 
:= begin
    intro,
    /- stop and think: **how many subgoals do i expect if i do induction t ?** -/
    /- stop and think: **what will each subgoal look like?** (generate the subgoals by hand!) -/





































































    induction t with x y t1 ih1 b t2 ih2 z t3 c t4 ih3 ih4,
    { -- base case: t = type4.bla 
        sorry,
    },
    { -- base case: t = type4.blu x for some x : ℕ 
        sorry,
    },
    { -- induction step: t = type4.foo y t1, for some y : ℕ and some t1 : type4 
        -- ih1: assume that the result holds for t1
        -- goal: prove that the result holds for type4.foo y t1
        sorry,
    },
    { -- induction step: t = type4.bar b t2, for some b : bool and some t2 : type4
        -- ih2: assume that the result holds for t2
        -- goal: prove that the result holds for type4.bar b t2
        sorry,
    },
    { -- induction step: t = type4.bor z t3 c t4, for some z : ℕ and some t3 : type4 and some c : bool and some t4 : type4
        -- ih3: assume that the result holds for t3
        -- ih4: assume that the result holds for t4
        -- goal: prove that the result holds for type4.bor z t3 c t4 
        sorry,
    },
end


/- IMPORTANT: LEARN TO GENERATE THE INDUCTION PROOF OBLIGATIONS BY HAND!

you will be asked in quizzes, homeworks, exam, etc, things like "how many proof obligations does this induction generate and which ones?". 
-/



/-
induction is a powerful tool. we are not done with induction. we will learn how to "smell" which induction scheme to use (we will see what that means), which variable to induct on, and other tricks. but before that, we must address one important topic: lemma discovery. 
-/





---------------------
-- LEMMA DISCOVERY 
---------------------

/- 
lemmas are like "helper" functions. often we reach a point in the proof where we have a goal which seems plausible, given the hypotheses that we have. we can go ahead and prove that goal within the proof of the main theorem using the "have" mechanism that we have already seen. but this leads to unreasonably long proofs, which are unreadable, and non-reusable. just like in programming, in proving also we need a principle of modularity. this is given to us by lemmas. instead of proving what we need within the main theorem, we separate it and prove it outside as a lemma. let us illustrate this:
-/


-- let's try to prove that plus is commutative: 
theorem plus_commut_try1: ∀ (x y : nat), plus x y = plus y x 
:= begin
    intros,
    induction x with z ih,
    {
        rw plus,
        /-
        lemma discovery 1: we know that plus y 0 = y, in fact we have proven that in our previous lecture. we go back, we copy that as a lemma, and we return here to complete the proof. 
        -/
        sorry,
    },
    sorry,
end

theorem plus_x_zero: ∀ x : ℕ, plus x 0 = x 
:= begin
    intros,
    induction x with y ih, 
    { 
        refl,
    },
    {
        rw plus,
        rewrite ih, 
    }
end

theorem plus_commut_try2: ∀ (x y : nat), plus x y = plus y x 
:= begin
    intros,
    induction x with z ih,
    {
        rw plus,
        rw plus_x_zero,
    },
    {
        rw plus,
        rw ih,
        -- current goal: (y+z) + 1 = y + (z+1) 
        -- we reached a point where we have something that looks true, but just _refl_ won't cut it:
        try {refl}, -- nothing happens
        -- indeed, dunfold doesn't apply:
        try {rw plus,},
        /- lemma discovery 2: this is a more realistic case of "lemma discovery". we need to invent a lemma that we haven't seen in class yet! we will face this situation very often. the first question now is, WHAT is the lemma that we want? (the second question will be how to prove it, but first we have to discover WHAT to prove!)
        
        in this example discovering the WHAT is actually easy. we can simply copy-paste the goal that we are stuck with and try to prove it for all y and z:
        -/
        sorry,
    }
end


lemma plus_y_succ_z: ∀ y z : ℕ, nat.succ (plus y z) = plus y (nat.succ z) 
:= begin
    intros,
    induction y with w ih,
    {
        refl,
    },
    {
        rw plus,
        rw plus,
        rw succeq, -- optional 
        rw ih,
    }
end

-- now we can return to our theorem and complete the proof:
theorem plus_commut: ∀ x y : ℕ, plus x y = plus y x 
:= begin
    intros,
    induction x with z ih,
    {
        rw plus_x_zero, 
        refl,
    },
    {
        rw plus,
        rw ih,
        rw plus_y_succ_z, -- we call the new lemma
    }
end

/- note that variable names in the lemma don't have to be identical to those in the theorem. a lemma is like a function. we can "call" it with any arguments that we want. let us illustrate this by restating and reproving the same lemma with different variable names:
-/
lemma plus_x_succ_y: ∀ x y : ℕ, nat.succ (plus x y) = plus x (nat.succ y) 
:= begin
    intros,
    induction x with z ih,
    {
        refl,
    },
    {
        rw plus,
        rw plus,
        rw ih,
    }
end

-- we can reprove our theorem using the modified lemma:
theorem plus_commut_2: ∀ x y : ℕ, plus x y = plus y x 
:= begin
    intros,
    induction x with z ih,
    {
        rw plus_x_zero, 
        rw plus,
    },
    {
        rw plus,
        rw ih,
        rw plus_x_succ_y, -- even though our variables are called y and z, LEAN can still match them ("unify" them) with the names x and y used in the lemma plus_x_succ_y
    }
end



-- yet another proof of the same theorem, with a more explicit "call" to lemma plus_x_succ_y :
theorem plus_commut_3: ∀ x y : ℕ, plus x y = plus y x 
:= begin
    intros,
    induction x with z ih,
    {
        rw plus_x_zero,
        refl,
    },
    {
        rw plus,
        rw ih,
        have h := plus_x_succ_y y z, 
        exact h,
    }
end


/-
lemma discovery is not always going to be as easy as the copy-paste that we did to discover plus_y_succ_z. this is to be expected: theorem proving is a creative process. it cannot be automated in general (we will see why when we talk about undecidability). some theorems require a lot of ingenuity in discovering the right lemmas, etc. this is what mathematicians do. even for proving software, we sometimes need to discover fundamental properties about our programs, and express those as lemmas, in order to prove our theorem. we will see this during the rest of the course, where we will learn how to prove more and more difficult theorems about our code. 
-/




--------------------
-- GENERALIZATION
--------------------

/-
one technique for lemma discovery is generalization. we sometimes need to discover and prove a _more general_ version of the theorem we are trying to prove. this is called "generalization" and it illustrates an amazing thing about proving theorems: that sometimes a _stronger_, (more general) result is easier to prove than its weaker (more specialized) version! how can this be? let's look at a couple of examples. 

consider the theorem below: 
-/

theorem app_L_3_times_failed: 
    ∀ L : list ℕ, app (app L L) L = app L (app L L) 
:= begin
  intro,
  induction L with x L2 ih,
  {
    refl,
  },
  {
    rw app,
    rw app,
    rw app,
    rw listeq,
    split,
    refl,
    -- stuck! the induction hypothesis doesn't help!!! the problem is that i have L2 everywhere... i should have some other lists for the 2nd and 3rd list, not L2 ... 
    sorry,
  }
end


/- solution: generalization! 

astonishingly, the _more general_ result is easier to prove!!! :
-/
theorem app_assoc: ∀ L1 L2 L3 : list ℕ, app L1 (app L2 L3) = app (app L1 L2) L3 
:= begin
    intros,
    induction L1 with x L4 ih,
    {
        refl,
    }    ,
    {
        rw app,
        rw ih,
        rw app,
        rw app,
    }
end

-- now the specialized result follows easily from the general result:
theorem app_L_3_times: ∀ L : list ℕ, app (app L L) L = app L (app L L) 
:= begin
  intro,
  rw app_assoc,
end

