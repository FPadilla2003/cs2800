-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2023, HOMEWORK 8

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: ...
-/




/-
Technical instructions: same as in the last homework plus ADDITIONAL INSTRUCTIONS:
-/


/- IMPORTANT: 

for ALL problems in this and following homework sets, you should do two things: 

first, try to prove whatever it is you are proving _without_ induction. you don't always need induction. you often do, but not always. if you did use induction in your proof, go back and check: did you ever actually use the induction hypothesis? if you didn't, you don't need induction. go back and remove it from your proof (e.g., replace it by cases) and see whether you can complete the proof without induction. 

second, every time you use induction, try to MANUALLY GENERATE the following without LEAN's help:
1. BASE CASE(S)
2. INDUCTION STEP(S)
3. INDUCTION HYPOTHESI(E)S 

then you can check to see whether what you got is the same thing as what LEAN generates. if they are not the same, ask yourselves why. 

YOU WILL BE ASKED TO DO THIS TYPE OF MANUAL GENERATION IN EXAMS AND QUIZZES!

ALSO: you may have to use lemmas to prove the theorems we give you. if these lemmas are not already in our libraries, copy them together with their proof before using them. 
-/


import .mylibrary20

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


/- HWK08-01: 

prove the following. 

hint: use listeq. 
-/

#check listeq 

example: ∀ (x y z : ℕ) (L : list ℕ) (p : Prop), x :: y :: L = [z] → p 
:= begin
-- ANSWER: 
  intros x y z L,
  intro p,
  intro h,
  cases h,
end




/- HWK08-02: 
prove the following:
-/
lemma plus_one_succ: ∀ x : ℕ, plus x 1 = nat.succ x 
:= begin
-- ANSWER:
  intro x,
  induction x with y ih,
  {
    refl,
  },
  {
    rw plus,
    rw ih,
  }
end



/- HWK08-03:
 prove associativity of app:
-/
theorem app_associative: ∀ L1 L2 L3 : list ℕ, 
    app L1 (app L2 L3) = app (app L1 L2) L3 
:= begin
-- ANSWER: 
  intros L1 L2 L3,
  induction L1 with x L1 ih,
  {
    refl,
  },
  {
    rw app,
    rw ih,
    refl,
  }
end




-- recall the definition of minus (subtraction on nats):
#check minus -- control-click to go to the definition 

/- HWK08-04:
is the following claim true? if so prove it in LEAN, if not, exhibit a counterexample. if you prove it: did you have to use induction? 
-/
theorem minus_x_x: ∀ x : ℕ, minus x x = 0 
-- ANSWER: Yes, it is true. Here's a proof:
:= begin
  intro x,
  induction x with y ih,
  {
    refl,
  },
  {
    rw minus,
    rw ih,
  }
end



/- HWK08-05: 
is the following claim true? if so prove it in LEAN, if not, exhibit a counterexample. if you prove it: did you have to use induction? 
-/
theorem mult_1_x: ∀ x : ℕ, mult 1 x = x
-- ANSWER: Yes, it is true. Here's a proof:
:= begin
  intro x,
  rw mult,
  rw mult,
  rw plus_x_zero,
end



/- HWK08-06: 
is the following claim true? if so prove it in LEAN, if not, exhibit a counterexample. if you prove it: did you have to use induction? 
-/
theorem mult_2_x: ∀ x : ℕ, mult 2 x = plus x x
-- ANSWER:
:= begin
  intro x,
  rw mult,
  rw mult,
  rw mult,
  rw plus_x_zero,
end



/- HWK08-07: 
is the following claim true? if so prove it in LEAN, if not, exhibit a counterexample. if you prove it: did you have to use induction? 
-/
def genzeros : ℕ → list ℕ 
  | 0 := []
  | (nat.succ n) := 0 :: (genzeros n)
--

theorem genzeros_n_len_n: ∀ n : ℕ, len (genzeros n) = n 
-- ANSWER: Yes, it is true. Here's a proof:
:= begin
  intro n,
  induction n with y ih,
  {
    refl,
  },
  {
    rw genzeros,
    rw len,
    rw ih,
  }
end


/- HWK08-08: 
is the following claim true? if so prove it in LEAN, if not, exhibit a counterexample. if you prove it: did you have to use induction? 
-/
def apply : list ℕ → (ℕ → ℕ) → list ℕ 
    | [] _ := []
    | (x :: L) f := (f x) :: (apply L f)
--

theorem map_identity: ∀ L : list ℕ, apply L (λ x, x) = L 
-- ANSWER:
:= begin
  intro L,
  induction L with y ih,
  {
    refl,
  },
  {
    rw apply,
    rw L_ih,
  }
end 



/- HWK08-09: 
is the following claim true? if so prove it in LEAN, if not, exhibit a counterexample. if you prove it: did you have to use induction? 
-/
def even : nat → bool 
    | 0 := tt 
    | 1 := ff 
    | (nat.succ (nat.succ x)) := even x 
--

def double : ℕ → ℕ 
    | 0 := 0
    | (nat.succ x) := nat.succ (nat.succ (double x))
--

theorem even_double: ∀ x : ℕ, even (double x) = tt 
-- ANSWER: Yes, it is true. Here's a proof:
:= begin
  intro x,
  induction x with y ih,
  {
    refl,
  },
  {
    rw double,
    rw even,
    rw ih,
  }
end



/- HWK08-10: 
is the following claim true? if so prove it in LEAN, if not, exhibit a counterexample. if you prove it: did you have to use induction? 
-/

lemma succ_commut: ∀ x y : ℕ, nat.succ (plus x y) = plus x (nat.succ y)
:= begin
  intros x y,
  induction x with a ih,
  {
    refl,
  },
  {
    rw plus,
    rw plus,
    rw ih,
  }
end

theorem double_plus: ∀ x : ℕ, double x = plus x x 
-- ANSWER: Yes, it is true. Here's a proof:
:= begin
  intro x,
  induction x with y ih,
  {
    refl,
  },
  {
    rw plus,
    rw double,
    rw ih,
    rw succ_commut,
  }
end



/- HWK08-11:
is the following claim true? if so prove it in LEAN, if not, exhibit a counterexample. if you prove it: did you have to use induction? 
-/
theorem plus_assoc: 
    ∀ x y z : ℕ, plus x (plus y z) = plus (plus x y) z 
-- ANSWER: Yes, it is true. Here's a proof:
:= begin
  intros x y z,
  induction x with a ih,
  {
    refl,
  },
  {
    rw plus,
    rw plus,
    rw plus,
    rw ih,
  }
end



/- HWK08-12:
is the following claim true? if so prove it in LEAN, if not, exhibit a counterexample:
-/

def rev : list nat -> list nat 
  | [] := []
  | (a :: L) := app (rev L) [a] 
--

lemma appnil: ∀ L : list ℕ, app L [] = L
:= begin
  intro L,
  induction L with y ih,
  {
    refl,
  },
  {
    rw app,
    rw L_ih,
  }
end

theorem rev_app_distr: ∀ L1 L2 : list ℕ,
    rev (app L1 L2) = app (rev L2) (rev L1) 
-- ANSWER: Yes, it is true. Here's a proof:
:= begin
  intros L1 L2,
  induction L1 with x L1 ih,
  {
    rw app,
    rw rev,
    rw appnil,
  },
  {
    rw app,
    rw rev,
    rw rev,
    rw ih,
    rw app_associative,
  }
end




/- HWK08-13:
is the following claim true? if so prove it in LEAN, if not, exhibit a counterexample:
-/

theorem rev_involutive : ∀ L : list nat, rev (rev L) = L 
-- ANSWER: Yes, it is true. Here's a proof:
:= begin
  intro L,
  induction L with x L ih,
  {
    refl,
  },
  {
    rw rev,
    rw rev_app_distr,
    rw rev,
    rw rev,
    rw app,
    rw app,
    rw app,
    rw ih,
  }
end


/- HWK08-14:
is the following claim true? if so prove it in LEAN, if not, exhibit a counterexample. if you prove it: did you have to use induction? 
-/
lemma revnil : rev [] = []
:= begin
  refl,
end

lemma appnil2 : ∀ L : list ℕ, app [] L = L
:= begin
  intro L,
  refl,
end

lemma double_rev : ∀ L : list ℕ, rev (rev L) = L
:= begin
  intro L,
  induction L with x L ih,
  {
    refl,
  },
  {
    rw rev,
    rw rev_app_distr,
    rw rev,
    rw ih,
    rw rev,
    rw app,
    rw app,
    rw appnil2,
  }
end

theorem rev_left_right: ∀ L1 L2 : list nat, rev L1 = L2 → L1 = rev L2 
-- ANSWER: Yes, it is true. Here's a proof:
:= begin
  intros L1 L2,
  induction L1 with x L1 ih,
  {
    intro h,
    rw revnil at h,
    rw <- h,
    rw revnil,
  },
  {
    intro h,
    rw <- h,
    rw double_rev,
  }
end




/- HWK08-15:
is the following claim true? if so prove it in LEAN, if not, exhibit a counterexample:
-/

lemma len_distribute: ∀ L1 L2 : list ℕ, len (app L1 L2) = plus (len L1) (len L2)
:= begin
  intros L1 L2,
  induction L1 with x L1 ih,
  {
    refl,
  },
  {
    rw app,
    rw len,
    rw len,
    rw ih,
    rw plus,
  }
end

theorem rev_length: ∀ L : list ℕ, len (rev L) = len L 
-- ANSWER: Yes, it is true. Here's a proof:
:= begin
  intro L,
  induction L with x L ih,
  {
    refl,
  },
  {
    rw rev,
    rw len,
    rw len_distribute,
    rw len,
    rw ih,
    rw len,
    rw plus_one_succ,
  }
end



/- HWK08-16:
is the following claim true? if so prove it in LEAN, if not, exhibit a counterexample:
-/

lemma plus_x_succ: 
    ∀ x y : ℕ, nat.succ (plus x y) = plus x (nat.succ y) 
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

lemma plus_commutative: ∀ x y : ℕ, plus x y = plus y x 
:= begin
    intros,
    induction x with w ih,
    {
        rw plus, 
        rw plus_x_zero,
    },
    {
        rw plus,
        rw ih,
        rw plus_x_succ,
    }
end

lemma mult_x_zero : ∀ x : ℕ, mult x 0 = 0
:= begin
  intro x,
  induction x with y ih,
  {
    refl,
  },
  {
    rw mult,
    rw ih,
    rw plus,
  }
end

lemma mult_distribut : ∀ x y z : ℕ, mult x (plus y z) = plus (mult x y) (mult x z)
:= begin
  intros x y z,
  induction x with a ih,
  {
    rw mult,
    rw mult,
    rw plus,
    rw mult,
  },
  {
    repeat {
      rw mult,
    },
    rw ih,
    rw plus_assoc,
    rw plus_commutative,


  }
end

lemma mult_one : ∀ x : ℕ, mult x 1 = x
:= begin
  intro x,
  induction x with y ih,
  {
    refl,
  },
  {
    rw mult,
    rw ih,
    rw plus,
    rw succeq,
    rw plus,
  }
end

theorem mult_commut: ∀ x y : ℕ, mult x y = mult y x 
-- ANSWER:
:= begin
  intros x y,
  induction x with a ih,
  {
    rw mult,
    rw mult_x_zero,
  },
  {
    rw mult,
    rw ih,
    rw <- plus_one_succ,
    rw mult_distribut,
    rw mult_one,
    rw plus_commutative,
  }
end




/- HWK08-17:
 prove app_assoc4:

HINT: There is a (really really) short proof for this one. If you find yourself getting tangled up, step back and try to look for a simpler way. 
-/
theorem app_assoc4: ∀ L1 L2 L3 L4 : list nat, 
    app L1 (app L2 (app L3 L4)) = app (app (app L1 L2) L3) L4 
:= begin
-- ANSWER: Yes, it is true. Here's a proof:
  intros L1 L2 L3 L4,
  repeat {rw app_associative},
end



/- HWK08-18:
state and prove that functions even and even_v2 are equivalent:
-/
def even_v2 : nat → bool
    | 0 := tt 
    | (nat.succ x) := negb (even_v2 x)
--

lemma double_negb: ∀ x : bool, negb (negb x) = x
:= begin
  intro x,
  cases x,
  refl,
  refl,
end

lemma negb_even : ∀ x : ℕ, even x.succ = negb (even x)
:= begin
  intro x,
  induction x with y ih,
  {
    refl,
  },
  {
    rw even,
    rw ih,
    rw double_negb,
  }
end

-- ANSWER: 
theorem even_even_v2: ∀ x : ℕ, even x = even_v2 x
:= begin
  intro x,
  induction x with y ih,
  {
    refl,
  },
  {
    rw even_v2,
    rw <- ih,
    rw negb_even,
  }
end






/- HWK08-19:
prove each of the following theorems. 

think: which ones need induction?
-/

def eqb : ℕ → ℕ → bool 
    | 0 0 := tt 
    | 0 (nat.succ y) := ff     
    | (nat.succ x) 0 := ff 
    | (nat.succ x) (nat.succ y) := eqb x y 
--

def leq : ℕ → ℕ → bool 
  | 0 y := tt 
  | (nat.succ x) 0 := ff 
  | (nat.succ x) (nat.succ y) := leq x y 
--


theorem eqb_succ_inj: 
∀ x y : ℕ, eqb (nat.succ x) (nat.succ y) = tt → eqb x y = tt 
:= begin
-- ANSWER:
  intros x y,
  intro h,
  rw eqb at h,
  rw h,
end


theorem eqb_refl: ∀ x : ℕ, eqb x x = tt 
:= begin
-- ANSWER:
  intro x,
  induction x with y ih,
  {
    refl,
  },
  {
    rw eqb,
    rw ih,
  }
end


theorem leq_succ: ∀ x : ℕ, leq x (nat.succ x) = tt 
:= begin
-- ANSWER:
  intro x,
  induction x with y ih,
  {
    refl,
  },
  {
    rw leq,
    rw ih,
  }
end


theorem eqb_eq_zero: ∀ x : ℕ, eqb x 0 = tt → x = 0 
:= begin
-- ANSWER:
  intro x,
  intro h,
  cases x,
  refl,
  rw eqb at h,
  contradiction,
end






/- HWK08-20 (not graded, just for your fun, you don't have to submit a solution): 

in this problem we will formalize the so-called "drinker's paradox" which goes like this: "There is someone in the pub such that, if they are drinking milk, then everyone in the pub is drinking milk." write a LEAN theorem expressing this fact. do not prove the theorem, just state it. 

notes: 
  - you can represent people in the pub by nats, so that "everyone in the pub" can be written as ∀ x : ℕ 
  - use the existential quantifier ∃ (exists) for "there is someone" 
  - you can represent the fact that someone drinks milk as a predicate Milk : ℕ → Prop, so that (Milk x) holds if x drinks milk, otherwise (Milk x) does not hold
  - think about why this statement is true (it is!) and notice that the truth of the statement doesn't depend on what everyone is drinking: milk, water, vodka, or anything else! so in fact the statement holds for _any_ predicate Drinks : ℕ → Prop. use the higher-order capability of LEAN to quantify your claim over all possible such predicates. 

you don't have to prove the theorem. just state it. (for those of you who are curious and want to go further, the theorem can be proven using LEAN's exists.elim axiom and existsi tactic.) 

-/ 
-- ANSWER:
theorem drinker: ∀ Drinks : ℕ → Prop, ∃ x : ℕ, (Drinks x → ∀ y : ℕ, Drinks y) 
:= begin 
  sorry, 
end