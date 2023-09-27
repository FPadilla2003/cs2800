-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!


-- lecture code 2023-09-25


/- LOGISTICS

- Lecture notes are updated weekly:
  https://course.ccs.neu.edu/cs2800f23/lecture-notes.pdf

- they provide a roadmap to our course: make sure you understand all the bullet points listed in the course outline: they represent what we have covered already. 

- if some of these concepts are foreign to you, you are falling behind. 

-/

/-  DO DIVIDE FROM HWK02
-/



---------------------------------------------------
-- LEAN's limitations
---------------------------------------------------
inductive mynat : Type   
    | Z : mynat 
    | S : mynat -> mynat 

open mynat 

def myplusLEANcanTrefl: mynat -> mynat -> mynat 
  | Z Z := Z
  | Z (S n) := S (myplusLEANcanTrefl Z n)
  | (S n) Z := S (myplusLEANcanTrefl n Z)
  | (S n1) (S n2) := S (S (myplusLEANcanTrefl n1 n2))

#reduce myplusLEANcanTrefl Z Z
#reduce myplusLEANcanTrefl (S Z) (S (S Z))

example: (myplusLEANcanTrefl Z Z) = Z := begin refl end -- error?!
example: (myplusLEANcanTrefl Z Z) = Z := begin unfold myplusLEANcanTrefl end -- works, we will learn the unfold tactic later
example: (myplusLEANcanTrefl Z (S Z)) = (S Z) := begin unfold myplusLEANcanTrefl end



def myplusLEANcanrefl: mynat -> mynat -> mynat 
  | Z Z := Z
  | (S x) Z := (S x)
  | Z (S y) := (S y)  
  | (S x) (S y) := S (S (myplusLEANcanrefl x y)) 



example: myplusLEANcanrefl Z Z = Z := begin refl, end 
example: myplusLEANcanrefl Z (S Z) = S Z := begin refl, end 
example: myplusLEANcanrefl (S Z) Z = S Z := begin refl, end 
example: myplusLEANcanrefl (S Z) (S Z) = S (S Z) := begin refl, end 


/- it's unclear why LEAN "can't do refl" on the claim "(myplusLEANcanTrefl Z Z) = Z" but can do refl on "(myplusLEANcanrefl Z Z) = Z". it's one of the mysteries of LEAN, that we are not interested in in this class. our goal is not to learn the internal subtleties of LEAN, but to learn the fundamentals. 

as far as we are concerned, (myplusLEANcanTrefl Z Z) = Z holds, because (myplusLEANcanTrefl Z Z) indeed reduces to Z, by the first line in the definition of myplusLEANcanTrefl.

in general, if you find that LEAN "can't refl" your example test, and you are positive that your test is correct, we will accept your solution and you will not lose points in the homework or exam, for instance. HOWEVER, NOTE: make sure that you are calling your function with CONSTANTS (so that computation can be done) and that your function definition is correct (no ambiguous/overlapping cases, obviously terminating, etc). 
-/







-- QUIZ TIME!






------------------------------------------------------------
-- INTRODUCTION TO FORMAL SPECIFICATIONS: THE TYPE Prop 
------------------------------------------------------------

/- 
enough with programming for now! let's start now talking about specs (specifications)! specifications are _properties that we want our programs to have_. we have already written some simple specifications, with "example:". 
-/

def len : list nat -> nat 
  | [] := 0
  | (_ :: L) := 1 + len L 

example: len [] = 0 := begin refl, end 
/- in english, we can read the above as saying "len should return zero when called with the empty list as input" or something like that. 

specs written in english are fine, but they are not precise enough. in this class, we will write specs in logic. specs written in logic are called _formal_ specifications. 
-/



/- what exactly can we write after "example:" ? we can write any statement of type "Prop" (for "Proposition"). a proposition is something that can be either true or false, but it is _not_ a boolean. for example, claims of equality are propositions:
-/

#check (0 = 0)  -- we can drop the parentheses, but note that what is being checked is the entire expression "0 = 0"
#check 0 = 0 
#check 2*3 = 6 
#check len [] = 0 
#check len [1,2,3] = 3

/-
we read the above in the usual way: "0 = 0" is of type Prop, "2*3 = 6" is of type Prop, etc. 

you can think of Prop as the type of all logical claims that we might want to make in LEAN. in particular, everything we might want to prove in LEAN will be a Prop. every theorem, lemma, example, etc. (we'll see theorems and lemmas below). 

Prop does not include just true claims. it includes ALL (well-typed) claims: 
-/

#check 0 = 1 
#check 2*3 = 7 
#check len [] = 1
/- you may find it shocking that obviously false statements such as "0 = 1" are well-typed expressions in LEAN. but you shouldn't be shocked. "0 = 1" is just an expression. it is a logical statement which _claims_ that 0 is equal to 1. this statement may be true, but it may also be false. we don't know yet, until we try to prove it. but we can always claim something, even if we don't know how to prove it. after all, there are many open problems in mathematics. we can state them, but we cannot prove them yet. the beauty of LEAN and similar logics is that everything has a type, including logical statements like "A = B". 
-/

/- "true" and "false" are predefined statements of type Prop. you can think of "true" as "a statement which is true" and of "false" as "a statement which is false". they are like canonical representatives of truth and falsehood. 
-/
#check true     -- not to be confused with tt of type bool
#check false    -- not to be confused with ff of type bool 

#check tt 
#check ff 


-- some equality claims do not type-check, so are rejected:
#check 0 = "abc" -- not well-typed 

-- strange that this works, we don't like it:
#check 0 = []  -- how can a nat be compared to a list? i don't know why LEAN does this... 


---------------------------------------------------
-- EQUALITY
---------------------------------------------------

/-
the = symbol in LEAN is infix notation for equality. it turns out that equality is just a predefined function in LEAN, called _eq_: 
-/

#check eq 
#print eq 

/-
what is the type of eq? it is interesting that the two statements above output the type of eq in a different manner, but you can think of eq as a function that takes two elements x and y both of some type α and returns an element of type Prop. 

now we can understand better what we write when we write things like "0 = 0", and why this is of type Prop. 
-/

#check 0 = 0   -- this is syntactic sugar for "eq 0 0" 
#check eq 0 0  

#check len [1,2,3] = 3 
#check eq (len [1,2,3]) 3 
example: eq (len [1,2,3]) 3 := begin refl, end 

#check eq 0 1   -- this is perfectly well typed, even though it's a false claim 

#check eq "stro"  "abc" 


---------------------------------------------------
-- FOR-ALL PROPOSITIONS
---------------------------------------------------

/- equalities of the form "len [1,2,3] = 3" are "mini-specifications". they are examples of properties that we want our programs to have. sure, these are simple properties/specifications, for now. but they are specifications nevertheless. in this course we will learn to write more interesting specifications, for example, specifications involving forall quantifiers, ∀, like the one below: 
-/

#check ∀ x : ℕ, len [x] = 1 
#check forall x : nat, len [x] = 1 

/- these more interesting specifications are also of type Prop. in general, every claim that we write in LEAN (every statement that might be true or false) is a Prop. we will not give a complete formal description of the logic of LEAN (which is one of the most advanced/powerful logics out there). instead, following our learning-by-doing philosophy, we will give examples. 

but it should already be clear that the type Prop is much "larger" than the type bool. poor type bool only contains two elements, tt and ff. but type Prop contains many, many elements. in fact it contains infinitely many elements, since there's an infinite set of logical statements that we can write!
-/

def plus : nat -> nat -> nat 
  | x  nat.zero := x
  | x (nat.succ y) := nat.succ (plus x y)  


-- what general thing can we say about plus? for example, we can say that (plus 0 x) should return x. we write this formally as follows:

#check (forall x : nat, plus 0 x = x)

/- the property is the "(forall x : nat, plus 0 x = x)" (with or without the parentheses, which are not needed in this case). the #check part just tells us the type of this expression, which is Prop, as we said earlier. 

we can read the above statement in english as _"for any x of type nat, (plus 0 x) is equal to x"_. the "forall" is the so-called _universal quantifier_ in logic. we can also write it as unicode ∀ :
-/
#check (∀ x : nat, plus 0 x = x)

-- we can omit the type of x because LEAN can infer it from the fact that we pass it to plus, and plus takes two nats:
#check (forall x, plus 0 x = x)

-- but as we said earlier, in this class we will insist on not omitting the types. 


-- can you think of other specifications that we can write about plus?

-- here's some:

#check ∀ x : nat, plus x 0 = x
#check ∀ (x y : nat), plus x y = plus y x       -- this is called commutativity
#check ∀ (x y z : nat), plus (plus x y) z = plus x (plus y z)   -- associativity



-- all these are logical claims (Props). some of them are true, some not!

#check ∀ x y : ℕ, x + y = y + x 
#check ∀ x y : ℕ, plus x y = plus y x 

#check ∀ x y z : ℕ, (x + y) + z = x + (y + z)
#check ∀ x y z : ℕ, plus (plus x y) z = plus x (plus y z) 

#check ∀ x y : ℕ, x = y 
#check ∀ x y : ℕ, x * y = y * x 
#check ∀ a b : bool, a && b = b && a 
#check ∀ a : bool, a = tt 





@[derive decidable_eq]
inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

open weekday 

def next_workday : weekday → weekday 
    | sunday := monday
    | monday := tuesday
    | tuesday := wednesday
    | wednesday := thursday
    | thursday := friday
    | friday := monday
    | saturday := monday
--

/- you should start thinking about properties (specifications) of the programs you write. even simple functions like next_workday have some interesting properties. can you think of a property that next_workday has? just express the property in english for now. later we'll see how to formalize it (i.e., write it down in logic). 

-- ANSWER:






























- one property is "for any weekday d, (next_workday d) is never a saturday nor a sunday". 

- another property: for any input day x the output day should be different from x.  

-/


----------------------------------------------------
-- sorry
----------------------------------------------------

example: ∀ x : nat, len [x] = 1 := begin sorry, end -- sorry, don't know how to prove it yet



#check len [x] = 1   -- i cannot write this, what is x ? 


#check len [_] = 1  -- it's weird that this works ... 
-- but it's hard / impossible to use: 
example: len [_] = 1 := begin refl, end 



---------------------------------------------------
-- EXAMPLES, LEMMAS, THEOREMS
---------------------------------------------------

/- in LEAN, apart from "example", we can use "lemma" and "theorem" to write down propositions. the only difference is that "lemma" and "theorem" require the proposition to have a name / label. for instance:
-/
example: len (0 :: [1,2,3]) = 4 := begin refl, end 

lemma my_first_lemma: len (0 :: [1,2,3]) = 4 := begin refl, end 

theorem my_first_theorem: len (0 :: [1,2,3]) = 4 := begin refl, end 

example: ∀ x : nat, len [x] = 1 := begin sorry, end 
lemma cant_prove_this_yet: ∀ x : nat, len [x] = 1 := begin sorry, end 
theorem but_it_must_be_true: ∀ x : nat, len [x] = 1 := begin sorry, end 



lemma a_simple_lemma: 1 = 1 := begin refl, end 

theorem a_simple_theorem: 2 + 2 = 4 := begin refl, end 




---------------------------------------------------
-- A BRIEF NOTE ON THE EXISTS QUANTIFIER ∃ 
---------------------------------------------------
/-
like many logics (e.g., first-order logic), LEAN's logic includes not just the forall quantifier ∀, but also the _exists_ quantifier:
-/

#check exists x : bool, x = tt 
#check ∃ x : bool, x = tt 

/-
we will not have to use the ∃ quantifier in this class. in one of the homeworks we will see how to write a specification which one might initially think requires ∃ without using ∃. 

we will also later see how to write formally the so-called "drinker's paradox" which goes like this: "There is someone in the pub such that, if they are drinking milk, then everyone in the pub is drinking milk." in order to formalize the drinker's paradox you will need ∃. 
-/



---------------------------------------------------
-- PROPOSITIONS COMBINING FORALL, EXISTS, FUNCTIONS, etc
---------------------------------------------------

#check forall x : nat, exists y : nat, x = y + 1 

#check forall x : nat, exists y : nat, x = plus y 1 

#check ∀ x : nat, ∃ y : nat, plus x 1 = y 

#check ∀ x : nat, ∃ y : nat, y = plus x x 
#check ∀ x : nat, ∃ y : nat, x = plus y y   
  
#check ∀ x : nat, ∃ y : int, y = x   
#check ∀ x : nat, ∃ y : int, (x:int) + y = 0 








/-
    SPECIFICATION AND FORMAL SPECIFICATION

A set of properties like the ones above is called a _specification_. We usually use the term _property_ to mean one statement of type Prop, like for example, the property (∀ x : nat, plus x 0 = x). We usually use the term _specification_ (sometimes abbreviated _spec_) to mean more than one properties. But we can always construct a BIG property by taking the _conjunction_ (logical AND) of many properties, so the distinction between one or many is not essential. 

Specifications can be written in many languages. They can be written in English, for example. These are "informal" specifications. In this course we will write _formal_ specifications, that is, specifications written in logic. English is imprecise and can lead to miscommunication and catastrophic errors. Logic is precise and unambiguous.

Funny: all yes/no questions in English have the same answer: it depends. :)
-/

/- FORMAL VERIFICATION

Writing down a formal specification / property is one thing, and proving it is another. The fact that we believe that our program has some property, doesn't mean that our program indeed has that property. We need to check. We need to _verify_. This process is called _verification_, and in the case of proving formally that (formal) programs satisfy their formal specifications, it is called _formal verification_. Formal verification is what we are doing in this course. 
-/

/- FORMAL PROOFS

We have already done a bit of formal verification, by proving simple theorems with "example" and "refl". These were pretty trivial: they were just tests (but still useful, as we said, for example, for regression testing). We don't need the entire LEAN machinery to prove such simple examples, since we can just evaluate (compute) a function and compare its output to the expected result (the function still needs to be guaranteed to terminate though). 

We will now start getting a bit more serious about proving program correctness. Proving is partly a science and partly an art. It is a science because it is precisely, formally, and mathematically defined. But it is also an art because theorem proving is not always easy, and cannot always be automated. Human creativity is often needed. We will understand why this is unavoidable later in the course. 

Sometimes this theorem-proving creativity is beyond the grasp of most humans and requires the expertise, intuition, and talent of top mathematicians and computer scientists. But often this creativity is also something that can be taught, just like one can be taught to improvise, say, a jazz solo in a music class. This is what we aim to do in the rest of this course. 

Let us then begin to do more interesting formal verification, by proving more interesting properties. 
-/

/- to summarize:

  - specification = making claims about properties of programs
  - formal specification = making these claims in formal logic 

  - verification = checking that a program satisfies its properties (i.e., its specification)
  - formal verification = doing verification using formal methods, i.e., mathematically rigorous methods like theorem proving, model checking, etc. 

-/


