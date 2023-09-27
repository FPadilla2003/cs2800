-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!


-- lecture code 2023-09-20

---------------------------------------------------
-- BOOL
---------------------------------------------------

-- "bool" (Booleans) is a predefined type that contains only two elements, "tt" ("true") and "ff" ("false"). we can see how bool is defined using #print:
#check bool 
#print bool -- you don't need to understand everything that this is saying, we'll come back to discuss type constructors later. 
#check tt 
#check bool.tt -- same as tt
#eval if (tt = bool.tt) then 0 else 1 
#check ff 
#check bool.ff -- same as ff


-- NOTE: "true" and "false" are _not_ the same as "tt" and "ff":
#check true
#check false 
#eval if (tt = true) then 0 else 1 -- the fact that this works is misleading. ignore it and don't use it. it shouldn't work, because tt is of type bool, whereas true is of type Prop. LEAN is being too lenient :)  we won't be. 


/- we will return to discuss type constructors and Prop later. for now, let's focus on the definition of bool: it tells us that the data type bool has two elements (or more precisely _constructors_),  namely tt (or bool.tt) and ff (or bool.ff). then, every time we define a function taking a bool as input, we can define that function by doing pattern-matching on the two possible cases for each bool argument: it can be either tt or ff. 
-/

-- for example, let's define the Boolean negation function:
def negb : bool → bool
    | tt := ff -- if the input is tt, return ff
    | ff := tt -- if the input is ff, return tt

#eval negb tt 
#eval negb ff 
#print bool 
#eval bool.tt 
#eval tt 
#check bool.tt 
#check tt 
#check ff 
#check bool.ff 



---------------------------------------
-- A LITTLE BIT OF SPECIFICATION
---------------------------------------

/-
"specification" refers to the process of specifying (i.e., defining) correctness (or other properties) of software (or other systems). 

in the case of a simple function like negb, we can specify it "exhaustively" by testing: since there's only two possible inputs, we can specify what the output should be in each of these two cases:
-/

-- specification by exhaustive testing:
example: negb tt = ff := begin refl, end    
example: negb ff = tt := begin refl, end    

/-
the above two tests are sufficient to _specify_ negb, because they exhaustively cover all possible inputs to negb. specification of functions like negb is possible via testing because the number of possible inputs to negb is finite. this is not always the case (e.g., think of a function on nats). 

we will talk more about formal specification later, but we can already get a glimpse of it here. one property that boolean negation has is that if you apply it twice you get the same result. we can write this as a formal specification using the ∀ ("forall") quantifier:

    forall x : bool, negb (negb x) = x 

or, using ∀ instead of "forall"

    ∀ x : bool, negb (negb x) = x 

forall-specifications are useful because they are not confined to booleans. we can write things like ∀ x : nat, ..., or ∀ L : list nat, ..., etc. we will later return to this type of specifications and learn how to prove them. 

for now, we can prove forall specifications on booleans by exhaustive testing, by enumerating all possibilities and proving each one of them using "example:" and "refl". for the above specification, this gives the following:
-/

example: negb (negb tt) = tt := begin refl, end 
example: negb (negb ff) = ff := begin refl, end 




-------------------------------------------------------
-- PROVING THINGS ABOUT BOOLS BY EXHAUSTIVE TESTING
-------------------------------------------------------


-- here's another way to define negb: 
def negbbis (b : bool) : bool := if (b = tt) then ff else tt 


/-
can we _prove_, using the methods that we have defined so far, that negb and negbbis are equivalent? two functions are equivalent if for any given input, they both return the same output when run on that input. 

in general, we cannot prove that two functions are equivalent using testing, because in general the number of possible inputs is infinite. 

but in the case of negb and negbbis, there's only two possible inputs!
those are tt and ff. because there's only two inputs, we can exhaustively test them:
-/


example: negb tt = negbbis tt := begin refl, end    -- test 1
example: negb ff = negbbis ff := begin refl, end    -- test 2 


-- this shows us a bit what's going on under the hood:
example: negb tt = negbbis tt 
:= begin 
  dunfold negb,
  dunfold negbbis,
  refl, 
end 


---------------------------------------------------
-- MORE ON PATTERN MATCHING, BOOLEAN CONJUNCTION 
---------------------------------------------------

/- 
what if we want to define Boolean AND (_conjunction_), which takes two bools as input arguments? we can do this simply by exhausting all possible cases (like in a _truth table_):
-/
def andb : bool → bool → bool
    | tt tt := tt 
    | tt ff := ff
    | ff tt := ff
    | ff ff := ff

-- we can exhaustively test andb:
example: andb tt tt = tt := begin refl, end 
example: andb tt ff = ff := begin refl, end 
example: andb ff tt = ff := begin refl, end 
example: andb ff ff = ff := begin refl, end 



-- what if we forget a case? LEAN complains:
def andb_incomplete : bool → bool → bool
    | tt tt := tt 
    | tt ff := ff
    | ff ff := ff

-- what if we repeat a case redundantly? LEAN complains:
def andb_redundant : bool → bool → bool
    | tt tt := tt 
    | tt ff := ff
    | ff tt := ff
    | tt tt := tt 
    | ff ff := ff

-- what if we repeat a case but define a different output? LEAN complains:
def andb_ambiguous : bool → bool → bool
    | tt tt := tt 
    | tt ff := ff
    | ff tt := ff
    | tt tt := ff  
    | ff ff := ff


-- here's another (correct) way to define andb:
def andbbis : bool → bool → bool 
    | ff _ := ff 
    | tt ff := ff 
    | tt tt := tt 

-- and another:
def andanother : bool -> bool -> bool 
    | tt tt := tt 
    | _ _ := ff 

#eval andanother ff tt 
#eval andanother tt ff 
#eval andanother ff ff 
#eval andanother tt tt  

-- and yet another:
def andsome : bool -> bool -> bool 
    | ff _ := ff 
    | tt x := x 





def andb2 : bool → bool → bool 
  | ff _ := ff 
  | _ ff := ff 
  | tt tt := tt 

def andb3 : bool → bool → bool 
  | tt tt := tt 
  | _ _ := ff 

def andb4 : bool → bool → bool 
  | ff _ := ff 
  | tt y := y 

example:  andb4 ff ff = ff := begin refl, end 
example:  andb4 ff tt = ff := begin refl, end 
example:  andb4 tt ff = ff := begin refl, end 
example:  andb4 tt tt = tt := begin refl, end 

example:  andb4 ff ff = andb ff ff := begin refl, end 
example:  andb4 ff tt = andb ff tt := begin refl, end 
example:  andb4 tt ff = andb tt ff := begin refl, end 
example:  andb4 tt tt = andb tt tt := begin 
  dunfold andb4,
  dunfold andb,
  refl, 
end 


def andb6 (x y : bool) : bool := 
  if (x = tt) then y else ff 


  
/- 
mini-quiz (ungraded): 

can we use the exhaustive testing method (_example:_) to prove that all these definitions are equivalent? how? how many tests will we need?
-/

-- for example, let's do it to show that andsome is equivalent to andb:

example: andsome tt tt = andb tt tt := begin refl, end 
example: andsome tt ff = andb tt ff := begin refl, end 
example: andsome ff tt = andb ff tt := begin refl, end 
example: andsome ff ff = andb ff ff := begin refl, end 



-- boolean implication ("if a then b"):
def ifb : bool → bool → bool 
    | tt tt := tt
    | tt ff := ff 
    | ff tt := tt 
    | ff ff := tt 

def ifbbis: bool -> bool -> bool 
    | tt tt := tt 
    | tt ff := ff 
    | ff _ := tt 








/- A STUDENT WONDERS: 

how exactly does reflexivity work? reflexivity relies on the axiom of logic that the equality relation = is _reflexive_, meaning that x = x, for any x. 

we are not going to worry about _how exactly_ reflexivity is _implemented_ in LEAN. we will only learn to use it. we will learn _what_ it does, not _how_ it does it. 

here's some examples of other cases where reflexivity applies. we will see more of those later, and for now, ignore the rest ("forall", "intro", etc). only focus on what happens to the proof state right before and right after issuing reflexivity:
-/

example: [1,2,3] = [1,2,3] := begin 
    refl,  
end 

example: forall x : nat, x = x := begin 
    intro, -- check the proof state here
    refl,  -- and here 
end 

example: forall L : list nat, L = L := begin 
    intro, -- check the proof state here
    refl,  -- and here 
end 

example: forall f : nat -> nat, f = f := begin 
    intro, -- check the proof state here
    refl,  -- and here 
end 

example: forall x : nat, 2*x+1 = 2*x+1 := begin 
    intro, -- check the proof state here
    refl,  -- and here 
end 

example: 2*10+1 = 21 := begin refl, end  -- refl does some arithmetic 

example: forall x : nat, 1+x+1 = x+2
:= begin
    intro,
    refl, -- but refl cannot do too much arithmetic!
end




---------------------------------------------------
-- A NOTE ABOUT PERFORMANCE
---------------------------------------------------

/-
program performance is of course critical to computer programming. but we will not worry much about it in this class. in particular, you will _never_ lose points in this class because your implementation of something is "inefficient". in this class we primarily care about correctness, not about efficiency. 

no matter what the function and its inputs are, we expect examples/tests to be discharged/proved just by using refl. this happens most of the times, but for some "large" examples, LEAN may timeout:
-/

def exponent : ℕ → ℕ → ℕ  
    | _ nat.zero  := 1
    | x (nat.succ n) := x * (exponent x n) 

example: exponent 2 5 = 32 := begin refl, end 

example: exponent 2 10 = 1024 := begin refl, end  -- takes some time, see the yellow bars to the left 

-- sometimes we might see "timeout". this is ok. it just means that LEAN ran out of steam. we can try smaller inputs. 
-- example: exponent 2 12 = 4096 := begin refl, end  -- this times out on my laptop 

-- #reduce exponent 2 14 -- #reduce is not very fast 

#eval exponent 2 100 -- #eval is much faster (because it bypasses the LEAN kernel, which is an "unsafe" thing to do)

/-
one reason why we don't care much about performance in this class is this: checking the proof of a theorem does not need to happen very often. in fact, in principle, it only needs to happen once! once a proof is checked to be correct (and assuming the proof checker is also correct) it doesn't have to be checked again, ever. this is very different from other kinds of programs, which need to run again and again, possibly on the same inputs. for such programs, we worry about performance a lot, because we need to run them all the time. for proof checkers, we worry less. still, this is only half of the story. we may not run the proof checker on the _same_ proof again and again, but we may still run it on many _different_ proofs. we want the proof checker to be efficient if we have many proofs to check. but in this course we are not going to worry about implementation and performance of proof checkers. 
-/
