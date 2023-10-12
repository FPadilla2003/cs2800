-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!


-- lecture code 2023-09-27




-- so that we don't have to define some functions that we use constantly, we put them in a separate file that we can "import" here: 
import ..hw04.mylibrary09

-- control-clicking on the names below, vscode takes you to the file mylibrary09.lean where they are defined
#check plus
#check len 
#check negb 
#check andb 
#check orb 
#check weekday
#check next_workday



--------------------------------------------------------------
-- MORE SPECIFICATIONS, INTRO TO LOGIC, LOGICAL CONNECTIVES
--------------------------------------------------------------

/- so far our specifications have been pretty simple: either examples/tests, or simple forall specifications of the form "∀ (x y ...), f1 x y ... = f2 x y ...". 

let's write some more sophisticated specifications. we won't be able to prove those yet, but we should get use to be able to write more complicated logic statements. in the process, we introduce the basic logic connectives: implication, conjunction, disjunction, negation, and so on. 
-/

-- recall our weekday example (it's in mylibrary09.lean):
#check weekday
#check next_workday
open weekday

/- remember the property that we stated about this function? "for any weekday d, (next_workday d) is never a saturday nor a sunday". how can we express this? there is actually several different ways to write this formally:
-/
#check ∀ d : weekday, next_workday d ≠ saturday
#check ∀ d : weekday, next_workday d ≠ sunday

-- A ≠ B ("A not equals B", or "A different from B") is actually the same as not (A = B):

-- these two are identical:
#check ∀ d : weekday, not (next_workday d = saturday) 
#check ∀ d : weekday, ¬ (next_workday d = saturday) 



--------------------------
-- NEGATION: not ¬ 
--------------------------


#check not 

#check not (1 = 2) 
#check not 1 = 2   -- type error, LEAN tries to read this as (not 1) = 2

#check ¬ (1 = 2) -- same as not (1 = 2) 
#check 1 ≠ 2     -- same as not (1 = 2), we'll see why later 


theorem next_workday_not_saturday: 
  ∀ d : weekday, next_workday d ≠ saturday 
:= begin
  sorry,
end

-- same thing, written with ASCII characters:
theorem nxtwkdaynotsaturday: 
  forall x : weekday, not (next_workday x = saturday) 
:= begin
  sorry,
end



-- notice that negation on Props (not) is _not_ the same as negation on bools!
#check not  -- this works on Props
#check not true 
#check not false 
#check not ([1] = [2]) 

#check negb -- our negation on bools 
#check bnot -- LEAN's negation on bools (should be equivalent to our negb, we'll prove it later)
#eval bnot tt 
#eval bnot ff 

#check not tt  -- ARGH! COERCIONS! TO BE AVOIDED AT ALL COSTS!




------------------------------
-- CONJUNCTION: and, ∧ , /\ 
------------------------------
/- above, we wrote two separate theorems for our property that (next_workday d) never falls on the weekend. what if we wanted to combine the two? we can use _conjunction_ (logical _AND_). 
-/

#check and 
#check and true false 
#eval and true false -- nothing to print ... 
#reduce and true false -- ... except the Prop itself 

#check ∀ d : weekday, and (next_workday d ≠ saturday) (next_workday d ≠ sunday)

-- infix notation for conjunction: ∧ or /\ 
#check ∀ d : weekday,  (next_workday d ≠ sunday)    ∧    (next_workday d ≠ saturday) 
#check ∀ d : weekday,  (next_workday d ≠ sunday)   /\   (next_workday d ≠ saturday) 

-- parentheses can be dropped in this case:
#check ∀ d : weekday, next_workday d ≠ saturday ∧ next_workday d ≠ sunday



theorem next_workday_not_weekend: 
    ∀ d : weekday, next_workday d ≠ saturday ∧ next_workday d ≠ sunday 
:= begin
    sorry,
end



-- mini-quiz: can you think of another way to write the same spec? (with another logical connective instead of and)






























/- there is another way, and that's to just list all possible days of the week, except the weekend: "the next workday is either a monday, or a tuesday, or a wed...". but how do we say "or"? we use _disjunction_ (logical _OR_). 
-/

-----------------------------
-- DISJUNCTION: or, ∨, \/ 
-----------------------------

#check or 

#check ∀ d : weekday, or (next_workday d = monday) (next_workday d = tuesday) 

-- infix notation for disjunction: ∨ or \/
#check ∀ d : weekday, (next_workday d = monday) ∨ (next_workday d = tuesday)
#check ∀ d : weekday, (next_workday d = monday) \/ (next_workday d = tuesday)

-- parentheses can be dropped in this case:
#check ∀ d : weekday, next_workday d = monday ∨ next_workday d = tuesday

-- the joys of infix notations:
#check ∀ d : weekday, next_workday d = monday ∨ 
                      next_workday d = tuesday ∨ 
                      next_workday d = wednesday ∨ 
                      next_workday d = thursday ∨ 
                      next_workday d = friday


theorem next_workday_is_a_5day_weekday: ∀ d : weekday, 
    next_workday d = monday ∨ 
    next_workday d = tuesday ∨ 
    next_workday d = wednesday ∨ 
    next_workday d = thursday ∨ 
    next_workday d = friday 
:= begin
    sorry,
end




--------------------------------
-- IMPLICATION: implies, ->, → 
--------------------------------

#check implies 

#check ∀ x : nat, implies (x = 0) (not (x=1))


/-
as it turns out (and for good reasons, which we will discuss later) the implication symbol is the same "right arrow" -> or → as the one we use for functions:
-/

#check forall x : nat, x = 0 -> (not (x=1)) 
#check ∀ x : nat, x = 0 → x ≠ 1


-- consider the predefined LEAN division operator on nats:

#eval 4/2 
#eval 4/3 
#eval 3/4 
#eval 2/0 -- a nat divided by 0 yields 0. let's say we don't like that. 


-- let's say we want to define our own function, called "mydivide", which returns -1 when a division by 0 is attempted:
def mydivide (x y : int) : int := if (y = 0) then -1 else x/y 
#check mydivide 

#eval mydivide 2 0 


-- now suppose we want to state the property that mydivide is "almost equivalent" to LEAN's /, specifically, that it behaves like "/", provided that the denominator (2nd argument) is not zero. how to write that? we use logical _implication_:

#check ∀ x y : int, (y ≠ 0) -> (mydivide x y = x/y)

#check ∀ x y : int, implies (y ≠ 0) (mydivide x y = x/y)   
--                             A               B 
--                             A     implies   B
--                             A        ->     B
--                             A        →      B


/- ENGLISH AND IMPLICATION

"A only if B"    =     A -> B
"B if A"         =     A -> B
"A if B"         =     B -> A
"if A then B"    =     A -> B

"A if and only if B"    =   A <-> B  =  A -> B and B -> A 

-/





-- DO NOT CONFUSE THESE TWO: the "if then else" function is different from implies !
#check ite  -- the "if then else" function returns a value, like a nat, a list, a string, etc
#check implies -- implies returns a proposition, i.e. a Prop 





--------------------------------------------------------
-- LOGICAL EQUIVALENCE: iff (if and only if), <->, ↔ 
--------------------------------------------------------

#check iff 
#check forall p : Prop, p <-> p 
#check ∀ p : Prop, p ↔ p 




--------------------------------------------------------
-- EXCLUSIVE OR: xor  
--------------------------------------------------------

#check xor  
#check forall p : Prop, xor p (not p)

#check ∀ p : Prop, p ⊕ p -- doesn't work, use xor 




----------------------------------------------------
-- LOGIC
----------------------------------------------------
/-
our course is called "logic and computation". you have probably already seen basic logic (propositional logic) previously. in this course we will go further. in fact we have already used more advanced logic statements, with the "for all" quantifier ∀. we also talked briefly about the difference between propositional ("quantifier-free") logic, first-order logic, higher-order logic, and dependent type theory (LEAN). 

logic is important, because it is a precise and formal language, which allows little to no ambiguity. it is therefore the perfect medium to express statements that we want to make about the programs that we write: what does it mean for our program to be correct? what exactly is the "specification" of our program? we can write this spec in english, but that's often inadequate. english (or any other natural language) is not precise enough, and its ambiguities can lead to miscommunication and ultimately errors. 

before returning to proving logical statements with LEAN, let's do a quick review of some basic concepts in logic, starting with propositional logic. 
-/


/-



READ SLIDES: 09-propositional-logic.pdf


-/


