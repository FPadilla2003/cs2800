-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!



---------------------------------------------------
-- LOGISTICS
---------------------------------------------------

-- Is there anyone who has NOT JOINED PIAZZA?

-- Is there anyone who has NOT BEEN ABLE TO INSTALL LEAN?






-----------------------------------------------------------------
-- FUNCTIONAL PROGRAMMING WITH TYPES, IN LEAN, CONTINUED
-----------------------------------------------------------------

/- compared to the functional programming that you might have seen so far, programming in LEAN has two main differences. one is types. the other is termination of recursive function. we look at these two aspects in turn. we begin with types. 
-/

-----------------------------------------------------------------
-- TYPES
-----------------------------------------------------------------

/- LEAN's programming language is "typed". we have already briefly talked about types and seen #check:
-/

#check 0 -- LEAN tells us (see infoview window) that 0 is of type nat (or ℕ)
        -- in general, the notation "x : T" means "x is of type T"

-- #check can be used to show the type of any expression
#check (3 + 2*7) -- this expression is also of type nat 

/- what exactly is a "type"? you can think of a type as a set of values. for example, you can think of ℕ (nat) as the set of natural numbers: {0, 1, 2, ...}. this is the mathematical / set-theory view, and it will be enough for now. later we will talk a bit more about type theory and we'll see how types can be "constructed". for now, you can think of "0 : ℕ" (0 is of type nat) as saying that "the value 0 belongs to the set ℕ". 

in LEAN everything, and we mean EVERYTHING, has a type. to be more precise, every syntactically legal LEAN expression is of some type. types in LEAN are "first-class citizens", which means in particular that types also are of some type:
-/

#check nat  -- nat is of type "Type"
#check ℕ -- nat and ℕ are the same thing

-- if all types are of some type, does it mean that "Type" also has a type? let's find out! 
#check Type -- "Type" is of type "Type 1"
#check Type 1 -- "Type 1" is of type "Type 2"
#check Type 2 
#check Type 100 
/- the types of types (like Type, Type 1, Type 2, etc.) are sometimes called _sorts_. what are Type, Type 1, Type 2, etc.? think of them as a type _hierarchy_. for now that's all we need to know (for more, see the references on type theory, in our lecture notes). 

we will have more to say about types (among other things, they are important to the proper foundation of logic and math, and therefore everything!) but we will only discuss as much about them as we need for the purposes of this course. 
-/



-- functions also have types, as we saw earlier: 
def f (x : nat) : nat := x + 1 

#check f  -- f is a function from ℕ to ℕ. in other circles this is also called the "signature" of f. 
-- you can think of the type ℕ → ℕ as "the set of all functions from ℕ to ℕ"



/- ℕ → ℕ is a type. therefore we expect ℕ → ℕ to have itself a type. we can check which one:
-/ 
#check ℕ → ℕ    -- ℕ → ℕ is of type Type  
#check nat -> nat   -- nat -> nat is the same as ℕ → ℕ 
#check ℕ -> nat     -- same thing
#check ℕ → nat      -- same thing, etc. 




-- what about the predefined operators like +, *, etc?
#check +    -- doesn't work: + is not really a function, but a generic infix notation for an "add" operation


#check nat.add  -- nat.add is the predefined addition function on nats
-- NOTE: you might see a red squiggly line underlying the #check command above, indicating a possible error on that line. there is no error on the "#check nat.add" line. the error message from the "#check +" line somehow propagates here. this is a bug. ignore it. the red line under "#check nat.add" should disappear if you comment out the "#check +" line. 

#eval nat.add 2 3 



#check nat.sub -- subtraction
#check nat.mul -- multiplication
#check nat.div -- division

#eval nat.sub 3 2
#eval nat.sub 2 3
#eval nat.mul 3 2
#eval nat.div 3 2


/-
how can we know what functions +, *, etc correspond to?

we can't unless we start digging into the LEAN libraries, which we won't do. instead, we will re-define everything from scratch before proving things, so that we know exactly what functions we are proving things about. 
-/

#check ite   -- this shows the type of the function ite, which is "Π (c : Prop) [h : decidable c] {α : Sort u_1}, α → α → α". 
/-
you DON'T have to understand what this says! we will not talk much about type theory in this class. if you want to learn more, check the references to type theory in the lecture notes (https://course.ccs.neu.edu/cs2800f23/lecture-notes.pdf) where you can find pointers to books and online notes. in particular, the type system of LEAN is briefly described here: https://leanprover.github.io/theorem_proving_in_lean/dependent_type_theory.html (this is actually a nice description, accessible to your level). 
-/

#check int.add 







/-
PollEv: let's take a quiz!

go to link:

https://pollev.com/tripakis


-/

-------------------------------------------------------
/- 
Qz01a: in LEAN, 3 is 
- a value
- a type
- both a type and a value
- neither a type nor a value 
-/





/- 
Qz01b: in LEAN, nat is 
- a value
- a type
- both a type and a value
- neither a type nor a value 
-/



#eval ℕ -- we cannot #eval ℕ because it doesn't have a "representation" (essentially a pretty-printing)
#reduce ℕ  -- but we can #reduce ℕ: it reduces to itself. 







-----------------------------------------------------------------
-- FUNCTION TYPES ARE "CONTRACTS"
-----------------------------------------------------------------

-- types are input-output contracts:

#check f 

/- 
 the type of f is ℕ → ℕ (or nat -> nat), that is, naturals to naturals. this means that f takes as input a natural number, and returns as output also a natural number. the type of a function f (also called its "signature") can be seen as an input-output contract: it is the responsibility of the caller to call f with a natural number as argument. it is the responsibility of f to return a natural number as a result. 
-/



-----------------------------------------------------------------
-- TYPE ERRORS
-----------------------------------------------------------------

-- when type contracts are violated, we get type errors:


#check 0 
#eval f 0  -- all good

#check (-1:int)  -- (-1:int) is of type int
#eval f (-1:int) -- type error: f expects a nat, but we give it an int. the environment (the callers of f) has "broken" the contract. 


#check (1:int)
#eval f (1:int) -- type error, again, the fault is with the environment 


-- here function fg breaks the output contract, the fault is with fg 
def fg (x:nat) : nat := x-(20:int)  
#eval fg 18 


#eval f [1,2] -- type error 
-- the error message of LEAN is pretty understandable: it tells us that [1,2] 
-- is a list, but f expects a nat as input. we'll look more at lists later. 



#eval f (f 0)  -- all good, because (f 0) is guaranteed to be a nat, because of f's type 

#eval (f f) 0 

#eval f f 0  -- type error: this is parsed as (f f) 0, because function application is _left associative_ ("stacks to the left") 
#eval (f f)  -- type error: f is not of type nat, so it cannot be passed to f which expects a nat


/- type errors vs "well-typed" code 

LEAN's programming language is "strongly" typed. when programming in LEAN, we must be careful about types, and we must resolve any typing errors. other languages are more flexible about types.  LEAN has strong typing, meaning that typing errors are not tolerated. we (in this class) will not accept programs with type errors (in homeworks, exams, etc). 

when a LEAN expression does not give any type error, we will say that it is "well-typed". we will ask you in quizzes and homeworks to recognize whether a given expression is well-typed or not. you will be supposed to be able to do that on your own, without the help of LEAN. 

note that when we say "LEAN expression" we mean everything that we can write in LEAN! it may be a well-typed expression, or it may be rubbish. you should learn to recognize the two. 
-/

#check 2+3 
#check nat.add 2 3 
-- #check + 2 3 -- we get an error: why? 
-- #check (2 3) -- we get an error: why? 
-- #check 2 + -- interesting! we'll talk about this later 
-- #check + 2 -- we get an error: why? 

#check nat -> nat   -- "nat -> nat" is a well-typed LEAN expression, just like "2+3" is a well-typed LEAN expression 

#check nat nat  -- we get an error: why? 





-----------------------------------------------------------------
-- SOME BASIC TYPES IN LEAN
-----------------------------------------------------------------

/-
we can (and later will) define our own types in LEAN. for now, let's go over LEAN's basic predefined types:
-/

-- natural numbers:
#check 0 
#check 1
#check 22


-- we have negative integers, but we will not deal with them too much:
#eval -1 -- this fails
#eval (-1:int)
#check (-1:int) 
#check ((-1):int)


#check 103.5 -- weird! we will not deal much with non-integers
#eval 103.5 -- weird!


-- we have booleans:
#check tt -- boolean "true"
#check ff -- boolean "false"

#check true -- not the same as the bool tt 

-- we have strings:
#check "abc" 
#check "hello i love you" 



-- we have lists:

#check [] 
#check list.nil   -- [] and list.nil are equivalent notations for the empty list 

#check [1] 
#check list.cons 1 list.nil 
#check 1 :: list.nil 
#check 1 :: [] -- infix notation for list.cons 
#check list.cons 1 1 -- cryptic message, but 2nd argument of cons must be a list! 

#check 1 :: 2 :: 3 :: []  
#check 1 :: (2 :: (3 :: []))   

#eval list.cons 1 (list.cons 2 (list.cons 3 list.nil))   
#eval [1,2,3]   



#check [1,2,3]   
#eval list.cons 0 [1,2,3]   -- this should be similar to what you've seen already in lisp/scheme
#eval 0 :: [1,2,3]          -- infix notation for list.cons 

#check [1,2,3]  -- LEAN infers that this is a list of nats
#check ["hello","bye"] -- LEAN infers that this is a list of strings 
#check [ [1,2], [3,4,5], []  ]   -- a list of lists of nats 

#check [1,"hello"] -- this is allowed in some languages, but not in LEAN (at least not directly, without defining some sort of union/sum type); we will not worry about this 

#check [(-1:int),2,3]   




-----------------------------------------------------------------
-- POLYMORPHISM
-----------------------------------------------------------------

-- LEAN has a "polymorphic" type system:
#check list.nil -- this is the empty list: its type can be read as "list of something / list of some type"
#check []   -- same as list.nil 

-- we will not talk much about polymorphism, so you can ignore that for now
#eval 0 :: [] 
#check 0 :: []  -- this is a "list of nats" 

#check list.cons 



-----------------------------------------------------------------
-- TYPE INFERENCE 
-----------------------------------------------------------------

-- LEAN can sometimes infer the types in function definitions too:
def f5 (x : nat)    := x + 1  -- notice that we omitted the output type
#check f5  -- LEAN infers that the output type is nat 
#eval f5 10 

-- we could also have omitted both:
def f6 (x) := x+1 
#check f6  -- LEAN is still able to infer the types. how? not the topic of this course, but probably because 1 is by default a nat. 

def f7 (x) := x + (1:int) 
#check f7  -- now that we forced 1 to be an int, the inferred type changes

/- type inference doesn't always work, and sometimes it might result in unexpected results that don't necessarily capture the intention of the programmer. _in this course, we will insist on specifying the type of every function, including input and output._
-/


-----------------------------------------------------------------
-- FUNCTIONS WITH MORE THAN ONE INPUTS
-----------------------------------------------------------------

-- here's a function that takes as input two nats, x and y, and returns a nat:
def g (x y : nat) : nat := x+y 

-- we could also have written it equivalently like this:
def gg (x : nat) (y : nat) : nat  := x+y 

#eval g 2 3 
#eval (g 2)  3    
#check (g 2)  

#eval (g 2) 
#reduce (g 2) 


-- the type of g is interesting:
#check g -- you should see "g : ℕ → ℕ → ℕ"    
        -- adding the dropped parentheses, this is the same as: "g : ℕ → (ℕ → ℕ)"

#check gg 

-- indeed ℕ → ℕ → ℕ is the same as ℕ → (ℕ → ℕ):
#check ℕ → (ℕ → ℕ)     
#check ℕ → ℕ → ℕ 

/- 
what the def of g says is: "g is a function that takes as input a nat, and returns another function that takes as input another nat and returns a nat". 

you might object here that this doesn't make sense. how can g take as input just one nat, since we just defined it to take as input TWO nats?
but if you think about it a little bit, you will see that the two interpretations are equivalent:
-/
#eval (g 3 4)
#eval g 3 4 -- this is the same as (g 3) 4
#eval (g 3) 4 

#check (g 3)  -- just (g 3) is a legal expression! it's a function from ℕ to ℕ. sometimes this is called "partial evaluation" 
#check g 3  -- this works and is the same as the above. it should give "g 3 : ℕ → ℕ"

#eval (g 3) -- this doesn't work, because (g 3) is a function. we cannot "#eval" functions
#eval f    -- same problem
#eval g    -- same problem 

-- but we can #reduce functions:
#reduce (g 3)   -- don't worry about the λ stuff, we'll learn that later
#reduce f 
#reduce g 



#eval g 3 4 
#eval (g 3) 4 

#eval g (3 4)    -- ERROR !  why?  



#check (4,3) 


-- this doesn't work either:
#eval g (4,3) -- type error: (4,3) is a pair, of type ℕ × ℕ 
#check (4,3) 
/-
from your previous experience with math courses, you might expect that functions that take two arguments are functions over pairs, like 

    f : A × B → C

or more precisely:

    f : (A × B) → C 

where A × B is the cartesian product of A and B. we can also have this in LEAN, but for the most part, it is far more useful to define functions with many arguments in the way we did above. we will return to this point soon. 
-/

