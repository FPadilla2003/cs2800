-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- this is a comment


/-
this is also a comment

it's a multiple line comment.

it's 
a 
multiple 
line 
comment.

-/






-----------------------------------------------------------------
-- FUNCTIONAL PROGRAMMING WITH TYPES, IN LEAN
-----------------------------------------------------------------
/-
    In your previous programming courses you have already seen functional programming (in Racket, Scheme, Lisp, ...).   But you may have not seen types. Types can be seen as "input-output contracts" between a program (a function f) and its environment (the functions that call f).  Types are useful because they allow the compiler to catch at compile-time many errors that would otherwise need to be caught at run-time. 

    Let's see a few examples of functional programs in LEAN, and how these use types.

    First, we begin with some basic LEAN commands:
    #eval
    #reduce
    #check

-/

-------------------------------------------------------------------
-- BASIC EXPRESSIONS, PREDEFINED OPERATORS, #eval, #reduce, #check
-------------------------------------------------------------------

-- first let's see some basic expressions and predefined operations in LEAN:

-- addition:
#eval 2+3  -- #eval is a "compute" command
#reduce 2+3 -- #reduce is another compute command; we won't worry about the difference between #eval and #reduce for now

-- subtraction:
#eval 3-2  

#eval 2-3 -- weird! subtraction defined over natural numbers
#eval 2-300 
#check 2-3 


#eval (2:int)-(3:int) -- by default, "2" is a nat, but "(2:int)" is an int

-- how do we know? we can use #check, which gives the type of an expression:

#check 2 

/- UNICODE CHARACTERS

what is this "ℕ" symbol? it means the same as "nat", the type of natural numbers. in LEAN we can also use unicode characters, in addition to ASCII. 

how to type ℕ? type "\nat". in general, hover over a symbol in VScode, it tells you how to type it. 
-/

#check (2+3) 
#check (2-3)

#eval 2 - 3
#check 2 - 3

#eval nat.sub 2 3 
 
#check (2:int) 
#check (2:int) - 3  
#check 3 


#eval (2:int) - (3 : int) 
#eval (2:int) - 3 
#eval 2 - (3 : int) 
#eval ((2-3):int) 


-- multiplication:
#eval 2*3  


-- division:
#eval 4/2 
#eval 4/3 -- integer division!
#eval 2/3 -- integer division!
#check 2/3



-- if-then-else
#eval ( if (1 = 1) then (10*2) else 1 )  
#eval ite (0 = 1) (10*2) 1 -- if-then-else is actually the ternary function "ite"
#eval if (0 = 1) then (0+2) else (1+13) 
#eval ite (0 = 1) 2 14 

#eval if (0 = 0) then 10 else 20 
#eval ite (0 = 1) 10 (ite (0 = 10) 10 (20+10))




#eval bla -- bla is undefined, we get an error message
#check bla -- bla is undefined, we get an error message




-----------------------------------------------------------------
-- FUNCTIONS
-----------------------------------------------------------------


def f (x : nat) : nat := x + 1 
-- function f takes x of type nat and returns a result also of type nat; the result is x + 1

-- ℕ ℤ →  

-- nat and ℕ are the same, so we could have defined f also as:
def f2 (x : ℕ) : ℕ := x+1
def f3 (x : nat) : ℕ := x+1
def f4 (x : ℕ) : nat := x+1 


-- all these functions have the same type
#check f  
#check f2 
#check f3
#check f4 


/-
 in fact, f, f2, f3, f4 are _equivalent_ meaning that they return the same output given the same input. we shall be able to prove this formally later in this course. for now, we can convince ourselves that these functions return the same thing by doing a bit of testing, i.e., evaluating them on a few inputs:
-/


-----------------------------------------------------------------
-- FUNCTION APPLICATION ("calling" functions)
-----------------------------------------------------------------


#eval (f 0)  -- (f 0) is function application (instead of f(0) we write (f 0))
#eval f 0  -- often parentheses are not needed
#eval f(0) -- this also works, but not necessary
#reduce f 130  -- we will see the difference between #eval and #reduce later 

#eval f2 0
#eval f3 0
#eval f4 0 



-- omitting parentheses is fine, except when they are needed to change the priority of operations:

def d (x : nat) : nat := 2*x  
#eval (d 2)  
#eval d 2 + 3    -- function application has higher priority than + so this is (d 2) + 3
#eval (d 2) + 3 
#eval d (2+3)    



-----------------------------------------------------------------
-- WHY FUNCTIONAL PROGRAMMING INSTEAD OF IMPERATIVE PROGRAMMING?
-----------------------------------------------------------------
/- 
brief discussion: why are we using a functional programming language in this course?

 answer:
 mainly because it's easier. it's easier to explain verification and proofs using a functional programming language, because the latter is closer to standard math than an imperative language, say C or Java. also, functional programming languages like LEAN's don't have some "hacky" features like pointers, memory allocation, side effects, etc, which make things complicated. having said that, reasoning about imperative code is both necessary and interesting. time permitting, we will touch upon this towards the end of the semester. 
-/



