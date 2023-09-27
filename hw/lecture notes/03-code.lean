-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

---------------------------------------------------
-- LOGISTICS
---------------------------------------------------

-- Is there anyone who has NOT installed LEAN 3?

#eval lean.version -- this should give something like (3, (51, 1))

/-
there's an online version of LEAN 3 that you can use, while you're troubleshooting your installation (please go to office hours / contact our TAs):

https://leanprover-community.github.io/lean-web-editor/

the online solution is TEMPORARY and NOT permanent. the web version is very slow and unreliable. it won't work for your homeworks, exams, etc. you are expected to have LEAN installed on your own machines, so that you are not dependent on internet connections and the online LEAN server. let us know if you are still having trouble with your installation. 

(if you have installed LEAN 4 instead come and see me, we may be able to figure something "creative")
-/



-- Is there anyone who has NOT found homework teammates?







-----------------------------------------------------------------
-- FUNCTIONAL PROGRAMMING WITH TYPES, IN LEAN, CONTINUED
-----------------------------------------------------------------


-----------------------------------------------------------------
-- FUNCTIONS WITH MORE THAN ONE INPUTS, CONTINUED
-----------------------------------------------------------------

def g (x y : nat) : nat := x+y 
#check g 

/-
all these expressions denote the same type:
-/
#check nat -> nat -> nat 
#check nat -> (nat -> nat) 
#check (nat -> nat -> nat)
#check (nat -> (nat -> nat)) 
#check ℕ → ℕ → ℕ
#check ℕ → (ℕ → ℕ)     
#check (ℕ → ℕ → ℕ)
#check (ℕ → (ℕ → ℕ))


-- but these two types are DIFFERENT! HOW? can someone guess?
#check nat -> (nat -> nat) 
#check (nat -> nat) -> nat 

-- def g (x y : nat) : nat := x+y 

-- how to define a function that has type (nat -> nat) -> nat ?
def FF (x y : nat) : nat := 42 
#check FF 

def FF2 (f : nat -> nat) : nat := f 42 
#check FF2 




-- here's a function which mixes a few types:
def h (x : nat) (b : bool) : int := if (b = tt) then x else -x 
#check h -- h : ℕ → bool → ℤ   
#eval (h 3) tt 
#eval h 3 ff 

#reduce h 3 
#check (h 3) 

#check h 4 

#check h 4 tt 
#eval h 4 ff 
#check h tt -- type error, why? 


-- these four types are identical:
#check (nat -> (bool -> int))
#check nat -> (bool -> int) 
#check (nat -> bool -> int) 
#check nat -> bool -> int  

-- but this one is different:
#check (nat -> bool) -> int 


#check (nat bool -> int) -- wrong syntax




-- here's a function with 3 inputs:
def add3 (x : nat) (y : nat) (z : nat) : nat := x+y+z 
#check add3 

#check add3 3 
#check add3 3 4 
#check add3 3 4 5 
#eval add3 3 4 5 




-- another (equivalent) way to define add3:
def add3alt (x y z : nat) : nat := x+y+z 
#check add3alt 

-- in types, parentheses "stack to the right"
#check ℕ → (ℕ → (ℕ → ℕ))    
#check ℕ → ℕ → ℕ → ℕ      

-- in function application, parentheses "stack to the left"
#check add3 10 100 1000   
#check ((add3 10) 100) 1000   




-- here's a function with 3 inputs of different types:
def fgh (x : nat) (y : bool) (z : int) : string := "hello" 
#check fgh 

#check list.cons 
#check list.cons 1 (list.cons 2 []) 


-- REMEMBER: in types, parentheses implicitly "stack" to the right:
#check ℕ → bool → ℤ → string       -- this ... 
#check ℕ → (bool → (ℤ → string))   -- ... means this!


-- REMEMBER: in function applications, parentheses implicitly "stack" to the left:
#eval fgh 34 tt (-1)             -- this ... 
#eval ((fgh 34) tt) (-1)         -- ... means this! 





-- note: LEAN accepts this definition (although it probably shouldn't):
-- def h (x : nat) (b : bool) : int := if (b = tt) then x else -x 
def h2 (x : nat) (b : bool) : int :=  if (b) then x else -x 
#check h2 
/-
the difference with h is that here we say "if (b)" instead of "if (b = tt)". 

we don't like the definition of h2 because it uses implicit "casting" (also called _coercion_) of the bool b into a Prop. we will talk later about the difference between bool and Prop. for now, we want to stick to the pattern "(b = tt)", "(b = ff)", etc., in if-then-else conditions.  
-/



-- QUIZ TIME! respond at: https://pollev.com/tripakis


/- 
Qz02a: Is the definition given in class correct? (Correct means accepted by LEAN.)

def f : nat -> nat := x+1 
-/



-- def fff (x : nat -> nat) := x+1 



/-
Qz02b: What is "[1]" in LEAN?

1. list.nil 
2. list.cons 
3. list.nil 1 
4. list.cons list.nil 
5. list.cons 1 list.nil 
6. none of the above 
-/

#check list.cons 1 list.nil 





-----------------------------------------------------------------
-- PATTERN MATCHING
-----------------------------------------------------------------

-- we've defined this function above:
-- def f (x : nat) : nat := x + 1 

-- here's another way to define the same function:
def fpat : nat -> nat -- we start by giving the type/contract
    | x := x + 1    -- then we define the function by "pattern matching"
-- in this case pattern matching is trivial: we basically say
-- "let the input be x" (| x), "then the output is x+1" (:= x+1)

#eval fpat 10 
#check fpat 


-- recall g: 
-- def g (x y : nat) : nat := x+y 
-- let's redefine g by pattern matching:
def gpat : nat -> nat -> nat 
    | x y := x+y 

#eval gpat 4 3 
#check gpat 

-- ->  →   ℕ 

-- recall h:
-- def h (x : nat) (b : bool) : int := if (b = tt) then x else -x 
-- we can also redefine h by pattern matching:
def hpat : nat -> bool -> int 
    | x y := if (y = tt) then x else -x 
    -- does it matter that the second input is called "y" here instead of "b" above? no. 

#check hpat 
#eval hpat 4 tt 
#eval hpat 4 ff 

/-
the above pattern matching examples are simple because there's only one pattern so there's not a lot of "matching" to be done. we will see more interesting pattern matching later. a first example is below: we can rewrite hpat by getting rid of the if-then-else and replacing it with two cases, one where the bool argument is tt, and the other when it is ff:
-/

def hpatbis : nat -> bool -> int 
    | x tt := x 
    | x ff := -x 




---------------------------------------------------
-- PRODUCT TYPES AND CURRYING
---------------------------------------------------

-- earlier we saw how functions taking multiple arguments have types of the form A → B → C → ... there's another way to pass multiple arguments to a function, namely by passing pairs, triples, etc. this is like we're used to in math, where we write f(x,y), g(x,y,z), etc. for this, we need to use so-called "product types". we will not deal with such types almost at all, but we illustrate them briefly by example. 


#check h

#eval h 0 tt 
#eval (h 13 ff) 

/-
def hpatbis : nat -> bool -> int 
    | x tt := x 
    | x ff := -x 

-/
-- let's define another version of function h above using a product type and pattern matching:
def hprod : (ℕ × bool) → int 
    | (x, tt) := x
    | (x, ff) := -x 

-- def h (x : nat) (b : bool) : int := if (b = tt) then x else -x 

def hprodwithoutpm (p : (ℕ × bool) ) : int := 
  if (p.snd = tt) then p.fst else -p.fst  

#eval  hprodwithoutpm  (3,tt) 
#eval  hprodwithoutpm  (3, ff ) 


#check hprod -- hprod : (ℕ × bool) → ℤ
#check hpatbis 

#eval hprod (3, tt) 
#eval hprod (3,ff)

-- compare to calling h:
#eval hpatbis 3 ff  -- this seems simpler: we don't need parentheses, comma

-- NOTE: h and hprod are NOT the same function. they have different types. 
-- indeed, we cannot call them in the same way:
#eval h (3,tt) -- type error
#eval hprod 3 tt -- type error


-- NOTE: product types and pattern matching are independent concepts. we could very well have defined h using pattern matching also: 
def h3 : ℕ → bool → ℤ 
    | x tt := x 
    | x ff := -x 

#check h3 -- same type as h

-- and we can also define hprod WITHOUT using pattern matching. how? we need to be able to access the first and second elements of a pair. we can do this using .fst and .snd: 

---------------------------------------------------
-- .fst and .snd for extracting elements from pairs
---------------------------------------------------

#eval (1,2).fst 
#eval (1,2).snd
#eval (1, (2,3)).snd.fst 
#eval (1,2,3).fst
#eval (1,2,3).snd
#eval (1,2,3).snd.fst
#eval (1,2,3).snd.snd


-- now, we can define hprod without pattern matching as follows: 
def hprod2 (p : nat × bool) : int := if (p.snd = tt) then p.fst else -p.fst 

-- def h (x : nat) (b : bool) : int := if (b = tt) then x else -x 



/- let's suppose we wish to define another version of addition that takes a product type:

def addprod : ℕ × ℕ → ℕ 

how can we access the numbers x and y in a given pair (x,y)?

this doesn't work:
-/
def addprodfail ((x,y) : ℕ × ℕ) : ℕ := x+y 

-- we can define it using pattern matching:
def addprodpat : ℕ × ℕ → ℕ 
    | (x,y) := x+y 

-- we can also define it like this:
def addprod (x : ℕ × ℕ) : ℕ := x.fst + x.snd  

#eval addprod (3, 4) 


def addprod3 (x : ℕ × ℕ × ℕ   ) : ℕ := x.fst + x.snd.fst + x.snd.snd 
#check addprod3 
#eval addprod3 (1,2,3) 
#eval addprod3 (1, (2, 3))  

-- as we can see, for programming, pairs and triples seem less convenient than just passing the arguments one after the other. moreover, the latter way allows also for not passing all the arguments, which is useful for partial evaluation (we saw an example of that last week). so, as it turns out, taking a function of type A × B → C and turning into a function of type A → B → C is beneficial as the function becomes more convenient to use. this is called "currying" (not from the Indian dishes, and not from the basketball player, but from Haskell Curry: https://en.wikipedia.org/wiki/Haskell_Curry). 





-----------------------------------------------------------------
-- RECURSION
-----------------------------------------------------------------

-- all the functions we defined so far are pretty simple, in the sense that they do not make use of perhaps the most powerful mechanism in programming: repetition. in imperative programming (C, Java, etc) repetition is achieved mainly using loops, like "while" and "for". in functional programming, it is achieved by _recursion_: a function calling itself. you have already seen recursive functions in your earlier courses. let us now look at how these are defined in LEAN:

-- here's a function that computes the sum 0+1+...+n for given nat n:
def sumall : ℕ → ℕ 
    | 0 := 0
    | (n+1) := (n+1) + (sumall n) -- recursive call


/-
this is a more interesting case of pattern matching, with a recursive 2nd case. what this is saying is the following:
    - if the input is 0 ("| 0") then output 0 (":= 0")
    - otherwise, if the input is n+1, then output (n+1) + (sumall n)

(i believe in your previous courses you called this "data-driven definition"?)
-/

#eval sumall 0 
#eval sumall 1 
#eval sumall 2 
#eval sumall 4 
#check sumall 


-- now, we might be tempted to define the same function without using pattern matching:
def sumall2 (n : ℕ) : ℕ := if (n = 0) then 0 else n + (sumall2 (n-1)) 

-- we see error "unknown identifier 'sumall2'"
-- what's going on? aren't the two definitions equivalent? in a sense yes, they are. but LEAN only accepts recursive definitions using the pattern-matching way of defining them. for non-recursive definitions, we can use both pattern-matching and ":=", but for recursive definitions, we must use pattern-matching. 

