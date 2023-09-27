-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!




---------------------------------------------------
-- LOGISTICS
---------------------------------------------------

-- homework02 has been released on canvas: you will submit it as a group on handins

-- Is there anyone who has NOT installed LEAN 3?

-- Is there anyone who has NOT found homework teammates?




/-
GENERAL NOTE:
 the lecture code that i post on canvas has sometimes stuff that we didn't get to cover during the lecture. you are supposed to read _everything_ in the lecture code files posted on canvas. if you don't understand something, ask us. 
-/




-----------------------------------------------------------------
-- FUNCTIONAL PROGRAMMING WITH TYPES, IN LEAN, CONTINUED
-----------------------------------------------------------------


-----------------------------------------------------------------
-- RECURSION, CONTINUED
-----------------------------------------------------------------

-- we defined this recursive function:
def sumall : ℕ → ℕ 
    | 0 := 0
    | (n+1) := (n+1) + (sumall n) -- recursive call


-- and we said that this doesn't work; for recursive functions we need pattern matching:
def sumall2 (n : ℕ) : ℕ := if (n = 0) then 0 else n + (sumall2 (n-1)) 


-----------------------------------------------------------------
-- A WORD ABOUT TERMINATION 
-----------------------------------------------------------------
-- maybe we can "cheat" LEAN into accepting this definition:
def sumall3 : ℕ → ℕ 
    | n := if (n = 0) then 0 else n + (sumall3 (n-1)) 

/- 
why doesn't LEAN accept this? we used pattern-matching, so what's the problem? well, the problem is that even though this definition uses patter-matching, it is really the same as the one for sumall2. and the problem with both these definitions is that they are not "obviously terminating". we will have a lot more to say about termination later in the course. it's one of the main topics of this course. 

for now, compare the definition of sumall3 with that of sumall. you will see that sumall is more "obviously terminating" than sumall3. first, because sumall's pattern-matching contains explicitly the base case n = 0. in sumall3, this is not the case: LEAN has to infer that from the structure of the if-then-else. this is too complicated for LEAN to do (as we will learn later, this is in fact an undecidable problem in general, so generally impossible to solve by an algorithm). 

second, sumall goes from (n+1) to n in the recursive call, whereas sumall3 goes from n to (n-1). now this might not look like a big difference, but as we will see later, it is. (n+1) is the same as (nat.succ n) which refers to the constructor for nats (we'll see what this is later). whereas (n-1) refers to the subtraction function for nats. what if n is 0? then n-1 is also 0, so nothing decreases here. 

to make a long story short, in your recursive definitions, use pattern-matching and break the definition into multiple cases, starting from the simple, base cases, with no recursive calls, and then adding cases with recursive calls, where at least one argument to the recursive call is getting "smaller" (like n is smaller than (n+1) in the definition of exponent above). 
-/


-- for the same reasons explained above, LEAN does not accept the definition below:
def sumall4 : ℕ → ℕ 
    | 0 := 0
    | x := x + (sumall4 (x-1)) 



-- _can we define non-terminating functions in LEAN?_ no we cannot. there are good reasons why we don't allow this, which we will explain later. for now, notice that this is not accepted:
def nonterminating : ℕ → ℕ 
    | 0 := 1 
    | (n+1) := n + (nonterminating (n+1))



-- is this terminating? 
/-
def sumall5 : int -> int  
  | 0 := 0
  | n := n + (sumall5 (n-1)) 
-/

/-

question: _what if i define a function which is obviously terminating to me, but LEAN does not accept it? will i lose points in the homeworks? in the exams?_ 

answer: we expect you to give us valid LEAN code (without errors) unless we explicitly ask for something that has errors (for exercise purposes). if you think that your function is terminating, but LEAN cannot figure it out, you can _transform_ your function into a terminating function using the trick that we will show you below. then, your code should be free of errors. if indeed your (original, prior to transformation) function is terminating, you will not lose points. if your function is not terminating, you will lose points. 

this transformation also allows you to continue your work, and to be able to call this function from other functions, etc. 
-/



------------------------------------------------------------------------------------------
-- TRANSFORMING A NON-TERMINATING FUNCTION INTO A TERMINATING ONE SO THAT LEAN ACCEPTS IT
------------------------------------------------------------------------------------------

/- we illustrate the transformation by example. you should be able to generalize to other examples. we will transform the function _nonterminating_ above so that it terminates. 

def nonterminating : ℕ → ℕ 
    | 0 := 1 
    | (n+1) := n + (nonterminating (n+1))

the idea is to add a _bound_ as an extra argument (a nat). the caller of the function is now forced to provide a bound on the max number of recursive calls: 
-/

def nonterminatingbounded : ℕ → ℕ → ℕ   -- the bound is the 2nd argument
    | 0 _ := 1 -- the first case of the original function is not recursive, so we leave it as it was (the _ means "i don't care what the value of the second argument is")
    | (n+1) 0 := 42  -- when the second argument (the bound) reaches 0, we MUST terminate. we can choose to return anything we want (something that makes sense for the function we are trying to define). here we chose 42 ... 
    | (n+1) (bound+1) := n + (nonterminatingbounded (n+1) bound)   -- at every recursive call, bound decreases by 1, so termination is guaranteed and "obvious" for LEAN to figure out

#eval nonterminatingbounded 10 100 




---------------------------------------------------
-- EXPONENT
---------------------------------------------------

def exponent : nat -> nat -> nat 
  | x 0 := 1 
  | x (e+1) := x * (exponent x e)

#eval exponent 2 10 
#eval exponent 0 10 
#eval exponent 10 0 
#eval exponent 0 0 




-- notice that in the first case of the pattern-matching: "| x 0 := 1", we don't use the "x" anywhere in the result. in such a case, we can leave this argument anonymous, or "un-named":
def exponent_ : ℕ → ℕ → ℕ 
    | _ 0 := 1
    | x (n+1) := x * (exponent_ x n)
#eval exponent_ 2 10
#eval exponent_ 2 100
#eval exponent_ 2 1000 
#eval exponent_ 0 0  





---------------------------------------------------
-- MORE ON PATTERN MATCHING
---------------------------------------------------

-- sometimes LEAN doesn't complain about overlapping cases that give different results:
def badchoice : ℕ → ℕ 
    | 0 := 0
    | 1 := 1
    | 2 := 2
    | (x+1) := badchoice x  -- this overlaps with case "1" if x=0 and with case "2" if x=1 

#eval badchoice 0
#eval badchoice 1
#eval badchoice 2
#eval badchoice 3
#eval badchoice 4
-- in this class we will insist on _not_ having overlapping cases. try to define your functions such as cases are mutually-exclusive (i.e., non-overlapping) and complete, in order to avoid any ambiguities. here's for example one way to fix the above:
    
def goodchoice : ℕ → ℕ 
    | 0 := 0
    | 1 := 1
    | 2 := 2
    | (x+3) := goodchoice x  -- no overlap with any of the base cases



/-
note that there are limits to the pattern matching that LEAN allows. 
for example, we might be tempted to try this:
-/

def even : ℕ → bool    -- a function that checks whether a given nat is even or odd 
    | (2*n) := tt       -- if the input is of the form 2*n then it's even
    | (2*n+1) := ff     -- if the input is of the form 2*n+1 then it's odd 

-- writing it this way doesn't help either:
def evenbis : ℕ → bool    
    | (n*2) := tt       
    | (n*2+1) := ff     

/-
the reason why the above don't work will become more clear when we explain inductive data types. we will get a glimpse of these soon, but first let's look at recursion on lists: 
-/



-----------------------------------------------------------------
-- RECURSION ON LISTS
-----------------------------------------------------------------

-- let's look at another example of recursion, this time on lists:
def len : list ℕ → ℕ 
    | [] := 0
    | (x :: L) := 1 + (len L)


#eval len [] 
#eval len [1,2,3]
#eval len [1,1,1]


/- the above definition of len can be read as follows, line by line:
def len : list ℕ → ℕ          READ: len is a function that takes a list of nat and returns a nat
    | [] := 0                  READ: if the input list is empty, return 0
    | (x :: L) := 1 + (len L)  READ: if the input list is of the form (x :: L) then return 1+(len L)
-/


-- since we are not using "x" in the pattern above, we can omit it and replace it with "_":
def len2 : list ℕ → ℕ 
    | [] := 0
    | (_ :: L) := 1 + len2 L 

#eval len2 [1,2,3] 







-----------------------------------------------------------------
-- A BRIEF PREVIEW OF INDUCTIVE DATA TYPES 
-----------------------------------------------------------------

-- we will see how to define our own so-called inductive data types later, and we will also (re)define natural numbers and functions on those. 
-- as a preview, we can see how natural numbers are already defined in LEAN:
#check nat 
#print nat -- this says that natural numbers can be "constructed" in two ways:
/-  
- nat.zero is a (constructor that returns a) natural number
- nat.succ is a constructor that takes a natural number, and returns a new natural number 
-/
#check nat.zero  -- 0 is shorthand notation for nat.zero 
#check nat.succ nat.zero -- 1 is shorthand for )nat.succ nat.zero)
#check nat.succ (nat.succ nat.zero) -- and so on 



#check nat.succ (nat.succ (nat.succ (nat.succ 0)))  -- "1.succ.succ.succ" looks weird, but it's the same as 4 


-- "+1" is the same as nat.succ, so when we write (n+1) in our recursive case definitions, what we really mean is (nat.succ n):


def sumallnat : nat -> nat 
    | nat.zero := nat.zero 
    | (nat.succ n) := (nat.succ n) + (sumallnat n)   


/- 
this hopefully makes it clearer why LEAN finds it easy to accept that the above definition is terminating. you can think of LEAN as "reasoning" like this:
  - i know what to return in the base case where the input is the simplest possible natural number, namely nat.zero
  - if the input is a natural number other than nat.zero, then it can only be of the form (nat.succ n), because that's the only other constructor for natural numbers
  - so in that second case, i have to call myself recursively with n instead of (nat.succ n) as the second argument
  - since n is a strictly "smaller" / "simpler" natural number than (nat.succ n), eventually i will "hit" the simplest natural number, which is nat.zero, so eventually the process will terminate. 
-/

def exponentagain : ℕ → ℕ → ℕ  
    | x nat.zero  := 1
    | x (nat.succ n) := x * (exponentagain x n) 


#eval exponentagain 2 10 
#reduce exponentagain 2  
#check exponentagain 2  



-- and what we really say when we define goodchoice is this:
def goodchoicebis : ℕ → ℕ 
    | nat.zero := 0
    | (nat.succ nat.zero) := 1
    | (nat.succ (nat.succ nat.zero)) := 2
    | (nat.succ (nat.succ (nat.succ x))) := goodchoicebis x  




/-
this hopefully also makes it clear why (2*n) and (2*n+1) are not acceptable patterns by LEAN. LEAN has no way to "deconstruct" a nat m into 2*n or 2*n+1, although it is easy to "deconstruct" m into either 0 (i.e., nat.zero) or (n+1) (i.e., nat.succ n). 
-/



-- what's wrong with the definition of missingcases?
def missingcases : nat -> nat 
    | nat.zero := 0
    | (nat.succ nat.zero) := 1
    | (nat.succ (nat.succ nat.zero)) := 2 
    | (nat.succ 3) := missingcases 2




/- what about the list data type?
-/

-- we already saw examples of lists: 
#eval 0 :: [] 
#eval 0 :: (1 :: []) 
#eval list.cons 0 (list.cons 1 list.nil) 
#eval [1,2,3,4,5,6,7]

-- the type "list ℕ" can be seen as denoting "a list whose elements are all natural numbers"
#check list ℕ 
#check list string
#check [1,2,3]
#check ["hi","bye"]
-- [] denotes the empty list (the list with no elements, and length 0)
-- [] is actually notation for list.nil:
#check list.nil -- ignore "?M_1" for now, it means the empty list is polymorphic

-- [1,2,3] is also notation for this:
#check list.cons 1 (list.cons 2 (list.cons 3 []))

-- arguably, [1,2,3] is much easier to write, but it's good to know where it comes from:

#check list 
#print list -- ignore the weird Π for now 

-- another equivalent notation is this:
#check 1 :: (2 :: (3 :: []))  -- so "::" is infix notation for list.cons 


-- just like with pattern matching on nats, pattern matching on lists is also based on the inductive data type definition of lists. so what we really wrote when we defined len above is this:
def lenbis : list ℕ → ℕ 
    | list.nil := 0
    | (list.cons x L) := 1 + (lenbis L)


def len3 : list nat -> nat 
  | list.nil := 0 
  | (list.cons _ L) := 1 + (len3 L) 


def mylen : list nat -> nat 
  | [] := 0 
  | [x] := 1 
  | (x :: (y :: L)) := 2 + (mylen L) 

#eval mylen [1,2,3]
#eval mylen [1,2,3,4,4,5,6] 



def mylen2 : list nat -> nat 
  | list.nil := 0 
  | (x :: []) := 1 
  | (x :: (y :: L)) := 2 + (mylen2 L) 



def mylen3 : list nat -> nat 
  | list.nil := 0 
  | (list.cons x list.nil) := 1 
  | (x :: (y :: L)) := 2 + (mylen3 L) 






/- CONCLUSIONS (FOR NOW) ABOUT DEFINING RECURSIVE FUNCTIONS:

we will talk more about termination later in the course. for now, just stick to this recipe for defining recursive functions over nats and lists of nats:

RECIPE:
    1. use the pattern matching style
    2. for recursion on nats, use 0 as the base case, and (x+1), (n+1), (x+2), etc, for recursive cases
    3. for recursion on lists, use [] as the base case, and (x :: L), (x :: (y :: L)), etc, for recursive cases
    4. if you need more than one base cases, that's OK, e.g., you can use 0 and 1 as two distinct base cases
    5. (if you follow steps 1-4 above, you should not need to use this 5th option) if LEAN complains about termination, but you believe that your function is terminating, use the bounding transformation described earlier  

this recipe should be pretty much the same as the "data-driven definitions" style you learned in fundies 1?
-/

