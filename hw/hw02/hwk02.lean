-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2023, HOMEWORK 2

/-
This homework is done in groups. Doing the homework in groups does not mean you split the problems among members of the group. EVERY member of the group should try to do ALL problems. Then you meet and compare notes. Help each other. If you cannot solve a problem, ask your team mates, but only after you tried it yourself.

 * Groups should consist of 2-3 people.
 * Homework is submitted by only one person per group. Therefore make sure the person responsible for submitting actually does so. If that person forgets to submit, your team gets 0.
 * Submitting the homework: you will submit it on handins as per instructions provided. 
 * You must list the names of ALL group members below, using the given format. This way we can confirm group membership with the Canvas groups.  If you fail to follow these instructions, it costs us time and it will cost you points, so please read carefully.

The format should be: FirstName1 LastName1, FirstName2 LastName2, ...
For example:
Names of ALL group members: Aretha Franklin, Billy Holiday, Etta James

There will be a 10 pt penalty if your names do not follow this format.

Replace "..." below with the names as explained above.

Names of ALL group members: Felipe Padilla, Artur Efremenko
-/

/-
Technical instructions:
- Open this file in LEAN. Some of the lines in this file are very long. You can enable "wrap line" under "View -> Toggle Word Wrap" in VS Code, so that you don't have to scroll left-right to see the entire line. 
- Insert your solutions into this file where indicated (usually as "..."). Sometimes we require textual explanations. In that case insert your answer in LEAN comments like these. 
- Make sure the entire file is accepted by LEAN (no red underlines, except when we specifically allow it). In particular, there must be no "..." left in the code. If you don't finish all problems, comment the unfinished ones out. 
- Only add to the file. Do not remove or comment out anything pre-existing (except the ..., which you will replace with your answers).
- Unless otherwise stated, when asked to define a function, you must specify all the types (both inputs and outputs) in the signature of the function yourself, rather than letting LEAN infer the types. For example, you should define your function like that:
    def f (x : nat) : nat := x+1
  and not like that:
    def f (x : nat) := x+1
  or like that:
    def f := fun x, x+1
  It's always OK to use ℕ instead of nat, ℤ instead of int, → instead of ->, etc. 
- Unless otherwise stated, you are NOT allowed to use any "non-trivial" LEAN library functions that you discovered somehow. You can certainly use predefined operators like +, *, etc, constants like 0, 1, ..., the empty list [], ::, list.cons, etc. But for example, you are not allowed to use the predefined _append_ function or the predefined list.length function, etc.
- Feel free to define "helper functions" if you need them. A "helper function" is a function that you define and call from your "main" function / solution to the problem. 
- When done, save your file WITHOUT renaming it. 
-/


/- THIS HOMEWORK GOALS:

- learn how to write simple programs in LEAN
- learn the concept of types / input-output contracts
- learn how to call functions in LEAN: function application, "passing" arguments to functions, etc. 
- determine the type of a well-typed expression, in particular a given function
- determine (without the use of LEAN) whether a LEAN expression is well-typed or has a type error 
- learn how to write functions in LEAN without patterns and with patterns, including recursive functions, so that they "obviously" terminate

-/


/- HWK02-01:
Define the function "multiply" which takes two natural numbers and returns their product (multiplication). You can use LEAN's predefined "*" operator in your definition. 
Evaluate your function on a number of examples using #eval. 
Make sure you can write down the type of multiply without help from LEAN. 
-/
-- ANSWER:
def multiply (x y : nat) : nat := x * y
#eval multiply 4 5
#eval multiply 20 3
#eval multiply 73 92
#check multiply

/- HWK02-02:
Write down in the place of "..." the type of the function given below. 
NOTE: THINK and come up with the answer yourself, without using #check. Then you can confirm your answer using #check. In the exams you may not have access to LEAN. You will be expected to be able to read LEAN code and come up with the types of functions "manually".
-/
def f (b : bool) (x : nat) := if (b = tt) then (x:int) else (-x:int)
-- ANSWER:
-- The type of f is bool -> nat -> int
#check f



/- HWK02-03:
A bunch of LEAN expressions are given below, where f is the function defined above:

def f (b : bool) (x : nat) := if (b = tt) then (x:int) else (-x:int)

Partition these expressions into two groups: all well-typed expressions, and all non-well-typed expressions (i.e., expressions that result in type errors). 

NOTE: THINK and come up with the answer yourself, without using LEAN. Then you can confirm your answer using LEAN. In the exams you may not have access to LEAN. You will be expected to be able to read LEAN code and come up with the answer to questions like this "manually".
-/

/-

WELL-TYPED EXPRESSIONS:
#check (f tt 0)
#check ((f) (tt) (0))
#check (f tt 10) + 1
#check f tt
#check (f tt) 0
#check (f tt) (0)
#check f tt 0

TYPE ERRORS:
#check f 0 tt
#check f 0 
#check f (0 tt) 
#check (f 0) tt
#check (f 0) (tt)
#check (f 0 tt)
#check ((f) (0) (tt))
#check f (f 10 tt) tt 
#check f (f 10 ff) tt 
#check (f 10 tt) + 1
#check (f 10 ff) + 1
#check f (tt 0) 
#check f (f tt 10) 42 
#check (f ff) + 1
#check f (f ff 42) tt 

-/


/- HWK02-04:
for each of the types given below, define a function that has that type. we don't care what exactly the function returns, and whether or not it actually uses all its arguments. we only care that your functions have the specified types. 
-/
#check (nat -> int) -> (nat -> int)   -- define function f1
#check (nat -> int -> nat -> int)     -- define function f2
#check nat -> int -> (nat -> int)     -- define function f3
#check bool -> (nat -> (nat -> nat) -> nat)  -- define function f4

-- ANSWER:

def f1 (x : nat -> int) (y : nat) : int := (y : int)
#check f1 

def f2 (x : nat) (y : int) (z : nat) : int := (x : int)
#check f2 

def f3 (x : nat) (y : int) (z : nat) : int := (x : int)
#check f3 

def f4 (x : bool) (y : nat) (z : nat -> nat) : nat := (y : nat)
#check f4 


/- HWK02-05:
Define the function "factorial" which takes a nat x and computes x!, the factorial of x. Recall that x! = x * (x-1) * ... * 1 if x>0 and that 0! = 1. Define the function "from scratch" using only addition, multiplication and recursion (no other predefined LEAN operations).  
-/
-- ANSWER:
def factorial : ℕ → ℕ 
  | 0 := 1
  | (n+1) := (n+1) * (factorial(n))

#eval factorial(3)
#eval factorial(5)





/- HWK02-06:
Define the function "fib" which takes as input a nat n and returns as output the n-th Fibonacci number. Recall that the Fibonacci sequence is: 0, 1, 1, 2, 3, 5, 8, 13, ..., and that each number in the sequence is obtained by adding the previous two numbers in the sequence. So, (fib 0) = 0, (fib 1) = 1, (fib 2) = 0+1 = 1, (fib 3) = 1+1 = 2, etc. 
-/
-- ANSWER:
def fib : ℕ → ℕ 
   | 0 := 0
   | 1 := 1
   | (n+2) := fib(n+1) + fib(n)
#eval fib 0
#eval fib 1
#eval fib 2
#eval fib 3
#eval fib 4
#eval fib 5
#eval fib 6
#eval fib 7
#eval fib 8
#eval fib 9
#eval fib 10





/- HWK02-07:
Define a function called "diff_by_one" which takes two natural numbers x and y, and returns a bool, tt ("true") if either x = y+1 or y = x+1, and ff ("false") otherwise. 
NOTE: Do NOT use a logical OR operator (no "||", "or", "∨", etc). 
HINT: you can do it by using if-then-elses (possibly nested). 
CHALLENGE: try to do it without if-then-else, using pattern matching only (recursion is OK). 
Evaluate your function on a number of examples.
-/
-- ANSWER:
def diff_by_one (x y : nat) : bool :=
  if (x = y+1)
  then tt
  else if (y = x+1)
       then tt
       else ff

#eval diff_by_one 3 1
#eval diff_by_one 3 2
#eval diff_by_one 3 5
#eval diff_by_one 3 4






/- HWK02-08:
Define the function "divide" which takes two natural numbers x and y, and divides them, returning x/y. The result should be a nat. If y=0 your function should return 0. Otherwise it should return x/y rounded down, so that (divide 3 2) for example should return 1 and (divide 2 3) should return 0. Try not to use LEAN's predefined "/" operator (or equivalently nat.div) in your definition. We will take 4 points off for solutions that do that. If you don't use LEAN's predefined division, you will have to come up with a recursive definition of divide. This will create some challenges of convincing LEAN that your recursion is "obviously terminating". It is instructive to face and think how to overcome these challenges. As always, you can (and should in this problem) use a helper function. 

Evaluate your function on a number of examples.
-/
-- ANSWER:

def counter (x y : nat) : nat := 0

def divide : nat -> nat -> nat
  | 0 0 := 0
  | x 0 := 0
  | 0 y := 0
  | (x+1) (y+1) := x - divide x y



#eval divide 10 0
#eval divide 0 10 
#eval divide 1 1
#eval divide 1 2 
#eval divide 13 7 
#eval divide 21 7 
#eval divide 21 3
#eval divide 20 3
#eval divide 10 3





/- HWK02-09:

is this function terminating? if it is, is LEAN able to prove that it's terminating?

def sumallint : int -> int  
  | 0 := 0
  | n := n + (sumallint (n-1)) 

independently of the answers you gave in the two questions above, use the transformation trick we provided in class to transform the above function into a terminating function called sumallintbounded. 

-/
-- ANSWER:
/-
  I believe that it is not terminating as the function returns an error in its recursive nature.
-/

def sumallintbounded : int → nat → int
    | 0 _ := 0
    | n 0 := n
    | n (bound+1) := n + (sumallintbounded (n-1) bound)



/- HWK02-10:
Define the function "list1toN" which takes a nat n and returns the list [1,2,...,n]. For example, (list1toN 3) should return [1,2,3] and (list1toN 0) should return [].
-/
-- ANSWER:
def list1toN : nat -> list nat
  | 0 := []
  | (n+1) := (n+1) :: (list1toN(n)) -- 1,2,3 (3-2), (3-1), (3-0)

#eval list1toN 0 
#eval list1toN 13
#eval list1toN 5




/- HWK02-11:
Define the function "app" which takes as input two lists of nats and concatenates them, that is, appends the second after the first one. For example (app [1,2,3] [3,4,5]) should return [1,2,3,3,4,5]. Define the function recursively, and NOT using LEAN's library function "append".  
-/
-- ANSWER:
def app : list ℕ → list ℕ → list ℕ 
  | [] [] := []
  | [] (y :: T) := (y :: T)
  | (x :: L) [] := (x :: L)
  | (x :: L) (y :: T) := x :: (app L (y :: T))

#eval app [1,2,3] [4,5]



/- HWK02-12:

Define the function "zip" which takes as input two lists of nats and "zips" or "merges" them. For example (zip [1,2,3] [4,5,6]) should return [1,4,2,5,3,6]. (zip [1,2,3] []) and (zip [] [1,2,3]) should both return [1,2,3]. (zip [1,2,3,4] [5,6]) should return [1,5,2,6,3,4]. Etc. 
-/
-- ANSWER:
def zip : list ℕ → list ℕ → list ℕ 
  | [] [] := []
  | [] (y :: T) := (y :: T)
  | (x :: L) [] := (x :: L)
  | (x :: L) (y :: T) := x :: y :: (zip L T)

#eval zip [1,2,3] [4,5,6]
#eval zip [1,2,3,4] [5,6]
#eval zip [1,2,3] []
#eval zip [] [1,2,3]




/- HWK02-13:

Write the function f:

def f (b : bool) (x : nat) := if (b = tt) then (x:int) else (-x:int)

as an anonymous (lambda) function. f and your anonymous definition of it must be equivalent, meaning they should have the same type and also return the same result, for every input. 
-/
#check ... write the anonymous function here and make sure it has the type you want ... 




/- HWK02-14:
Define the function "apply" which takes as input a list of nats L = [x1,x2,...] and a function f : ℕ → ℕ, and returns the list L' = [(f x1), (f x2), ...], that is, it applies f to all the elements of L. 

Evaluate your function on a number of examples using the empty list [] and the list [0,1,2,3], and passing the second argument f the anonymous (lambda) functions that multiply their input by 3, and add 42 to their input. Also evaluate on the same lists where f is the Fibonacci function. 

Then define the function "apply2int" which is the same as "apply", except that its argument f has type ℕ → ℤ, and therefore its output list L' has type list ℤ. Observe what happens when you call "apply2int" with exactly the same arguments as in the examples we requested for "apply", above: do you get any type errors? Finally, use "apply2int" and the lambda function you defined in HWK02-13 to turn the list of nats [0,1,2,3] into the list of ints [0,-1,-2,-3] (this should be a single #eval call). 
-/
-- ANSWER:

def apply ... 

#eval apply [] ... 
#eval apply [] ... 
#eval apply [] ...  
#eval apply [0,1,2,3] ... 
#eval apply [0,1,2,3] ...
#eval apply [0,1,2,3] ...  


def apply2int ... 

#eval apply2int [] ... 
#eval apply2int [] ... 
#eval apply2int [0,1,2,3] ... 
#eval apply2int [0,1,2,3] ... 
#eval apply2int [] ... 
#eval apply2int [0,1,2,3] ... 


#eval apply2int [0,1,2,3] ...pass here the anonymous function from HWK02-13... 



/- HWK02-15:
Define the function "compose" that takes as input two functions f : ℕ → bool and g : bool → ℤ and composes them, yielding a function h : ℕ → ℤ such that (h x) = g (f x). 
Make sure you can write down the type of compose without help from LEAN. 
-/
-- ANSWER:

def compose ... 




/- HWK02-16:
The serial composition of two functions f : A → B and g : B → C, is the function f ∘ g : A → C, such that (f ∘ g) x = g (f x). 

Define the function _serialcompo_ which takes as input a list of functions L = [f1,f2,...], where each function fi is from ℕ to ℕ, and returns as output the serial composition f1 ∘ (f2 ∘ (f3 ∘ ...)). 
If the input list is empty, then _serialcompo_ should return the identity function (λ x : nat, x). If the input list has only one element f, then _serialcompo_ should return f. 

Evaluate your function on the examples given below:
-/
-- ANSWER:

def serialcompo ... 

#eval serialcompo [] 123 
#eval serialcompo [fib] 10 
#eval serialcompo [nat.mul 2, nat.add 0, fib] 10 





/- HWK02-17:
The parallel composition of two functions f : A → B and g : C → D, is the function f||g : (A × B) → (C × D), such that (f||g) (x,y) = (f x, f y). 

Define the function _parallelcompo_ which takes as input two functions f : ℕ → bool and g : ℤ → string, and returns as output the function f||g. 
-/
-- ANSWER:
def parallelcompo ... 



