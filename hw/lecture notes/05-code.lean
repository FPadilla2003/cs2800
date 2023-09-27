-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!


-- lecture code 2023-09-18



-----------------------------------------------------------------
-- FUNCTIONAL PROGRAMMING WITH TYPES, IN LEAN, CONTINUED
-----------------------------------------------------------------


-----------------------------------------------------------------
-- ANONYMOUS FUNCTIONS - LAMBDAS
-----------------------------------------------------------------

-- in all the examples so far, every function that we defined has
-- a name, like f, f13, f15, etc:
def f (x : nat) : nat := x+1
def f13 (x) := x+1 
def f15 : nat -> nat
    | x := x + 1

-- then we can call the function as follows:
#eval f 0
#eval f13 0
#eval (f (f13 0))
#eval (f (f13 11) + (f15 7))
-- "calling a function" is also called "function application".
-- we "apply" the function to a given argument. for example,
-- in (f 0) we apply f to 0. in (f (f13 0)) we apply f to (f13 0),
-- and we also apply f13 to 0. etc. 

/- 
it is often useful to be able to define functions without names, "anonymous functions" so to speak. why would we ever want to do that? this is useful, for example, when treating functions as "first-class citizens". for example, we might want to pass a function as an argument to another function. or a function might return a function as a result. we will see several examples of this later in this course. 

functions without names can be defined using "fun" or (unicode) λ (\lambda). you may encounter this under the term "lambda abstraction":
-/


#eval (fun x : ℕ, x+1) 0 -- "(fun x, x+1)" is the unamed/anonymous function that takes x as input and returns x+1 as output. NOTE: we didn't have to define anything, we just went ahead and evaluated this anonymous function applied to 0.  

#check (fun x : ℕ, x+1) -- we can check the type of an anonymous function

#eval (fun x, x+1) 0 -- sometimes we can omit types (but we don't want to do that in this course)
#check (fun x, x+1)  -- same as above: λ (x : ℕ), x + 1 : ℕ → ℕ 

#eval (fun (x:ℕ), (x+1 : ℕ)) 0 -- here we specify the types of both input and output, although the latter seems a bit redundant in this case, so we won't insist on specifying the types of the output in λ expressions 
#check (fun (x:ℕ), (x+1 : ℕ)) -- same as above: λ (x : ℕ), x + 1 : ℕ → ℕ

#eval (λ (x:ℕ), (x+1 : ℕ)) 17 -- "fun" can be replaced by λ 
#check λ (x:ℕ), x+1



-- anonymous functions can have multiple inputs:
#check (λ (x : ℕ) (b : bool), (if (b=tt) then x else 2*x) ) 


-- now that you know anonymous functions, you can read these:
def add3 (x y z : nat) : nat := x+y+z 

#reduce add3 1 2   -- what is (add3 1 2)? it's a function that takes a z and returns (3.add z), i.e., (3+z)

#reduce add3 1  -- what is (add3 1)? it's a function that takes a y and a z ... etc 



-----------------------------------------------------------------
-- FUNCTIONS ARE FIRST-CLASS CITIZENS
-----------------------------------------------------------------

/- functions in LEAN are not different from other objects. just like we can pass to a function a number, say 0 or 1, or a bool, say tt, we can also pass a function, provided that this is allowed by the input-output contract. let us illustrate this by example.

here's a function gg which takes as input a nat x and a function f : nat -> nat and returns as output (f x):
-/

def gg (x : ℕ) (f : ℕ → ℕ) : ℕ := f x 

-- what is the type of gg? let's ask LEAN:
#check gg -- LEAN says "gg : ℕ → (ℕ → ℕ) → ℕ", which means that gg takes something of type ℕ, and something of type "(ℕ → ℕ)", and returns something of type ℕ. this is as we would expect. the second input to gg, of type "(ℕ → ℕ)", is a function that takes a nat and returns a nat. gg can be called with any function that has this type, for example:

#eval gg 10 f -- f is the function we defined earlier
#eval gg 3 f 

#eval gg 10 (fun x : nat, x+3) 
#eval gg 10 (λ x, x+3) -- here we pass an anonymous function as input to gg 

#eval gg 10 f15 


def exponent : nat -> nat -> nat 
  | x 0 := 1 
  | x (e+1) := x * (exponent x e)


#eval gg 10 (exponent 2)  -- here we see an example of "partial evaluation". remember the function exponent that we defined above? what is its type?
#check exponent 
#check exponent 2 
#eval exponent 2 10 

-- we cannot pass "exponent" to gg, because "exponent" doesn't have the required type, ℕ → ℕ. indeed, if we try, we get a type error:
#eval gg 10 exponent -- type error

-- but we can pass "(exponent 2)". why? what is the type of "(exponent 2)"?
#check exponent 2 -- (exponent 2) is a function! it takes a nat n, and returns 2^n, another nat. 

#eval (gg 10) (exponent 2) 




-- which of these three types are the same?
#check nat -> bool -> nat 
#check nat -> (bool -> nat) 
#check (nat -> bool) -> nat
-- ANSWER: the first two types are the same, but the third one is different

-- can we find some functions that have the above types?


def h (f : nat -> bool) : nat :=
  if f 0 = tt then
    0
  else
    1
#check h 




-----------------------------------------------------------------
-- TYPES ARE FIRST-CLASS CITIZENS TOO
-----------------------------------------------------------------

-- g is a function that takes as input some type x and returns as output the same type x 
def g (x : Type) : Type := x 
#check g 
#check g nat 
#eval g nat  -- doesn't work, just like "#eval nat" doesn't work 
#reduce g nat 
#reduce g (list nat) 
#reduce g (nat -> bool)


-- what is the type of this function? 
def GH (x : Type) : Type := x → x 
#check GH 

-- what is the type of this function? 
def GL (x : Type) : Type := list x 
#check GL 


-- what is the type of GH nat?
#check GH nat 
-- what is the value of GH nat?
#reduce GH nat 


-- what is the type of GL nat?
#check GL nat 
-- what is the value of GL nat?
#reduce GL nat 





/-
again, we will not delve much into type theory. for more info, see the lecture notes or https://leanprover.github.io/theorem_proving_in_lean/dependent_type_theory.html

-/





---------------------------------------------------
-- TESTING AS PROVING
---------------------------------------------------
/-
there are two basic ways of checking the correctness of our programs: testing and proving. although this course focuses on proving, testing is very important too. moreover, (simple) testing can be seen as (simple) proving. we illustrate this and at the same time introduce the basic proof concepts in LEAN.
-/

----------------------------------------------------
-- reflexivity, refl
----------------------------------------------------

-- consider the len function that we defined earlier:
def len : list ℕ → ℕ 
    | [] := 0
    | (_ :: L) := 1 + (len L)

/- we want to test this function, to make sure that it works as intended. one way to do that is simply to evaluate the function on a bunch of inputs:
-/

#eval len [] 
#eval len [1] 
#eval len [13] 
#eval len [1,2] 
#eval len [1,2,3]
#eval len [1,1,1,2,22,0,0,0]

/- the problem with this testing approach is that it requires a human to check ("eyeball") the results. if we later change the code for some reason, we have to go over all our tests to make sure they are all still returning what they are supposed to return. a better way is to assert what we know the function _should_ return in each case. then, if later we change the function and introduce a bug, some of these assertions might fail automatically. in LEAN, we can use the "example" mechanism to do that. an "example" is actually a "mini-theorem" (in fact not so mini, since we can write arbitrary complicated logical statements inside an example), with a proof and all:
-/

example: len [] = 0 
:= begin
    reflexivity,  -- _reflexivity_ is a _tactic_ 
end

/-
yeah! we just did our first proof in this course! let's explain a bit what just went on. first, everything between "begin" and "end" is a _proof_. a proof will be essentially a sequence of "commands", that we call _tactics_. so a proof is essentially a program! 

now, place your cursor at the end of the "begin" above, and look at LEAN's "Infoview" window. you should see something called "Tactic state", which in this course we will also call _proof state_: it's the current state of our proof. at the end of "begin", i.e., at the beginning of the proof, the proof state should look like this:

1 goal
⊢ len list.nil = 0

LEAN tells us that we still have 1 goal to prove (sometimes we will "split" proofs into multiple goals, we'll see this later) and that this goal is to prove the equality "len list.nil = 0", without assuming anything. in general, the proof state will look like this:

h1 : ... some assumption here ... 
h2 : ... another assumption here ... 
... a bunch of more assumptions here ...
⊢ ... some goal here ... 

the assumptions are also called _hypotheses_. 

in our example we have no assumptions, so there is nothing above the ⊢ symbol (type "\entails" to generate this symbol - by the way, in VS Code you can hover your pointer on top of a symbol, and it tells you how to generate it).

now move your cursor at the next line of "begin" but _before_ the word "reflexivity". as you should see, the proof state doesn't change. 

now move your cursor at the end of the line "reflexivity,". the proof state should change. in fact, you should see 

goals accomplished

this is the moment every prover awaits: the proof is done, and we can close it with an "end"!

but how exactly did we accomplish this? we accomplished it with a sort of magic spell, which is this case was the command _reflexivity_. from now on we will call "magic spells" _tactics_.  _reflexivity_, also abbreviated _refl_, is our first and perhaps the most basic tactic. it applies to goals of the form A = A, that is, goals that state that a certain expression is identical to itself. that A = A is a basic axiom of equality (the axiom of reflexivity) and it's built into the logic of LEAN. 
-/


example: len [] = 0 := -- where you put the ":=" is a matter of taste
begin
    refl,  -- _refl_ is an abbreviation for _reflexivity_
end

/-
but wait! in the case of the example above, the goal is _not_ of the form A = A! it's "len list.nil = 0". the left-hand-side of that equality looks nothing like the right-hand-side. you are absolutely right, it doesn't. but reflexivity still works. the reason is that reflexivity actually does a bit more. it sometimes tries to simplify the two sides, to a point where they are identical. in this case, "simplify" means "compute" (or "reduce") the expression "len list.nil". indeed, this expression reduces to 0, and then reflexivity applies, to the simplified goal 0 = 0. we will say more about simplifications later. 
-/


-- if we really want to see what's going on, we can issue the _dunfold_ tactic prior to _refl_:

example: len [] = 0  := 
begin
    -- start issuing magic spells!
--    dunfold len,  -- not needed, but useful to illustrate what _reflexivity_ does under the hood  
    refl,  
end 


example: len [1,2,3] = 3  := 
begin
    -- comment / uncomment the things below to see what they do:
    -- dunfold len, -- interesting, why doesn't it simplify it more?  
    -- unfold len, -- wow!
    refl,  
end 

example: 0 = 0 := 
begin
    refl,  -- the goal is of the form A = A 
end




/-
one thing to note is the comma "," at the end of reflexivity. do we need this? in general we need it when we issue many tactics one after another. for the last tactic in the proof, we don't really need it, but adding it is useful. if you remove it, you have to switch to the next line (where the "end" is) to see "goals accomplished". as a stylistic convention, it's useful to add it even after the last tactic in the proof. 

admittedly, this proof was too simple. this is fine for now. we will see more complicated proofs soon. be patient. for now, we are not really doing proofs, we are really doing regression testing disguised as proofs. 
-/

-- note that these work outside proofs:
#reduce len list.nil 
#reduce len [1,2,3] 

-- but not inside proofs:
example: len [1,2,3] = 3  := 
begin
    -- #reduce [1,2,3],  -- don't use inside proof
    -- #reduce,          -- don't use inside proof
    -- #eval [1,2,3],    -- don't use inside proof
    -- #print nat,       -- don't use inside proof
    refl,  
end 






/-
if we claim something false, our proof doesn't go through:
-/

example: len [1,2,3] = 4 := begin refl, end  
example: len [1,1,1,2,22,0,0,0] = 10 := begin refl end



---------------------------------------------------
-- REGRESSION TESTING:
---------------------------------------------------

/-
our testing-as-proving approach is based on the above fact: we cannot prove false equalities! so, if we change the function and make a mistake, some tests may no longer pass:
-/

def len_bad : list ℕ → ℕ 
    | [] := 0
    | (_ :: L) := len_bad L -- bug!

-- now some of the test cases would fail (notice that some would still pass):
example: len_bad [] = 0 := begin refl, end             -- this test still passes
example: len_bad [1,2,3] = 3 := begin refl end         -- this test fails
example: len_bad [1,1,1,2,22,0,0,0] = 8 := begin refl end  -- this fails too



-- from now on, for every function we define, instead of testing it with #eval, we will test it with "example": 
example: len [1,2,3] = 3 := begin refl end
example: len [1,1,1,2,22,0,0,0] = 8 := begin refl end



