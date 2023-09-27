-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!


-- lecture code 2023-09-21



---------------------------------------------------
-- DEFINING OUR OWN (INDUCTIVE DATA) TYPES
---------------------------------------------------

/-
"Algorithms + Data Structures = Programs" is a 1976 book written by Niklaus Wirth, a famous computer scientist who among other things created the Pascal programming language. we have already defined many programs, but have we defined any data structures? not really. we have been using the basic predefined data types of LEAN, like nat, bool, and list nat. these can only take us so far. sometimes we need more elaborate data structures. sometimes we need more complex data types. although we will not focus on this topic in this course, let us still gain some basic understanding on how to define our own data types in LEAN. 
-/

-- Defining our own types, and function definitions on those by case matching:

-- as an example, let's define a new type called "weekday": 
@[derive decidable_eq]  -- you can ignore this. it can be omitted but then LEAN has problems with expressions like  ( ite (sunday = monday)  0  1 )
inductive weekday : Type
    | sunday : weekday
    | monday : weekday
    | tuesday : weekday
    | wednesday : weekday
    | thursday : weekday
    | friday : weekday
    | saturday : weekday

#check weekday -- weekday is indeed a type 
#print weekday -- weekday has 7 "constructors" 

-- recall the predefined type bool:
#print bool -- bool has 2 constructors 
#print nat -- nat also has 2 constructors 

-- we can check the type of the new elements we just defined:
#check weekday.friday -- friday is the best day!
-- we cannot #eval them:
#eval weekday.friday
-- but we can #reduce them (in fact they don't reduce to anything else but themselves):
#reduce weekday.friday



-- let's define a function on the newly defined type:
def next_workday_too_much_typing : weekday → weekday 
    | weekday.sunday := weekday.monday
    | weekday.monday := weekday.tuesday
    | weekday.tuesday := weekday.wednesday
    | weekday.wednesday := weekday.thursday
    | weekday.thursday := weekday.friday
    | weekday.friday := weekday.monday
    | weekday.saturday := weekday.monday

open weekday -- so that we can write just "sunday" instead of "weekday.sunday" 

def next_workday : weekday → weekday 
    | sunday := monday
    | monday := tuesday
    | tuesday := wednesday
    | wednesday := thursday
    | thursday := friday
    | friday := monday
    | saturday := monday

example: next_workday friday = monday := begin refl, end
example: next_workday saturday = monday := begin refl, end
example: next_workday (next_workday monday) = wednesday := begin refl, end




#check monday 
#check weekday.monday 

#check if (monday = sunday) then 0 else 1   -- this doesn't type check unless we add the "@[derive decidable_eq]" in the type 


---------------------------------------------------
-- RE-DEFINING THE NAT DATA TYPE
---------------------------------------------------

-- now let's look at a more interesting definition of an inductive data type (by the way, why are these called "inductive"? because they are strongly related to "induction", a fundamental proof technique that we will see later). 
-- let's re-define the natural numbers:
-- (for a similar treatment with Coq, see https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#lab31)

inductive mynat : Type   -- we give it the name "mynat" because "nat" is taken
    | Z : mynat 
    | S : mynat -> mynat 


/- what does the above definition do? it provides a step-by-step method to "construct" natural numbers. this is part of the "constructive" philosophy in mathematics and computer science. the method is: you can construct a mynat in two ways (and only those two ways):
  - either by calling the constructor mynat.Z
  - or, if you already have constructed another mynat, say x, by calling (mynat.S x)
-/

#check mynat.Z -- just Z here doesn't work

#check mynat.Z -- 0
#check mynat.S (mynat.Z) -- 1
#check mynat.S (mynat.S mynat.Z) -- 2  
-- etc ...

-- continuing this way ad infinitum, we can construct all the mynats! 


open mynat -- this allows us to omit "mynat." 


#check Z -- zero
#check S Z -- one
#check S (S Z) -- two



#check S S Z -- notice that this doesn't work. why?
#check (S S) Z -- type error 



/- FINITE and INFINITE types

the types bool and weekday are _finite_: we can only construct a finite number of elements of these types: only 2 elements for bool, and only 7 elements for weekday. 

in contrast, the types nat and mynat are _infinite_ types: we can construct infinitely many nats, by applying nat.succ again and again. similarly we can construct infinitely many mynats by applying mynat.S again and again. 
-/

-- NOTE: the constructors of a newly defined data type must return that type:

inductive bla : Type 
    | bli : bla 
    | blu : bla → nat   -- constructor blu is invalid, because it returns a nat! it should return a bla

-- but this is ok: 
inductive bla : Type 
    | bli : bla 
    | blu : bla → bla 
    | ble : ℕ → ℤ → bool → bla 
    | blo : ℕ → bla → bla → int → bla 

#check bla.bli 
#check bla.blu bla.bli 
#check bla.blu (bla.blu bla.bli )
#check bla.blu (bla.blu (bla.blu bla.bli )) 

#check bla.ble 3 (-5) ff 




inductive ble : Type 
  | foo : ble  
  | toto : bool -> ble 
/-
  | fifi : nat -> ble 
  | fofo : nat -> ble 
  | bar : nat -> ble -> ble 
  | foobar : ble -> bool -> string -> ble -> ble 
-/

open ble 
/-
#check fifi 13 
#check fifi 0 
#check fifi 1 
#check fifi 100 

#reduce fifi 100 
#reduce fifi 10 
-/

#check foo 
#check (toto ff) 
#check (toto tt)  

inductive boundednat : Type
  | one : boundednat 
  | two : boundednat 
  | three : boundednat 


/- ON THE MEANING OF CONSTRUCTORS:

inductive data type constructors like nat.succ, mynat.S, bla.blu, etc, are like functions, but they are not exactly the same thing. in particular, functions have a "body" definition, where we define exactly how the return value is going to be computed. but constructors don't have that. so how do constructors work? what do they return exactly?

constructors don't "return" anything in the standard sense. the constructor expression _itself_ is the result. you can think of (nat.succ nat.zero) as "returning" (nat.succ nat.zero) itself. (nat.succ nat.zero) is a nat, so it has the right type. 

what is the meaning of things like ble.foo, (ble.toto tt), etc? their meaning is whatever meaning we want to give them. the types bla and ble above are meaningless really, they are just for illustration. but boundednat could mean to us the set of three nats {1,2,3}. and mynat means the set of nats. (S (S (S Z))) means 3. the romans wrote 3 as III. in binary, 3 is written as 11. so there's different ways to write 3. as a mynat, (S (S (S Z))) "means" 3. 
-/

---------------------------------------------------
-- DEFINING BASIC ARITHMETIC OPERATIONS ON mynats:
---------------------------------------------------

-- addition on mynat :
def myplus: mynat -> mynat -> mynat 
  | mynat.Z y := y 
  | (S x) y := S (myplus x y)    -- (x+1) + y  =  (x+y) + 1  
--  | (mynat.S x) y := (myplus x (S y))     -- (x+1) + y  =  x + (y+1)   


#check myplus 


#reduce myplus Z Z 
#reduce myplus (S Z) (S Z)  
#reduce myplus (S (S (S Z)))  (S (S (S (S Z))))

example: myplus Z Z = Z := begin refl, end 
example: myplus Z (S Z) = S Z := begin refl, end 
example: myplus (S Z) Z = S Z := begin refl, end 
example: myplus (S Z) (S Z) = S (S Z) := begin refl, end 
example: myplus (S (S (S Z)))  (S (S (S (S Z)))) = S (S (S (S (S (S (S Z)))))) := begin refl, end 




/- this is great, but mynats are unreadable. so we will continue by defining functions on nats. we will re-define the well-known operations like addition and multiplication on nats, so that we can reason about them. notice that we know how nats are defined. we can see that using #print:
-/

#print nat 

/- in fact, if we use something called a "namespace" we can redefine exactly the same type ourselves:
-/
namespace nat_playground
-- every name defined between here and "end nat_playground" is prefixed by "nat_playground." now we can re-define the type "nat" (i.e., "nat_playground.nat")  without worrying that it will clash with the predefined type nat:

inductive nat : Type 
    | zero : nat 
    | succ : nat → nat 

end nat_playground

/- so from now on, we will assume that nat is defined as above, and we will re-define the same operations on nat instead of mynat. the advantage is that we can use 0, 1, 2, etc, instead of nat.zero, nat.succ nat.zero, etc. 
-/

example: 3 = nat.succ (nat.succ (nat.succ nat.zero)) := begin refl, end 


---------------------------------------------------
-- REDEFINING BASIC ARITHMETIC OPERATIONS ON nats:
---------------------------------------------------

-- addition: 
def plus : nat -> nat -> nat 
  | x  nat.zero := x
-- | x (nat.succ y) := nat.succ ( plus x y)  
  | x (nat.succ y) := ( plus (nat.succ x) y)  


example: plus 100 10 = 110 := begin refl, end 


#eval plus 100 200 


#eval plus 110 33  

#check plus 
example: plus 0 0 = 0 := begin refl, end 
example: plus 0 1 = 1 := begin refl, end 
example: plus 1 0 = 1 := begin refl, end 
example: plus 1 1 = 2 := begin refl, end 
example: plus 111 1111 = 1222 := begin refl, end 

-- we could also have defined plus like this:
def plusbis : nat -> nat -> nat 
    | 0 y := y 
    | (x+1) y := (plus x y) + 1

-- but we will avoid the above definition, because it's not immediate obvious that "x+1" is the same as "nat.succ x". now that we know how nats are defined, we will use the constructors for nats. we will make an exception for 0: we can use 0 instead of nat.zero. 



