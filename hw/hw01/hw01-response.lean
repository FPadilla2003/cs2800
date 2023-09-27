/-

1.
To elaborate, the definition of "correct", in most cases, varies from one person to another.
However, since proofs are the antithesis of that (proofs have to be true in every instance), 
correctness in the case of insertion sort means that any list inputted into the algorithm will be rearranged
from the lowest value to the highest value, which includes the extra number being inserted. 

2.
To prove correctness, we can use the #eval command in LEAN to calculate the new list and check if it is correctly sorted 
with the new number inserted. Using the list used in the homework, [2,1,4,1,3,5,1,2], we can see
that LEAN sorted the list to [1, 1, 1, 2, 2, 3, 4, 5], which is the correct way to sort it. The logic is sound too.
In the example, there are two functions that work together to sort the list in the right order: insrt and isort. 
The insrt function works by iterating through each number and checking which two numbers in the list the inserted one can fit in between. 
For example, if the number being inserted is 4, it would find that 3 and 5 are the two numbers that 4 is bigger or smaller than. 
So in the end, the function inserts the number in between those two. The other function, isort, uses the first function to insert every number 
in the list back into another list, which outputs a new sorted one with every number in the correct order. Using both functions at the same 
time and some recursion, a new list can be outputted and it comes out with the correct sorting order every time. 
Any list used in this function will be succesfully sorted.

3.
Using #eval, I tried five distinct lists to check if my definition of "correct" is "complete". 
These are the lists I used and their outputs after applying isort to them:

  1. #eval isort [10, 40, 6, 2] = [2, 6, 10, 40]
  2. #eval isort [1000, 5, 24, 57] = [5, 24, 57, 1000]
  3. #eval isort [35, 132567, 5, 69] = [5, 35, 69, 132567]
  4. #eval isort [74, 85, 90, 101] = [74, 85, 90, 101]
  5. #eval isort [53, 0, 36, 1] = [0, 1, 36, 53]

As you can see, all lists are sorted correctly using my definition.
However, there are other implementations of this sort that are buggy in design 
and will fail my definition of "correct". Here are three examples of them:

Example 1
def insrt : ℕ → list ℕ → list ℕ
  | x [] := [x] 
  | x (y :: L) := if (x ≤ y) 
                  then x :: (y :: L) 
                  else y :: (insrt x L)

def isort : list ℕ → list ℕ
  | [] := [1]
  | (x :: L) := insrt x (isort L)

Example 2 
def insrt : ℕ → list ℕ → list ℕ
  | x [] := [x] 
  | x (y :: L) := if (x ≥ y) 
                  then x :: (y :: L) 
                  else y :: (insrt x L)

def isort : list ℕ → list ℕ
  | [] := []
  | (x :: L) := insrt x (isort L)

Example 3
def insrt : ℕ → list ℕ → list ℕ
  | x [] := [x] 
  | x (y :: L) := if (x ≤ y) 
                  then x :: (y :: L) 
                  else y :: (insrt x L)

def isort : list ℕ → list ℕ
  | [] := []
  | (x :: L) := insrt x (insrt L)

In the first example, it gives the incorrect sort because while the algorithm
still gives the correct answer to a non-empty list, if the list is empty, 
it gives a list back with 1 in it. Therefore, no every instance of a list will be sorted
correctly or even include the same numbers as it was inputted with.#check

In the second example, the sort is incorrect because the insrt function is wrong. 
Instead of adding the inserted number where it is less than or equal to y, 
placing it before the bigger number, it is using a greater than symbol instead, 
giving us an incorrect sort.

The third and last example is also incorrect for a different reason. 
In this implementation, the isort function is not recursive on itself but 
rather on the insrt function instead since it has double insrt's in the code, 
which breaks it and gives the wrong sort as well.

-/
