-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .mylibrary09

def mult : ℕ → ℕ → ℕ 
  | nat.zero _ := nat.zero 
  | (nat.succ x) y := plus y (mult x y)  
--

def exponent : nat -> nat -> nat 
  | x 0 := 1 
  | x (e+1) := mult x (exponent x e)
--

def evenb : nat -> bool 
  | 0 := tt 
  | (nat.succ x) := negb (evenb x)
--
