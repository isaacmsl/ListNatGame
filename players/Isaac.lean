inductive ListNat where
  | nil
  | cons : Nat → ListNat → ListNat
  deriving Repr

-- LEVEL 1: Recognizing


open ListNat -- Easier to write ListNat things

#check nil -- With open command
#check ListNat.nil -- Without "open ListNat" command
#check cons 0 nil
#eval nil -- deriving Repr








-- LEVEL 2: Defining operations

def length : ListNat → Nat
  | nil => 0
  | cons _ l => length l + 1

#check length nil -- Judgement
#eval length nil -- Evaluation (?)
#eval length (cons 0 nil) -- Fix it

def greatest : ListNat → Nat 
  | nil => 0
  | cons n l => if n > greatest l then n else greatest l

#eval greatest nil
#eval greatest (cons 4 (cons 20 (cons 10 nil)))
#eval greatest (cons 1 (cons 1 nil))

-- Assume ordered lists
-- First element greater than n
def upper_bound : Nat → ListNat → Nat
  | _, nil => 0
  | n, cons x l => if x > n then x else upper_bound n l

#eval upper_bound 0 nil
#eval upper_bound 3 (cons 1 (cons 3 (cons 4 (cons 8 nil))))
#eval upper_bound 5 (cons 1 (cons 3 (cons 4 (cons 8 nil))))

-- Assume ordered lists
-- First element not less than n
def lower_bound : Nat → ListNat → Nat
  | _, nil => 0
  | n, cons x l => if x >= n then x else lower_bound n l

#eval lower_bound 0 nil
#eval lower_bound 3 (cons 1 (cons 3 (cons 4 (cons 8 nil))))
#eval lower_bound 5 (cons 1 (cons 3 (cons 4 (cons 8 nil))))

def filter : (Nat → Bool) → ListNat → ListNat
  | _, nil => nil
  | p, (cons x xs) => if p x then cons x (filter p xs) else filter p xs

open Nat

def even : Nat → Bool
 | 0 => true
 | 1 => false
 | succ (succ x) => even x

#eval filter even nil
#eval filter even (cons 0 (cons 2 (cons 3 nil)))

-- [1,2,3] → [2,4,6]
def doubleList : ListNat → ListNat
  | nil => nil
  | cons x xs => cons (x * 2) (doubleList xs)

def map : (Nat → Nat) → ListNat → ListNat
  | _, nil => nil
  | f, cons x xs => cons (f x) (map f xs)

#eval doubleList nil
#eval doubleList (cons 1 (cons 3 nil))

-- Use \. + space to write · 
#eval map (· * 2) (cons 1 (cons 3 nil))
#eval map (· + 3) (cons 1 nil)


def concat : ListNat → ListNat → ListNat
  | nil, ys => ys
  | cons x xs, ys => cons x (concat xs ys)

#eval concat nil nil
#eval concat (cons 1 nil) (cons 3 (cons 4 nil))
-- Yours!

-- Add an nat to the end
def append : Nat → ListNat → ListNat
  | n, nil => cons n nil
  | n, cons x l => cons x (append n l)

-- Define append in function of concat

def append_cat : Nat → ListNat → ListNat
  | n, l => concat l (cons n nil)

#eval append 0 nil
#eval append 3 (cons 0 nil)

-- esreveR...
def reverse : ListNat → ListNat
  | nil => nil
  | cons n l => append n (reverse l)

-- Obviously eval it...

-- LEVEL 3: Theorems

variable (l : ListNat)

theorem same_functions :
  doubleList l = map (· * 2) l :=
by
  induction l with
  | nil =>
    rw [doubleList, map]
  | cons x xs gift =>
    rw [doubleList, map, gift]

theorem reverse_nil : reverse nil = nil := rfl

theorem cool_theorem (x : Nat) :
  reverse (append x l) = cons x (reverse l) :=
by
  induction l with
  | nil => 
    rw [append, reverse, reverse, reverse, append]
  | cons n l h =>
    rw [
      reverse,
      append,
      reverse,
      h,
      append
    ]

theorem reverse_reverse :
  reverse (reverse l) = l :=
by
  induction l with
  | nil => rw [reverse, reverse]
  | cons a xs h =>
    rw [reverse]
    cases h' : reverse xs with
    | nil =>
      rw [h'] at h
      rw [reverse] at h
      rw [
        append,
        reverse,
        reverse,
        append,
        ←h
      ]
    | cons x l' =>
      rw [h'] at h
      rw [reverse] at h
      rw [
        append,
        reverse,
        ←h,
        ←append,
        cool_theorem
      ]








-- LEVEL 4: Your own theorems

-- Sugestions:
-- Can you think cool theorems about lower_bound and upper_bound?
-- How about append_cat?
-- Buy me a KitKat from myself

-- By Isaac Lourenço 2023, IMD - UFRN, Brazil.