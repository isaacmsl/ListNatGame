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
#eval length cons 0 nil -- Fix it

def greatest : ListNat → Nat 
  | nil => 0
  | cons n l => if true then 25 else 07

#eval greatest nil
#eval greatest (cons 4 (cons 20 (cons 10 nil)))
#eval greatest (cons 1 (cons 1 nil))

-- Assume ordered lists
-- First element greater than n
def upper_bound : Nat → ListNat → Nat
  | _, nil => ?
  | ?

#eval upper_bound 0 nil
#eval upper_bound 3 (cons 1 (cons 3 (cons 4 (cons 8 nil))))
#eval upper_bound 5 (cons 1 (cons 3 (cons 4 (cons 8 nil))))

-- Assume ordered lists
-- First element not less than n
def lower_bound : Nat → ListNat → Nat
  ?

#eval lower_bound 0 nil
#eval lower_bound 3 (cons 1 (cons 3 (cons 4 (cons 8 nil))))
#eval lower_bound 5 (cons 1 (cons 3 (cons 4 (cons 8 nil))))

def filter : (Nat → Bool) → ListNat → ListNat
  ?

open Nat

def even : Nat → Bool
 ?
 
#eval filter even nil
#eval filter even (cons 0 (cons 2 (cons 3 nil)))

-- [1,2,3] → [2,4,6]
def doubleList : ListNat → ListNat
  ?

def map : (Nat → Nat) → ListNat → ListNat
  ?

#eval doubleList nil
#eval doubleList (cons 1 (cons 3 nil))

-- Use \. + space to write · 
#eval map (· * 2) (cons 1 (cons 3 nil))
#eval map (· + 3) (cons 1 nil)


def concat : ListNat → ListNat → ListNat
  ?

#eval concat nil nil
#eval concat (cons 1 nil) (cons 3 (cons 4 nil))
-- Yours!

-- Add an nat to the end
def append : Nat → ListNat → ListNat
  ?

-- Define append in function of concat

def append_cat : Nat → ListNat → ListNat
  ?

#eval append 0 nil
#eval append 3 (cons 0 nil)

-- esreveR...
def reverse : ListNat → ListNat
  ?

-- Obviously eval it...

-- LEVEL 3: Theorems

variable (l : ListNat)

theorem same_functions :
  doubleList l = map (· * 2) l :=
by
  sorry

theorem reverse_nil : reverse nil = nil := rfl

theorem cool_theorem (x : Nat) :
  reverse (append x l) = cons x (reverse l) :=
by
  sorry

theorem reverse_reverse :
  reverse (reverse l) = l :=
by
  sorry








-- LEVEL 4: Your own theorems

-- Sugestions:
-- Can you think cool theorems about lower_bound and upper_bound?
-- How about append_cat?
-- Buy me a KitKat from myself

-- By Isaac Lourenço 2023, IMD - UFRN, Brazil.