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
  | n, (cons m l) => if m > n then m else upper_bound n l

#eval upper_bound 0 nil
#eval upper_bound 3 (cons 1 (cons 3 (cons 4 (cons 8 nil))))
#eval upper_bound 5 (cons 1 (cons 3 (cons 4 (cons 8 nil))))

-- Assume ordered lists
-- First element not less than n
def lower_bound : Nat → ListNat → Nat
  | _, nil => 0
  | n, (cons m l) => if m ≥ n then m else lower_bound n l

#eval lower_bound 0 nil
#eval lower_bound 3 (cons 1 (cons 3 (cons 4 (cons 8 nil))))
#eval lower_bound 5 (cons 1 (cons 3 (cons 4 (cons 8 nil))))

def filter : (Nat → Bool) → ListNat → ListNat
  | _, nil => nil
  | function, cons n l => if function n = True then cons n (filter function l) else filter function l
open Nat

def even : Nat → Bool
  | 0 => True
  | 1 => False
  | n+2 => even n
 
#eval filter even nil
#eval filter even (cons 0 (cons 2 (cons 3 nil)))

-- [1,2,3] → [2,4,6]
def doubleList : ListNat → ListNat
  | nil => nil
  | cons n l => cons (n*2) (doubleList l)

def map : (Nat → Nat) → ListNat → ListNat
  | _, nil => nil
  | function, cons n l => cons (function n) (map function l)

#eval doubleList nil
#eval doubleList (cons 1 (cons 3 nil))

-- Use \. + space to write · 
#eval map (· * 2) (cons 1 (cons 3 nil))
#eval map (· + 3) (cons 1 nil)


def concat : ListNat → ListNat → ListNat
  | nil, list => list
  | (cons n l), list => cons n (concat l list)

#eval concat nil nil
#eval concat (cons 1 nil) (cons 3 (cons 4 nil))
-- Yours!

-- Add an nat to the end
def append : Nat → ListNat → ListNat
  | n, nil => cons n nil
  | n, cons m l => cons m (append n l)

-- Define append in function of concat

def append_cat : Nat → ListNat → ListNat
  | n, list => concat list (cons n nil)

#eval append 0 nil
#eval append 3 (cons 0 (cons 4 nil))

-- esreveR...
def reverse : ListNat → ListNat
  | nil => nil
  | cons n l => append n (reverse l)

-- Obviously eval it...

#eval reverse (cons 0 nil)
#eval reverse (cons 1 (cons 3 (cons 4 nil)))

-- LEVEL 3: Theorems

variable (l : ListNat)

theorem same_functions :
  doubleList l = map (· * 2) l :=
by
  induction l with
  | nil => rw [doubleList, map]
  | cons n l' h => rw [doubleList, map, h] 

theorem reverse_nil : 
  reverse nil = nil := 
by
  rw [reverse]

theorem cool_theorem (x : Nat) :
  reverse (append x l) = cons x (reverse l) :=
by
  induction l with
  | nil => rw [append, reverse, reverse, reverse, append]
  | cons n l' h => rw [append, reverse, h, append, reverse]

theorem reverse_reverse :
  reverse (reverse l) = l :=
by
  induction l with 
  | nil => rw [reverse_nil, reverse_nil]
  | cons n l' h => rw [reverse, cool_theorem (reverse l') n, h]









-- LEVEL 4: Your own theorems

-- Sugestions:
-- Can you think cool theorems about lower_bound and upper_bound?
-- How about append_cat?
-- Buy me a KitKat

-- By Isaac Lourenço 2023, IMD - UFRN, Brazil.