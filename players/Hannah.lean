inductive ListNat where
  | nil
  | cons : Nat → ListNat → ListNat
  deriving Repr

-- LEVEL 1: Recognizing


open ListNat -- Easier to write ListNat things
open Nat


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

def elem : Nat → ListNat → Bool
  | _, nil => false
  | n, (cons m l) => n == m || elem n l

#eval elem 8 nil
#eval elem 5 (cons 4 (cons 6 (cons 5 nil)))

def sum : ListNat → Nat
  | nil => 0
  | cons n l => n + (sum l)  

#eval sum nil
#eval sum (cons 3 (cons 5 (cons 8 nil)))

def product : ListNat → Nat
  | nil => 1
  | cons n l => n * (product l)

#eval product nil
#eval product (cons 3 (cons 2 nil))

-- Same as (++)
def concat : ListNat → ListNat → ListNat
  | nil, list => list
  | (cons n l), list => cons n (concat l list)

#eval concat nil nil
#eval concat (cons 1 nil) (cons 3 (cons 4 nil))

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

#eval reverse (cons 0 nil)
#eval reverse (cons 1 (cons 3 (cons 4 nil)))

def min₂ : Nat → Nat → Nat
  | n+1, m+1 => (min n m) + 1
  | _, _ => 0

#eval min₂ 0 1
#eval min₂ 5 9

def max₂ : Nat → Nat → Nat
  | 0, m => m
  | n, 0 => n
  | n+1, m+1 => (max n m) + 1

#eval max₂ 0 1
#eval max₂ 9 7

def filter : (Nat → Bool) → ListNat → ListNat
  | _, nil => nil
  | p, cons n l => if p n then cons n (filter p l) else filter p l

def even : Nat → Bool
  | 0 => true
  | succ 0 => false
  | succ (succ n) => even n
 
#eval filter even nil
#eval filter even (cons 0 (cons 2 (cons 3 nil)))

def odd : Nat → Bool
  | 0 => false
  | succ 0 => true
  | succ (succ n) => odd n

#eval odd 4
#eval odd 7

def Zero : Nat → Bool
  | 0 => true
  | _ => false

#eval Zero 1
#eval Zero zero

def all : (Nat → Bool) → ListNat → Bool
  | _, nil => true
  | p, cons n l => p n && all p l

#eval all even (cons 8 (cons 4 (cons 6 nil)))
#eval all even (cons 2 (cons 6 (cons 7 nil)))
#eval all odd (cons 5 (cons 2 (cons 7 (cons 9 nil))))
#eval all odd nil
#eval all Zero (cons 0 (cons 0 (cons 0 (cons 0 nil))))
#eval all Zero (cons 0 (cons 1 (cons 0 (cons 6 nil))))


def any : (Nat → Bool) → ListNat → Bool
  | _, nil => false
  | p, cons n l => p n || any p l

#eval any even (cons 2 (cons 6 (cons 7 nil)))
#eval any even (cons 5 (cons 7 (cons 9 (cons 3 nil))))
#eval any odd (cons 6 (cons 4 (cons 2 (cons 1 nil))))
#eval any odd (cons 4 nil)
#eval any Zero (cons 7 (cons 5 (cons 1 (cons 6 nil))))
#eval any Zero (cons 5 (cons 6 (cons 8 (cons 0 nil))))

#eval doubleList nil
#eval doubleList (cons 1 (cons 3 nil))

def map : (Nat → Nat) → ListNat → ListNat
  | _, nil => nil
  | p, cons n l => cons (p n) (map p l)

-- Use \. + space to write · 
#eval map (· * 2) (cons 1 (cons 3 nil))
#eval map (· + 3) (cons 1 nil)

def addNat : Nat → ListNat → ListNat
  | n, l => map (· + n) l

#eval addNat 4 nil
#eval addNat 8 (cons 0 (cons 5 (cons 1 nil)))

def multNat : Nat → ListNat → ListNat
  | n, l => map (· * n) l

#eval multNat 3 (cons 1 (cons 2 (cons 3 nil)))
#eval multNat 2 nil

def expNat : Nat → ListNat → ListNat
  | n, l => map (· ^ n) l

#eval expNat 2 (cons 5 (cons 7 (cons 2 (cons 1 nil))))
#eval expNat 3 nil

def enumTo : Nat → ListNat
  | n+1 => append (n+1) (enumTo n)
  | _ => cons 0 nil

#eval enumTo 3
#eval enumTo 0

def take : Nat → ListNat → ListNat
  | n+1, (cons m l) => cons m (take n l)
  | _, _ => nil

#eval take 4 (cons 3 (cons 4 (cons 2 (cons 1 nil))))
#eval take 6 (cons 3 (cons 3 nil))

def drop : Nat → ListNat → ListNat
  | n+1, (cons _ l) => drop n l
  | _, l => l

#eval drop 2 (cons 3 (cons 4 (cons 2 (cons 1 nil))))
#eval drop 4 (cons 3 (cons 3 nil))

def elemIndices : Nat → ListNat → ListNat
  | n, cons m l => if n == m then cons 0 (addNat 1 (elemIndices n l)) else (addNat 1 (elemIndices n l))
  | _, nil => nil

#eval elemIndices 1 (cons 1 (cons 1 (cons 1 (cons 2 nil))))
#eval elemIndices 3 (cons 2 (cons 1 (cons 0 (cons 9 nil))))

def pwAdd : ListNat → ListNat → ListNat
  | (cons n ns), (cons m ms) => cons (n+m) (pwAdd ns ms)
  | _, _ => nil

#eval pwAdd (cons 2 (cons 4 (cons 5 nil))) (cons 5 (cons 6 nil))
#eval pwAdd (cons 1 (cons 2 nil)) (cons 6 (cons 5 (cons 4 nil)))

def pwMult : ListNat → ListNat → ListNat
  | (cons n ns), (cons m ms) => cons (n*m) (pwMult ns ms)
  | _, _ => nil

#eval pwMult (cons 2 (cons 4 (cons 5 nil))) (cons 5 (cons 6 nil))
#eval pwMult (cons 1 (cons 2 nil)) (cons 6 (cons 5 (cons 4 nil)))

def isSorted : ListNat → Bool
  | cons n (cons m l) => n ≤ m && isSorted l
  | _ => true

#eval isSorted (cons 3 (cons 2 nil))
#eval isSorted (cons 1 (cons 2 (cons 3 (cons 4 nil))))

def minimum : ListNat → Nat
  | cons n nil => n
  | cons n l => min₂ n (minimum l)
  | _ => 100000000000-- Error (to be fixed)

#eval minimum (cons 3 (cons 5 (cons 1 (cons 8 nil))))
#eval minimum (cons 4 nil)

def maximum : ListNat → Nat 
  | nil => 0
  | cons n l => max₂ n (maximum l)

#eval maximum nil
#eval maximum (cons 10 (cons 5 (cons 7 nil)))
#eval maximum (cons 1 (cons 1 nil))

def isPrefixOf : ListNat → ListNat → Bool
  | nil, _ => true
  | cons n ns, cons m ms => n == m && isPrefixOf ns ms
  | _, _ => false

#eval isPrefixOf (cons 1 (cons 2 (cons 3 nil))) (cons 1 (cons 2 (cons 3 (cons 4 nil))))
#eval isPrefixOf (cons 3 nil) (cons 2 nil)
#eval isPrefixOf (cons 7 nil) nil

def mix : ListNat → ListNat → ListNat
  | cons n ns, cons m ms => (cons n (cons m (mix ns ms)))
  | _, _ => nil

#eval mix (cons 1 (cons 2 nil)) (cons 10 (cons 20 (cons 30 nil)))
#eval mix nil (cons 3 nil)

def interspace : Nat → ListNat → ListNat
  | _, cons m nil => cons m nil
  | n, cons m l => (cons m (cons n (interspace n l)))
  | _, nil => nil

#eval interspace 4 (cons 7 nil)
#eval interspace 5 (cons 10 (cons 20 (cons 30 nil)))
#eval interspace 7 nil

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

-- HW Theorems

-- Level 4.1
theorem sum_distr_concat (xs ys : ListNat) :
  sum (concat xs ys) = sum xs + sum ys :=
by
  induction xs with
  | nil => rw [concat, sum, Nat.zero_add]
  | cons x xs h => rw [concat, sum, h, sum, Nat.add_assoc]

-- Level 4.2
theorem product_distr_concat (xs ys : ListNat) :
  product (concat xs ys) = product xs * product ys :=
by
  induction xs with
  | nil => rw [concat, product, Nat.one_mul]
  | cons x xs h => rw [concat, product, h, product, Nat.mul_assoc]

-- Level 4.3
theorem le_succ_succ_self (n : Nat) :
  n < succ (succ n) :=
by
  have h: (succ n < succ (succ n) ∨ succ n ≥ succ (succ n)) := Nat.lt_or_ge (succ n) (succ (succ n))
  apply Or.elim h
  intro h'
  have h1: (n ≤ succ n) := Nat.le_succ n
  exact Nat.lt_of_le_of_lt h1 h'
  intro h2
  have h_boom: (¬succ (succ n) ≤ succ n) := Nat.not_succ_le_self (succ n)
  exact False.elim (h_boom h2)

theorem odd_eq_not_even (n : Nat) :
  odd n = not (even n) :=
by
  induction n using Nat.strongInductionOn with
  | ind n ih =>
    match n with
    | 0 => rw [odd, even, Bool.not_true]
    | succ 0 => rw [odd, even, Bool.not_false]
    | succ (succ n') => 
      rw [odd, even, ih n' (le_succ_succ_self n')]

theorem length_concat_distr (xs ys : ListNat) :
  length (concat xs ys) = length xs + length ys :=
by
  induction xs with
  | nil => rw [concat, length, Nat.zero_add]
  | cons x xs h => rw [concat, length, h, length, Nat.add_right_comm]

theorem false_not_true :
  false ≠ true :=
by
  intro H
  cases H

theorem length_concat_filter_even_odd_list (l : ListNat):
  length (concat (filter even l) (filter odd l)) = length l :=
by
  induction l with
  | nil => rw [filter, filter, concat]
  | cons x xs h => 
    rw [filter, filter, odd_eq_not_even]
    cases even x
    rw [Bool.not_false,
        if_neg false_not_true,
        if_pos rfl,
        length,
        length_concat_distr,
        length,
        ← Nat.add_assoc, 
        ← length_concat_distr,
        h]
    rw [if_pos rfl,
        Bool.not_true,
        if_neg false_not_true,
        concat, 
        length,
        length_concat_distr,
        length,
        ← length_concat_distr,
        h]
