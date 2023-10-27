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
  | cons _ l => succ (length l)

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

def All : (Nat → Bool) → ListNat → Bool
  | _, nil => true
  | p, cons n l => p n && All p l

#eval All even (cons 8 (cons 4 (cons 6 nil)))
#eval All even (cons 2 (cons 6 (cons 7 nil)))
#eval All odd (cons 5 (cons 2 (cons 7 (cons 9 nil))))
#eval All odd nil
#eval All Zero (cons 0 (cons 0 (cons 0 (cons 0 nil))))
#eval All Zero (cons 0 (cons 1 (cons 0 (cons 6 nil))))


def Any : (Nat → Bool) → ListNat → Bool
  | _, nil => false
  | p, cons n l => p n || Any p l

#eval Any even (cons 2 (cons 6 (cons 7 nil)))
#eval Any even (cons 5 (cons 7 (cons 9 (cons 3 nil))))
#eval Any odd (cons 6 (cons 4 (cons 2 (cons 1 nil))))
#eval Any odd (cons 4 nil)
#eval Any Zero (cons 7 (cons 5 (cons 1 (cons 6 nil))))
#eval Any Zero (cons 5 (cons 6 (cons 8 (cons 0 nil))))

#eval doubleList nil
#eval doubleList (cons 1 (cons 3 nil))

def map : (Nat → Nat) → ListNat → ListNat
  | _, nil => nil
  | p, cons n l => cons (p n) (map p l)

-- Use \. + space to write · 
#eval map (· * 2) (cons 1 (cons 3 nil))
#eval map (· + 3) (cons 1 nil)

def addNat : Nat → ListNat → ListNat
  | _, nil => nil
  | n, cons x xs => cons (x + n) (addNat n xs)

#eval addNat 4 nil
#eval addNat 8 (cons 0 (cons 5 (cons 1 nil)))

def multNat : Nat → ListNat → ListNat
  | _, nil => nil
  | n, cons x xs => cons (x * n) (multNat n xs)

#eval multNat 3 (cons 1 (cons 2 (cons 3 nil)))
#eval multNat 2 nil

def expNat : Nat → ListNat → ListNat
  | _, nil => nil
  | n, cons x xs => cons (x ^ n) (expNat n xs)

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
  | cons n (cons m l) => n ≤ m && isSorted (cons m l)
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

theorem concat_nil (l : ListNat) :
  concat l nil = l :=
by
  induction l with
  | nil => rw [concat]
  | cons x xs h => rw [concat, h]

theorem concat_append (x : Nat) (xs ys : ListNat) :
  concat ys (append x xs) = append x (concat ys xs) :=
by
  induction ys with
  | nil => rw [concat, concat]
  | cons y ys h => rw [concat, h, concat, append]

theorem same_functions (l : ListNat):
  doubleList l = map (· * 2) l :=
by
  induction l with
  | nil => rw [doubleList, map]
  | cons n l' h => rw [doubleList, map, h] 

theorem reverse_nil : 
  reverse nil = nil := 
by
  rw [reverse]

theorem cool_theorem (x : Nat) (l : ListNat):
  reverse (append x l) = cons x (reverse l) :=
by
  induction l with
  | nil => rw [append, reverse, reverse, reverse, append]
  | cons n l' h => rw [append, reverse, h, append, reverse]

theorem reverse_reverse (l : ListNat):
  reverse (reverse l) = l :=
by
  induction l with 
  | nil => rw [reverse_nil, reverse_nil]
  | cons n l' h => rw [reverse, cool_theorem n (reverse l'), h]

theorem length_append (n : Nat) (l : ListNat):
  length (append n l) = (length l) + 1 :=
by
  induction l with
  | nil => rw [append, length, length, length]
  | cons x xs h => rw [append, length, h, length]

theorem length_reverse (l : ListNat):
  length (reverse l) = length l :=
by
  induction l with
  | nil => rw [reverse]
  | cons x xs h => rw [reverse, length, length_append, h]

theorem length_concat_distr (xs ys : ListNat) :
  length (concat xs ys) = length xs + length ys :=
by
  induction xs with
  | nil => rw [concat, length, Nat.zero_add]
  | cons x xs h => rw [concat, length, h, length, Nat.succ_add]

theorem reverse_concat_concat_reverse (xs ys : ListNat) :
  reverse (concat xs ys) = concat (reverse ys) (reverse xs) :=
by
  induction xs with
  | nil => rw [concat, reverse, concat_nil]
  | cons x xs h => rw [concat, reverse, h, reverse, concat_append]

theorem addNat_distr (n : Nat) (xs ys : ListNat) :
  addNat n (concat xs ys) = concat (addNat n xs) (addNat n ys) :=
by
  induction xs with
  | nil => rw [concat, addNat, concat]
  | cons x xs h => rw [concat, addNat, h, addNat, concat]
  
theorem concat_assoc (as bs cs : ListNat) :
  concat (concat as bs) cs = concat as (concat bs cs) :=
by
  induction as with
  | nil => rw [concat, concat]
  | cons a as h => rw [concat, concat, h, concat,]

theorem nil_one_id_concat :
  (∀l, (concat nil l = l) ∧ (concat l nil = l)) :=
by
  intro l
  apply And.intro
  rw [concat]
  rw [concat_nil]

-- LEVEL 4: Your own theorems

-- HW Theorems

-- Even relations
theorem false_not_true :
  false ≠ true :=
by
  intro H
  cases H

theorem lt_succ_succ_self (n : Nat) :
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
      rw [odd, even, ih n' (lt_succ_succ_self n')]

theorem not_even_succ (a : Nat) :
  (!even (succ a)) = even a :=
by
  induction a using Nat.strongInductionOn with
  | ind a' ih =>
    match a' with
    | 0 => rw [even, even, Bool.not_false]
    | succ 0 => rw [even, even, even, Bool.not_true]
    | succ (succ a') => rw [even, even, ih a' (lt_succ_succ_self a')]

theorem even_succ (a : Nat) :
  (!even a) = even (succ a) :=
by
  induction a using Nat.strongInductionOn with
  | ind a' ih =>
    match a' with
    | 0 => rw [even, even, Bool.not_true]
    | succ 0 => rw [even, even, even, Bool.not_false]
    | succ (succ a') => rw [even, even, ih a' (lt_succ_succ_self a')]

-- Some things about Decide
theorem not_congr (h : P ↔ Q) : 
  ¬P ↔ ¬Q := 
by
  apply Iff.intro
  intro np
  intro q
  suffices p : P from np p
  exact h.mpr q
  intro nq
  intro p
  suffices q : Q from nq q
  exact h.mp p

theorem decide_iff (p : Prop) [d : Decidable p] : decide p = true ↔ p := by simp

theorem decide_true {p : Prop} [Decidable p] : p → decide p :=
  (decide_iff p).2

theorem of_decide_true {p : Prop} [Decidable p] : decide p → p :=
  (decide_iff p).1

theorem bool_iff_false {b : Bool} : 
  ¬b ↔ b = false := 
by 
  cases b 
  apply Iff.intro
  intro 
  rfl
  intro _ h'
  exact false_not_true h'
  apply Iff.intro
  intro h
  suffices h': (true = true) from False.elim (h h')
  rfl
  intro h
  exact False.elim (false_not_true h.symm)

theorem bool_eq_false {b : Bool} : ¬b → b = false :=
  bool_iff_false.1

theorem decide_false_iff (p : Prop) [Decidable p] : decide p = false ↔ ¬p :=
  bool_iff_false.symm.trans (not_congr (decide_iff _))

theorem of_decide_false {p : Prop} [Decidable p] : decide p = false → ¬p :=
  (decide_false_iff p).1

theorem decide_false {p : Prop} [Decidable p] : ¬p → decide p = false :=
  (decide_false_iff p).2

theorem decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  cases h' : decide q with
  | false => exact decide_false (mt h.1 <| of_decide_false h')
  | true => exact decide_true (h.2 <| of_decide_true h')

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
        if_pos rfl, length,
        length_concat_distr,
        length, Nat.add_succ, 
        ← length_concat_distr,
        h]
    rw [if_pos rfl,
        Bool.not_true,
        if_neg false_not_true,
        concat, length,
        length_concat_distr,
        length,
        ← length_concat_distr,
        h]

-- Level 4.4
theorem filter_append (n : Nat) (ns : ListNat) (p : Nat → Bool):
  filter p (append n ns) = (if p n then append n (filter p ns) else (filter p ns)) :=
by
  induction ns with
  | nil => rw [filter, append, filter, filter]
  | cons x xs h => 
    rw [filter, append, filter, h]
    cases p x
    rw [if_neg false_not_true, if_neg false_not_true]
    rw [if_pos rfl, if_pos rfl, append]
    cases p n
    rw [if_neg false_not_true, if_neg false_not_true]
    rw [if_pos rfl, if_pos rfl]

theorem rev_filter_eq_filter_rev (l : ListNat):
  reverse (filter even l) = filter even (reverse l) :=
by
  induction l with
  | nil => rw [filter, reverse, filter]
  | cons n ns h =>
    rw [filter, reverse, filter_append]
    cases even n
    rw [if_neg false_not_true, if_neg false_not_true, h]
    rw [if_pos rfl, if_pos rfl, reverse, h]

-- Level 4.5
theorem length_same_addNat (n : Nat) (l : ListNat) :
  length (addNat n l) = length l :=
by
  induction l with
  | nil => rw [addNat]
  | cons x xs h => rw [addNat, length, length, h]

-- Level 4.6
theorem sum_addNat (n : Nat) (l : ListNat) :
  sum (addNat n l) = (n * length l) + sum l :=
by
  induction l with
  | nil => rw [addNat, length, Nat.mul_zero, Nat.zero_add]
  | cons x xs h => 
    rw [addNat, sum, h, 
        Nat.add_assoc,
        ← Nat.add_assoc n (n * length xs) (sum xs),
        ← Nat.mul_one n,
        Nat.mul_assoc,
        ← Nat.left_distrib,
        length,
        Nat.mul_assoc,
        Nat.left_distrib 1 (length xs) 1,
        Nat.mul_one 1,
        Nat.add_comm (1 * length xs) 1,
        sum,
        ← Nat.add_assoc (n * (1 + 1 * length xs)) x (sum xs),
        Nat.add_comm (n * (1 + 1 * length xs)) x,
        Nat.add_assoc x (n * (1 + 1 * length xs)) (sum xs)]

-- Level 4.7
theorem sum_multNat (n : Nat) (l : ListNat) :
  sum (multNat n l) = n * sum l :=
by
  induction l with
  | nil => rw [multNat, sum, Nat.mul_zero]
  | cons x xs h => 
    rw [multNat, 
        sum, h, sum,
        Nat.mul_comm x n,
        Nat.left_distrib]

-- Level 4.8
theorem product_multNat (n : Nat) (l : ListNat) :
  product (multNat n l) = (n ^ length l) * product l:=
by
  induction l with
  | nil => rw [multNat, length, product, Nat.pow_zero, Nat.mul_one]
  | cons x xs h => 
    rw [multNat, product,
        h, length, product,
        Nat.pow_succ n (length xs),
        Nat.mul_assoc (n ^ length xs) n (x * product xs),
        ← Nat.mul_assoc n x (product xs),
        Nat.mul_comm n x,
        ← Nat.mul_assoc (n ^ length xs) (x * n) (product xs),
        Nat.mul_comm (n ^ length xs) (x * n),
        Nat.mul_assoc (x * n) (n ^ length xs) (product xs)]

-- Level 4.9
theorem one_pow (m : Nat) :
  1 ^ m = 1 :=
by
  induction m with
  | zero => rw [Nat.pow_zero]
  | succ m' h => rw [Nat.pow_succ, h, Nat.mul_one]

theorem mul_pow (a b n : Nat) :
  (a * b) ^ n = (a ^ n) * (b ^ n):=
by  
  induction n with
  | zero => rw [Nat.pow_zero, Nat.pow_zero, Nat.pow_zero, Nat.mul_one]
  | succ n' h => 
    rw [Nat.pow_succ (a * b) n',
        h,
        Nat.mul_assoc (a ^ n') (b ^ n') (a * b),
        Nat.mul_comm (b ^ n') (a * b),
        Nat.mul_assoc a b (b ^ n'),
        Nat.mul_comm b (b ^ n'),
        ← Nat.mul_assoc (a ^ n') a (b ^ n' * b),
        ← Nat.pow_succ a n',
        ← Nat.pow_succ b n']

theorem product_expNat (n : Nat) (l : ListNat) :
  product (expNat n l) = (product l) ^ n :=
by
  induction l with
  | nil => rw [expNat, product, one_pow]
  | cons x xs h => 
    rw [expNat, product,
        h, product,
        mul_pow]

-- Level 4.10
theorem length_matters {l l' : ListNat} :
  l = l' → length l = length l' :=
by
  intro h
  rw [h]

axiom succ_inj {a b : Nat} : (succ a = succ b) → a = b
theorem not_eq_Add {n m : Nat} :
  m ≠ 0 → ¬ n = n + m :=
by
  intro h h'
  induction n with
  | zero => 
    rw [Nat.zero_add] at h'
    exact h h'.symm
  | succ n' H => 
    rw [Nat.succ_add] at h'
    exact H (succ_inj h')

theorem and_cancel_right (a b c : Bool) :
  (a && c) = (b && c) ∧ (c = true) → a = b :=
by
  intro h
  have h1: ((a && c) = (b && c)) := And.left h
  rw [(And.right h), Bool.and_true, Bool.and_true] at h1
  exact h1

theorem cons_one_neq_cons_more {x : Nat} :
  ∀ (n m : Nat) (l : ListNat), ¬ cons x nil = cons n (cons m l) :=
by
  intro n m l h
  have lh: (length (cons x nil) = length (cons n (cons m l))) := length_matters h
  rw [length, length, 
      length, length, 
      ← Nat.zero_add (succ (length l)), 
      ← Nat.succ_add] at lh
  exact not_eq_Add (Nat.succ_ne_zero (length l)) lh

theorem addNat_zero (l : ListNat) :
  addNat zero l = l :=
by
  induction l with
  | nil => rw [addNat]
  | cons x xs h => rw [addNat, Nat.add_zero, h]

theorem add_le_add_iff {a b n : Nat}  : 
  a + n ≤ b + n ↔ a ≤ b := 
by
  apply Iff.intro
  intro h
  induction n with
  | zero => 
    rw [Nat.add_zero, Nat.add_zero] at h
    exact h
  | succ n' h' => 
    rw [Nat.add_succ, Nat.add_succ] at h 
    suffices h'': (a + n' ≤ b + n') from h' h''
    exact Nat.le_of_succ_le_succ h
  intro h
  induction n with
  | zero => 
    rw [Nat.add_zero, Nat.add_zero]
    exact h
  | succ n' h' => 
    rw [Nat.add_succ, Nat.add_succ]
    exact Nat.succ_le_succ h'

theorem isSorted_addNat (n : Nat) (l : ListNat) :
  isSorted (addNat n l) = isSorted l :=
by
  induction l with
  | nil => rw [addNat]
  | cons x xs h =>
    rw [addNat]
    cases xs with
    | nil =>
      rw [addNat, isSorted, isSorted]
      exact cons_one_neq_cons_more
      exact cons_one_neq_cons_more
    | cons y ys =>
      rw [addNat] at h
      rw [addNat, isSorted, h, isSorted]
      rw [decide_congr add_le_add_iff]

-- Level 4.11
theorem or_inl {a b : Bool} (H : a) : a || b := 
by 
  rw [or, H]

theorem or_comm : ∀ a b, (a || b) = (b || a) :=
by
  intro a b
  cases a
  cases b
  rfl
  rw [or, or]
  cases b
  rw [or, or]
  rfl

theorem or_inr {a b : Bool} (H : b) : a || b := 
by 
  rw [or_comm, or_inl H]

theorem even_Add (a b : Nat) :
  even (a + b) = ((even a && even b) || (odd a && odd b)) :=
by
  induction a using Nat.strongInductionOn with
  | ind a' ih =>
    match a' with
    | 0 => 
      rw [Nat.zero_add, odd_eq_not_even, odd_eq_not_even]
      cases even b
      rw [Bool.and_false, Bool.not_false, 
          Bool.and_true, even, Bool.false_or, 
          Bool.not_true]
      rw [even, Bool.and_self, Bool.true_or]
    | succ 0 => 
      rw [Nat.succ_add, Nat.zero_add, 
          odd_eq_not_even, odd_eq_not_even, 
          ← even_succ]
      cases even b
      rw [Bool.not_false, even, Bool.false_and, 
          Bool.not_false, Bool.and_true, 
          Bool.or_true]
      rw [Bool.not_true, even, Bool.false_and, 
          Bool.and_false, Bool.or_false]
    | succ (succ a') => 
      rw [Nat.succ_add (succ a') b, 
          Nat.succ_add a' b, 
          even, even, odd, 
          ih a' (lt_succ_succ_self a')]


theorem odd_Add (a b : Nat) :
  odd (a + b) = ((even a && odd b) || (odd a && even b)) :=
by
  rw [odd_eq_not_even, even_Add, odd_eq_not_even, odd_eq_not_even]
  cases even a
  rw [Bool.false_and, Bool.not_false, 
      Bool.true_and, Bool.false_and, 
      Bool.true_and, Bool.false_or, 
      Bool.false_or, Bool.not_not]
  rw [Bool.true_and, Bool.not_true, 
      Bool.false_and, Bool.or_false, 
      Bool.true_and, Bool.false_and, 
      Bool.or_false]

theorem not_and (b : Bool) :
  (!b && b) = false :=
by
  cases b
  rw [Bool.and_false]
  rw [Bool.not_true, Bool.false_and]

theorem and_comm (a b : Bool) :
  (a && b) = (b && a) :=
by
  cases a
  rw [Bool.and_false, Bool.false_and]
  rw [Bool.and_true, Bool.true_and]

theorem and_not (b : Bool) :
  (b && !b) = false :=
by
  rw [and_comm, not_and]

theorem my_simp (a b c : Bool) :
  (a && (b && (b && (c || !c) || !b && (c && !c || !c && c)) || 
  !b && (b && (c && !c || !c && c) || !b && (c || !c))) || 
  !a && (b && (b && (c && !c || !c && c) || !b && (c || !c)) || 
  !b && (b && (c || !c) || !b && (c && !c || !c && c)))) 
  = (a && (c || !c) || !a && (c && !c || !c && c)) :=
by
  rw [not_and, and_not, 
      Bool.or_false, Bool.and_false, 
      Bool.and_false, Bool.and_false, 
      Bool.false_or, Bool.or_false, Bool.or_false]
  cases b
  rw [Bool.not_false, Bool.false_and, 
      Bool.false_and, Bool.false_and, 
      Bool.and_false, Bool.or_false, 
      Bool.and_false, Bool.true_and, 
      Bool.false_or, Bool.true_and, 
      Bool.or_false]
  rw [Bool.not_true, Bool.false_and, 
      Bool.false_and, Bool.and_false, 
      Bool.false_and, Bool.false_or, 
      Bool.true_and, Bool.true_and,
      Bool.and_false, Bool.or_false,
      Bool.or_false]

theorem even_succ_succ_product (a b : Nat) :
  even ((succ (succ a)) * b) = even (a * b) :=
by
  match b with
  | 0 => rw [Nat.mul_zero, Nat.mul_zero]
  | succ 0 => 
    rw [Nat.mul_succ, Nat.mul_zero, 
        Nat.add_succ 0 (succ a),
        Nat.add_succ 0 a,
        Nat.mul_succ, Nat.mul_zero,
        even]
  | succ (succ b') => 
    rw [Nat.mul_succ, Nat.mul_succ, 
        Nat.mul_succ, Nat.mul_succ, 
        Nat.succ_mul, Nat.succ_mul,
        Nat.add_assoc, Nat.add_assoc,
        Nat.add_assoc, Nat.add_assoc,
        even_Add, even_Add, 
        even_Add, even_Add,
        even_Add, odd,
        odd_Add, odd_Add,
        odd_Add, odd_Add,
        odd_Add, odd_Add,
        odd_Add, even,
        odd, even_Add,
        even_Add, even_Add,
        even_Add, odd_Add,
        even, odd,
        Bool.and_self,
        Bool.and_self,
        odd_eq_not_even,
        odd_eq_not_even,
        odd_eq_not_even]
    rw [my_simp]

theorem even_product (x y : Nat) :
  even (x * y) = (even x || even y) :=
by
  induction x using Nat.strongInductionOn with
  | ind x' ih =>
    match x' with
    | 0 => rw [Nat.zero_mul, even, Bool.true_or]
    | 1 => rw [Nat.one_mul, even, Bool.false_or]
    | succ (succ k) => 
      rw [even, even_succ_succ_product, ih k (lt_succ_succ_self k)]
    
theorem even_list_product (l : ListNat) :
  even (product l) = Any even l :=
by
  induction l with
  | nil => rw [product, Any, even]
  | cons x xs h => 
    rw [product, Any, even_product, h]

-- Level 4.12
theorem even_sum_even_length_filter_odd (l : ListNat) :
  even (sum l) = even (length (filter odd l)) :=
by
  induction l with
  | nil => rw [sum, filter, length]
  | cons x xs h => 
    rw [filter, sum, even_Add, odd_eq_not_even, odd_eq_not_even, h]
    cases even x
    rw [if_pos Bool.not_false, 
        Bool.not_false,
        Bool.false_and,
        Bool.true_and,
        Bool.false_or,
        length,
        even_succ]
    rw [Bool.not_true,
        if_neg false_not_true,
        Bool.false_and,
        Bool.true_and, 
        Bool.or_false]

-- Level 4.13
theorem zero_Add_eq_zero_and_zero (a b : Nat) :
  Zero (a + b) = (Zero a && Zero b) :=
by
  cases a with
  | zero => 
    rw [Nat.zero_add]
    cases Zero b
    rw [Bool.and_false]
    rw [Bool.and_true, Zero]
  | succ a' => 
    rw [Nat.succ_add]
    cases Zero b
    rw [Zero, Bool.and_false]
    rfl
    rw [Bool.and_true, Zero, Zero]
    rfl

theorem zero_sum_all_zero (l : ListNat) :
  Zero (sum l) = All Zero l :=
by
  induction l with
  | nil => rw [sum, All, Zero]
  | cons x xs h => 
    rw [sum, All, zero_Add_eq_zero_and_zero, h]

-- Level 4.14
theorem zero_succ_false (a : Nat) :
  Zero (succ a) = false :=
by
  rw [Zero]
  rfl

theorem zero_Mult_eq_zero_or_zero (a b : Nat) :
  Zero (a * b) = (Zero a || Zero b) :=
by
  cases a with
  | zero => rw [Nat.zero_mul, or, Zero]
  | succ a' => 
    cases b with
    | zero => rw [Nat.mul_zero, Zero, Zero, Bool.or_true]
    | succ b' => 
      rw [Nat.mul_succ, 
          Nat.succ_mul, 
          zero_Add_eq_zero_and_zero, 
          zero_Add_eq_zero_and_zero, 
          Bool.and_assoc,
          zero_succ_false,
          zero_succ_false,
          Bool.and_false,
          Bool.and_false]
      rfl

theorem zero_product_any_zero (l : ListNat) :
  Zero (product l) = Any Zero l :=
by
  induction l with
  | nil => rw [product, Any, Zero]
  | cons x xs h => 
    rw [product, 
        Any, 
        zero_Mult_eq_zero_or_zero,
        h]

-- Level 4.15
theorem addNat_Add (n m : Nat) (l : ListNat) :
  addNat (n + m) l = addNat n (addNat m l) :=
by
  induction l with
  | nil => rw [addNat, addNat, addNat]
  | cons x xs h => 
    rw [addNat, h, 
        addNat, addNat, 
        Nat.add_assoc, 
        Nat.add_comm m n]

-- Level 4.16
theorem multNat_Mult (n m : Nat) (l : ListNat) :
  multNat (n * m) l = multNat n (multNat m l) :=
by
  induction l with
  | nil => rw [multNat, multNat, multNat]
  | cons x xs h => 
    rw [multNat, h, 
        multNat, multNat, 
        Nat.mul_assoc, 
        Nat.mul_comm m n]