import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic

/-
Today's class is heavily based on the "Inductive Types" and "Induction"
chapters of "Theorem Proving in Lean"
-/

universe u v

/-
# Basic inductive types: Containers

The most basic inductive types are "containers" of finitely many possbilities

This is a weekday.
There are 7 different ways of constructing a weekday.
-/
inductive Weekday : Type where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
-- (Pretend the line below is not here until next week)
deriving Repr

-- Inductive types come with a "recursor/cases" map:
#print Weekday.casesOn
#print Weekday.recOn

-- Easier to understand if I specify the motive
#check Weekday.casesOn (motive := fun _↦ ℕ)

-- They are the opposite of the constructors
def numberOfDay : Weekday → ℕ := fun t ↦ Weekday.casesOn t 0 1 2 3 4 5 6


#check numberOfDay Weekday.wednesday


#check Weekday.sunday


/-
## Interlude: namespaces

The types have been stored in the namespace `Weekday`
- If we don't want to write Weekday.xxxx every time we can enter the namespace
-/


namespace Weekday

#check sunday

-- Inductive types have "different constructors are different" map
#check Weekday.noConfusion

-- I don't really need to write Weekday
#check noConfusion

example : monday ≠ sunday := Weekday.noConfusion


-- Given an inductive type we can use `match` to define functions by cases

def numberOfDay' (d : Weekday) :  ℕ :=
  match d with
  | sunday    => 0
  | monday    => 1
  | tuesday   => 2
  | wednesday => 3
  | thursday  => 4
  | friday    => 5
  | saturday  => 7

#eval numberOfDay' monday
-- Outside of the namespace we need to write Weekday.numberOfDay
-- #eval Weekday.numberOfDay Weekday.monday




def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday

#eval next (previous tuesday)  -- Weekday.tuesday


example : next (previous tuesday) = tuesday := rfl

-- Throw-back to last week: Proofs are elements of a type!
-- Should be a map that goes from Weekday to Prop
example (w : Weekday) : next (previous w) = w :=
  match w with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl

-- The tactic `cases` does the matching in tactic mode

example (w : Weekday) : next (previous w) = w := by
  cases w with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl

-- the <;> tactic: apply the same tactic while you can
example (w : Weekday) : next (previous w) = w := by
  cases w
  <;> rfl


end Weekday





/-
# More examples
-/

-- We will now reproduce a bunch of internal definitions in Lean
/- In order to do so, we will define a new namespace
   to not override the standard library -/

namespace Hidden


-- ## Examples: Booleans

inductive Bool where
  | T : Bool
  | F  : Bool
deriving Repr

open Bool

def and (a b : Bool) : Bool :=
  match a with
  | T  => b
  | F => F

def or (a b : Bool) : Bool :=
  match a with
  | T  => T
  | F => b

-- We can match on multiple things at once
example (a b : Bool) : and a b = and b a :=
  match a,b with
  | T,T => rfl
  | F,T => rfl
  | T,F => rfl
  | F,F => rfl

-- Or we can explode into cases
example (a b : Bool) : or a b = or b a := by
  cases b
  <;> cases a
  <;> rfl

#eval (and T T)




-- ## Examples depending on data: Products and sums

-- Cartesian products and direct sums are defined as inductibe types with parameters
inductive Sum (α : Type*) (β : Type*) where
  | inl : α → Sum α β
  | inr : β → Sum α β
deriving Repr

def injection (x : Sum ℕ ℤ) : ℤ :=
  match x with
  | Sum.inr y => 2*y
  | Sum.inl y => 2*y+1

-- We can test it
#eval injection (Sum.inl 2)
#eval injection (Sum.inr 2)

-- Context is important!
#eval (Sum.inl (β := ℤ) 2)


inductive Prod (α : Type*) (β : Type*)
  | mk : α → β → Prod α β

def Prod.fst {α β : Type*} (p : Prod α β) : α :=
  match p with
  | Prod.mk a _ => a

#print Prod.casesOn

def Prod.snd {α β : Type*} (p : Prod α β) : β := Prod.casesOn p (fun _ y ↦ y)

#eval Prod.snd (Prod.mk 2 3)



-- Of course all of this is composable

def SP_to_PS {a b c d : Type}
  (x : Sum (Prod a b) (Prod c d)) :
  (Prod (Sum a c) (Sum b d)) :=
  match x with
  | Sum.inl (Prod.mk x y) => Prod.mk (Sum.inl x) (Sum.inl y)
  | Sum.inr (Prod.mk x y) => Prod.mk (Sum.inr x) (Sum.inr y)


end Hidden
/- In general, we do not want to use our "custom" definition
 of sum and product but the one provided in Mathlib.
 We exit Hidden_Stuff to have access to the "normal" one
 -/


def SP_to_PS {a b c d : Type}
  (x : (a × b) ⊕ (c × d)) :
  (Prod (Sum a c) (Sum b d)) :=
  match x with
  | Sum.inl (s, t) => (Sum.inl s, Sum.inl t)
  | Sum.inr (s, t) => (Sum.inr s, Sum.inr t)


-- Since proofs are maps, same applies
-- Use by match x with in the proof
theorem SP_to_PS_injective
  {a b c d : Type}
  (x y : (a × b) ⊕ (c × d))
  (h : SP_to_PS x = SP_to_PS y) :
  x = y :=  by
  match x with
  | Sum.inl (a1, a2) =>
    match y with
    | Sum.inl (Prod.mk b1 b2) => simp [SP_to_PS] at *; exact h
    | Sum.inr _ => simp [SP_to_PS] at *;
  | Sum.inr (a1, a2) =>
    match y with
    | Sum.inl _ => simp [SP_to_PS] at *;
    | Sum.inr (b1, b2) => simp [SP_to_PS] at *; exact h




-- ## Examples: The Option inductive type

-- An useful example

namespace Hidden -- Again, to not override the library

inductive Option (α : Type*) where
  | none : Option α
  | some : α → Option α

-- Def option_upgrade:
def Opt {α : Type*} (f : α → Option α) : (Option α → Option α) :=
fun x ↦ match x with
  | Option.none => Option.none
  | Option.some x => f x

-- This will not work over ℝ, because equality is not decidable there
def safeDiv (x y : ℚ) :  (Option ℚ) :=
  match x,y with
  | _,0 => Option.none
  | x, y => Option.some (x/y)



-- ## Examples: Inductively defined props


-- Here is a philosophical difference comming from last week
-- Bool are not props
inductive False : Prop
-- False is a Prop with no constructor (empty)

inductive True : Prop where
  | intro : True
-- True is a Prop that is explicitly inhabited (by intro)
-- Rembember that by Proposition extensionality every proposition is the same

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b


noncomputable def false_imp_everything (α : Sort*) (x : False) : α := False.recOn (fun _ ↦ α) x
--- Google what's going on


-- ## Examples: Subtypes
-- A subtype of x is all the elements of x that satisfy some property

inductive Subtype (α : Type*) (p : α → Prop) where
  | mk : (a:α) → (p a) → Subtype α p

def NNR := Subtype ℝ (fun x ↦ (x≥ 0))

#check (Subtype.mk 2  (by simp_all only [ge_iff_le, Nat.ofNat_nonneg]) : NNR)
#check (⟨2, by simp_all only [ge_iff_le, Nat.ofNat_nonneg]⟩ : NNR)
-- Proof extensionality is crucial here!



/-
# Structures

Very often we want inductive types with a single constructor.
Lean has an convenient way to do that

-/

structure RealPoint where
  x : ℝ
  y : ℝ

#check RealPoint.mk
#check RealPoint.mk 2 3

structure Point (T : Type*) where
  x : T
  y : T

def mypoint := Point.mk (2:ℕ) 3

def mypoint2 := Point where
  x := 2
  y := 3


#print mypoint

#eval Point.x mypoint


/-
We use structures to store algebraic data
-/
structure Semigroup' where
  carrier : Type*
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

/-
Remember two weeks ago:
def nilrad : Ideal R where
  ...
-/



-- # Further realms

-- ## Mutually inductive types

mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end

-- This is useful to define "trees" of arbitrary length
mutual
    inductive Tree (α : Type u) where
      | node : α → TreeList α → Tree α

    inductive TreeList (α : Type u) where
      | nil  : TreeList α
      | cons : Tree α → TreeList α → TreeList α
end

-- But Lean is smart, and knows how to create the intermediate
-- inductive types as needed
inductive Tree' (α : Type u) where
  | mk : α → List (Tree' α) → Tree' α

-- ## Inductive Families

inductive Vect (α : Type*) : ℕ → Type _ where
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)

end Hidden




-- # Constructing our own natural numbers in Lean

namespace Hidden

inductive Nat where
 | zero : Nat
 | succ : Nat → Nat
deriving Repr


namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

-- Magic (Next week) that lets us use `+` and `0` for our version of Nat
instance : Add Nat where add := add
instance : Zero Nat where zero := zero

theorem add_zero (m : Nat) : m + 0 = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

#check Nat.recOn

-- we could try to brute force build it but it won't work
-- def add' (m n : Nat) : Nat := Nat.recOn n m (fun n mplusn ↦ succ mplusn)

-- Now we can redo (one!) of the proofs from the first day while understanding what's going on

theorem zero_add (m : Nat) : zero + m = m :=
  Nat.recOn
    m
    (show 0+0 = 0 by rfl)
    (show  ∀ (a : Nat), zero + a = a → zero + a.succ = a.succ by
      intro a ha;
      rw[add_succ zero a];
      simp_all  )

example (m : Nat) : zero + m = m := by
  induction m using Nat.recOn
  case zero => rfl
  case succ a ha =>
    rw[add_succ]
    congr
#check Nat.recOn

end Nat
end Hidden

-- Normal natural numbers, not hidden ones

def divides (x n : ℕ) : Prop := ∃ k: ℕ , n = x*k

theorem divides_trans {a b c : ℕ} :
  divides a b → divides b c → divides a c := by
  intro ha hb
  rcases ha with ⟨ka, hka⟩
  rcases hb with ⟨kb, hkb⟩
  use ka*kb
  rw [hkb,hka]
  rw [mul_assoc]

theorem divides_self (a : ℕ) : divides a a := by
  use 1
  rw [mul_one]

theorem divides_smaller {a b : ℕ} (h0 : b > 0) (hd : divides a b) : a ≤ b
  := by
  rcases hd with ⟨k,hk⟩
  have kpos: k>0 := by grind
  rw [hk]
  aesop

def isPrime (p : ℕ) : Prop := (p>1)∧(∀ x>1,divides x p → x=p)

-- ## Interlude: Subtypes are an inductive type
-- A subtype of x is all the elements of x that satisfy some property

namespace Hidden

inductive Subtype' (α : Type*) (p : α → Prop) where
  | mk : (a:α) → (p a) → Subtype' α p

def NNR' := Subtype ℝ (fun x ↦ (x≥ 0))

#check (Subtype.mk 2  (by simp_all only [ge_iff_le, Nat.ofNat_nonneg]) : NNR)
#check (⟨2, by simp_all only [ge_iff_le, Nat.ofNat_nonneg]⟩ : NNR)
-- Proof extensionality is crucial here!

end Hidden

#check Subtype

def P:= {n: ℕ// n>0}
#check P

#check (⟨1, by aesop⟩ : P)

--- End interlude

theorem not_prime_has_factors
  (n : ℕ) (h1 : n > 1) (hn : ¬ isPrime n) :
  ∃ m>1, divides m n ∧ m<n := by
  convert_to ∃ m>1, divides m n ∧ m≠n
  · funext a
    simp_all only [gt_iff_lt, ne_eq, eq_iff_iff, and_congr_right_iff]
    intro a_1 a_2
    have hle: a ≤ n := by
      apply divides_smaller (by omega) a_2
    omega
  by_contra hf

  have hp: (∀ m>1, divides m n → m=n):= by aesop
  exact hn ⟨h1, hp⟩


#check Nat.recOn
#check Nat.strongRec

theorem my_strong_recursion
  (p : ℕ → Prop)
  (ind : (n : ℕ) → ((m : ℕ) → m < n → p m) → p n)
  (t : ℕ) :
  p t := by
  have stronger : ∀ n < t+1, p n := by
    induction t
    case zero =>
      intro n hn
      have nzero : n=0 := by omega
      specialize ind 0
      simp_all only [not_lt_zero', IsEmpty.forall_iff, forall_const]
    · case succ k hk =>
      intro n hn
      specialize ind n
      have pre_goal: (∀ m < n, p m) := by grind
      exact ind pre_goal
  simp_all only [lt_add_iff_pos_right, zero_lt_one]

theorem prime_divides (n : ℕ) (hn : n > 1) :
  ∃ p, isPrime p ∧ divides p n := by
  induction n using Nat.strongRec
  case ind n hind =>
    by_cases self_prime : isPrime n
    case pos =>
      use n
      exact ⟨ self_prime,divides_self n⟩
    case neg =>
    have exists_m := not_prime_has_factors n hn self_prime
    rcases exists_m with ⟨a,b⟩
    specialize hind a b.2.2 b.1
    rcases hind with ⟨ p, hp⟩
    use p
    constructor
    · exact hp.1
    · apply divides_trans hp.2 b.2.1



-- At this point you could do the whole NNG on lean,
-- luckily for you, you don't need to..

-- # Back to pattern matching: structural recursion

open Nat
variable (x : Nat) {α β : Type}

-- Lean has a powerful pattern-matching engine

def swap (p : α × β) : β × α :=
  match p with
  | (a, b) => (b, a)


def sub1 : Nat → Nat
  | 0     => 0
  | x + 1 => x

def isZero : Nat → Bool
  | 0     => true
  | _ + 1 => false

def factorial : ℕ → ℕ
  | 0 => 1
  | n+1 => (n+1)*(factorial n)

#eval factorial 5

def sub2 : Nat → Nat
  | 0     => 0
  | 1     => 0
  | x + 2 => x

example : (x : ℕ) → sub1 (sub1 x )= sub2 x
  | 0 =>  rfl
  | 1 =>  rfl
  | _+2 =>  rfl

def foo : Nat → Nat → Nat
  | 0,     n     => n
  | m + 1, 0     => foo m 0
  | m + 1, n + 1 => m+n


-- Which also applies to propositions
#print And

example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h₁ h₂ => And.intro h₂ h₁

#print Exists
example (p q : α → Prop) :
        (∃ x, p x ∨ q x) →
        (∃ x, p x) ∨ (∃ x, q x)
  | Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
  | Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)

namespace Nat
-- congrArg f a=b -> fa = fb
theorem zero_add'' : ∀ n, Nat.add Nat.zero n = n
  | Nat.zero   => rfl
  | Nat.succ n => congrArg Nat.succ (Nat.zero_add'' n)
end Nat


-- # Induction beyond the natural numbers

-- ## Examples: Lists

namespace Hidden

inductive List (α : Type*) where
| nil  : List α
| cons : α → List α → List α

namespace List
variable {α : Type*}

def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
 rfl
theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
 rfl
------
theorem append_nil (as : List α) :
    append as nil = as :=
    by
    induction as
    case nil => rfl
    case cons a la ha => rw[cons_append, ha]


def length (a : List α) : ℕ :=
  match a with
  | nil => 0
  | cons _ la => 1 + length la

theorem len_append (a b : List α) :
  length (append a b) = length a + length b
  := by
  induction a
  case nil => rw [nil_append]; simp [length]
  case cons a la IH => simp [cons_append, length, IH]; omega

end List

end Hidden

-- # Examples: Trees

inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree


def Depth (t : BinaryTree):ℕ := match t with
  | BinaryTree.leaf => 0
  | BinaryTree.node t1 t2 => 1 + max (Depth t1) (Depth t2)



namespace BinaryTree

#eval Depth (node (node leaf (node leaf leaf)) leaf)


def Isomorphic (t1 t2 : BinaryTree) : Prop :=
  match t1  with
  | leaf  => match t2 with
    | leaf => true
    | node _ _ => false
  | node n1 n2 => match t2 with
    | leaf => false
    | node m1 m2 => (Isomorphic n1 m1)∧(Isomorphic n2 m2)∨
                    (Isomorphic n1 m2)∧(Isomorphic n2 m1)

#reduce Isomorphic (node (node leaf (node leaf leaf)) leaf)
                 (node leaf (node leaf (node leaf leaf)))

example (t1 t2 : BinaryTree) (HI : Isomorphic t1 t2) : Depth t1 = Depth t2 := by
  induction t1 generalizing t2
  case leaf =>
    cases t2
    case leaf => tauto
    case node _ _ => simp [Isomorphic] at HI
  case node l1 l2 I1 I2 =>
    cases t2
    case leaf => simp [Isomorphic] at HI
    case node n1 n2 =>
      simp [Isomorphic] at HI
      cases HI
      case inl h =>
        rcases h with ⟨ h1, h2⟩
        apply I1 at h1
        apply I2 at h2
        unfold Depth
        rw [h1, h2]
      case inr h =>
        rcases h with ⟨h1, h2⟩
        apply I1 at h1
        apply I2 at h2
        unfold Depth
        rw [h1, h2]
        rw [Nat.max_comm]

example (t1 t2 : BinaryTree) (HI : Isomorphic t1 t2) : Isomorphic t2 t1 := by
  induction t1 generalizing t2
  case leaf =>
    cases t2
    case leaf =>
      tauto
    case node t1 t2 => simp [Isomorphic] at  HI
  case node =>
    cases t2
    case leaf => simp [Isomorphic] at HI
    case node t1 t2 h1 h2 t3 t4 =>
      simp [Isomorphic] at *
      cases HI
      case inl h => exact Or.inl ⟨h1 t3 h.1, h2 t4 h.2⟩
      case inr h => exact Or.inr ⟨h2 t3 h.2, h1 t4 h.1⟩



end BinaryTree
