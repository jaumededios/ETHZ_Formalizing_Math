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

-- They are the opposite of the constructors
def numberOfDay : Weekday → ℕ := fun t ↦ Weekday.casesOn t 0 1 2 3 4 5 6



/-
## Interlude: namespaces

The types have been stored in the namespace `Weekday`
- If we don't want to write Weekday.xxxx every time we can enter the namespace
-/


namespace Weekday

#check sunday

-- Inductive types have "different constructors are different" map
#check Weekday.noConfusion


example : monday ≠ sunday := sorry


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



example : next (previous tuesday) = tuesday := sorry

-- Throw-back to last week: Proofs are elements of a type!
-- Should be a map that goes from Weekday to Prop

example (w : Weekday) : next (previous w) = w := sorry

-- The tactic `cases` does the matching in tactic mode

example (w : Weekday) : next (previous w) = w := sorry

-- the <;> tactic: apply the same tactic while you can
example (w : Weekday) : next (previous w) = w := sorry


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

namespace Bool

def and (a b : Bool) : Bool := sorry

def or (a b : Bool) : Bool := sorry

-- We can match a,b with | T,F on multiple things at once
example (a b : Bool) : and a b = and b a := sorry

-- Or we can explode into cases
example (a b : Bool) : or a b = or b a := sorry

end Bool


-- ## Examples depending on data: Products and sums

-- Cartesian products and direct sums are defined as inductibe types with parameters
inductive Sum (α : Type*) (β : Type*) where
  | inl : α → Sum α β
  | inr : β → Sum α β
deriving Repr

-- Some example
def injection (x : Sum ℕ ℤ) : ℤ :=
  match x with
  | Sum.inr y => 2*y
  | Sum.inl y => 2*y+1

-- We can test it

inductive Prod (α : Type*) (β : Type*)
  | mk : α → β → Prod α β

def Prod.fst {α β : Type*} (p : Prod α β) : α :=
  match p with
  | Prod.mk a _ => a

#print Prod.casesOn
-- we can use casesOn to build second if we want
def Prod.snd {α β : Type*} (p : Prod α β) : β := sorry

#eval Prod.snd (Prod.mk 2 3)



-- Of course all of this is composable

def SP_to_PS {a b c d : Type}
  (x : Sum (Prod a b) (Prod c d)) :
  (Prod (Sum a c) (Sum b d)) := sorry


end Hidden
/- In general, we do not want to use our "custom" definition
 of sum and product but the one provided in Mathlib.
 We exit Hidden_Stuff to have access to the "normal" one
 -/


def SP_to_PS {a b c d : Type}
  (x : (a × b) ⊕ (c × d)) :
  (Prod (Sum a c) (Sum b d)) := sorry

-- Since proofs are maps, same applies
-- Use by match x with in the proof
theorem SP_to_PS_injective
  {a b c d : Type}
  (x y : (a × b) ⊕ (c × d))
  (h : SP_to_PS x = SP_to_PS y) :
  x = y :=  sorry



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

-- Build a safe division using Options
def safeDiv (x y : ℚ) :  (Option ℚ) := sorry
-- This will not work over ℝ, because equality is not decidable there


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

-- Since false has no constructors, we can use False.casesOn
#check False.casesOn
def false_imp_everything (α : Sort*) (x : False) : α := sorry



-- ## Examples: Subtypes
-- A subtype of x is all the elements of x that satisfy some property

inductive Subtype (α : Type*) (p : α → Prop) where
  | mk : (a:α) → (p a) → Subtype α p

def NNR := Subtype ℝ (fun x ↦ (x≥ 0))


-- Proof extensionality is crucial here!



/-
# Structures

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
