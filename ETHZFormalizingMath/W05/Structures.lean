import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib

universe u

/-
# Structures

Lean has an convenient way to do that

-/

structure NatPoint where
  x : ℕ
  y : ℕ


structure Point (T : Type*) where
  x : T
  y : T
deriving Repr

def p := Point.mk 1 2


/-
We use structures to store algebraic data
-/
structure Semigroup' where
  carrier : Type*
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

/-
Remember three weeks ago:
def nilrad : Ideal R where
  ...
-/

inductive Color where
  | red | green | blue
deriving Repr

-- # extends structures to build more complex structures

structure CPoint (α : Type u) extends Point α where
  c : Color
deriving Repr

def mypoint := ({x:=2, y:=3, c:=Color.red } : CPoint _)
#eval mypoint
#eval CPoint.toPoint mypoint



structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RGBPoint (α : Type u) extends Point α, RGBValue

structure RGPoint (α : Type u) extends RGBPoint α where
  noBlue : (blue = 0)

def origin := {x:=0, y:=0 : Point ℕ}

-- use "with" syntax to extend a pre-existing object
def yelloworigin : RGBPoint ℕ := sorry

def noblueorigin : RGPoint ℕ := sorry



-- # Classes: The problem we are trying to solve


namespace Hidden

-- Let's say you want a function that works whenever we have addition

structure HasAddition (α : Type*) where
  add : α → α → α

def double {α : Type*} (s : HasAddition α) (x : α) := s.add x x

def PointsHaveAddition : HasAddition (Point ℕ) where
  add : (Point ℕ → Point ℕ → Point ℕ) := sorry

#check PointsHaveAddition

#reduce double (PointsHaveAddition) (Point.mk 1 2)

-- Classes let you remember that.

class AddType (α : Type*) where
  add : α → α → α

instance PointsHaveAddition' : AddType (Point ℕ) where
  add :=  PointsHaveAddition.add

def double' {α : Type*} [AddType α] (a : α) :α
  := AddType.add a a

#reduce double' (Point.mk 1 2)

end Hidden


-- ## Parametrized Instances

def p1 : Point ℤ := ⟨1,-2⟩

def Nat_Point_Add (a b : Point ℕ) : Point ℕ := ⟨a.x+b.x, a.y+b.y⟩

instance AddPoint_from_Add (α : Type) [Add α] : Add (Point α) where add :=
  fun a b ↦ ⟨a.x+b.x, a.y+b.y⟩

#eval Add.add p1 p1
#eval p1 + p1


instance MulPoint_from_Mul (α : Type) [Mul α] : Mul (Point α) where mul :=
  fun a b ↦ ⟨a.x*b.x, a.y*b.y⟩


#check (inferInstance : Mul (Point ℝ))
#synth Mul (Point ℝ)



-- Zero instance


-- #eval p1*0+p1*p1

-- ## Most parametrized instances already implemented

-- What happens if we consider *tuples of points*?

#check (p1,p1)+(p1,p1)

#synth Add ((Point ℝ)×(Point ℝ))

-- You can tell Lean "If A is add and B is add, A×B is add"
instance Product_add (α : Type) (β : Type) [Add α] [Add β] : Add ((Point α)×(Point β))  where add :=
  fun (a1,a2) (b1,b2) ↦ ⟨⟨a1.x+b1.x, a1.y+b1.y⟩,⟨a2.x+b2.x, a2.y+b2.y⟩⟩


-- # The integers

variable (n : ℕ) (z : ℤ)

structure Integer where
  negative : Bool --
  abs : Nat
  no_dupl : ¬(negative ∧ (abs = 0)) -- We don't want 0  and -0

-- There is a class Called OfNat X n which tells you
-- "natural number n can be thought of as an element of type x"
instance : OfNat Integer n where
  ofNat := { abs := n, negative := False, no_dupl := by aesop }


#eval (2 : Integer)

-- There is a class called ToString for things that have a
-- string reperesentation. Print calls this!

instance : ToString Integer where
  toString r := if r.negative then s!"-{r.abs}"else s!"{r.abs}"


#eval (2 : Integer)


instance : Neg Integer where
  neg F :=   sorry

-- What tactic should I use?
-- 1. If the proof is "very tedious application of logical rules", use grind
-- 2. If the proof is transitivity + chaining of inequalities use gcongr
-- 3. If it "should be obvious" but uses complicated lemas use aesop
-- 4. If you want to bring things to a "normal form" use simp

instance : PartialOrder Integer where
  le x y := ((x.negative ∧ (¬ y.negative))∨
            ((¬ x.negative) ∧ (¬ y.negative) ∧ (x.abs ≤ y.abs))∨
            (x.negative ∧ y.negative ∧ (y.abs ≤ x.abs)))


-- ## Should I use classes or records?

#print Semigroup
#print Semigroup'


-- ## Dependency hyerarchies

class Group' (A : Type) extends Semigroup A, Inv A where


-- ### Dependency Hyerarchies go deep:
-- The whole hierarchy of Algebra, quite literally
-- https://github.com/leanprover-community/mathlib4/blob/a19486351878a13e2737bf5a838468e244624787/Mathlib/Algebra/Ring/Defs.lean#L142-L143


variable (R : Type*) [Ring R]

def nilrad : Ideal R where
  carrier := sorry
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

-- ## Coercion
-- There is a type class called Coe which records "Things that can be coerced into"
instance (α : Type) : Coe (Point α) (α × α) where
  coe a := (a.x, a.y)

#check (Point.mk 2 2 : ℕ × ℕ)
