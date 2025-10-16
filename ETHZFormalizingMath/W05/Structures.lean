import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

universe u

/-
# Structures

Lean has an convenient way to do that

-/

structure NatPoint where
  x : ℕ
  y : ℕ



def double (p : NatPoint) := sorry


-- #reduce


-- ## Structures of a certain type



-- ## Why we use structures
/-
We  canuse structures to store algebraic data
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

-- ## Extending pre-existing structures

inductive Color where
  | red | green | blue

structure CPoint (α : Type u) extends NatPoint where
  c : Color

#check ({x:=2, y:=3, c:=Color.red } : CPoint _ )

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RGBPoint (α : Type u) extends NatPoint, RGBValue

structure RGPoint (α : Type u) extends RGBPoint α where
  noBlue : (blue = 0)




-- # Classes: The problem we are trying to solve


namespace Hidden

-- Classes define "types with certain properties"

def Add2Points (a b : NatPoint) : NatPoint := sorry

structure AdditiveType (α : Type*) where
  add : α → α → α


def PointAdd : AdditiveType (NatPoint) where
  add := sorry


def double {α : Type*} (s : AdditiveType α) (x : α) := s.add x x



end Hidden



def Nat_Point_Add (a b : Point ℕ) : Point ℕ := ⟨a.x+b.x, a.y+b.y⟩

instance AddPoint_from_Add(α : Type) [Add α] : Add (Point α) where add :=
  fun a b ↦ ⟨a.x+b.x, a.y+b.y⟩

instance MulPoint_from_Mul (α : Type) [Mul α] : Mul (Point α) where mul :=
  fun a b ↦ ⟨a.x*b.x, a.y*b.y⟩

instance ZeroPoint_from_Mul (α : Type) [Zero α] :
  Zero (Point α) where zero := Point.mk 0 0


#check (inferInstance : Mul (Point ℝ))
#synth Mul (Point ℝ)

def p1 : Point ℤ := ⟨1,-2⟩

#eval p1*0+p1*p1


-- # Example: Building the integers

variable (n:ℕ) (z:ℤ)

structure Integer where
  negative : Bool --
  num : Nat
  no_dupl : ¬(negative ∧ (num = 0)) -- We don't want 0  and -0

instance : OfNat Integer n where
  ofNat := { num := n, negative := False, no_dupl := by aesop }


#eval (2 : Integer)

instance : ToString Integer where
  toString r := if r.negative then s!"-{r.num}"else s!"{r.num}"


#eval (2 : Integer)

instance : Neg Integer where
  neg F :=  match F with
  | ⟨_,0,_⟩ => ⟨False, 0, by aesop⟩
  | ⟨s,a+1,_⟩ => ⟨!s, a+1, by simp⟩
