import Mathlib




-- # The Ext tactic
-- Two structures are equal iff their components are equal
-- Two functions are equal iff they map every input to the same output
-- Two sets are equal iff they contain the same elements

variable (n : ℕ) (z : ℤ)

@[ext]
structure Integer where
  negative : Bool --
  abs : Nat
  no_dupl : ¬(negative ∧ (abs = 0)) -- We don't want 0  and -0


instance : OfNat Integer n where
  ofNat := { abs := n, negative := False, no_dupl := by aesop }


#eval (2 : Integer)

-- There is a class called ToString for things that have a
-- string reperesentation. Print calls this!

instance : ToString Integer where
  toString r := if r.negative then s!"-{r.abs}"else s!"{r.abs}"


#eval (2 : Integer)


instance : Neg Integer where
  neg x := match x with
    | {abs := 0, negative := _, no_dupl := _ } =>
        { abs := 0, negative := False, no_dupl := by simp }
    | {abs := a+1, negative := n, no_dupl := _ } =>
        { abs := a+1, negative := ¬ n, no_dupl := by simp }


instance : PartialOrder Integer where
  le x y := ((x.negative ∧ (¬ y.negative))∨
            ((¬ x.negative) ∧ (¬ y.negative) ∧ (x.abs ≤ y.abs))∨
            (x.negative ∧ y.negative ∧ (y.abs ≤ x.abs)))
  le_refl := by
    intro a
    grind
  le_antisymm := by sorry
  le_trans := by
    intro a b c
    grind

-- # Coercions

structure Point (T : Type*) where
  x : T
  y : T
deriving Repr

-- # Coe

-- There is a type class called Coe which records "Things that can be coerced into"

@[coe]
def toProduct {α : Type} (a : Point α) : (α × α ) := (a.x, a.y)

instance (α : Type) : Coe (Point α) (α × α) where
  coe := toProduct

#check (Point.mk 2 2 : ℕ × ℕ)

-- # CoeFun

structure InjectiveFunction (α β : Type*) where
  function : α → β
  injective: ∀ a₁ a₂ :α, function a₁= function a₂ → a₁ =a₂


instance (α β : Type*) : CoeFun (InjectiveFunction α β) (fun _ ↦ α → β) where
  coe injFun := injFun.function

-- # CoeSort

structure Monoid' where
  Carrier : Type*
  [carrier_mul: Mul Carrier]
  mul_assoc : ∀ a b c : Carrier, (a*b)*c = a* (b*c)

instance : CoeSort Monoid' Type where
  coe m := m.Carrier

def natMonoid : Monoid' where
  Carrier   := ℕ
  mul_assoc := by bound

#check ((2:ℕ) : natMonoid)


-- # Notation
-- How do you come up with your own notation?

structure Ball where
  x : ℚ
  r : ℚ
  rpos: r≥0


notation "(" a " ± " b ")" => (Ball.mk a b (by bound))

#eval (2.1±0.3)

instance : ToString Ball where
  toString r := s!"{r.x} ± {r.r}"

#eval (2.1±0.3)
