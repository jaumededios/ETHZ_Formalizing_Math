
# Some more tactics and tools to clean up

## The `rcases` tactic

The `rcases` tactic recursively breaks down structured hypotheses.
It is like `cases`, but with **pattern-matching** and **nesting**.

### Common Patterns

| Structure        | Example hypothesis            | `rcases` usage                                | Resulting names                       |
|------------------|--------------------------------|-----------------------------------------------|---------------------------------------|
| Conjunction (∧)  | `h : p ∧ q`                   | `rcases h with ⟨hp, hq⟩`                      | `hp : p`, `hq : q`                    |
| Existential (∃)  | `h : ∃ x, P x`                 | `rcases h with ⟨x, hx⟩`                       | `x : α`, `hx : P x`                   |
| Nested (∃ ∧)     | `h : ∃ x, P x ∧ Q x`           | `rcases h with ⟨x, ⟨hx, hq⟩⟩`                 | `x : α`, `hx : P x`, `hq : Q x`       |
| Disjunction (∨)  | `h : p ∨ q`                   | `rcases h with hp \| hq`                       | Case split: `hp : p` or `hq : q`      |
| Ignore part      | `h : ∃ x, P x ∧ Q x`           | `rcases h with ⟨x, ⟨hx, _⟩⟩`                  | Ignore `Q x` proof                    |
| Multiple hyps    | `h₁ : p ∧ q, h₂ : r ∨ s`      | `rcases h₁ with ⟨hp, hq⟩; rcases h₂ with hr \| hs` | Break both at once                |
| Deep recursion   | `h : ∃ x, P x ∧ (Q x ∧ True)` | `rcases h -! with ⟨x, hx, hq, _⟩`              | Fully destruct into 4 parts            |

---

## The `case` vs `\.` vs `brute force`.

```
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp
```

# The Nilradical

**Theorem** The Nilradical is an ideal contained in all prime ideals.


- The nilradical is an ideal
  1. The nilradical is the set of nilpotent elements elements (for which there is an n such that x^n = 0)
  2. The nilradical is closed under multiplication in R
  3. The nilradical is closed under addition

- The Nilradical is contained in all ideals

**Random facts**

- Note how in the definition we are using $\le$ isntead of $\subseteq$. This is the "Ideal" order relation.


## Classes

Classes are ways of attaching "data" to a type. Examples:

A Semigroup is a type /set/ with extra attached information:
 - A multiplication operation
 - Which is associatiove

## Braces

Braces are a way of "hiding" variables in Lean.

When needed, one can also explicitly name variables `sum3 (x := 1) (y := 3) (z := 8)`


# Continuous functions

Lean has a definition of a metric on a product space automatically (FIND).

```simp [Prod.dist_eq] at *```