# Task 10: Bilateral sum infrastructure for Chan's Ch 2 / Ch 4

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Chan's book repeatedly uses bilateral sums of the form
`∑_{j = -∞}^{∞} (...)` — Eq (2.1), Eq (3.15), Theorems 4.1, 4.2, 4.3,
4.4. To formalize finite truncations of these (and ultimately limits),
we need a bilateral sum primitive.

## Goal

Add to `QseriesFormalization/Basic.lean`, after `natSum`:

```lean
section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- Bilateral sum `∑_{j = -N}^{N} f j`. Implemented as
`f 0 + ∑_{k=1}^{N} (f k + f (-k))`. -/
def bilateralSum (f : Int → R) : Nat → R
  | 0 => f 0
  | Nat.succ n => bilateralSum f n + (f (n + 1 : Int) + f (-(n + 1 : Int)))

@[simp] theorem bilateralSum_zero (f : Int → R) : bilateralSum f 0 = f 0 := rfl

@[simp] theorem bilateralSum_succ (f : Int → R) (n : Nat) :
    bilateralSum f (Nat.succ n) =
      bilateralSum f n + (f (n + 1 : Int) + f (-(n + 1 : Int))) := rfl

theorem bilateralSum_congr {f g : Int → R} :
    ∀ n, (∀ j : Int, -n ≤ j ∧ j ≤ n → f j = g j) → bilateralSum f n = bilateralSum g n

theorem bilateralSum_neg (f : Int → R) (n : Nat) :
    bilateralSum (fun j => f (-j)) n = bilateralSum f n

end CommSemiring
```

Then in `QseriesFormalization/Chapter04.lean` (Part I Ch 4), add a
finite-truncation **statement** (not a proven theorem) for Euler's
pentagonal theorem (Theorem 4.2):

```lean
section Field

variable {R : Type*} [Field R]

/-- Truncated product side `∏_{n=1}^{N} (1 - q^n)` (Chan Theorem 4.2 LHS). -/
def eulerPentagonalProductTrunc (q : R) (N : Nat) : R :=
  qPochhammer q N

/-- Pentagonal-number index `j ↦ j(3j+1)/2` (Int → Nat for use as exponent). -/
def pentagonalIndex (j : Int) : Nat :=
  Int.toNat (j * (3 * j + 1) / 2)

/-- Truncated bilateral sum `∑_{j=-N}^{N} (-1)^j q^{j(3j+1)/2}` (Chan Theorem 4.2 RHS). -/
noncomputable def eulerPentagonalSeriesTrunc (q : R) (N : Nat) : R :=
  bilateralSum (fun j : Int => (-1 : R) ^ j.toNat * q ^ pentagonalIndex j) N

/-- Sanity: at `N = 0` both sides equal 1. -/
theorem euler_pentagonal_truncated_zero (q : R) :
    eulerPentagonalProductTrunc q 0 = 1 ∧ eulerPentagonalSeriesTrunc q 0 = 1

end Field
```

## Hints

- `bilateralSum_neg` proof: induction on `n`, using
  `(-(n+1 : Int)) = -((n+1 : Int))` and arithmetic on negatives.
- `euler_pentagonal_truncated_zero`: unfold defs, simplify
  `pentagonalIndex 0 = 0`, `(-1 : R)^0 = 1`, `q^0 = 1`. Done.
- For `pentagonalIndex`, the formula `j(3j+1)/2` is **always
  non-negative for integer `j`** (it's the j-th pentagonal number for
  positive j, and `(-j)(−3j+1)/2 = (3j²+j)/2 - j² + ...` — actually the
  generalized pentagonal `j(3j-1)/2` gives sequence `0, 1, 2, 5, 7, ...`
  for `j = 0, 1, -1, 2, -2, ...`). We cheat with `Int.toNat` to make
  the exponent a `Nat`. This is fine for the truncation since we'll
  only ever evaluate at indices where the formula is non-negative.

## Constraints

- **No `axiom`, no `sorry`, no `native_decide`** in the final code.
- `lake build` clean.
- Touch `Basic.lean` and `Chapter04.lean`.

## Deliverable

1. Modified files.
2. Reply file with status, diff summary, lake build final line.
