# Task 35: Ch18 — t-cores stub (Part IV)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Chan Ch 18 covers t-core partitions — partitions whose Young diagram
has no removable t-hooks. The number of t-cores has a simple
generating function `∏_{n≥1} (1-q^{tn})^t / (1-q^n)`.

## Goal

Replace `QseriesFormalization/Chapter18.lean` with:

```lean
import QseriesFormalization.Basic

namespace QseriesFormalization
namespace PartIV
namespace Ch18

section Field

variable {R : Type*} [Field R]

/-- Truncated t-core generating function numerator: `∏_{n=1}^N (1 - q^{tn})^t`. -/
noncomputable def tCoreNumeratorTrunc (t : Nat) (q : R) : Nat → R
  | 0 => 1
  | Nat.succ n => tCoreNumeratorTrunc t q n * (1 - q ^ (t * (n + 1))) ^ t

/-- Truncated t-core generating function denominator: `∏_{n=1}^N (1 - q^n)`. -/
noncomputable def tCoreDenominatorTrunc (q : R) (N : Nat) : R :=
  qPochhammer q N

/-- Truncated t-core ratio. -/
noncomputable def tCoreRatioTrunc (t : Nat) (q : R) (N : Nat) : R :=
  tCoreNumeratorTrunc t q N / tCoreDenominatorTrunc q N

@[simp] theorem tCoreNumeratorTrunc_zero (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 0 = 1 := rfl

@[simp] theorem tCoreDenominatorTrunc_zero (q : R) :
    tCoreDenominatorTrunc q 0 = 1 := rfl

end Field

end Ch18
end PartIV
end QseriesFormalization
```

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter18.lean`.

## Deliverable

Modified `Chapter18.lean` + reply file.
