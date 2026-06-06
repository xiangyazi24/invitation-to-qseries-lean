# Task 33: Ch14 — Lost Notebook + cranks stub (Part III)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Chan Ch 14 covers a remarkable identity from Ramanujan's Lost Notebook
plus the **crank** statistic on partitions (introduced by Andrews-Garvan
to combinatorially explain the p(11n+6) ≡ 0 (mod 11) congruence).

## Goal

Replace `QseriesFormalization/Chapter14.lean` with:

```lean
import QseriesFormalization.Basic

namespace QseriesFormalization
namespace PartIII
namespace Ch14

/-- Crank of a partition: for a partition λ with no ones, crank = largest part.
For a partition with at least one 1, crank = #(parts > number of ones) − #(ones).
This is the placeholder definition; concrete implementation TODO. -/
def crankPlaceholder (n : Nat) : Int := 0

/-- Sanity: placeholder zero. -/
@[simp] theorem crankPlaceholder_zero : crankPlaceholder 0 = 0 := rfl

end Ch14
end PartIII
end QseriesFormalization
```

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter14.lean`.

## Deliverable

Modified `Chapter14.lean` + reply file.
