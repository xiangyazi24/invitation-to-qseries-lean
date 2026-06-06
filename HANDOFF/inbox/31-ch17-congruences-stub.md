# Task 31: Ch17 — Ramanujan congruences I stub (Part IV)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Chan Ch 17 proves Ramanujan's three classic partition congruences:
- `p(5n + 4) ≡ 0 (mod 5)`
- `p(7n + 5) ≡ 0 (mod 7)`
- `p(11n + 6) ≡ 0 (mod 11)`

via analytical (q-series) methods.

## Goal

Replace `QseriesFormalization/Chapter17.lean` with concrete *finite*
checks using our proved partition values:

```lean
import QseriesFormalization.Basic
import QseriesFormalization.Chapter01

namespace QseriesFormalization
namespace PartIV
namespace Ch17

open QseriesFormalization.Ch01 (partitionCount)

/-- Concrete check for `p(5n+4) ≡ 0 (mod 5)` at n=0: p(4) = 5. -/
theorem partition_5n_plus_4_mod_5_n_zero :
    partitionCount (5 * 0 + 4) % 5 = 0 := by
  simp [partitionCount_four]

/-- Concrete check at n=1: p(9) = 30 = 6·5, divisible by 5. -/
theorem partition_5n_plus_4_mod_5_n_one :
    partitionCount (5 * 1 + 4) % 5 = 0 := by
  simp [partitionCount_nine]

/-- Concrete check for `p(7n+5) ≡ 0 (mod 7)` at n=0: p(5) = 7. -/
theorem partition_7n_plus_5_mod_7_n_zero :
    partitionCount (7 * 0 + 5) % 7 = 0 := by
  simp [partitionCount_five]

/-- Concrete check at n=1: p(12) = 77 = 11·7. (Need partitionCount_twelve!
Sub-deliverable: if you can't access p(12), drop this theorem and note it.) -/
-- theorem partition_7n_plus_5_mod_7_n_one : … TODO once p(12) is known.

/-- Concrete check for `p(11n+6) ≡ 0 (mod 11)` at n=0: p(6) = 11. -/
theorem partition_11n_plus_6_mod_11_n_zero :
    partitionCount (11 * 0 + 6) % 11 = 0 := by
  simp [partitionCount_six]

end Ch17
end PartIV
end QseriesFormalization
```

These are concrete finite verifications of the famous Ramanujan
congruences using our case-analyzed partitionCount values. The general
theorem (for all n) requires more machinery and is deferred.

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter17.lean`.

## Deliverable

1. Modified `Chapter17.lean`.
2. Reply file with status, lake build final line.
