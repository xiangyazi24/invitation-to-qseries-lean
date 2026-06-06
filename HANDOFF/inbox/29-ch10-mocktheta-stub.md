# Task 29: Ch10 — Mock theta functions stub (Part II excursus)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Chan Ch 10 is an excursus on Ramanujan's mock theta functions —
historical and motivational. Just a structural stub.

## Goal

Replace `QseriesFormalization/Chapter10.lean` with:

```lean
import QseriesFormalization.Basic

namespace QseriesFormalization
namespace PartII
namespace Ch10

section Field

variable {R : Type*} [Field R]

/-- Ramanujan's third-order mock theta `f(q) := ∑_{n=0}^N q^{n²} / (-q;q)_n²`,
finite truncation. -/
noncomputable def ramanujanMockF_trunc (q : R) (N : Nat) : R :=
  natSum (fun n => q ^ (n * n) / (qPoch (-q) q n) ^ 2) N

/-- N=0 sanity: ramanujanMockF_trunc q 0 = 1. -/
@[simp] theorem ramanujanMockF_trunc_zero (q : R) :
    ramanujanMockF_trunc q 0 = 1 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]

end Field

end Ch10
end PartII
end QseriesFormalization
```

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter10.lean`.

## Deliverable

1. Modified `Chapter10.lean`.
2. Reply file with status, lake build final line.
