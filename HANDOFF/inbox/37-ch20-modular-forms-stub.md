# Task 37: Ch20 — modular forms excursus stub (Part IV)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Chan Ch 20 is an excursus on modular forms and their relation to
partition congruences.

## Goal

Replace `QseriesFormalization/Chapter20.lean` with:

```lean
import QseriesFormalization.Basic

namespace QseriesFormalization
namespace PartIV
namespace Ch20

section Field

variable {R : Type*} [Field R]

/-- The Dedekind eta function (formal placeholder, polynomial form
without the q^{1/24} prefactor). -/
noncomputable def etaPolyPart (q : R) (N : Nat) : R :=
  qPochhammer q N

/-- Sanity: η_poly q 0 = 1. -/
@[simp] theorem etaPolyPart_zero (q : R) : etaPolyPart q 0 = 1 := rfl

/-- The discriminant Δ(q) = q · η^24, polynomial part. -/
noncomputable def discriminantPolyPart (q : R) (N : Nat) : R :=
  q * etaPolyPart q N ^ 24

end Field

end Ch20
end PartIV
end QseriesFormalization
```

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter20.lean`.

## Deliverable

Modified `Chapter20.lean` + reply file.
