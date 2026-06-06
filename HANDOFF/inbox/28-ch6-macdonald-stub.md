# Task 28: Ch6 — Macdonald's identities stub (Part I)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Chan Ch 6 covers Macdonald identities (`η^{t²-1}` formulas and JTP as
the simplest case). Heavy machinery (affine Lie algebras, Weyl-Kac
denominator). For now we just want a structural stub.

## Goal

Replace `QseriesFormalization/Chapter06.lean` with:

```lean
import QseriesFormalization.Basic

namespace QseriesFormalization
namespace PartI
namespace Ch06

section Field

variable {R : Type*} [Field R]

/-- Truncated Dedekind-η-style product `q^{1/24} ∏_{m=1}^N (1 - q^m)`.
We omit the q^{1/24} prefactor here (it requires fractional powers);
this defines the polynomial part `η_red q N := (q;q)_N`. -/
noncomputable def dedekindEtaTrunc (q : R) (N : Nat) : R :=
  qPochhammer q N

/-- Sanity: η_red q 0 = 1. -/
@[simp] theorem dedekindEtaTrunc_zero (q : R) :
    dedekindEtaTrunc q 0 = 1 := rfl

/-- Sanity: η_red q (N+1) = (1 - q^{N+1}) · η_red q N. -/
theorem dedekindEtaTrunc_succ (q : R) (N : Nat) :
    dedekindEtaTrunc q (N + 1) =
      dedekindEtaTrunc q N * (1 - q ^ (N + 1)) := by
  rfl

end Field

end Ch06
end PartI
end QseriesFormalization
```

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter06.lean`.

## Deliverable

1. Modified `Chapter06.lean`.
2. Reply file with status, lake build final line.
