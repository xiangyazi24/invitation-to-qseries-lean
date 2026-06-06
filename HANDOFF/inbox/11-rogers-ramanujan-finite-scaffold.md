# Task 11: Rogers-Ramanujan identities — finite truncation scaffold (Chan Ch 7-9)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

The Rogers-Ramanujan identities (Chan Eq 1.2, p. 1) are

```
∑_{n=0}^∞ q^{n² + a n} / (q;q)_n
  = ∏_{n=1}^∞ 1 / ((1 - q^{5n - 1 - a})(1 - q^{5n - 4 + a}))
```

for `a = 0, 1`. The infinite versions need analytic infrastructure;
**finite truncations** are within reach now.

Chan Chapter 7 proves them via a functional equation.

## Goal

Add to `QseriesFormalization/Chapter07.lean` (currently a stub):

```lean
import QseriesFormalization.Basic

namespace QseriesFormalization
namespace PartII
namespace Ch07

section Field

variable {R : Type*} [Field R]

/-- Truncated LHS of the Rogers-Ramanujan identity for parameter `a ∈ {0,1}`:
`∑_{n=0}^N q^{n² + a n} / (q;q)_n`. -/
noncomputable def rogersRamanujanLHSTrunc (q : R) (a N : Nat) : R :=
  natSum (fun n => q ^ (n * n + a * n) / qPochhammer q n) N

/-- Truncated RHS: partial product `∏_{n=1}^N 1 / ((1 - q^{5n-1-a}) (1 - q^{5n-4+a}))`. -/
noncomputable def rogersRamanujanRHSTrunc (q : R) (a N : Nat) : R :=
  natSum (fun n => (1 : R)) N -- placeholder; see hint below

end Field

end Ch07
end PartII
end QseriesFormalization
```

The placeholder for `rogersRamanujanRHSTrunc` is intentional — it
should be replaced with a proper recursive product. Use a recursive
`Nat` definition similar to `qPochhammer`, but as a *quotient* sequence:

```lean
noncomputable def rogersRamanujanRHSTrunc (q : R) (a N : Nat) : R :=
  match N with
  | 0 => 1
  | Nat.succ n =>
      rogersRamanujanRHSTrunc q a n /
        ((1 - q ^ (5 * (n + 1) - 1 - a)) * (1 - q ^ (5 * (n + 1) - 4 + a)))
```

(Be careful with `Nat` subtraction `5n - 1 - a` etc. If `a = 0, n ≥ 1`,
the value is `5n - 1`. For `n = 0`, the index is `5·1 - 1 - a` which
for `a = 0` gives `4`, ok. Always ensure `Nat.sub` doesn't truncate to
zero unintentionally.)

Then prove **two concrete sanity checks** at `N = 0`:

```lean
theorem rogersRamanujan_a0_zero (q : R) :
    rogersRamanujanLHSTrunc q 0 0 = 1 ∧ rogersRamanujanRHSTrunc q 0 0 = 1

theorem rogersRamanujan_a1_zero (q : R) :
    rogersRamanujanLHSTrunc q 1 0 = 1 ∧ rogersRamanujanRHSTrunc q 1 0 = 1
```

## Constraints

- **No `axiom`, no `sorry`, no `native_decide`** in the final code.
- `lake build` clean.
- Touch only `Chapter07.lean`.
- Use `noncomputable` where division is involved.

## Deliverable

1. Modified `Chapter07.lean`.
2. Reply file with status, lake build final line.
