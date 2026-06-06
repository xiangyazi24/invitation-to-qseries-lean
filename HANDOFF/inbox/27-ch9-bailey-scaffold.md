# Task 27: Ch9 — Bailey's lemma scaffold (Part II)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Chan Ch 9 proves the Rogers-Ramanujan identities via Bailey's lemma —
the most algebraic of the three RR proofs. Bailey pairs are pairs of
sequences `(α_n, β_n)` related by

`β_n = ∑_{k=0}^n α_k / ((q;q)_{n-k} (a q; q)_{n+k})`

(over `[Field R]`).

## Goal

Replace `QseriesFormalization/Chapter09.lean` with:

```lean
import QseriesFormalization.Basic

namespace QseriesFormalization
namespace PartII
namespace Ch09

section Field

variable {R : Type*} [Field R]

/-- The Bailey pair relation, finite form. `BaileyTerm a q n α k` is the
k-th summand in the Bailey defining relation
`β_n = ∑_{k=0}^n α_k / ((q;q)_{n-k} (a q; q)_{n+k})`. -/
noncomputable def BaileyTerm (a q : R) (α : Nat → R) (n k : Nat) : R :=
  α k / (qPochhammer q (n - k) * qPoch (a * q) q (n + k))

/-- The β-side of a Bailey pair, defined by the truncated sum. -/
noncomputable def BaileyBeta (a q : R) (α : Nat → R) (n : Nat) : R :=
  natSum (fun k => BaileyTerm a q α n k) n

/-- Trivial Bailey pair: α_0 = 1, α_k = 0 for k ≥ 1. Then β_0 = 1 / (1 · (a q; q)_0) = 1. -/
theorem BaileyBeta_trivial_zero (a q : R) (h : qPochhammer q 0 ≠ 0)
    (h' : qPoch (a * q) q 0 ≠ 0) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 0 = 1 := by
  simp [BaileyBeta, BaileyTerm, natSum, qPochhammer, qPoch]

end Field

end Ch09
end PartII
end QseriesFormalization
```

## Constraints

- **No `axiom`, no `sorry`, no `native_decide`.**
- `lake build` clean.
- Touch only `Chapter09.lean`.

## Deliverable

1. Modified `Chapter09.lean`.
2. Reply file with status, lake build final line.
