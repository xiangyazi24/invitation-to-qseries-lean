# Task 07: Ch 1 — generating function for partitions (Eq 1.8) at finite truncation

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Chan's Eq (1.8): the generating function for partitions is

`∑_{n=0}^∞ p(n) q^n = ∏_{n=1}^∞ 1/(1 - q^n)`.

The infinite version requires power series / convergence. A clean
**finite** statement provable without analytic infrastructure:

For any `N : ℕ` and any `[CommRing R]`-valued `q`, denote by
`partGen N q := ∑_{n ≤ N} p(n) · q^n`. There is a finite product
`∏_{k=1}^N (1 + q^k + q^{2k} + ... + q^{Nk})` which equals `partGen N q`
truncated.

For Phase 1 we want a simpler concrete check:

```
partGen 4 q = 1 + q + 2 q^2 + 3 q^3 + 5 q^4   (over [CommRing R])
```

— since `p(0)=1, p(1)=1, p(2)=2, p(3)=3, p(4)=5` (already proved in
`Chapter01.lean`).

## Goal

Add to `QseriesFormalization/Chapter01.lean`:

```lean
section CommRing

variable {R : Type*} [CommRing R]

/-- Truncated partition generating function `∑_{n=0}^N p(n) q^n`. -/
def partitionGenFn (q : R) (N : Nat) : R :=
  natSum (fun n => (partitionCount n : R) * q ^ n) N

/-- Concrete value for `N = 4`: matches Chan's `1 + q + 2q^2 + 3q^3 + 5q^4`. -/
theorem partitionGenFn_four (q : R) :
    partitionGenFn q 4 = 1 + q + 2 * q^2 + 3 * q^3 + 5 * q^4 := …

end CommRing
```

`natSum` is in `Basic.lean`. `partitionCount` is in `Chapter01.lean`.

## Hints

- `partitionGenFn_four q` should unfold via `partitionGenFn`,
  `natSum_succ` repeatedly and the partitionCount values.
- `simp [partitionGenFn, natSum, partitionCount_zero, partitionCount_one,
  partitionCount_two, partitionCount_three, partitionCount_four]; ring`
  may close it directly. Watch for `Nat.cast_ofNat` simp.

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter01.lean`.

## Deliverable

1. Modified `Chapter01.lean`.
2. Reply file with status, lake build final line.
