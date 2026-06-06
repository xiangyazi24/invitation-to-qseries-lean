# Task 19: Ch7 Rogers-Ramanujan — extend truncation sanity to N=1

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`Chapter07.lean` defines truncations `rogersRamanujanLHSTrunc` and
`rogersRamanujanRHSTrunc` and proves N=0 sanity (both sides equal 1).

The N=1 case is NOT an exact equality (Rogers-Ramanujan is exact only
in the limit). However, the **finite truncation values** can still be
computed in closed form. Document them.

## Goal

Add to `Chapter07.lean`:

```lean
/-- LHS truncation at N=1 for parameter a. -/
theorem rogersRamanujanLHSTrunc_one (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 1 = 1 + q ^ a / (1 - q)

/-- RHS truncation at N=1 for parameter a (a ∈ {0,1}). -/
theorem rogersRamanujanRHSTrunc_one_a0 (q : R) (hq : (1 - q^4) ≠ 0)
    (hq' : (1 - q) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 1 = 1 / ((1 - q^4) * (1 - q))

theorem rogersRamanujanRHSTrunc_one_a1 (q : R) (hq : (1 - q^3) ≠ 0)
    (hq' : (1 - q^2) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 1 = 1 / ((1 - q^3) * (1 - q^2))
```

(For a=0: 5·1-1-0=4, 5·1-4+0=1, so RHS factors are (1-q^4)(1-q^1).
For a=1: 5·1-1-1=3, 5·1-4+1=2, so RHS factors are (1-q^3)(1-q^2).)

LHS computation: at N=1, `natSum f 1 = f 0 + f 1`.
- f(0) = q^{0+0} / (q;q)_0 = 1 / 1 = 1.
- f(1) = q^{1+a} / (q;q)_1 = q^{1+a} / (1-q).

So LHS = 1 + q^{1+a}/(1-q). Wait — the spec writes `q ^ a / (1 - q)`
but that's `f(1)` only with `n=0+a` term... let me recompute.

Actually `f(n) = q^{n²+an}/(q;q)_n` so:
- `f(0) = q^0 / (q;q)_0 = 1`.
- `f(1) = q^{1+a} / (1-q)`.

So LHS at N=1 = `1 + q^{1+a} / (1-q)`. The spec in the goal has a typo
(`q^a`). **Use the corrected formula `1 + q^{1+a} / (1-q)`** in your
implementation. Document the correction.

## Constraints

- **No `axiom`, no `sorry`, no `native_decide`.**
- `lake build` clean.
- Touch only `Chapter07.lean`.

## Deliverable

1. Modified `Chapter07.lean`.
2. Reply file with status, lake build final line.
