# Task 40: Ch7 — Rogers-Ramanujan LHSTrunc N=2 closed form

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`Chapter07.lean` has `rogersRamanujanLHSTrunc q a 1` closed form.
Extend to `N = 2`:

LHS at N=2 = `f(0) + f(1) + f(2)` where `f(n) = q^{n²+an}/(q;q)_n`
- `f(0) = 1`
- `f(1) = q^{1+a}/(1-q)`
- `f(2) = q^{4+2a}/((1-q)(1-q²))`

So `LHS_2 = 1 + q^{1+a}/(1-q) + q^{4+2a}/((1-q)(1-q²))`.

## Goal

Add to `Chapter07.lean`:

```lean
theorem rogersRamanujanLHSTrunc_two (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 2 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) := by
  …
```

This unfolds via `rogersRamanujanLHSTrunc`, `natSum`, and
`qPochhammer` definitions. `simp` + `field_simp` + `ring` may close
it (with side conditions on `(1 - q)` and `(1 - q²)` being nonzero, if
Lean's division simp doesn't behave).

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter07.lean`.

## Deliverable

Modified `Chapter07.lean` + reply file.
