# Task 08: q-Pochhammer functional equation (Chan Eq 3.10)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Inside Chan's proof of the finite q-binomial theorem (Theorem 3.2,
p. 14), the polynomial `f(z) := (z; q)_n = qPoch z q n` is shown to
satisfy

```
(1 - z) · f(z q) = (1 - z q^n) · f(z)             (Chan Eq 3.10)
```

which is an algebraic identity (no convergence assumptions). This is
useful infrastructure for later chapters (especially Ch7 first proof of
Rogers-Ramanujan via functional equations).

## Goal

Add to `QseriesFormalization/Chapter03.lean` (in the existing
`section CommRing` block):

```lean
theorem qPoch_functional_eq (q z : R) :
    ∀ n : Nat,
      (1 - z) * qPoch (z * q) q n = (1 - z * q ^ n) * qPoch z q n
```

## Hints

- Induction on `n`.
- Base `n = 0`: both sides simplify to `1 - z`.
- Step: use `qPoch_succ` to unfold both `qPoch (z*q) q (n+1)` and
  `qPoch z q (n+1)`, apply IH, and close with `ring`.
- Key algebraic identity to make the `ring` close cleanly:
  `(1 - z) * qPoch (z*q) q n * (1 - z*q*q^n)
       = (1 - z*q*q^n) * (1 - z) * qPoch (z*q) q n`
  (just commutativity), then by IH the inner `(1-z) * qPoch (z*q) q n`
  becomes `(1 - z q^n) * qPoch z q n`, and we need
  `(1 - z*q*q^n) * (1 - z q^n) * qPoch z q n = (1 - z q^{n+1}) * qPoch z q n * (1 - z*q^n)`.
  Both sides equal — close by `ring` and `pow_succ`.

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter03.lean`.

## Deliverable

1. Modified `Chapter03.lean`.
2. Reply file with status and lake build final line.
