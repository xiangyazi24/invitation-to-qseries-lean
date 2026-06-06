# Task 24: Ch3 — Chan's "(z; q)_n with z⁻¹" reflection identity

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

In the second proof of JTP (Chan Ch 3 §3.3), Chan derives the algebraic
identity (between Eqs 3.13 and 3.14):

`(z; q)_{2n} = (-z)^n · q^{-n(n+1)/2} · (z⁻¹ q; q)_n · (z; q)_n`   (★)

valid over a field with `z ≠ 0` and `q ≠ 0`. This is the cleanest
finite reflection identity (Chan walks the reader through it as part of
the JTP derivation).

The existing `Chapter03.lean` infrastructure supports stating this:
- `qPoch_split` for `(z; q)_{2n} = (z; q)_n · (z q^n; q)_n`
- Algebraic manipulation of factors like `(1 - z q^k) = (-z) (1 - q^k / z) · q^k / q^k` etc.

## Goal

Add to `Chapter03.lean`, in the `section CommRing` (or a new
`section Field` for cleaner division):

```lean
section Field

variable {R : Type*} [Field R]

theorem qPoch_reflection_two_mul (q z : R) (hq : q ≠ 0) (hz : z ≠ 0)
    (n : Nat) :
    qPoch z q (2 * n) =
      (-z) ^ n * q ^ (n * (n + 1) / 2)⁻¹ ^ 1 *
      qPoch (z⁻¹ * q) q n * qPoch z q n := by
  …

end Field
```

(That's a bit of a typo; I want `q ^ (- n*(n+1)/2)` which over a field
is `(q^{n(n+1)/2})⁻¹`. Use whichever Lean spelling works.)

Or more simply, prove the rearranged form

```lean
theorem qPoch_reflection_two_mul (q z : R) (hq : q ≠ 0) (hz : z ≠ 0)
    (n : Nat) :
    qPoch z q (2 * n) * q ^ (n * (n + 1) / 2) =
      (-z) ^ n * qPoch (z⁻¹ * q) q n * qPoch z q n
```

which sidesteps division by `q^{n(n+1)/2}`.

## Hints

- Use `qPoch_split` at `k = n` to write `qPoch z q (2*n) = qPoch z q n · qPoch (z*q^n) q n`.
- Then transform `qPoch (z*q^n) q n` factor by factor:
  `(1 - z q^n q^k) = (-z q^n) · (q^{-n-k}/z - 1) · (-1) = … = (-z) q^{n+k} (1 - z⁻¹ q^{-n-k}) · (-1)`
  This is fiddly. Use `qPoch (z⁻¹ * q^{1-n}) q n` (or similar) and simplify.

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter03.lean`.
- If the algebra is too gnarly, deliver a **partial result** at small
  `n` (n=0, n=1) and document the blocker.

## Deliverable

1. Modified `Chapter03.lean`.
2. Reply file with status, lake build final line.
