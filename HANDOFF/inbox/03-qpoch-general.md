# Task 03: General q-Pochhammer `(a; q)_n` and Chan-form q-binomial theorem

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.
**`lake build` must end clean** when you finish.

## Background

Chan's book uses the general q-Pochhammer symbol pervasively (Eq 1.5):

`(a; q)_n := ∏_{k=0}^{n-1} (1 - a q^k)`

(with `(a; q)_0 = 1`). Our current `Basic.lean` defines only the special
case

```lean
def qPochhammer (q : R) : Nat → R
  | 0 => 1
  | Nat.succ n => qPochhammer q n * (1 - q ^ (Nat.succ n))
```

which corresponds to `(q; q)_n` (i.e. `a = q`).

In Chan's Theorem 3.2 (q-binomial theorem) the statement is

`(z; q)_n = ∑_{k=0}^n [n,k]_q (-1)^k q^{k(k-1)/2} z^k`

— the LHS is `(z; q)_n` with general `z`, not `(q; q)_n`.

Our `Chapter03.lean` already proves the equivalent

```lean
qBinomialLHS q x n = qBinomialRHS q x n        (finiteQBinomialTheorem)
```

where `qBinomialLHS q x n = ∏_{k=0}^{n-1} (1 + x q^k)`. Setting `x = -z`
gives Chan's identity.

## Goal

1. Add to `QseriesFormalization/Basic.lean`, in the existing
   `section CommRing` block (alongside `qPochhammer`):

   ```lean
   /-- General q-Pochhammer symbol `(a; q)_n = ∏_{k=0}^{n-1} (1 - a q^k)`. -/
   def qPoch (a q : R) : Nat → R
     | 0 => 1
     | Nat.succ n => qPoch a q n * (1 - a * q ^ n)
   ```

   plus `@[simp]` lemmas:
     - `qPoch_zero (a q : R) : qPoch a q 0 = 1 := rfl`
     - `qPoch_succ (a q : R) (n : Nat) : qPoch a q (Nat.succ n) = qPoch a q n * (1 - a * q ^ n)`
     - `qPoch_q_eq_qPochhammer (q : R) (n : Nat) : qPoch q q n = qPochhammer q n`
       (this should be a clean induction).

2. In `QseriesFormalization/Chapter03.lean` add a corollary that states
   the q-binomial theorem in Chan's notation. We need to be careful about
   typeclass: `(1 - a * q^k)` is fine in `[CommRing R]` (we have negation),
   while our existing `Chapter03.lean` works in `[CommSemiring R]`. So this
   corollary lives in a `[CommRing R]` block.

   Concretely add:

   ```lean
   section CommRing

   variable {R : Type*} [CommRing R]

   /-- Chan's q-binomial theorem (Theorem 3.2): `(z; q)_n = ∑ [n,k]_q (-1)^k q^{k(k-1)/2} z^k`. -/
   theorem qBinomialTheorem_chanForm (q z : R) (n : Nat) :
       qPoch z q n =
         natSum (fun k => gaussianBinom q n k * q ^ (k * (k - 1) / 2) * (-1 : R) ^ k * z ^ k) n := by
     …
   ```

   Hint: prove first `qBinomialLHS q (-z) n = qPoch z q n` (clean induction
   using `qBinomialLHS_succ` and `qPoch_succ`), then chain through
   `finiteQBinomialTheorem q (-z) n` and unfold `qBinomialRHS / qBinomialTerm`
   pulling out `(-z)^k = (-1)^k * z^k`.

   You may need a `natSum_congr` helper (or reuse `natSum_congr_le`).

## Constraints

- **No `axiom`, no `sorry`** in the final code.
- `lake build` clean.
- Touch only `Basic.lean` and `Chapter03.lean`.
- Keep the existing `qPochhammer` definition for backward compatibility
  (don't replace it; let `qPoch_q_eq_qPochhammer` bridge the two).

## Deliverable

1. Modified `Basic.lean` and `Chapter03.lean`.
2. Reply file with status, diff summary, and `lake build` final line.
