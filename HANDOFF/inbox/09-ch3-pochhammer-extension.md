# Task 09: q-Pochhammer extension lemmas (used heavily in Chan Ch 4-7)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Chan repeatedly uses **factorization** identities for `qPoch` that
amount to splitting the index. These are clean polynomial identities,
provable by induction.

## Goal

Add to `QseriesFormalization/Chapter03.lean`, in the existing
`section CommRing` block (so they live alongside `qPoch_functional_eq`):

1.  **Multiplicative split**: `(a; q)_{m+n} = (a; q)_m · (a q^m; q)_n`.

    ```lean
    theorem qPoch_add (q a : R) (m n : Nat) :
        qPoch a q (m + n) = qPoch a q m * qPoch (a * q ^ m) q n
    ```

2.  **Reflection**: relate `(a; q)_n` and the "shifted" form
    `(a q^k; q)_{n-k}` for `k ≤ n`. (Specialization of (1) with `m = k`,
    `n = n - k`.)

    ```lean
    theorem qPoch_split (q a : R) (n k : Nat) (hk : k ≤ n) :
        qPoch a q n = qPoch a q k * qPoch (a * q ^ k) q (n - k)
    ```

3.  **Connection** of `qPochhammer` to `qPoch`: explicit form
    `qPochhammer q n = qPoch q q n` is already proven; add the
    multiplicative split for `qPochhammer` as a corollary:

    ```lean
    theorem qPochhammer_split (q : R) (n k : Nat) (hk : k ≤ n) :
        qPochhammer q n = qPochhammer q k * qPoch (q * q ^ k) q (n - k)
    ```

## Hints

- For (1), induct on `n`. Base `n = 0`: trivial. Step uses `qPoch_succ`
  and `pow_add`.
- (2) follows by setting `m = k`, `n = n - k` in (1) and using
  `Nat.add_sub_of_le hk : k + (n - k) = n`.
- (3) is a one-liner: `rw [← qPoch_q_eq_qPochhammer, qPoch_split]`.

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter03.lean`.

## Deliverable

1. Modified `Chapter03.lean`.
2. Reply file with status and lake build final line.
