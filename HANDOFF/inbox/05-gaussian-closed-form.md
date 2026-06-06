# Task 05: Gaussian binomial closed form `[n,m] · (q;q)_m · (q;q)_{n-m} = (q;q)_n` (Chan Eq 3.2 / 3.6)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.
**`lake build` must end clean.**

## Background

Chan's Eq (3.2) (page 12) gives the closed form

`[n, m]_q = (q;q)_n / ((q;q)_m · (q;q)_{n-m})`

valid for `m ≤ n`. Multiplying both sides by the (always-defined)
denominator yields the **product form** identity

`[n, m]_q · (q;q)_m · (q;q)_{n-m} = (q;q)_n`     (★)

which is well-typed in `[CommSemiring R]` (no division required) and
should be provable by induction on `n` using the q-Pascal recursion
already in `Chapter03.lean`.

Existing infrastructure:
- `qPochhammer q n = (q;q)_n` (Basic.lean).
- `gaussianBinom q n k` (Basic.lean), recursion baked in.
- `gaussianBinom_pascal_alt` and `gaussianBinom_symm` (Chapter03.lean).
- `gaussianBinom_eq_zero_of_lt`, `gaussianBinom_self`.

## Goal

Add to `QseriesFormalization/Chapter03.lean` (in the existing
`section CommSemiring`):

```lean
theorem gaussianBinom_mul_qPochhammer_eq (q : R) :
    ∀ n m, m ≤ n →
      gaussianBinom q n m * qPochhammer q m * qPochhammer q (n - m) =
        qPochhammer q n
```

Note `qPochhammer q n` is currently defined in the `[CommRing R]` block
of `Basic.lean`. Since (★) is an algebraic identity not requiring
negation in its statement (the recursion uses `(1 - q^k)` which lives
in `CommRing` — that's fine), state and prove it in `[CommRing R]`.
Place it inside an appropriate `section CommRing` block in
`Chapter03.lean` (you may need to introduce one).

## Hints

- Induction on `n`. Base `n = 0` forces `m = 0`; both sides are `1`.
- For the step `n → n+1`, split on `m`:
  - If `m = 0`: trivial.
  - If `m = n+1`: use `gaussianBinom_self`, `Nat.sub_self`, `qPochhammer_zero`.
  - If `0 < m ≤ n`: use the def's q-Pascal `[n+1,m] = [n,m] + q^{n-m+1} [n,m-1]`.
    Multiply by `(q;q)_m · (q;q)_{n+1-m}`. Manipulate using
    `(q;q)_m = (q;q)_{m-1} · (1 - q^m)`,
    `(q;q)_{n+1-m} = (q;q)_{n-m} · (1 - q^{n+1-m})`,
    and the IH on both `[n,m]` and `[n,m-1]` to combine into
    `(q;q)_{n+1} = (q;q)_n · (1 - q^{n+1})`.
  - You will need careful `Nat.sub` manipulation — `Nat.succ_sub`,
    `Nat.sub_add_cancel`, etc.

If you genuinely cannot close the proof, leave a partial attempt with a
detailed status, but keep `lake build` clean (i.e., comment out the
unfinished theorem, or wrap it with `private` and leave a TODO).

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter03.lean`.

## Deliverable

1. Modified `Chapter03.lean`.
2. Reply file with status, lake build final line, and details on any
   intermediate lemmas added.
