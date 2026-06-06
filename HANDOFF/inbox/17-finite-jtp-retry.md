# Task 17: Finalize finite Jacobi triple product (Chan Eq 3.15) — retry with new infrastructure

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`Chapter03.lean` already has:

- `finite_jacobi_triple_product_zero` (n=0)
- `finite_jacobi_triple_product_one` (n=1)
- `finiteJTPSummand`, `finiteJTPRHS` (definitions)

These came from task 06, which left the **general n proof blocked**.
Since then, several supporting lemmas have landed that may help:

- `qPoch_functional_eq`: `(1 - z) · qPoch (zq) q n = (1 - z q^n) · qPoch z q n`
- `qPoch_split`: `qPoch a q n = qPoch a q k · qPoch (a q^k) q (n-k)` for `k ≤ n`
- `qPoch_add`: `qPoch a q (m+n) = qPoch a q m · qPoch (a q^m) q n`
- `qBinomialTheorem_chanForm`: Chan's q-binomial theorem in `(z;q)_n` form
- `gaussianBinom_mul_qPochhammer_eq`: `[n,m]_q · (q;q)_m · (q;q)_{n-m} = (q;q)_n`
- `gaussianBinom_pascal_alt`, `gaussianBinom_symm`,
  `gaussianBinom_eq_zero_of_lt`, `gaussianBinom_self`
- `natSum_*` family

## Goal

In `Chapter03.lean`, prove the general theorem

```lean
theorem finite_jacobi_triple_product
    (q z : R) (hz : z ≠ 0) (hq : q ≠ 0) (n : Nat) :
    qPoch z q n * qPoch (z⁻¹ * q) q n =
      finiteJTPRHS q z n
```

Chan's derivation (pp. 14-15):

1. Apply `qBinomialTheorem_chanForm` with `n → 2n`:
   `qPoch z q (2*n) = ∑_{k=0}^{2n} [2n,k]_q (-1)^k q^{k(k-1)/2} z^k`
   (call this Eq 3.13).
2. Re-write the LHS of Eq 3.13 by splitting `qPoch z q (2*n)` via
   `qPoch_split` at `k = n`, giving
   `qPoch z q n · qPoch (z q^n) q n`
3. Then in the second factor `qPoch (z q^n) q n`, substitute `z → z/q^n`
   to obtain `qPoch z q n` itself; while the first factor `qPoch z q n`
   transforms similarly using the (z → z/q^n) substitution and Chan's
   "(−z)^n q^{−n(n+1)/2}" prefactor manipulation.
4. The result is Eq 3.15: a re-indexed sum over `l = k - n ∈ [-n, n]`.

## Hints

- The key algebraic step is the `z → z/q^n` substitution. Try working
  it out as a separate lemma:
  ```lean
  lemma qPoch_substitute_div_qpow (q z : R) (hq : q ≠ 0) (n : Nat) :
      qPoch (z / q ^ n) q (2 * n) = (some explicit form)
  ```
- An alternative approach: directly induct on `n`. The inductive step
  needs to relate `qPoch z q (n+1) · qPoch (z⁻¹ q) q (n+1)` to
  `qPoch z q n · qPoch (z⁻¹ q) q n` and to the RHS finite sum's
  difference.
- If both approaches are too gnarly, deliver a **stronger partial**
  (e.g., n = 2 case as concrete verification) and document the blocker
  precisely.

## Constraints

- **No `axiom`, no `sorry`, no `native_decide`** in the modified code.
- `lake build` clean.
- Touch only `Chapter03.lean`.

## Deliverable

1. Modified `Chapter03.lean`.
2. Reply file with status (completed / partial / blocked), diff
   summary, lake build final line, and (if partial) the precise
   subgoal that blocked you.
