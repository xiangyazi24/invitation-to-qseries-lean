# Task 06: Finite Jacobi triple product (Chan Eq 3.15)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Chan's book proves the (infinite) Jacobi triple product identity via a
**finite intermediate** (Eq 3.15, p. 15):

```
(z;q)_n · (z^{-1} q; q)_n
  = ∑_{l = -n}^{n} [2n, n+l]_q · q^{l(l-1)/2} · (-z)^l
```

Both sides are polynomial expressions in `q, z, z^{-1}` (the LHS has `z`
and `z^{-1}`, hence `[Field R]`). The infinite JTP follows by letting
`n → ∞`, which we are *not* doing here — the finite version (★) is
self-contained and provable algebraically.

Existing infrastructure we can use (in `Chapter03.lean` /  `Basic.lean`):
- `finiteQBinomialTheorem`: `qBinomialLHS q x n = qBinomialRHS q x n`
- `qPoch (a q : R) n` (general q-Pochhammer in `[CommRing R]`)
- `qBinomialLHS_neg_eq_qPoch`: `qBinomialLHS q (-z) n = qPoch z q n`
- `qBinomialTheorem_chanForm`: `qPoch z q n = ∑ [n,k] (-1)^k q^{k(k-1)/2} z^k`
- `gaussianBinom_*` lemmas, `natSum_*` helpers.

Chan's derivation (pp. 14-15):
1. Start from `(z;q)_{2n} = ∑_{k=0}^{2n} [2n, k]_q (-1)^k q^{k(k-1)/2} z^k`
   (apply `qBinomialTheorem_chanForm` with `n → 2n`).
2. Re-index the LHS: split `(z;q)_{2n}` into the first `n` factors and
   the last `n` factors. Pull `-z` out of the first `n` factors (and
   `q^i` from the i-th factor) to rewrite as
   `(-z)^n · q^{n(n-1)/2} · (z^{-1}; q^{-1})_n · (z q^n; q)_n`.
3. Substitute `z → z / q^n` to get
   `(-z/q^n)^n · q^{-n(n+1)/2} · (z^{-1} q; q)_n · (z; q)_n`
   on the LHS (after simplifying the substituted expressions).
4. Apply the same substitution `z → z/q^n` to the RHS series and
   re-index `l = k - n` to get the symmetric `l ∈ [-n, n]` form.

This derivation is **finite and algebraic** — no limits, no convergence
arguments. Just `ring`-style manipulations and re-indexing.

## Goal

Add to a new section in `QseriesFormalization/Chapter03.lean`:

```lean
section FiniteJTP

variable {R : Type*} [Field R]

/-- Symmetric finite Jacobi triple product (Chan Eq 3.15):
`(z;q)_n · (z⁻¹ q; q)_n = ∑_{l=-n}^{n} [2n, n+l]_q · q^{l(l-1)/2} · (-z)^l`. -/
theorem finite_jacobi_triple_product
    (q z : R) (hz : z ≠ 0) (n : Nat) :
    qPoch z q n * qPoch (z⁻¹ * q) q n =
      natSumZ (-(n : Int)) n
        (fun l : Int =>
          gaussianBinom q (2 * n) (n + l).toNat *
            q ^ (l.toNat * (l.toNat - 1) / 2) *
            (-z) ^ l.toNat) := by
  …

end FiniteJTP
```

You may need a helper `natSumZ : Int → Int → (Int → R) → R` that sums
over a closed integer interval (or use `Finset.sum (Finset.Icc lo hi)`).
The exact statement is flexible — what matters is the mathematical
content (Chan Eq 3.15) being formalized. **Pick the cleanest finite-sum
encoding for the bilateral form** and document it.

## Hints

- Use `Finset.sum (Finset.Icc (-n : ℤ) n) f` for the bilateral sum if
  reasonable; converting between `natSum` and `Finset.sum` is fine.
- Multiple intermediate lemmas (each being a clean algebraic identity)
  are encouraged — break the proof into chunks.
- The `z → z/q^n` substitution might be cleaner if you state the
  intermediate Eq (3.13) form (`(z;q)_{2n}` finite expansion) and
  derive Eq (3.15) by substitution as a separate lemma.
- If you genuinely need `q ≠ 0` (e.g., for the `z/q^n` step), add it as
  a hypothesis. Also `z ≠ 0` is required since we use `z⁻¹`.

## Constraints

- **No `axiom`, no `sorry`, no `native_decide`.**
- `lake build` clean.
- Touch only `Chapter03.lean` (and possibly `Basic.lean` for a sum
  helper if needed).
- This is hard. If the full proof eludes you, add a **partial**
  result — e.g. the `n = 1` or `n = 2` case as a concrete check —
  rather than nothing. Document what's left.

## Deliverable

1. Modified files.
2. Reply file with status (completed / partial / blocked), diff
   summary, lake build final line, and (if partial) which subgoal
   blocked you.
