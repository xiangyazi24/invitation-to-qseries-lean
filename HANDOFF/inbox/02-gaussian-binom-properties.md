# Task 02: Gaussian binomial properties — q-Pascal (Eq 3.4) and symmetry (Eq 3.5)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.
**`lake build` must end clean** when you finish.

## Background

`QseriesFormalization/Basic.lean` defines

```lean
def gaussianBinom (q : R) : Nat → Nat → R
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | Nat.succ n, Nat.succ k =>
      gaussianBinom q n (Nat.succ k) + q ^ (n - k) * gaussianBinom q n k
```

over `[CommSemiring R]`.

This definition matches **Chan's Eq (3.3)** in Theorem 3.1 (Hei-Chi Chan,
*An Invitation to q-Series*, p. 12):

`[n, m]_q = [n-1, m]_q + q^{n-m} [n-1, m-1]_q`

Two more standard properties are stated in the same theorem:

- **Eq (3.4)**: `[n, m]_q = q^m [n-1, m]_q + [n-1, m-1]_q`
- **Eq (3.5)** (symmetry): `[n, m]_q = [n, n-m]_q`   (for `m ≤ n`)

The Chapter03.lean file already has an out-of-range vanishing lemma
`gaussianBinom_eq_zero_of_lt q (h : n < k) : gaussianBinom q n k = 0`
and `gaussianBinom_self q n : gaussianBinom q n n = 1`.

## Goal

Add and prove these two lemmas in `QseriesFormalization/Chapter03.lean`
(inside the existing `namespace QseriesFormalization` /
`namespace PartI` / `namespace Ch03` block, in the `section CommSemiring`):

1.  ```lean
    lemma gaussianBinom_pascal_alt (q : R) (n k : Nat) (hk : k ≤ n) :
        gaussianBinom q (Nat.succ n) (Nat.succ k) =
          q ^ Nat.succ k * gaussianBinom q n (Nat.succ k) +
          gaussianBinom q n k := …
    ```
    (This is Chan's Eq (3.4) with the index shift `n → n+1`, `m → k+1`.)

2.  ```lean
    lemma gaussianBinom_symm (q : R) :
        ∀ n k, k ≤ n → gaussianBinom q n k = gaussianBinom q n (n - k) := …
    ```

## Hints

For Eq (3.4):
- The two recursions (3.3 = our def, and 3.4) coincide because both
  expand to the same polynomial in `q`. One slick proof: induct on `n`
  using the def for one form and assemble the other; or compute both
  recursions agree via algebraic identity at the level of the closed
  formula `(q)_n / ((q)_k (q)_{n-k})` — but that closed formula isn't in
  scope, so direct induction is cleaner.

For symmetry (3.5):
- Induct on `n`. Base `n = 0` forces `k = 0`. Step splits on `k` vs
  `n - k`. You'll need `n.succ - k.succ = n - k` and the alt-Pascal
  lemma you just proved together with our defining recursion to pivot
  between `[n, k]` and `[n, n-k]`.

If the symmetry proof gets gnarly, an alternative path is to prove a
closed-form representation in `[CommRing R]` (passing through Mathlib
machinery) — but please first try to keep things in `[CommSemiring R]`.

## Constraints

- **No `axiom`, no `sorry`** in the final code.
- `lake build` must end "Build completed successfully" with zero error.
- Free use of Mathlib lemmas and `simp`/`omega`/`ring`/`nlinarith` etc.
- If genuinely stuck on (3.5), commit (3.4) and report (3.5) as blocked
  with the exact subgoal — partial progress > silence.

## Deliverable

1. Modified `Chapter03.lean` (and only that file).
2. Reply file at the dispatcher-mandated path:
   - Status: completed / partial / blocked.
   - Diff summary.
   - `lake build` final line.
   - If blocked / partial: the precise subgoal you couldn't close.
