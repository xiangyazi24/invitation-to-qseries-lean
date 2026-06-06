# Batch 26: Ch15 — q-Falling Factorial Properties

## Context
Chapter15.lean has:
- `qFallingFactorial q n k = ∏ i ∈ Finset.range k, qInt q (n - i)`
- `qFallingFactorial_zero`, `qFallingFactorial_succ`
- `qFallingFactorial_self` : [n]_q^{(n)} = [n]_q!
- `qFactorial q n` — [n]_q! recursively defined
- `qFactorial_eq_prod` : [n]_q! = ∏ i ∈ range n, [i+1]_q
- `qFactorial_succ` : [n+1]_q! = [n]_q! · [n+1]_q
- `qInt q n` — q-integer

All within `section Field` / `variable {R : Type*} [Field R]`.

## Goal: Key properties of q-falling factorial

### Task 1: qFallingFactorial equals ratio of q-factorials

When k ≤ n and [n-k]_q! ≠ 0:
[n]_q^{(k)} = [n]_q! / [n-k]_q!

This is the q-analog of n^{(k)} = n! / (n-k)!.

```lean
/-- The q-falling factorial is the ratio of q-factorials:
[n]_q^{(k)} = [n]_q! / [n-k]_q! when [n-k]_q! ≠ 0. -/
theorem qFallingFactorial_eq_div (q : R) (n k : ℕ) (hk : k ≤ n)
    (hfac : qFactorial q (n - k) ≠ 0) :
    qFallingFactorial q n k = qFactorial q n / qFactorial q (n - k) := by
  sorry
```

**Proof sketch** (induction on k):
- k = 0: [n]_q^{(0)} = 1 = [n]_q! / [n]_q! ✓ (using div_self hfac)
- k+1: [n]_q^{(k+1)} = [n]_q^{(k)} · [n-k]_q
  By IH: = ([n]_q! / [n-k]_q!) · [n-k]_q
  = [n]_q! · [n-k]_q / [n-k]_q!
  = [n]_q! · [n-k]_q / ([n-k-1]_q! · [n-k]_q)  [using qFactorial_succ on n-k]
  = [n]_q! / [n-k-1]_q!
  = [n]_q! / [n-(k+1)]_q!  ✓

The key identity used: [n-k]_q! = [n-k-1]_q! · [n-k]_q (i.e., qFactorial_succ).
Need: [n-k]_q ≠ 0 (follows from qFactorial q (n-k) ≠ 0... actually need to be careful).

Actually, a cleaner hypothesis: `∀ j, 1 ≤ j → j ≤ n → qInt q j ≠ 0`.

Let me simplify: use `hfac : qFactorial q (n - k) ≠ 0` for k case and derive what's needed for k+1.

### Task 2: qFallingFactorial vanishes when k > n (if q ≠ 1)

When k > n, the product includes qInt q 0 = 0 (since n - i = 0 for some i in range).

Wait: with Nat subtraction, `n - i` when `i > n` equals 0, and `qInt q 0 = 0`. So the product contains a zero factor.

Actually more precisely: when k > n, there exists i ∈ range k with i = n, giving qInt q (n - n) = qInt q 0 = 0.

```lean
/-- The q-falling factorial vanishes when k > n because qInt q 0 = 0. -/
theorem qFallingFactorial_eq_zero_of_gt (q : R) (n k : ℕ) (hk : n < k) :
    qFallingFactorial q n k = 0 := by
  rw [qFallingFactorial]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : n < k))
  simp [qInt_zero, show n - n = 0 from by omega]
```

### Task 3: Product form of qFallingFactorial

```lean
/-- qFallingFactorial expanded: [n]_q^{(k)} = [n]_q · [n-1]_q · ⋯ · [n-k+1]_q.
Restated: the product form makes explicit that we multiply q-integers from n down. -/
theorem qFallingFactorial_one (q : R) (n : ℕ) :
    qFallingFactorial q n 1 = qInt q n := by
  simp [qFallingFactorial]

theorem qFallingFactorial_two (q : R) (n : ℕ) :
    qFallingFactorial q n 2 = qInt q n * qInt q (n - 1) := by
  simp [qFallingFactorial, Finset.prod_range_succ]
```

## File: QseriesFormalization/Chapter15.lean
Insert after `qDerivIter_pow_self` (line 512) and before `R_trunc_nesting_eleven` (line 514).
(If batch25 code is also there, insert after that.)

## Constraints
- No sorry, no axiom, no native_decide
- `lake build QseriesFormalization.Chapter15` must pass
- Work within `section Field` / `variable {R : Type*} [Field R]`
- For the division proof, `field_simp` may help but be careful with Nat subtraction: `n - k` in ℕ
- Key Finset API: `Finset.prod_eq_zero` to show a product with a zero factor is zero
- `qInt_zero : qInt q 0 = 0` is the key fact for vanishing

## Build command
```
lake build QseriesFormalization.Chapter15
```
