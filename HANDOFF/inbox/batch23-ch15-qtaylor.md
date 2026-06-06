# Batch 23: q-Taylor Formula (Ch15)

## Context
Chapter15.lean now has a complete q-calculus theory layer:
- `qDeriv` — q-derivative operator
- `qInt q n` — q-integer [n]_q = ∑_{i=0}^{n-1} q^i
- `qDeriv_pow` — D_q(x^n) = [n]_q · x^{n-1}
- `qDeriv_add`, `qDeriv_sub`, `qDeriv_smul` — linearity
- `qDeriv_mul`, `qDeriv_mul'` — Leibniz product rule
- `qDerivIter` — iterated q-derivative D_q^k
- `qDerivIter_two_pow` — D_q^2(x^n) = [n]_q[n-1]_q x^{n-2}
- `qFactorial q n` — [n]_q! = [1]_q·[2]_q·...·[n]_q
- `qFactorial_ne_zero` — nonzero when all q-integers are nonzero
- `qExpTrunc` — truncated q-exponential
- `qDeriv_qPoch` — D_q((z;q)_n) = -[n]_q·(aq;q)_{n-1}

All within `section Field` / `variable {R : Type*} [Field R]`.
All imports: Basic + Chapter11.

## Goal: q-Taylor formula (truncated)

The q-analog of Taylor's theorem says:
```
f(x) = ∑_{k=0}^{n} D_q^k(f)(0) / [k]_q! · x^k + remainder
```

For polynomials (our case), the remainder vanishes.

### Task 1: D_q^k(x^n) evaluated at 0

```lean
/-- D_q^k(x^n) at x = 0 equals [n]_q! / [n-k]_q! when k ≤ n, and 0 otherwise.
For the special case k = n: D_q^n(x^n)(0) = [n]_q!. -/
theorem qDerivIter_pow_at_zero (q : R) (hq : q ≠ 1) (n k : ℕ) (hk : k ≤ n) :
    qDerivIter (fun t => t ^ n) q k 0 = 0 := by
  sorry -- Actually this is 0 for k < n because x^(n-k) at x=0 is 0
```

Wait — we need to be careful. D_q^k(x^n)(x) = [n]_q·[n-1]_q·...·[n-k+1]_q · x^{n-k}.
At x = 0 with k < n: this is 0 (because x^{n-k} = 0^{n-k} = 0).
At x = 0 with k = n: this involves x^0 = 1, so it equals [n]_q!.

BUT: qDeriv at x = 0 is problematic because the denominator (q-1)·x = 0.
The q-derivative is only defined when (q-1)x ≠ 0, so we can't evaluate at x=0 directly.

### Revised Task 1: q-falling factorial

Instead of evaluating at 0, prove the iterated derivative formula:

```lean
/-- Iterated q-derivative of x^n: D_q^k(x^n) = [n]_q·[n-1]_q·...·[n-k+1]_q · x^{n-k}.
This is the q-analog of the falling factorial. -/
noncomputable def qFallingFactorial (q : R) (n k : ℕ) : R :=
  ∏ i ∈ Finset.range k, qInt q (n - i)

theorem qDerivIter_pow (q x : R)
    (hiter : ∀ j : ℕ, j < k → (q - 1) * (q ^ j * x) ≠ 0)
    (n k : ℕ) (hk : k ≤ n) :
    qDerivIter (fun t => t ^ n) q k x = qFallingFactorial q n k * x ^ (n - k) := by
  sorry
```

The proof is by induction on k:
- k = 0: D_q^0(x^n) = x^n = 1 · x^n = qFallingFactorial q n 0 · x^n ✓
- k+1: D_q^{k+1}(x^n) = D_q(D_q^k(x^n))
  = D_q(qFallingFactorial q n k · x^{n-k})  [by IH]
  = qFallingFactorial q n k · D_q(x^{n-k})   [by qDeriv_smul]
  = qFallingFactorial q n k · [n-k]_q · x^{n-k-1} [by qDeriv_pow]
  = qFallingFactorial q n (k+1) · x^{n-(k+1)} ✓

### Task 2: q-falling factorial equals ratio of q-factorials

```lean
theorem qFallingFactorial_eq_div (q : R) (n k : ℕ) (hk : k ≤ n)
    (hq : qFactorial q (n - k) ≠ 0) :
    qFallingFactorial q n k = qFactorial q n / qFactorial q (n - k) := by
  sorry
```

### Task 3: Special case D_q^n(x^n) = [n]_q!

```lean
theorem qDerivIter_pow_self (q x : R)
    (hiter : ∀ j : ℕ, j < n → (q - 1) * (q ^ j * x) ≠ 0)
    (n : ℕ) :
    qDerivIter (fun t => t ^ n) q n x = qFactorial q n := by
  sorry
```

## File: QseriesFormalization/Chapter15.lean
Insert after `qDeriv_qPoch` and before `R_trunc_nesting_eleven`.

## Constraints
- No sorry, no axiom, no native_decide
- `lake build QseriesFormalization.Chapter15` must pass
- Work within `section Field` / `variable {R : Type*} [Field R]`
- Use `∈` not `in` for Finset membership
- The qDeriv_smul hypothesis for the IH step: the inner function
  `qDerivIter (fun t => t ^ n) q k` at point `q^j * x` requires careful handling

## Build command
```
lake build QseriesFormalization.Chapter15
```
