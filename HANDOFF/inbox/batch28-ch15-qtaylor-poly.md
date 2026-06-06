# Batch 28: Ch15 — q-Taylor Formula for Monomials

## Context
Chapter15.lean (2521 lines) now has:
- `qDeriv`, `qDeriv_pow`, `qDeriv_add`, `qDeriv_smul`, `qDeriv_const`
- `qDerivIter`, `qDerivIter_pow` — D_q^k(x^n) = [n]_q^{(k)} · x^{n-k}
- `qDerivIter_pow_self` — D_q^n(x^n) = [n]_q!
- `qFallingFactorial`, `qFallingFactorial_self`, `qFallingFactorial_eq_div`, `qFallingFactorial_eq_zero_of_gt`
- `qFactorial`, `qFactorial_ne_zero`, `qFactorial_succ`, `qFactorial_eq_prod`
- `qExpTrunc`, `qDeriv_qExpTrunc`
- `qInt`, `qInt_zero/one/two`, `qInt_mul_sub`, `qInt_succ`
- All within `section Field` / `variable {R : Type*} [Field R]`

## Goal: q-Taylor expansion for x^n

The q-Taylor formula says: for a polynomial f, f(x) = ∑_{k=0}^{deg f} D_q^k(f)(0)/[k]_q! · x^k.

For monomials f(x) = x^n, this gives:
x^n = ∑_{k=0}^{n} (D_q^k(x^n))(0)/[k]_q! · (something involving x and q)

BUT: D_q^k(x^n)(0) is problematic because qDeriv requires (q-1)x ≠ 0, and at x=0 this fails.

### Alternative: q-Taylor at x = a (nonzero)

The q-Taylor expansion of f around a:
f(x) = ∑_{k=0}^{n} D_q^k(f)(a) / [k]_q! · ∏_{j=0}^{k-1}(x - q^j·a)

For our case, prove the identity for monomials using what we already have.

### Practical Task: Prove D_q^{n+1}(x^n) = 0

Since qDerivIter_pow gives D_q^k(x^n) = [n]_q^{(k)} · x^{n-k} when k ≤ n,
and qFallingFactorial_eq_zero_of_gt shows [n]_q^{(k)} = 0 when k > n,
we should be able to prove D_q^{n+1}(x^n) = 0.

BUT: qDerivIter_pow_aux requires k ≤ n, so we can't directly apply it for k = n+1.

Instead, we can prove:
D_q^{n+1}(x^n) = D_q(D_q^n(x^n)) = D_q([n]_q!) = 0

since [n]_q! is a constant and D_q of a constant is 0.

```lean
/-- D_q^{n+1}(x^n) = 0: the (n+1)-th q-derivative of x^n vanishes. -/
theorem qDerivIter_pow_succ (q x : R) (n : ℕ)
    (hiter : ∀ j : ℕ, j < n + 1 → (q - 1) * (q ^ j * x) ≠ 0) :
    qDerivIter (fun t => t ^ n) q (n + 1) x = 0 := by
  rw [qDerivIter, qDerivIter_pow_self q _ n (fun j hj => hiter j (by omega))]
  -- Goal: qDeriv (fun _ => qFactorial q n) q x = 0
  sorry
```

### Task 1: D_q of constant function (if not already present)

Check if `qDeriv_const` exists. If it does, use it.

```lean
-- This should already exist as qDeriv_const
-- theorem qDeriv_const (c q x : R) : qDeriv (fun _ => c) q x = 0
```

### Task 2: D_q^{n+1}(x^n) = 0

```lean
theorem qDerivIter_pow_succ_self (q x : R) (n : ℕ)
    (hiter : ∀ j : ℕ, j < n + 1 → (q - 1) * (q ^ j * x) ≠ 0) :
    qDerivIter (fun t => t ^ n) q (n + 1) x = 0 := by
  simp only [qDerivIter_succ]
  rw [qDerivIter_pow_self q x n (fun j hj => hiter j (by omega))]
  -- Now need: qDeriv (fun _ => qFactorial q n) q x = 0
  exact qDeriv_const (qFactorial q n) q x
```

Wait — there's a subtlety. `qDerivIter_pow_self` gives us:
`qDerivIter (fun t => t ^ n) q n x = qFactorial q n`

This is an *equation* saying the result is a particular value. But `qDerivIter ... q (n+1) x = qDeriv (qDerivIter (fun t => t^n) q n) q x`, and `qDerivIter (fun t => t^n) q n` is a *function* R → R, not a constant.

The key: we need `qDerivIter (fun t => t ^ n) q n = fun _ => qFactorial q n` (as a function equality), not just pointwise.

This needs: `funext x => qDerivIter_pow_self` but that requires the hiter hypothesis for each x.

Actually this is trickier. Let me re-scope.

### Revised Task 2: qDeriv applied to qFactorial after iterated derivative

The clean approach uses the fact that after n iterations on x^n, we get a constant:

```lean
/-- After n q-derivatives, x^n becomes the constant [n]_q!.
The next derivative kills it: D_q^{n+1}(x^n) = 0. -/
theorem qDerivIter_pow_succ_self (q x : R) (n : ℕ)
    (hiter : ∀ j : ℕ, j ≤ n → (q - 1) * (q ^ j * x) ≠ 0) :
    qDerivIter (fun t => t ^ n) q (n + 1) x = 0 := by
  -- D_q^{n+1}(x^n)(x) = D_q(D_q^n(x^n))(x)
  -- = D_q(fun y => [n]_q^{(n)} · y^0)(x)  by qDerivIter_pow_aux
  -- = D_q(fun y => [n]_q!)(x)              by qFallingFactorial_self
  -- = 0                                     by qDeriv_const
  simp only [show n + 1 = n + 1 from rfl]
  rw [qDerivIter_succ]
  -- qDerivIter_pow_aux gives us the function form
  have hfn : qDerivIter (fun t => t ^ n) q n =
      fun y => qFallingFactorial q n n * y ^ (n - n) := by
    ext y
    -- Need hypothesis for arbitrary y, which we don't have...
    sorry
  sorry
```

Hmm, this is the core difficulty: qDerivIter_pow_aux requires the nonzero hypothesis for the specific point, so we can't get function-level equality.

### Revised approach: Direct computation via qDerivIter_pow for k = n, then show one more step

Actually let's try a different, more direct approach. Since we have
`qDerivIter_pow q x n n le_rfl hiter_n : qDerivIter (fun t => t^n) q n x = [n]_q!`

and we want to show `qDerivIter (fun t => t^n) q (n+1) x = 0`, we can unfold:
`qDerivIter (fun t => t^n) q (n+1) x = qDeriv (qDerivIter (fun t => t^n) q n) q x`

Then show `qDeriv (qDerivIter (fun t => t^n) q n) q x = qDeriv (fun y => [n]^(n) * y^0) q x`.

We'd need `qDerivIter (fun t => t^n) q n` to be *equal as a function* to `fun y => [n]^(n) * y^0`.

This requires the hypothesis to hold for all relevant points, including q*x.

Let's just state a cleaner version:

```lean
theorem qDerivIter_pow_succ_self (q x : R) (n : ℕ)
    (hiter : ∀ j : ℕ, j ≤ n → (q - 1) * (q ^ j * x) ≠ 0) :
    qDerivIter (fun t => t ^ n) q (n + 1) x = 0 := by
  rw [qDerivIter_succ]
  -- Show qDerivIter (fun t => t ^ n) q n behaves as fun y => [n]_q! on {x, qx}
  simp only [qDeriv]
  -- qDerivIter at q*x and at x both equal [n]_q!
  have h1 : qDerivIter (fun t => t ^ n) q n x = qFactorial q n :=
    qDerivIter_pow_self q x n (fun j hj => hiter j (by omega))
  have h2 : qDerivIter (fun t => t ^ n) q n (q * x) = qFactorial q n :=
    qDerivIter_pow_self q (q * x) n (fun j hj => by
      rw [show q ^ j * (q * x) = q ^ (j + 1) * x from by ring]
      exact hiter (j + 1) (by omega))
  rw [h2, h1, sub_self, zero_div]
```

THIS should work! The key insight: evaluate qDerivIter at both x and q*x, show both give [n]_q!, so the q-derivative (difference quotient) is (c-c)/denominator = 0.

## File: QseriesFormalization/Chapter15.lean
Insert after `qFallingFactorial_eq_div` and before `R_trunc_nesting_eleven`.

## Constraints
- No sorry, no axiom, no native_decide
- `lake build QseriesFormalization.Chapter15` must pass
- The proof for qDerivIter_pow_succ_self uses `qDeriv` unfolding + two pointwise evaluations

## Build command
```
lake build QseriesFormalization.Chapter15
```
