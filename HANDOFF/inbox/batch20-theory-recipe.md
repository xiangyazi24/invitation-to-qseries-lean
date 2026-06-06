# Batch 20: q-Calculus Theoretical Proofs

## Context
Chapter15.lean now has the basic q-calculus infrastructure:
- `qDeriv` definition (line 15)
- `qInt` definition (q-integer [n]_q = ∑_{i=0}^{n-1} q^i)
- `qDeriv_pow` (general: D_q(x^n) = [n]_q · x^{n-1})
- `qDeriv_add`, `qDeriv_smul` (linearity)
- `qDeriv_mul`, `qDeriv_mul'` (Leibniz product rule)

## Task 1: Iterated q-derivative and D_q^2(x^n)

Define the iterated q-derivative and prove the second derivative formula.

```lean
noncomputable def qDerivIter (f : R → R) (q : R) : ℕ → R → R
  | 0 => f
  | n + 1 => fun x => qDeriv (qDerivIter f q n) q x

theorem qDerivIter_two_pow (q x : R) (hqx : (q - 1) * x ≠ 0)
    (hq2x : (q - 1) * (q * x) ≠ 0) (n : ℕ) :
    qDerivIter (fun t => t ^ n) q 2 x =
    qInt q n * qInt q (n - 1) * x ^ (n - 2) := by
  sorry
```

The proof: `D_q^2(x^n) = D_q([n]_q · x^{n-1}) = [n]_q · D_q(x^{n-1}) = [n]_q · [n-1]_q · x^{n-2}`.
Uses `qDeriv_smul` and `qDeriv_pow`.

## Task 2: q-factorial and q-binomial via q-integers

```lean
noncomputable def qFactorial (q : R) : ℕ → R
  | 0 => 1
  | n + 1 => qFactorial q n * qInt q (n + 1)

theorem qFactorial_pos_of_qInt_pos (q : R) (hq : ∀ k, 0 < k → qInt q k ≠ 0) (n : ℕ) :
    qFactorial q n ≠ 0 := by
  sorry
```

## Task 3: q-exponential and q-Taylor base case

Define the q-exponential e_q(x) = ∑_{n≥0} x^n / [n]_q! (truncated):

```lean
noncomputable def qExpTrunc (q x : R) : ℕ → R
  | 0 => 1
  | n + 1 => qExpTrunc q x n + x ^ (n + 1) / qFactorial q (n + 1)

theorem qDeriv_qExpTrunc_succ (q x : R) (hqx : (q - 1) * x ≠ 0) (n : ℕ) :
    qDeriv (qExpTrunc q · (n + 1)) q x = qExpTrunc q (q * x) n := by
  sorry
```

## Task 4: q-derivative of q-Pochhammer (key for RRCF diff eq)

The q-Pochhammer `(a;q)_n = ∏_{k=0}^{n-1}(1-aq^k)` satisfies:
`D_q((a;q)_n)(a) = -[n]_q · (aq;q)_{n-1}`

This connects the q-calculus to the partition theory.

```lean
theorem qDeriv_qPoch (q a : R) (ha : a ≠ 0) (hqa : (q - 1) * a ≠ 0) (n : ℕ) :
    qDeriv (fun z => qPoch z q n) q a = 
    -qInt q n * qPoch (a * q) q (n - 1) := by
  sorry
```

## Constraints
- No sorry in final output
- No axiom, no native_decide
- Must `lake build QseriesFormalization.Chapter15` pass
- Insert after `qDeriv_mul'` and before `R_trunc_nesting_eleven`
- All within `section Field` / `variable {R : Type*} [Field R]`
- Use `∈` not `in` for Finset membership

## Build command
```
lake build QseriesFormalization.Chapter15
```
