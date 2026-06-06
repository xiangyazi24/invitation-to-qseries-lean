# Batch 25: Ch15 — q-Exponential Derivative Property

## Context
Chapter15.lean has a complete q-calculus layer:
- `qDeriv f q x = (f(qx) - f(x)) / ((q-1)x)`
- `qDeriv_pow` — D_q(x^n) = [n]_q · x^{n-1}
- `qDeriv_add` — D_q(f+g) = D_q(f) + D_q(g)
- `qDeriv_smul` — D_q(c·f) = c · D_q(f)
- `qInt q n` — q-integer [n]_q = ∑_{i<n} q^i
- `qFactorial q n` — [n]_q! = [1]_q·[2]_q·...·[n]_q
- `qFactorial_succ` — [n+1]_q! = [n]_q! · [n+1]_q
- `qFactorial_ne_zero` — nonzero when all q-integers are nonzero
- `qExpTrunc q x n` — truncated q-exponential ∑_{k=0}^{n} x^k/[k]_q!
- `qExpTrunc_succ` — e_q(x; n+1) = e_q(x; n) + x^{n+1}/[n+1]_q!

All within `section Field` / `variable {R : Type*} [Field R]`.

## Goal: D_q(e_q(x; n+1)) = e_q(x; n)

This is the q-analog of the classical fact that d/dx(e^x) = e^x.
For the truncated q-exponential:

D_q(e_q(x; n+1))(a) = e_q(a; n)

### Proof sketch by induction on n:

**Base case (n=0):**
D_q(e_q(x; 1))(a) = D_q(1 + x)(a) = D_q(1)(a) + D_q(x)(a) = 0 + 1 = 1 = e_q(a; 0) ✓

**Inductive step (n → n+1):**
D_q(e_q(x; n+2))(a)
= D_q(e_q(x; n+1) + x^{n+2}/[n+2]_q!)(a)     [by qExpTrunc_succ]
= D_q(e_q(x; n+1))(a) + D_q(x^{n+2}/[n+2]_q!)(a)  [by qDeriv_add]
= D_q(e_q(x; n+1))(a) + (1/[n+2]_q!) · D_q(x^{n+2})(a)  [by qDeriv_smul]
= e_q(a; n) + (1/[n+2]_q!) · [n+2]_q · a^{n+1}  [by IH + qDeriv_pow]
= e_q(a; n) + a^{n+1} / [n+1]_q!  [because [n+2]_q/[n+2]_q! = 1/[n+1]_q!]
= e_q(a; n+1)  [by qExpTrunc_succ]

### Task 1: Helper lemma for the division simplification

```lean
/-- [n+1]_q / [n+1]_q! = 1 / [n]_q! when [n+1]_q ≠ 0. -/
theorem qInt_div_qFactorial_succ (q : R) (n : ℕ) (hqn : qInt q (n + 1) ≠ 0) :
    qInt q (n + 1) / qFactorial q (n + 1) = 1 / qFactorial q n := by
  rw [qFactorial_succ, mul_comm]
  rw [div_mul_eq ... ]  -- or field_simp approach
```

Actually the cleanest approach: since [n+1]_q! = [n]_q! · [n+1]_q, we have:
  x^{n+2} / [n+2]_q! = x · x^{n+1} / ([n+1]_q! · [n+2]_q)

And D_q(c · x^{n+2}) for constant c = c · [n+2]_q · x^{n+1}, so:
  (1/[n+2]_q!) · [n+2]_q · x^{n+1} = x^{n+1} · [n+2]_q / [n+2]_q!
  = x^{n+1} · [n+2]_q / ([n+1]_q! · [n+2]_q) = x^{n+1} / [n+1]_q!

```lean
private lemma qDeriv_pow_div_factorial (q a : R) (hqa : (q - 1) * a ≠ 0)
    (n : ℕ) (hfac : qFactorial q (n + 1) ≠ 0) (hqn : qInt q (n + 1) ≠ 0) :
    qDeriv (fun x => x ^ (n + 1) / qFactorial q (n + 1)) q a =
      a ^ n / qFactorial q n := by
  rw [show (fun x => x ^ (n + 1) / qFactorial q (n + 1)) =
      (fun x => (1 / qFactorial q (n + 1)) * x ^ (n + 1)) from by ext; ring]
  rw [qDeriv_smul]
  rw [qDeriv_pow q a hqa (n + 1)]
  simp only [Nat.add_sub_cancel]
  rw [qFactorial_succ]
  field_simp
  ring
```

### Task 2: The main theorem

```lean
/-- The q-derivative of the truncated q-exponential:
D_q(e_q(x; n+1)) = e_q(x; n). This is the q-analog of d/dx(e^x) = e^x. -/
theorem qDeriv_qExpTrunc (q a : R) (hqa : (q - 1) * a ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → qInt q k ≠ 0) (n : ℕ) :
    qDeriv (fun x => qExpTrunc q x (n + 1)) q a = qExpTrunc q a n := by
  induction n with
  | zero =>
    -- D_q(1 + x) = 1
    simp only [qExpTrunc_succ, qExpTrunc_zero, qFactorial, qInt_one]
    rw [show (fun x => 1 + x ^ 1 / 1) = (fun x => 1 + x) from by ext; simp]
    rw [qDeriv_add]
    -- D_q(1) = 0, D_q(x) = [1]_q · x^0 = 1
    simp [qDeriv, qInt_one]
    sorry -- fill in details
  | succ m ih =>
    -- D_q(e_q(x; m+2)) = D_q(e_q(x; m+1) + x^{m+2}/[m+2]_q!)
    rw [show (fun x => qExpTrunc q x (m + 2)) =
        (fun x => qExpTrunc q x (m + 1) + x ^ (m + 2) / qFactorial q (m + 2)) from by
      ext; rfl]
    rw [qDeriv_add, ih]
    rw [qDeriv_pow_div_factorial q a hqa (m + 1)
      (qFactorial_ne_zero q hq_int (m + 2)) (hq_int (m + 2) (by omega))]
    rfl
```

## File: QseriesFormalization/Chapter15.lean
Insert after `qDerivIter_pow_self` (line 512) and before `R_trunc_nesting_eleven` (line 514).

## Constraints
- No sorry, no axiom, no native_decide
- `lake build QseriesFormalization.Chapter15` must pass
- Work within `section Field` / `variable {R : Type*} [Field R]`
- Key subtlety: `qDeriv_add` takes two functions; you need to show that `fun x => qExpTrunc q x (n+1)` equals `fun x => qExpTrunc q x n + x^{n+1}/[n+1]_q!` via `ext` + `rfl`
- The base case D_q(1) needs special handling since qDeriv(const) = 0
- D_q(const) = 0 proof: `simp [qDeriv]` should handle `(c - c) / _ = 0`

## Build command
```
lake build QseriesFormalization.Chapter15
```
