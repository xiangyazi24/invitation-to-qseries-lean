# Task: Extend Ch11 CF coefficient verification degrees 11-20

## Context
`QseriesFormalization/Pending/Chapter11_RRCF_Convergent.lean` has CF-side
coefficient verification for `rrcf_r_via_CF.coeff k` at degrees 0-10.

The proof pattern uses the product identity `R_k · A_k = B_k` and extracts
degree-k coefficient via Cauchy product + recurrence peeling of A_k/B_k.

## What to do
Add `coeff_eleven_rrcf_r_via_CF` through `coeff_twenty_rrcf_r_via_CF`.

Expected values of r(q): degrees 0-20 are
`[1, -1, 1, 0, -1, 1, -1, 1, 0, -1, 2, -3, 3, -2, 1, 0, -1, 2, -4, 5, -4]`

## Proof pattern (CRITICAL — use recurrence peeling, NOT explicit polynomials)
```lean
@[simp] theorem coeff_N_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff N = <value> := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS N
  have hcoeff : (rrcf_RPS N * rrcf_APS N).coeff N = (rrcf_BPS N).coeff N :=
    congr_arg (·.coeff N) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [show (Finset.antidiagonal N : Finset (ℕ × ℕ)) = {...} from rfl] at hcoeff
  rw [Finset.sum_insert ..., ..., Finset.sum_singleton] at hcoeff
  -- hR0 through hR{N-1}: stabilization + prior coeff lemmas
  -- hA0 through hAN: recurrence peeling (conv_lhs => rw [rrcf_APS_succ_succ ...])
  -- hBN: same peeling for B
  rw [...] at hcoeff
  linarith
```

For A_k/B_k coefficient extraction at degree j < k:
- Peel `rrcf_APS_succ_succ (n := m)` repeatedly until reaching `rrcf_APS_three`/`rrcf_APS_two`
- Use `PowerSeries.coeff_X_pow_mul'` with `if_neg/if_pos` to handle `X^m * f` terms
- At the base (`rrcf_APS_three = 1+X+X²+X³+X⁴`): `simp [coeff_one, coeff_X_pow] + norm_num`

## Build
```
export PATH=$HOME/.elan/bin:$PATH
lake env lean QseriesFormalization/Pending/Chapter11_RRCF_Convergent.lean
```
This is a Pending file, not in the main build graph.

## Constraints
- NO sorry, NO axiom, NO native_decide
- Add `@[simp]` to each new theorem
- Insert before `end Ch11RRCFConvergent`
- If compile time per theorem exceeds 10 min, note and stop
