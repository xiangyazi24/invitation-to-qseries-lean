# Task: Close degree-1 coefficient verification of Chan Theorem 11.5

## Context
`QseriesFormalization/Pending/Chapter13_CoeffVerification.lean` has 5 sorry stubs
for degree-level verification of Chan's "difficult and deep" identity:

```
r(q)^5 * B(v) = expand(5, r) * A(v)
```

where `v = X * expand(5, r)`, `A(v) = 1 - 2v + 4v² - 3v³ + v⁴`,
`B(v) = 1 + 3v + 4v² + 2v³ + v⁴`.

## What to prove (start with degree 1 only)

```lean
theorem coeff_one_chan_theorem_11_5_LHS_eq_RHS :
    (rrcf_r ^ 5 * (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4)).coeff 1 =
      ((PowerSeries.expand 5 (by decide) rrcf_r) *
        (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4)).coeff 1
```

## Key coefficient values (already proved in the file)
- `rrcf_r.coeff 0 = 1`, `rrcf_r.coeff 1 = -1`
- `rrcf_v.coeff 0 = 0`, `rrcf_v.coeff 1 = 1`, `rrcf_v.coeff k = 0` for k=2,3,4,5
- `(expand 5 rrcf_r).coeff 0 = 1`, `(expand 5 rrcf_r).coeff k = 0` for 1≤k≤4

## Numerical computation
LHS.coeff 1 = (r^5).coeff 0 * B(v).coeff 1 + (r^5).coeff 1 * B(v).coeff 0
            = 1 * 3 + (-5) * 1 = -2

RHS.coeff 1 = (expand5 r).coeff 0 * A(v).coeff 1 + (expand5 r).coeff 1 * A(v).coeff 0
            = 1 * (-2) + 0 * 1 = -2

So both sides = -2 at degree 1.

## Strategy
1. Compute `(rrcf_r ^ 5).coeff 0 = 1` and `(rrcf_r ^ 5).coeff 1 = -5`
   - coeff 0: `map_pow constantCoeff`, `(constantCoeff rrcf_r)^5 = 1^5 = 1`
   - coeff 1: `coeff 1 (f^5) = 5 * f.coeff 0^4 * f.coeff 1` (power series power rule)
     = `5 * 1 * (-1) = -5`
2. Compute B(v).coeff 0 = 1, B(v).coeff 1 = 3
   - B(v) = 1 + 3v + ..., and v.coeff 0 = 0, so B(v).coeff 0 = 1
   - B(v).coeff 1 = 3 * v.coeff 1 = 3 * 1 = 3
3. Similarly A(v).coeff 0 = 1, A(v).coeff 1 = -2
4. (expand5 r).coeff 0 = 1, (expand5 r).coeff 1 = 0
5. Both sides: 1*3 + (-5)*1 = -2 = 1*(-2) + 0*1

## Build
```
export PATH=$HOME/.elan/bin:$PATH
lake env lean QseriesFormalization/Pending/Chapter13_CoeffVerification.lean
```

## Constraints
- NO sorry, NO axiom, NO native_decide
- Only close the degree-1 sorry. Leave degrees 2-5 as sorry.
- Use `PowerSeries.coeff_mul` for products, `PowerSeries.coeff_pow` or iterated
  `coeff_mul` for `rrcf_r^5`
