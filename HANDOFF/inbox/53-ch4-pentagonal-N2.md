# Task 53: Ch4 — Euler pentagonal truncation N=2 explicit

## Goal

In `Chapter04.lean`, add:

```lean
theorem eulerPentagonalProductTrunc_two (q : R) :
    eulerPentagonalProductTrunc q 2 = (1 - q) * (1 - q^2)

theorem eulerPentagonalSeriesTrunc_two (q : R) :
    eulerPentagonalSeriesTrunc q 2 = ?  -- compute it
```

For `eulerPentagonalSeriesTrunc q 2`:
bilateralSum at N=2 has terms j ∈ {-2,-1,0,1,2}.
- j=0: (-1)^0 · q^{0} = 1
- j=1: (-1)^1 · q^{pentagonalIndex 1} = -q^{1·4/2} = -q^2
- j=-1: (-1)^0 · q^{pentagonalIndex (-1)} = q^{(-1)·(-2)/2} = q^1
- j=2: (-1)^0 · q^{pentagonalIndex 2} = q^{2·7/2} = q^7
- j=-2: (-1)^0 · q^{pentagonalIndex (-2)} = q^{(-2)·(-5)/2} = q^5

(Note: Int.toNat of negative j is 0, so signs may not match real
pentagonal series. Document the N=2 truncation as Lean computes it.)

Touch only Chapter04.lean. No axiom/sorry/native_decide. lake build clean.
