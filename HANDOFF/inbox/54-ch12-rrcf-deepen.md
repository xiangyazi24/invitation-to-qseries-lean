# Task 54: Ch12 — RRCF deepen with α/β identities

## Goal

In `Chapter12.lean` (currently has just `ramanujanRRCFValue := α⁻¹ + β`):

Add concrete sanity using golden ratio identities (from Ch11):

```lean
theorem ramanujanRRCFValue_eq_simple : ramanujanRRCFValue = (α - 1) + β := by
  rw [ramanujanRRCFValue, α_inv]  -- needs t51 to be merged

-- Using α + β = 1: α - 1 + β = α + β - 1 = 0. But Chan's identity says
-- R(e^{-2π}) = 2 + β - β = 2. So our def `α⁻¹ + β` isn't quite right;
-- the actual Ramanujan value should be the result of evaluating the
-- continued fraction R(q) at q = e^{-2π}. Document this discrepancy
-- and the correct numerical value.

-- Concrete: ramanujanRRCFValue (as defined α⁻¹ + β = α - 1 + β = 0)
-- is a placeholder — Chan's actual value is 2 (give or take β arithmetic).
-- Real evaluation needs the continued fraction, which is analytic.
```

If t51 hasn't merged yet (parallel race), make this self-contained by
proving locally that `α⁻¹ = α - 1` from `α² = α + 1` (which IS in Ch11).

Touch only Chapter12.lean. No axiom/sorry/native_decide. lake build clean.
