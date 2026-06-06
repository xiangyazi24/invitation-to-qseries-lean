# Task 51: Ch11 — more golden ratio identities

## Goal

Add to `Chapter11.lean` (current has α, β, α+β=1, αβ=-1, α²=α+1):

```lean
theorem β_sq : β^2 = β + 1 := …  -- since β satisfies same minimal polynomial

theorem α_cubed : α^3 = 2 * α + 1 := …  -- α^3 = α·α² = α(α+1) = α² + α = (α+1) + α = 2α+1
theorem β_cubed : β^3 = 2 * β + 1 := …

theorem α_inv : α⁻¹ = α - 1 := …  -- since α(α-1) = α² - α = 1
theorem β_inv : β⁻¹ = β - 1 := …  -- using β² = β+1, β(β-1) = β²-β = 1
```

Use `field_simp`, `Real.sq_sqrt`, `ring` patterns.

Touch only Chapter11.lean. No axiom/sorry/native_decide. lake build clean.
