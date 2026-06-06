# Task 59: Ch11 — finite continued fraction R_trunc

Add to `Chapter11.lean`:

```lean
/-- Finite Rogers-Ramanujan continued fraction `R_trunc q N`.
At N=0: 1 (empty fraction). At N+1: 1 / (1 + q^(N+1) · R_trunc q N).
This builds the fraction "from the inside out". -/
noncomputable def R_trunc (q : ℂ) : Nat → ℂ
  | 0 => 1
  | Nat.succ n => 1 / (1 + q ^ (n + 1) * R_trunc q n)

theorem R_trunc_zero (q : ℂ) : R_trunc q 0 = 1 := rfl

theorem R_trunc_one (q : ℂ) : R_trunc q 1 = 1 / (1 + q) := by
  simp [R_trunc]
```

(Note: this is not exactly Chan's R(q), which has q^{1/5} prefactor and
a different convergent ordering. This is a placeholder/sanity stub.)

Touch only Chapter11.lean. No axiom/sorry/native_decide. lake build clean.
