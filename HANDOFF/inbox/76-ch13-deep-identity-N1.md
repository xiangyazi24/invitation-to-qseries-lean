# Task 76: Ch13 — deep identity truncation N=1 + product structure

In `Chapter13.lean`, extend the "difficult and deep" identity scaffold.

Chan Ch 13 concerns the identity (Eq 13.1):
```
∑_{n≥0} q^{n²} / (q;q)_n² = ∏_{n≥1} 1/(1-q^n) · (1 + ∑_{n≥1} ...)
```

The truncated LHS sum (partial sum of q^{n²}/(q;q)_n²) is more useful than the current `qPochhammer` placeholder.

Replace the current placeholder with:

```lean
/-- Truncated LHS of Chan Ch 13 identity: `∑_{k=0}^N q^{k²} / (q;q)_k²`. -/
noncomputable def deepIdentityLHSTrunc (q : R) (N : Nat) : R :=
  natSum (fun k => q ^ (k * k) / (qPochhammer q k) ^ 2) N

/-- N=0 sanity: the 0-truncation is 1. -/
@[simp] theorem deepIdentityLHSTrunc_zero (q : R) :
    deepIdentityLHSTrunc q 0 = 1 := by
  simp [deepIdentityLHSTrunc, natSum, qPochhammer]

/-- N=1: `1 + q / (1 - q)²`. -/
theorem deepIdentityLHSTrunc_one (q : R) :
    deepIdentityLHSTrunc q 1 = 1 + q / (1 - q) ^ 2 := by
  simp [deepIdentityLHSTrunc, natSum, qPochhammer]
```

You may keep or remove the old `deepIdentityTrunc` placeholder (which was just `qPochhammer q N`). If you keep it, rename it to `deepIdentityRHSTrunc_placeholder` or similar to avoid confusion.

Touch only Chapter13.lean. No axiom/sorry/native_decide. lake build clean.
