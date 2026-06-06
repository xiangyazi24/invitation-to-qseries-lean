# Task 68: Ch3 — qBinomialTerm zero / one identities

In `Chapter03.lean`:

```lean
theorem qBinomialTerm_one_zero (q x : R) : qBinomialTerm q x 1 0 = 1 := by
  simp [qBinomialTerm, gaussianBinom]

theorem qBinomialTerm_one_one (q x : R) : qBinomialTerm q x 1 1 = x := by
  simp [qBinomialTerm, gaussianBinom]

theorem qBinomialTerm_n_n (q x : R) (n : Nat) :
    qBinomialTerm q x n n = q ^ (n * (n - 1) / 2) * x ^ n := by
  simp [qBinomialTerm, gaussianBinom_self]
```

Touch only Chapter03.lean. No axiom/sorry/native_decide. lake build clean.
