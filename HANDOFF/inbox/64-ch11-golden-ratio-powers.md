# Task 64: Ch11 — α/β powers (Fibonacci-like recurrences)

In `Chapter11.lean` (pre-existing α/β/α²/β²/α³/β³/α⁻¹/β⁻¹):

```lean
/-- α^n satisfies Fibonacci-like recurrence α^{n+2} = α^{n+1} + α^n. -/
theorem α_recurrence (n : Nat) :
    α ^ (n + 2) = α ^ (n + 1) + α ^ n := by
  …  -- multiply α² = α + 1 by α^n

theorem β_recurrence (n : Nat) :
    β ^ (n + 2) = β ^ (n + 1) + β ^ n := …

theorem α_pow_four : α^4 = 3 * α + 2 := …
theorem α_pow_five : α^5 = 5 * α + 3 := …
```

(Each of these is `α^{n+2} = α^{n+1} + α^n` applied iteratively;
coefficients are Fibonacci numbers F(n+1)·α + F(n).)

Touch only Chapter11.lean. No axiom/sorry/native_decide. lake build clean.
