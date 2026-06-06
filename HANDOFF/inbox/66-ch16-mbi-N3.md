# Task 66: Ch16 — MBI N=3 RHS num/den explicit

In `Chapter16.lean`:

```lean
theorem mbiRHSNumeratorTrunc_three (q : R) :
    mbiRHSNumeratorTrunc q 3 = (1 - q^5)^5 * (1 - q^10)^5 * (1 - q^15)^5

theorem mbiRHSDenominatorTrunc_three (q : R) :
    mbiRHSDenominatorTrunc q 3 = (1 - q)^6 * (1 - q^2)^6 * (1 - q^3)^6
```

Touch only Chapter16.lean. No axiom/sorry/native_decide. lake build clean.
