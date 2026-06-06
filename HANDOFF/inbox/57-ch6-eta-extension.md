# Task 57: Ch6 — extend dedekindEtaTrunc to N=4, N=5

In `Chapter06.lean`:

```lean
theorem dedekindEtaTrunc_four (q : R) :
    dedekindEtaTrunc q 4 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4)

theorem dedekindEtaTrunc_five (q : R) :
    dedekindEtaTrunc q 5 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5)
```

Touch only Chapter06.lean. No axiom/sorry/native_decide. lake build clean.
