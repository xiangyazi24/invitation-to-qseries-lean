# Task 61: Ch18 — t-core ratio N=1 explicit

In `Chapter18.lean`:

```lean
theorem tCoreNumeratorTrunc_one (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 1 = (1 - q^t)^t

theorem tCoreDenominatorTrunc_one (q : R) :
    tCoreDenominatorTrunc q 1 = 1 - q
```

Touch only Chapter18.lean. No axiom/sorry/native_decide. lake build clean.
