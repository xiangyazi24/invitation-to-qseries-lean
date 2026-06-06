# Task 62: Ch1 partitionGenFn N=11 closed form

In `Chapter01.lean`, extend t23's `partitionGenFn_ten` to N=11:

```lean
theorem partitionGenFn_eleven (q : R) :
    partitionGenFn q 11 =
      1 + q + 2*q^2 + 3*q^3 + 5*q^4 + 7*q^5 + 11*q^6 + 15*q^7 +
      22*q^8 + 30*q^9 + 42*q^10 + 56*q^11 := by
  …
```

Use partitionCount_eleven (= 56) from t22.

Touch only Chapter01.lean. No axiom/sorry/native_decide. lake build clean.
