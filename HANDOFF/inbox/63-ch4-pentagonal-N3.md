# Task 63: Ch4 — Euler pentagonal N=3 explicit

In `Chapter04.lean`:

```lean
theorem eulerPentagonalProductTrunc_three (q : R) :
    eulerPentagonalProductTrunc q 3 = (1 - q) * (1 - q^2) * (1 - q^3)
```

(eulerPentagonalSeriesTrunc N=3 has many terms; skip if too gnarly.)

Touch only Chapter04.lean. No axiom/sorry/native_decide. lake build clean.
