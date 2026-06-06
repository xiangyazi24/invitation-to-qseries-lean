# Task 71: Ch10 — mock theta truncation N=2

In `Chapter10.lean`:

```lean
theorem ramanujanMockF_trunc_two (q : R) :
    ramanujanMockF_trunc q 2 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2)

-- f(0)=1, f(1)=q/(1+q)², f(2)=q^4/((1+q)(1+q²))² = q^4/((1+q)(1+q²))^2
```

Touch only Chapter10.lean. No axiom/sorry/native_decide. lake build clean.
