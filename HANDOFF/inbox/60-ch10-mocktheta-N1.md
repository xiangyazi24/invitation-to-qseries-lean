# Task 60: Ch10 — ramanujanMockF_trunc N=1 closed form

Add to `Chapter10.lean`:

```lean
theorem ramanujanMockF_trunc_one (q : R) :
    ramanujanMockF_trunc q 1 = 1 + q / (1 + q)^2

-- f(0) = q^0 / (-q;q)_0² = 1 / 1 = 1
-- f(1) = q^1 / (-q;q)_1² = q / (1+q)² (since (-q;q)_1 = 1 + q)
-- Sum = 1 + q/(1+q)²
```

Touch only Chapter10.lean. No axiom/sorry/native_decide. lake build clean.
