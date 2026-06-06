# Task 56: Ch7 RR LHSTrunc N=3 closed form

In `Chapter07.lean`:

```lean
theorem rogersRamanujanLHSTrunc_three (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 3 =
      1 + q^(1+a)/(1-q) +
      q^(4+2*a)/((1-q)*(1-q^2)) +
      q^(9+3*a)/((1-q)*(1-q^2)*(1-q^3))
```

Touch only Chapter07.lean. No axiom/sorry/native_decide. lake build clean.
