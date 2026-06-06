# Task 50: Ch7 — RR RHSTrunc N=2 closed form

## Goal

In `Chapter07.lean`, add (complementing `rogersRamanujanLHSTrunc_two`
from t40):

```lean
theorem rogersRamanujanRHSTrunc_two_a0 (q : R)
    (h1 : (1 - q) ≠ 0) (h4 : (1 - q^4) ≠ 0)
    (h6 : (1 - q^6) ≠ 0) (h9 : (1 - q^9) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 2 =
      1 / ((1 - q^9) * (1 - q^6) * (1 - q^4) * (1 - q))

theorem rogersRamanujanRHSTrunc_two_a1 (q : R)
    (h2 : (1 - q^2) ≠ 0) (h3 : (1 - q^3) ≠ 0)
    (h7 : (1 - q^7) ≠ 0) (h8 : (1 - q^8) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 2 =
      1 / ((1 - q^8) * (1 - q^7) * (1 - q^3) * (1 - q^2))
```

(For a=0, N=2: factors are `(1 - q^{5·1-1-0})(1 - q^{5·1-4+0})` for k=1,
`(1 - q^{5·2-1-0})(1 - q^{5·2-4+0})` for k=2 = (1-q^4)(1-q)·(1-q^9)(1-q^6).
For a=1: (1-q^3)(1-q^2)·(1-q^8)(1-q^7).)

Touch only Chapter07.lean. No axiom/sorry/native_decide. lake build clean.
