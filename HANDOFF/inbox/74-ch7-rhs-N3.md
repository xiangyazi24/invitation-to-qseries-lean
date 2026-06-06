# Task 74: Ch7 — Rogers-Ramanujan RHS truncation N=3

In `Chapter07.lean`, extend `rogersRamanujanRHSTrunc` closed forms to N=3.

Pattern from N=2 (a=0): the RHS product `∏_{m=1}^N 1/((1-q^{5m-1})(1-q^{5m-4}))`.

Add:

```lean
/-- RHS truncation at `N = 3` for parameter `a = 0`. -/
theorem rogersRamanujanRHSTrunc_three_a0 (q : R)
    (h1 : (1 - q) ≠ 0) (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0) (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0) (h14 : (1 - q ^ 14) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 3 =
      1 / ((1 - q ^ 14) * (1 - q ^ 11) * (1 - q ^ 9) * (1 - q ^ 6) *
           (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14]

/-- RHS truncation at `N = 3` for parameter `a = 1`. -/
theorem rogersRamanujanRHSTrunc_three_a1 (q : R)
    (h2 : (1 - q ^ 2) ≠ 0) (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0) (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0) (h13 : (1 - q ^ 13) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 3 =
      1 / ((1 - q ^ 13) * (1 - q ^ 12) * (1 - q ^ 8) * (1 - q ^ 7) *
           (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13]
```

Verify the exponents from the definition of `rogersRamanujanRHSTrunc`. The factors for a=0 are `(1 - q^{5m-4})(1 - q^{5m-1})` for m=1,2,3 giving exponents 1,4,6,9,11,14. For a=1 they are `(1 - q^{5m-3})(1 - q^{5m-2})` for m=1,2,3 giving exponents 2,3,7,8,12,13.

Touch only Chapter07.lean. No axiom/sorry/native_decide. lake build clean.
