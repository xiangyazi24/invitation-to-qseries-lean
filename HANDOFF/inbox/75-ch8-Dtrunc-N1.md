# Task 75: Ch8 — D_trunc and D_partialSum at N=1

In `Chapter08.lean`, add closed-form evaluations at N=1.

The definition is:
```
D_partialSum q a N = natSum (fun n => q ^ (n * n + a * n) / qPochhammer q n) N
```

At N=1 the sum has terms n=0 and n=1:
- n=0: q^0 / qPochhammer q 0 = 1 / 1 = 1
- n=1: q^(1 + a) / qPochhammer q 1 = q^(1+a) / (1 - q)

Add:

```lean
/-- N=1 closed form for D_partialSum. -/
theorem D_partialSum_one (q : R) (a : Nat) :
    D_partialSum q a 1 = 1 + q ^ (1 + a) / (1 - q) := by
  simp [D_partialSum, natSum, qPochhammer]

/-- N=1 closed form for D_trunc. -/
theorem D_trunc_one (q : R) (a : Nat) :
    D_trunc q a 1 = 1 + q ^ (1 + a) / (1 - q) := by
  exact D_partialSum_one q a

/-- Specialization: D_trunc q 0 1 = 1 + q / (1 - q). -/
theorem D_trunc_one_a0 (q : R) :
    D_trunc q 0 1 = 1 + q / (1 - q) := by
  simp [D_trunc_one]

/-- Specialization: D_trunc q 1 1 = 1 + q^2 / (1 - q). -/
theorem D_trunc_one_a1 (q : R) :
    D_trunc q 1 1 = 1 + q ^ 2 / (1 - q) := by
  simp [D_trunc_one]
```

Adjust the proof if `natSum` unfolding or `qPochhammer` normalization requires `ring` or `field_simp` instead of plain `simp`.

Touch only Chapter08.lean. No axiom/sorry/native_decide. lake build clean.
