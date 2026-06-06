# Task 45: Ch2 — jacobiProductTrunc / jacobiSeriesTrunc small-N values

## Goal

Add to `Chapter02.lean` (in the existing `[Field R]` block):

```lean
theorem jacobiProductTrunc_one (q z : R) :
    jacobiProductTrunc q z 1 =
      (1 - q) * (1 + z) * (1 + q / z) := by
  simp [jacobiProductTrunc]; ring

theorem jacobiSeriesTrunc_one (q z : R) :
    jacobiSeriesTrunc q z 1 =
      1 + z * q + z⁻¹ * q := by
  simp [jacobiSeriesTrunc, triangular]; ring
```

(Note: `triangular 1 = 1`, so `q ^ triangular 1 = q ^ 1 = q`. The
factor `Inv.inv z` is `z⁻¹`.)

If the simp lemmas need help, unfold by hand.

Touch only `Chapter02.lean`. No axiom/sorry/native_decide. lake build clean.

## Deliverable

Modified file + reply.
