Ch20 Eisenstein update:

Worked in `QseriesFormalization/Pending/Chapter20_Eisenstein.lean`.

What I added:

- Factored the finite Ramanujan-theta residual check into
  `ramanujanThetaResidualCoeffZThroughCheck (N : Nat)`.
- Kept the existing degree-10 result via this generic checker:
  `ramanujanThetaResidualCoeffZThrough10Check_true`.
- Added native-computed degree-50 and degree-100 checks:
  `ramanujanThetaResidualCoeffZThrough50Check_true`
  and `ramanujanThetaResidualCoeffZThrough100Check_true`.
- Added a generic bridge theorem:

```lean
theorem ramanujanThetaResidual_coeff_zero_through_of_check
    {N : Nat} (hcheck : ramanujanThetaResidualCoeffZThroughCheck N = true)
    (n : Nat) (hn : n ≤ N) :
    (((3 : ℚ⟦X⟧) * thetaOp eisensteinE4PS -
        (eisensteinE2PS * eisensteinE4PS - eisensteinE6PS)).coeff n = 0) ∧
    (((2 : ℚ⟦X⟧) * thetaOp eisensteinE6PS -
        (eisensteinE2PS * eisensteinE6PS - eisensteinE4PS ^ 2)).coeff n = 0)
```

- Added instantiated coefficient vanishing theorems through 10, 50, and 100:
  `ramanujanThetaResidual_coeff_zero_through_ten`,
  `ramanujanThetaResidual_coeff_zero_through_fifty`,
  and `ramanujanThetaResidual_coeff_zero_through_one_hundred`.

Verification:

```bash
lake env lean QseriesFormalization/Pending/Chapter20_Eisenstein.lean
```

passes.

Status of the all-n proof:

I did not close the global Ramanujan theta equations. The finite `native_decide`
route now reaches degree 100 cleanly, but this still does not imply the
all-coefficient identities without an additional global recurrence / Sturm-type
bound / modular-forms theorem. The suggested residual recurrence route remains
the right next target, but I did not find an existing non-circular recurrence in
the current file: deriving a product-structure recurrence for the residual seems
to require essentially the same Ramanujan theta equations or another modular
forms input.

So the current file is stronger computational evidence plus reusable finite
coefficient theorems, not a completed all-n proof.
