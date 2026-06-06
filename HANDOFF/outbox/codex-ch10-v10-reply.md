# Codex Ch20 Eisenstein reply

Implemented `QseriesFormalization/Pending/Chapter20_Eisenstein.lean`.

Single-file check passes:

```bash
lake env lean QseriesFormalization/Pending/Chapter20_Eisenstein.lean
```

No `sorry`, `axiom`, or `admit` in the new file.

What is proved:

- Defined the formal series over `ℚ⟦X⟧`:
  `divisorSigmaPS`, `eisensteinE2PS`, `eisensteinE4PS`, `eisensteinE6PS`.
- Proved the eta-product side:
  `thetaOp_discriminantPS_eq_eisensteinE2PS_mul`
  and
  `eisensteinDiscriminantRHS_theta_eq`.
- Proved the correct uniqueness lemma for this first-order theta equation:
  `eq_of_same_theta_eq_mul_coeff_zero_one`.
  Since here `A.coeff 0 = 1`, coefficient `1` is a free initial datum; constant term alone is not enough.
- Proved the needed initial coefficients:
  `coeff_zero_eisensteinDiscriminantLHS`,
  `coeff_one_eisensteinDiscriminantLHS`,
  `coeff_zero_eisensteinDiscriminantRHS`,
  `coeff_one_eisensteinDiscriminantRHS`.
- Proved the final assembly theorem conditional on the two Ramanujan theta equations:

```lean
theorem eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS
    (hE4 : RamanujanThetaE4) (hE6 : RamanujanThetaE6) :
    eisensteinE4PS ^ 3 - eisensteinE6PS ^ 2 =
      (PowerSeries.C (1728 : ℚ)) * discriminantPS ℚ
```

Remaining gap:

```lean
def RamanujanThetaE4 : Prop :=
  (3 : ℚ⟦X⟧) * thetaOp eisensteinE4PS =
    eisensteinE2PS * eisensteinE4PS - eisensteinE6PS

def RamanujanThetaE6 : Prop :=
  (2 : ℚ⟦X⟧) * thetaOp eisensteinE6PS =
    eisensteinE2PS * eisensteinE6PS - eisensteinE4PS ^ 2
```

These are exactly the missing sigma convolution identities for `σ₁ * σ₃` and
`σ₁ * σ₅`.  Once those two are proved, the formal Eisenstein identity follows
immediately from the theorem above.

Important correction to the proposed route: the existing theta-log uniqueness
with `A.coeff 0 = 0` does not apply directly to `E4^3 - E6^2` and `1728Δ`.
Both series have constant term `0`, and their common theta equation has
`A = E2` with `A.coeff 0 = 1`.  The recurrence determines all coefficients
from degrees `0` and `1`, not from degree `0` alone.
