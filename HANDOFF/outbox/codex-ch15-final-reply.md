# codex-ch15-final reply

I did not close `chan_theorem_11_7_int_core`.

What changed:

- Added `chan_theorem_11_7_int_core_of_complex` in
  `QseriesFormalization/Pending/Chapter15_R_ODE.lean`.
- This proves the descent step: the Complex formal-PS identity
  ```lean
  chan15LHSPS ℂ * (PowerSeries.expand 5 (by decide) (qPochInfPS ℂ)) =
    (qPochInfPS ℂ) ^ 5
  ```
  implies the integral core by `PowerSeries.map_injective` and
  `Int.cast_injective`.

Verification:

- Ran:
  ```bash
  lake env lean QseriesFormalization/Pending/Chapter15_R_ODE.lean
  ```
- Result: success, with the existing warning that
  `chan_theorem_11_7_int_core_coeff` uses `sorry`.

Precise blocker:

- The missing theorem is not the `ℤ → ℂ` descent. That step is now formalized.
- The missing theorem is the Complex/formal analytic identity itself,
  equivalently the all-`N` coefficient theorem
  `chan_theorem_11_7_int_core_coeff`.
- Existing `Chapter16_MBI_Proof.lean` and `RamanujanQuinticJTP.lean` provide
  the fifth-root product collapse / MBI denominator identity. Existing
  `Chapter13_Eq1237.lean` packages the product-core identity. None of these
  identifies the eta quotient with the Lambert/divisor-sum series
  `chan15LHSPS`.
- Mathlib has eta differentiability/log-derivative infrastructure and level-1
  Eisenstein q-expansions, but I did not find a ready level-5 eta-quotient
  modularity/Sturm route or a Dobbie identity that would close this.

Likely next routes:

1. Formalize Dobbie Eq. 15.1 specialized at `x = ζ`, `z = ζ^2`, then collapse
   the residue classes to the mod-5 character `χ₅`.
2. Prove a fifth-root/Jacobi derivative identity analogous to the existing
   derivative proof in `Chapter04_T43.lean`.
3. Build the modular-forms route: eta quotient modularity, the level-5
   Eisenstein/Lambert q-expansion, and the Sturm-bound comparison.
