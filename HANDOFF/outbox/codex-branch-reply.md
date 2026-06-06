# Eta branch extraction at tau = 5i

Closed in `QseriesFormalization/Pending/EtaSTransform.lean`.

What changed:
- Replaced the old global branch placeholder name with
  `GlobalEtaSBranchFormula`, so the unproved full-plane branch statement is
  still available under an explicit name.
- Proved `EtaSBranchFormula` unconditionally as the local Chapter 12 branch:

```lean
ModularForm.eta (Complex.I / 5) =
  (Real.sqrt 5 : ℂ) * ModularForm.eta ((5 : ℂ) * Complex.I)
```

Proof route:
- Kept the existing 24th-power identity
  `eta(S • tau)^24 = tau^12 * eta(tau)^24`.
- Specialized it at `tau = 5i` and rewrote the S-factor as `sqrt 5`.
- Proved `eta(I*t)` is the coercion of a positive real for `t > 0` from
  Mathlib's product definition:
  `qParam 24 (I*t)` is a positive real exponential, and the Euler product is a
  positive real product using `Real.rexp_tsum_eq_tprod`.
- Applied `pow_left_inj₀` on positive reals to extract the 24th root.

Validation:
```bash
lake env lean QseriesFormalization/Pending/EtaSTransform.lean
lake env lean QseriesFormalization/Pending/Chapter12_EtaValue.lean
rg -n "sorry|axiom|admit" QseriesFormalization/Pending/EtaSTransform.lean QseriesFormalization/Pending/Chapter12_EtaValue.lean -S
```

All checks pass. The grep returns no hits.
