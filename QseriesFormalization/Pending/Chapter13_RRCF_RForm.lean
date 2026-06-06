import QseriesFormalization.Pending.JTP_FormalPS_Pentagonal
import QseriesFormalization.Pending.Chapter16_MBI_Proof

/-!
# Chapter 13 / §11.5 — the Rogers–Ramanujan continued fraction in fractional-power-free form

Chan's "difficult and deep" identity (Theorem 11.5) relates `u = R(q)` and `v = R(q⁵)`:
`u⁵ = v · (1 − 2v + 4v² − 3v³ + v⁴) / (1 + 3v + 4v² + 2v³ + v⁴)`.

The repo's `Chapter11.R_trunc` is a DEGENERATE truncation (its recurrence
`R_{n+1} = 1/(1+q^{n+1}R_n)` has `q^{n+1}→0`, so it converges trivially to `1`, NOT to the RRCF).
This file builds the CORRECT, fractional-power-free object.

**Key device.** `R(q) = q^{1/5}·r(q)` where
`r(q) = (q;q⁵)∞(q⁴;q⁵)∞ / ((q²;q⁵)∞(q³;q⁵)∞)` has NO fractional power — it is a genuine formal
power series. Moreover `r(q) = H(q)/G(q)` where `G,H` are the two Rogers–Ramanujan products; in the
repo's keystone variables `r = pentagonal014SeriesPS / pentagonal023SeriesPS` (numerically confirmed:
`pentagonal014 = (q,q⁴,q⁵;q⁵)`, `pentagonal023 = (q²,q³,q⁵;q⁵)`, and the `(q⁵;q⁵)` factors cancel in the
ratio, leaving exactly `r`).

With `u = q^{1/5} r(q)`, `v = q·r(q⁵)` (note `(q⁵)^{1/5} = q`, so `v` is fractional-power-free too),
Theorem 11.5 becomes the FORMAL POWER SERIES identity (verified numerically to degree 60, residual 0):
```
r(q)⁵ · (1 + 3v + 4v² + 2v³ + v⁴)  =  r(q⁵) · (1 − 2v + 4v² − 3v³ + v⁴),    v := X · r(q⁵).
```
`r(q⁵) = PowerSeries.expand 5 r`.

**Proof strategy (next steps, deep — Hardy: "difficult and deep").** This `u⁵ = v·N(v)/D(v)` form is
NOT the same as the R(q)-only quintic already proved in `RamanujanQuinticJTP` (`core·E(q⁵)=E(q)¹¹`); it
ADDITIONALLY relates `R(q)` to `R(q⁵)`, and the standard route is the **Gugg telescoping** (Chan §13.1 /
Hirschhorn §9.2): a product `Q = ∏ₖ tₖ` of single-mode factors telescopes to `R(q)⁵/R(q⁵)`, while a
second evaluation gives the rational function in `R(q⁵)`. Formalizing that telescoping is the substantial
remaining work. This file lays the fractional-power-free foundation only.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch13RRCF

open QseriesFormalization.Pending.JTPFormalPSPentagonal

/-- The fractional-power-free part of the Rogers–Ramanujan continued fraction,
`r(q) = R(q)·q^{-1/5} = (q,q⁴,q⁵;q⁵)∞ / (q²,q³,q⁵;q⁵)∞`, as a formal power series over `ℚ`.
(The shared `(q⁵;q⁵)∞` factor cancels, so this equals `H(q)/G(q)` for the RR functions `G,H`;
in keystone variables `r = pentagonal014SeriesPS / pentagonal023SeriesPS`.) -/
noncomputable def rrcf_r : PowerSeries ℚ :=
  pentagonal014SeriesPS ℚ * (pentagonal023SeriesPS ℚ)⁻¹

/-- `v := X · r(q⁵)`, the fractional-power-free image of `v = R(q⁵)` (since `(q⁵)^{1/5}=q=X`).
`r(q⁵) = PowerSeries.expand 5 rrcf_r`. -/
noncomputable def rrcf_v : PowerSeries ℚ :=
  PowerSeries.X * (PowerSeries.expand 5 (by decide) rrcf_r)

/-! ## Well-definedness of `rrcf_r`

Section 13.1 of Chan (and §9.2 of Hirschhorn) treats `r(q)` as if it were a
genuine power series; that is justified here because the denominator
`pentagonal023SeriesPS ℚ` has constant term `1`, hence is a unit in `ℚ⟦X⟧`,
hence has the standard formal-PS inverse and `rrcf_r · pentagonal023 =
pentagonal014` as a formal equality.  None of this is the deep Chan §13
identity (that requires Gugg telescoping); these are the bookkeeping facts
that need to be in place before any closure attempt can begin.
-/

open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.Ch16MBIProof

/-- The bilateral pentagonal series `(q²,q³,q⁵;q⁵)_∞ = ∑_{k∈ℤ}(-1)^k q^{k(5k-1)/2}`
has constant term `1` (its `k=0` term). -/
theorem coeff_zero_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 0 = 1 := by
  rw [← pentagonalProduct023PS_eq_pentagonal023SeriesPS_rat,
      coeff_pentagonalProduct023PS_eq_coeff_partial ℚ 0]
  simp [pentagonalTripleFactor023PS, apFactorPS]

/-- Likewise the bilateral pentagonal series `(q,q⁴,q⁵;q⁵)_∞ =
∑_{k∈ℤ}(-1)^k q^{k(5k-3)/2}` has constant term `1` (its `k=0` term). -/
theorem coeff_zero_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 0 = 1 := by
  rw [← pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat,
      coeff_pentagonalProduct014PS_eq_coeff_partial ℚ 0]
  simp [pentagonalTripleFactor014PS, apFactorPS]

/-- Explicit value of `pentagonal014Exp` at small integers: `pentagonal014Exp 1 = 1`. -/
theorem pentagonal014Exp_one : pentagonal014Exp 1 = 1 := by
  unfold pentagonal014Exp; rfl

/-- Explicit value of `pentagonal023Exp` at small integers: `pentagonal023Exp 0 = 0`. -/
theorem pentagonal023Exp_zero : pentagonal023Exp 0 = 0 := by
  unfold pentagonal023Exp; rfl

/-- The denominator of `rrcf_r` is a unit in the power-series ring `ℚ⟦X⟧`,
because its constant coefficient `1` is a unit in `ℚ`. -/
theorem isUnit_pentagonal023SeriesPS_rat :
    IsUnit (pentagonal023SeriesPS ℚ) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_zero_pentagonal023SeriesPS_rat]
  exact isUnit_one

/-- Equivalent statement: the constant coefficient of `pentagonal023SeriesPS ℚ`
is nonzero, which is exactly the hypothesis required for the formal inverse
`(pentagonal023SeriesPS ℚ)⁻¹` to be a genuine multiplicative inverse. -/
theorem constantCoeff_pentagonal023SeriesPS_rat_ne_zero :
    PowerSeries.constantCoeff (pentagonal023SeriesPS ℚ) ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_zero_pentagonal023SeriesPS_rat]
  exact one_ne_zero

/-- **Multiplicative form of `rrcf_r`:** `r(q) · (q²,q³,q⁵;q⁵)_∞ = (q,q⁴,q⁵;q⁵)_∞`,
the defining algebraic relation for the fractional-power-free part of `R(q)`.

This is the formal-power-series statement that `r(q) = H(q)/G(q)` (in keystone
variables `r = pentagonal014SeriesPS / pentagonal023SeriesPS`) is a *genuine*
multiplicative inverse, not a place-holder. It is the first non-trivial fact
about `r(q)` and the prerequisite for any later identity involving products
of `r(q)` and `r(q⁵)`. -/
theorem rrcf_r_mul_pentagonal023SeriesPS_eq :
    rrcf_r * pentagonal023SeriesPS ℚ = pentagonal014SeriesPS ℚ := by
  unfold rrcf_r
  rw [mul_assoc,
      PowerSeries.inv_mul_cancel _ constantCoeff_pentagonal023SeriesPS_rat_ne_zero,
      mul_one]

/-! ### Algebraic relations for `rrcf_v` (image of `r(q⁵)` under `X·expand 5`)

`rrcf_v` is intentionally chosen so that `rrcf_v.coeff 0 = 0` (no constant
term), which makes any polynomial `1 + c₁·rrcf_v + c₂·rrcf_v² + ⋯` a unit
in `ℚ⟦X⟧` (constant term `1`).  This is the technical reason Chan's
Theorem 11.5 can be stated as a clean formal-PS identity.
-/

/-- `rrcf_v` vanishes at `X = 0`; equivalently its constant term is zero,
because `rrcf_v = X · (expand 5 rrcf_r)` carries an explicit factor of `X`. -/
theorem coeff_zero_rrcf_v_eq_zero :
    rrcf_v.coeff 0 = 0 := by
  unfold rrcf_v
  rw [PowerSeries.coeff_zero_X_mul]

/-- Algebraic relation expressing `rrcf_v` through the `expand 5`-lifted
pentagonal products: `rrcf_v · (q¹⁰,q¹⁵,q²⁵;q²⁵)_∞ = X · (q⁵,q²⁰,q²⁵;q²⁵)_∞`,
the `q ↦ q⁵` image of `rrcf_r_mul_pentagonal023SeriesPS_eq`.

This is the analogue of `rrcf_r_mul_pentagonal023SeriesPS_eq` after applying
the ring homomorphism `PowerSeries.expand 5` (which sends `X ↦ X⁵`,
intertwining `r(q)` with `r(q⁵)`) and then multiplying through by `X`. -/
theorem rrcf_v_mul_expand_pentagonal023SeriesPS_eq :
    rrcf_v * (PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ)) =
      PowerSeries.X * (PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ)) := by
  unfold rrcf_v
  rw [mul_assoc, ← map_mul, rrcf_r_mul_pentagonal023SeriesPS_eq]

/-- **Denominator unit:** `1 + 3·rrcf_v + 4·rrcf_v² + 2·rrcf_v³ + rrcf_v⁴`
is a unit in `ℚ⟦X⟧`, because `rrcf_v.coeff 0 = 0` forces every `rrcf_v^k`
term with `k ≥ 1` to vanish at `X = 0`, leaving constant coefficient `1`.
This is the LHS denominator of Chan's Theorem 11.5. -/
theorem isUnit_rrcfDenomLHS :
    IsUnit (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have hv : PowerSeries.constantCoeff rrcf_v = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact coeff_zero_rrcf_v_eq_zero
  simp [map_add, map_mul, map_pow, map_ofNat, hv]

/-- **Denominator unit:** likewise `1 − 2·rrcf_v + 4·rrcf_v² − 3·rrcf_v³ + rrcf_v⁴`
is a unit in `ℚ⟦X⟧` (constant coefficient `1`). This is the RHS denominator
appearing on the right-hand side of Chan's Theorem 11.5 once cleared. -/
theorem isUnit_rrcfDenomRHS :
    IsUnit (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have hv : PowerSeries.constantCoeff rrcf_v = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact coeff_zero_rrcf_v_eq_zero
  simp [map_add, map_sub, map_mul, map_pow, map_ofNat, hv]

/-! ### Constant-coefficient verification of Chan Theorem 11.5

A first step toward Chan's Theorem 11.5 (`Pending/Chapter13_DeepIdentity`):
both sides of the conjectured formal-PS identity have the same constant
coefficient (=1), so the *difference* of the two sides has constant
coefficient 0. This is the simplest nontrivial verification.

Verifying the full identity coefficient-by-coefficient up to all orders is
the open work (Gugg telescoping); this constant-coefficient match is the
first of infinitely many such matches.
-/

/-- Constant coefficient of `rrcf_r` is `1`. -/
theorem coeff_zero_rrcf_r :
    rrcf_r.coeff 0 = 1 := by
  -- rrcf_r = pentagonal014SeriesPS ℚ * (pentagonal023SeriesPS ℚ)⁻¹
  -- coeff 0 of product = product of coeff 0
  have h_inv : (pentagonal023SeriesPS ℚ)⁻¹.coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        coeff_zero_pentagonal023SeriesPS_rat, inv_one]
  unfold rrcf_r
  rw [PowerSeries.coeff_mul, Finset.antidiagonal_zero, Finset.sum_singleton,
      coeff_zero_pentagonal014SeriesPS_rat, h_inv, mul_one]

/-- **Constant-coefficient version of Chan Theorem 11.5**: both sides of
the conjectured formal-PS identity

  `r(q)⁵ · (1 + 3v + 4v² + 2v³ + v⁴) = r(q⁵) · (1 − 2v + 4v² − 3v³ + v⁴)`

reduce at `X = 0` to `1·1 = 1·1`, hence the difference is zero in the
zeroth coefficient. This is the first (trivial-but-honest) coefficient-wise
verification of the full identity. -/
theorem coeff_zero_chan_theorem_11_5_LHS_eq_RHS :
    (rrcf_r ^ 5 * (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4)).coeff 0 =
      ((PowerSeries.expand 5 (by decide) rrcf_r) *
        (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4)).coeff 0 := by
  -- Use that constant coefficient is a ring hom
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hv : PowerSeries.constantCoeff rrcf_v = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact coeff_zero_rrcf_v_eq_zero
  have hr : PowerSeries.constantCoeff rrcf_r = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact coeff_zero_rrcf_r
  have hexp : PowerSeries.constantCoeff (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) rrcf_r) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_expand]
    simp [hr]
  simp [map_add, map_sub, map_mul, map_pow, map_ofNat, hv, hr, hexp]

end Ch13RRCF
end Pending
end QseriesFormalization
