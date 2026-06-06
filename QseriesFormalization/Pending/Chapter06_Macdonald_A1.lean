import QseriesFormalization.Chapter19
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal

/-!
# Chapter 6 — Macdonald's identity, the affine `A₁` (`t = 2`) case

Chan §6 Theorem 6.1 is Macdonald's identity for `η(q)^{t²-1}`, the
Weyl–Macdonald–Kac denominator formula for the affine root system
`A_{t-1}^{(1)}`.  For general `t` this requires affine Lie theory and is **not**
formalized in this repository.

This file formalizes the **foundational `t = 2` case** (affine `A₁`,
i.e. `ŝl(2,ℂ)`), which is exactly **Jacobi's identity**

  `(q;q)_∞³ = ∑_{k ≥ 0} (-1)^k (2k+1) q^{k(k+1)/2}`.

This is the prototype Macdonald's identity (`η^{2²-1} = η³`), the one Chan
derives in detail.  We prove it **unconditionally** as a corollary of the
formal-power-series Jacobi cube identity B2
(`qPochInfPS_pow_three_eq_jacobiThetaPS`).

**Dictionary to the Macdonald denominator sum** (`A₁`, `t = 2`): summing over
`v = (v₀, v₁) ∈ ℤ²` with `v₀ ≡ 0, v₁ ≡ 1 (mod 2)` and `v₀ + v₁ = 0`, write
`v₁ = 2k+1`, `v₀ = -(2k+1)`.  Then the Weyl factor `∏_{i<j}(vᵢ - vⱼ) = v₀ - v₁
= -2(2k+1)` and the exponent `(v₀² + v₁²)/(2·2) = (2k+1)²/8 = k(k+1)/2 + 1/8`.
Dividing out the universal `q^{1/8}` (= `q^{3/24}`) prefactor of `η³` and
folding the `±k` symmetry into `k ≥ 0` (factor of 2 absorbed) yields exactly
`∑_{k ≥ 0} (-1)^k (2k+1) q^{k(k+1)/2}`, i.e. `jacobiThetaPS`.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch06Macdonald

open PowerSeries
open QseriesFormalization.PartIV.Ch19

/-- **Macdonald's identity, affine `A₁` (`t = 2`) case = Jacobi's identity**,
formal-power-series form over any commutative ring `R`:

  `(q;q)_∞³ = ∑_{k ≥ 0} (-1)^k (2k+1) X^{k(k+1)/2}`.

Proven unconditionally via the Jacobi cube identity B2. -/
theorem macdonald_A1_identity (R : Type*) [CommRing R] :
    (qPochInfPS R)^3 = jacobiThetaPS R :=
  QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS R

/-- **Coefficient form**: the `n`-th coefficient of `(q;q)_∞³` is the Jacobi
triple sign `(-1)^k (2k+1)` at triangular `n = k(k+1)/2`, else `0`. -/
theorem coeff_macdonald_A1 (R : Type*) [CommRing R] (n : ℕ) :
    ((qPochInfPS R)^3).coeff n = ((jacobiTripleSign n : ℤ) : R) := by
  rw [macdonald_A1_identity, coeff_jacobiThetaPS]

/-- **At a triangular index** `n = k(k+1)/2`, the coefficient is `(-1)^k (2k+1)`,
exhibiting the Weyl factor `2k+1` and the sign `(-1)^k` of the Macdonald sum. -/
theorem coeff_macdonald_A1_triangular (R : Type*) [CommRing R] (k : ℕ) :
    ((qPochInfPS R)^3).coeff (k * (k + 1) / 2) =
      ((((-1 : ℤ) ^ k * (2 * k + 1) : ℤ)) : R) := by
  rw [coeff_macdonald_A1, jacobiTripleSign_triangular]

/-- **Off triangular indices** the coefficient vanishes: if `n` is not a
triangular number, then `((q;q)_∞³).coeff n = 0`. -/
theorem coeff_macdonald_A1_of_not_triangular (R : Type*) [CommRing R] (n : ℕ)
    (h : ∀ k ≤ n, n ≠ k * (k + 1) / 2) :
    ((qPochInfPS R)^3).coeff n = 0 := by
  rw [coeff_macdonald_A1, jacobiTripleSign_of_not_triangular n h]
  simp

end Ch06Macdonald
end Pending
end QseriesFormalization
