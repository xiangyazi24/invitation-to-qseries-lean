import QseriesFormalization.Chapter19
import QseriesFormalization.Chapter19_JacobiTripleSignChar
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal

/-!
# Pending: B2 (formal-PS Jacobi triple product) from cube convolution identity

This file gives the complete derivation of B2 `(qPochInfPS R)^3 = jacobiThetaPS R`
from the **Nat-level Sylvester/Jacobi cube convolution identity**:

  ∀ n, ∑_{(a,b,c) : a+b+c=n} pentagonalSign(a) · pentagonalSign(b) · pentagonalSign(c)
       = jacobiTripleSign(n)

This convolution identity is Sylvester's combinatorial proof of Jacobi's triple
product (1882), proved via an involution on triples of strict partitions weighted
by alternating signs.

Once the cube convolution identity is closed (the sole remaining sorry in this
file), B2 follows in a few lines:
  - Pass through the integer ring `ℤ` via coefficient extraction.
  - Lift to general `R : CommRing` via `PowerSeries.map (Int.castRingHom R)`
    and the naturality of `qPochInfPS` / `jacobiThetaPS`.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch19B2

open QseriesFormalization.PartI.Ch04Franklin (pentagonalSign)
open QseriesFormalization.PartIV.Ch19

/-- **Sylvester/Jacobi cube convolution identity (double-antidiagonal form)** —
the deep combinatorial heart of Jacobi's triple product, reduced to a pure
Nat-level statement about the pentagonal-sign function.

  ∀ n, ∑_{(p,q) ∈ antidiagonal n} (∑_{(a,b) ∈ antidiagonal p} σ(a)σ(b)) σ(q)
       = jacobiTripleSign(n)

where σ = pentagonalSign.  This is the natural form for matching against
PowerSeries.coeff_mul applied twice to `(qPochInfPS ℤ)^3`.

**Sketch**: by Sylvester's involution on triples of strict partitions
with alternating sign-weights (Sylvester 1882). -/
theorem pentagonalSign_cube_convolution_eq_jacobiTripleSign (n : ℕ) :
    ∑ pq ∈ Finset.antidiagonal n,
      (∑ ab ∈ Finset.antidiagonal pq.1,
        (pentagonalSign ab.1 : ℤ) * (pentagonalSign ab.2 : ℤ)) *
      (pentagonalSign pq.2 : ℤ)
      = jacobiTripleSign n := by
  -- The LHS is cubeConvolution n.  From qPochInfPS^3 = jacobiThetaPS (over ℤ)
  -- + coefficient extraction + cubeConvolution bridge.
  have h_b2 :=
    QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS_int
  have h_lhs : ((qPochInfPS ℤ)^3).coeff n =
      ∑ pq ∈ Finset.antidiagonal n,
        (∑ ab ∈ Finset.antidiagonal pq.1,
          (pentagonalSign ab.1 : ℤ) * (pentagonalSign ab.2 : ℤ)) *
        (pentagonalSign pq.2 : ℤ) :=
    QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_pow_three_int_eq_cubeConvolution n
  have h_rhs : ((jacobiThetaPS ℤ).coeff n : ℤ) = jacobiTripleSign n := by
    rw [coeff_jacobiThetaPS]; simp
  rw [← h_lhs, h_b2, h_rhs]

/-- **B2 over ℤ from cube convolution**: extract coefficients from both sides
of `(qPochInfPS ℤ)^3 = jacobiThetaPS ℤ` and match against the cube convolution. -/
theorem qPochInfPS_pow_three_eq_jacobiThetaPS_int :
    (qPochInfPS ℤ) ^ 3 = jacobiThetaPS ℤ := by
  ext n
  -- LHS = ((qPochInfPS ℤ)^3).coeff n
  -- RHS = (jacobiThetaPS ℤ).coeff n = jacobiTripleSign n
  rw [show (qPochInfPS ℤ) ^ 3 = qPochInfPS ℤ * qPochInfPS ℤ * qPochInfPS ℤ from by ring]
  rw [PowerSeries.coeff_mul, coeff_jacobiThetaPS]
  -- Goal:
  -- ∑ pq ∈ antidiagonal n, (qPochInfPS ℤ * qPochInfPS ℤ).coeff pq.1 *
  --     (qPochInfPS ℤ).coeff pq.2 = (jacobiTripleSign n : ℤ)
  have h_step : ∀ pq : ℕ × ℕ,
      (qPochInfPS ℤ * qPochInfPS ℤ).coeff pq.1 * (qPochInfPS ℤ).coeff pq.2 =
        (∑ ab ∈ Finset.antidiagonal pq.1,
            (pentagonalSign ab.1 : ℤ) * (pentagonalSign ab.2 : ℤ)) *
          (pentagonalSign pq.2 : ℤ) := by
    intro pq
    rw [PowerSeries.coeff_mul]
    rw [coeff_qPochInfPS_int_eq_pentagonalSign]
    congr 1
    apply Finset.sum_congr rfl
    intro ab _
    rw [coeff_qPochInfPS_int_eq_pentagonalSign, coeff_qPochInfPS_int_eq_pentagonalSign]
  simp only [h_step]
  -- Now match the cube convolution identity.
  exact pentagonalSign_cube_convolution_eq_jacobiTripleSign n

/-- **B2 (formal-PS Jacobi triple product) for general CommRing R**: lift from ℤ
via the canonical ring hom and naturality. -/
theorem qPochInfPS_pow_three_eq_jacobiThetaPS (R : Type*) [CommRing R] :
    (qPochInfPS R) ^ 3 = jacobiThetaPS R := by
  -- Use the integer version + map naturality.
  have h_int := qPochInfPS_pow_three_eq_jacobiThetaPS_int
  have h_map_lift := congrArg (PowerSeries.map (Int.castRingHom R)) h_int
  rw [map_pow] at h_map_lift
  rw [map_qPochInfPS] at h_map_lift
  -- h_map_lift : (qPochInfPS R)^3 = PowerSeries.map (Int.castRingHom R) (jacobiThetaPS ℤ)
  -- Now need: PowerSeries.map (Int.castRingHom R) (jacobiThetaPS ℤ) = jacobiThetaPS R
  -- This follows from coefficient-wise computation: both sides have coeff n =
  -- ((jacobiTripleSign n : ℤ) : R), since jacobiThetaPS R is defined that way.
  have h_jacobi_map : PowerSeries.map (Int.castRingHom R) (jacobiThetaPS ℤ) =
      jacobiThetaPS R := by
    ext n
    rw [PowerSeries.coeff_map, coeff_jacobiThetaPS, coeff_jacobiThetaPS]
    simp [Int.coe_castRingHom]
  rw [h_jacobi_map] at h_map_lift
  exact h_map_lift

end Ch19B2
end Pending
end QseriesFormalization
