import QseriesFormalization.Chapter20
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal

/-!
# Ramanujan τ via the B2 cube identity

Using B2 `(qPochInfPS R)^3 = jacobiThetaPS R`, we get:
  `(qPochInfPS R)^24 = (jacobiThetaPS R)^8`
  `discriminantPS R = X · (qPochInfPS R)^24 = X · (jacobiThetaPS R)^8`
  `ramanujanTau R (n+1) = ((jacobiThetaPS R)^8).coeff n`

This expresses Ramanujan τ as the 8-fold convolution of the jacobi triple
sign sequence — a sparse-support sequence supported on triangular indices.
The k-th nonzero index in jts is `T_k = k(k+1)/2` with value `(-1)^k (2k+1)`.

So `τ(n+1) = ∑_{k_1+...+k_8 such that T_{k_1}+...+T_{k_8} = n}
                 ∏_{i=1}^8 (-1)^{k_i} (2 k_i + 1)`

— a finite-support combinatorial sum.  This is the "Jacobi-Bressoud" form
of τ that appears in Hecke theory.
-/

namespace QseriesFormalization
namespace Pending
namespace RTau

open QseriesFormalization.PartIV.Ch19 (qPochInfPS jacobiThetaPS)
open QseriesFormalization.PartIV.Ch20 (etaPS discriminantPS ramanujanTau)

/-- `(qPochInfPS R)^24 = (jacobiThetaPS R)^8` via 24 = 3 · 8 + B2. -/
theorem qPochInfPS_pow_twentyfour_eq_jacobiThetaPS_pow_eight (R : Type*) [CommRing R] :
    (qPochInfPS R) ^ 24 = (jacobiThetaPS R) ^ 8 := by
  have h_b2 :=
    QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS R
  calc (qPochInfPS R) ^ 24
      = ((qPochInfPS R) ^ 3) ^ 8 := by ring
    _ = (jacobiThetaPS R) ^ 8 := by rw [h_b2]

/-- `discriminantPS R = X · (jacobiThetaPS R)^8`. -/
theorem discriminantPS_eq_X_mul_jacobiThetaPS_pow_eight (R : Type*) [CommRing R] :
    discriminantPS R = PowerSeries.X * (jacobiThetaPS R) ^ 8 := by
  unfold discriminantPS
  rw [show etaPS R = qPochInfPS R from rfl]
  rw [qPochInfPS_pow_twentyfour_eq_jacobiThetaPS_pow_eight]

/-- **τ(n+1) = ((jacobiThetaPS R)^8).coeff n**: Ramanujan tau as an
8-fold convolution of the Jacobi triple sign sequence. -/
theorem ramanujanTau_succ_eq_jacobiThetaPS_pow_eight_coeff
    (R : Type*) [CommRing R] (n : ℕ) :
    ramanujanTau R (n + 1) = ((jacobiThetaPS R) ^ 8).coeff n := by
  unfold ramanujanTau
  rw [discriminantPS_eq_X_mul_jacobiThetaPS_pow_eight]
  rw [PowerSeries.coeff_succ_X_mul]

end RTau
end Pending
end QseriesFormalization
