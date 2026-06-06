import QseriesFormalization.Chapter19
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal

/-!
# A mod-3 identity between the two fundamental sign sequences

Over `ZMod 3`, the Jacobi-triple-sign sequence (coefficients of `(q;q)_∞^3`) is the
pentagonal-sign sequence (coefficients of `(q;q)_∞`) stretched by a factor of 3:

  `jacobiTripleSign n ≡ [3 ∣ n] · pentagonalSign (n/3)   (mod 3).`

Proof: B2 gives `(qPoch)^3 = jacobiThetaPS`, and the char-3 Frobenius gives
`(qPoch)^3 = expand 3 qPoch` over `ZMod 3`.  Hence `jacobiThetaPS (ZMod 3) =
expand 3 (qPochInfPS (ZMod 3))`, and reading off coefficients (with
`coeff_qPochInfPS_eq_pentagonalSign`) yields the claim.
-/

namespace QseriesFormalization
namespace Pending
namespace SignMod3

open PowerSeries
open QseriesFormalization.PartIV.Ch19

/-- Over `ZMod 3`, `jacobiThetaPS = expand 3 qPochInfPS` (B2 + Frobenius cube). -/
theorem jacobiThetaPS_eq_expand_qPochInfPS :
    jacobiThetaPS (ZMod 3) =
      PowerSeries.expand 3 (by norm_num) (qPochInfPS (ZMod 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [← QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS]
  exact (PowerSeries.expand_eq_pow_zmod 3 (by norm_num) (qPochInfPS (ZMod 3))).symm

/-- **Mod-3 sign-sequence identity**: the Jacobi triple sign equals the
pentagonal sign stretched by 3, modulo 3. -/
theorem jacobiTripleSign_mod3 (n : ℕ) :
    ((jacobiTripleSign n : ℤ) : ZMod 3) =
      if 3 ∣ n then ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign (n / 3) : ℤ) : ZMod 3)
      else 0 := by
  have h := congrArg (fun φ => PowerSeries.coeff (R := ZMod 3) n φ)
    jacobiThetaPS_eq_expand_qPochInfPS
  simp only [coeff_jacobiThetaPS] at h
  rw [h, PowerSeries.coeff_expand 3 (by norm_num)]
  by_cases hd : 3 ∣ n
  · rw [if_pos hd, if_pos hd, coeff_qPochInfPS_eq_pentagonalSign]
  · rw [if_neg hd, if_neg hd]

end SignMod3
end Pending
end QseriesFormalization
