import QseriesFormalization.Chapter19_Section5
import QseriesFormalization.Chapter17_SectionBridge
import QseriesFormalization.Chapter17_Mod7PerTermAnalysis
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal

/-!
# Chapter 17 — Ramanujan's second congruence `∀ n, 7 ∣ p(7n+5)`

UNCONDITIONAL proof via the analytic-formal Taylor uniqueness chain +
mod-7 per-term residue analysis.

Chain:
  - B2 cube identity (qPochInfPS R)^3 = jacobiThetaPS R  (JacobiCubeAnalyticToFormal)
  - Squaring: (qPochInfPS R)^6 = (jacobiThetaPS R)^2 (in particular for R = ZMod 7)
  - Coefficient at 7n+5: by PowerSeries.coeff_mul, sum over antidiagonal
  - Per-term mod-7 zero (Chapter17_Mod7PerTermAnalysis)
  - ramanujan_from_pochInf_vanishes 7 ... 5
-/

namespace QseriesFormalization
namespace Pending
namespace Ch17p7

open QseriesFormalization.PartIV.Ch19

/-- **Ramanujan's second congruence (UNCONDITIONAL)**: `∀ n, 7 ∣ p(7n + 5)`. -/
theorem ramanujan_7_dvd_p_7n_plus_5 :
    ∀ n, 7 ∣ QseriesFormalization.Ch01.partitionCount (7 * n + 5) := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro n
  apply (ZMod.natCast_eq_zero_iff _ 7).mp
  refine ramanujan_from_pochInf_vanishes 7 (by decide) 5 (by decide) ?_ n
  intro m
  rw [show (7 - 1 : ℕ) = 6 from rfl]
  have h_pow6 : (qPochInfPS (ZMod 7)) ^ 6 = (jacobiThetaPS (ZMod 7)) ^ 2 :=
    QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_six_eq_jacobiThetaPS_pow_two
      (ZMod 7)
  rw [h_pow6]
  rw [sq, PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  rw [coeff_jacobiThetaPS, coeff_jacobiThetaPS]
  exact QseriesFormalization.PartIV.Ch17.jacobiTripleSign_squared_per_term_zero_mod_7
    i j m hij

/-- **Restatement in `ZMod 7`**: `p(7n+5) ≡ 0 (mod 7)`. -/
theorem ramanujan_partition_7n_plus_5_eq_zero_mod_7 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (7 * n + 5) : ℕ) : ZMod 7) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 7).mpr (ramanujan_7_dvd_p_7n_plus_5 n)

/-- **Specialisation**: `p(5) ≡ 0 (mod 7)` (n = 0 case, p(5) = 7). -/
theorem ramanujan_partition_five_mod_seven_via_general :
    ((QseriesFormalization.Ch01.partitionCount 5 : ℕ) : ZMod 7) = 0 :=
  ramanujan_partition_7n_plus_5_eq_zero_mod_7 0

/-- **Specialisation**: `p(12) ≡ 0 (mod 7)` (n = 1 case, p(12) = 77). -/
theorem ramanujan_partition_twelve_mod_seven :
    ((QseriesFormalization.Ch01.partitionCount 12 : ℕ) : ZMod 7) = 0 :=
  ramanujan_partition_7n_plus_5_eq_zero_mod_7 1

/-- **Specialisation**: `p(19) ≡ 0 (mod 7)` (n = 2 case, p(19) = 490). -/
theorem ramanujan_partition_nineteen_mod_seven :
    ((QseriesFormalization.Ch01.partitionCount 19 : ℕ) : ZMod 7) = 0 :=
  ramanujan_partition_7n_plus_5_eq_zero_mod_7 2

/-- **Formal-PS strong form**: `((qPochInfPS (ZMod 7))^6).coeff (7n+5) = 0`.

Underlying formal power series statement driving the divisibility result. -/
theorem coeff_qPochInfPS_pow_six_at_7n_plus_5_eq_zero (n : ℕ) :
    ((qPochInfPS (ZMod 7)) ^ 6).coeff (7 * n + 5) = 0 := by
  have h_pow6 : (qPochInfPS (ZMod 7)) ^ 6 = (jacobiThetaPS (ZMod 7)) ^ 2 :=
    QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_six_eq_jacobiThetaPS_pow_two
      (ZMod 7)
  rw [h_pow6, sq, PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  rw [coeff_jacobiThetaPS, coeff_jacobiThetaPS]
  exact QseriesFormalization.PartIV.Ch17.jacobiTripleSign_squared_per_term_zero_mod_7
    i j n hij

/-- **Integer-level divisibility**: `7 ∣ ((qPochInfPS ℤ)^6).coeff (7n+5)`. -/
theorem seven_dvd_coeff_qPochInfPS_pow_six_int_at_7n_plus_5 (n : ℕ) :
    (7 : ℤ) ∣ ((qPochInfPS ℤ) ^ 6).coeff (7 * n + 5) := by
  have h_zmod : ((((qPochInfPS ℤ)^6).coeff (7 * n + 5) : ℤ) : ZMod 7) = 0 := by
    have h_map : PowerSeries.map (Int.castRingHom (ZMod 7)) ((qPochInfPS ℤ)^6) =
        (qPochInfPS (ZMod 7))^6 := by
      rw [map_pow, map_qPochInfPS]
    have h_cast : ((((qPochInfPS ℤ)^6).coeff (7 * n + 5) : ℤ) : ZMod 7) =
        ((qPochInfPS (ZMod 7))^6).coeff (7 * n + 5) := by
      rw [← h_map, PowerSeries.coeff_map]; rfl
    rw [h_cast]
    exact coeff_qPochInfPS_pow_six_at_7n_plus_5_eq_zero n
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp h_zmod

end Ch17p7
end Pending
end QseriesFormalization
