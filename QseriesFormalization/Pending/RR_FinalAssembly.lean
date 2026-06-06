import QseriesFormalization.Pending.RR_TaylorBridge
import QseriesFormalization.Pending.RR_LiftToFormalPS
import QseriesFormalization.Pending.RR_AnalyticProof_H
import QseriesFormalization.Pending.Chapter11_Thm111
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Final assembly for the formal Rogers-Ramanujan identities

This file connects the analytic identities to the formal power series over
`ℚ` via Taylor uniqueness over `ℂ`, then descends through `ℚ → ℂ`.
-/

namespace QseriesFormalization
namespace Pending
namespace RRFinalAssembly

open Filter Topology
open scoped ENNReal

open PowerSeries
open QseriesFormalization.PartII.Ch07
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartI.Ch04
open QseriesFormalization.Pending.RRAnalyticProof
open QseriesFormalization.Pending.RRTaylorBridge
open QseriesFormalization.Pending.RRLiftToFormalPS
open QseriesFormalization.Pending.RogersRamanujanFormalPS
open QseriesFormalization.Pending.JTPFormalPSPentagonal

noncomputable def psFMLS (P : PowerSeries ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => P.coeff n)

private lemma psFMLS_apply_eq (P : PowerSeries ℂ) (z : ℂ) (n : ℕ) :
    psFMLS P n (fun _ : Fin n => z) = P.coeff n * z ^ n := by
  rw [psFMLS, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]

private lemma psFMLS_ext_coeff {p : FormalMultilinearSeries ℂ ℂ ℂ} {P : PowerSeries ℂ}
    (hcoeff : ∀ n : ℕ, p.coeff n = P.coeff n) :
    p = psFMLS P := by
  ext n
  rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  rw [hcoeff n]
  simp [psFMLS, FormalMultilinearSeries.coeff_ofScalars]

private lemma summable_norm_coeff_of_radius
    (P : PowerSeries ℂ) (s : NNReal)
    (hs : (s : ENNReal) < (psFMLS P).radius) :
    Summable fun n : ℕ => ‖P.coeff n * (((s : ℝ) : ℂ)) ^ n‖ := by
  have h := (psFMLS P).summable_norm_mul_pow hs
  convert h using 1
  ext n
  rw [psFMLS, FormalMultilinearSeries.ofScalars_norm]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg s.coe_nonneg]

private lemma summable_norm_coeff_mul_of_summable_norm
    (P Q : PowerSeries ℂ) (z : ℂ)
    (hPnorm : Summable fun k : ℕ => ‖P.coeff k * z ^ k‖)
    (hQnorm : Summable fun k : ℕ => ‖Q.coeff k * z ^ k‖) :
    Summable fun n : ℕ => ‖(P * Q).coeff n * z ^ n‖ := by
  let f : ℕ → ℂ := fun k => P.coeff k * z ^ k
  let g : ℕ → ℂ := fun k => Q.coeff k * z ^ k
  have hconvnorm := summable_norm_sum_mul_range_of_summable_norm hPnorm hQnorm
  refine hconvnorm.congr ?_
  intro n
  dsimp [f, g]
  congr 1
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b : ℕ => P.coeff a * Q.coeff b * z ^ n) n]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hpow : z ^ n = z ^ k * z ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk_le]
  rw [hpow]
  ring

private lemma hasSum_coeff_mul_of_hasSum
    (P Q : PowerSeries ℂ) (z p qv : ℂ)
    (hP : HasSum (fun k : ℕ => P.coeff k * z ^ k) p)
    (hQ : HasSum (fun k : ℕ => Q.coeff k * z ^ k) qv)
    (hPnorm : Summable fun k : ℕ => ‖P.coeff k * z ^ k‖)
    (hQnorm : Summable fun k : ℕ => ‖Q.coeff k * z ^ k‖) :
    HasSum (fun n : ℕ => (P * Q).coeff n * z ^ n) (p * qv) := by
  let f : ℕ → ℂ := fun k => P.coeff k * z ^ k
  let g : ℕ → ℂ := fun k => Q.coeff k * z ^ k
  have hconv :
      HasSum (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), f k * g (n - k))
        ((∑' n, f n) * (∑' n, g n)) :=
    hasSum_sum_range_mul_of_summable_norm hPnorm hQnorm
  have htarget : (∑' n, f n) * (∑' n, g n) = p * qv := by
    rw [hP.tsum_eq, hQ.tsum_eq]
  rw [htarget] at hconv
  refine hconv.congr_fun ?_
  intro n
  dsimp [f, g]
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b : ℕ => P.coeff a * Q.coeff b * z ^ n) n]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hpow : z ^ n = z ^ k * z ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk_le]
  rw [hpow]
  ring

private lemma psFMLS_mul_radius_le
    {P Q : PowerSeries ℂ} {rP rQ : ENNReal}
    (hPr : rP ≤ (psFMLS P).radius)
    (hQr : rQ ≤ (psFMLS Q).radius) :
    min rP rQ ≤ (psFMLS (P * Q)).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro s hs
  have hsP : (s : ℝ≥0∞) < (psFMLS P).radius :=
    lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_left _ _)) hPr
  have hsQ : (s : ℝ≥0∞) < (psFMLS Q).radius :=
    lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_right _ _)) hQr
  have hPnorm := summable_norm_coeff_of_radius P s hsP
  have hQnorm := summable_norm_coeff_of_radius Q s hsQ
  have hprod :=
    summable_norm_coeff_mul_of_summable_norm P Q (((s : ℝ) : ℂ)) hPnorm hQnorm
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  convert hprod using 1
  ext n
  rw [psFMLS, FormalMultilinearSeries.ofScalars_norm]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg s.coe_nonneg]

private lemma summable_norm_coeff_of_apply
    (P : PowerSeries ℂ) {z : ℂ}
    (hz : z ∈ EMetric.ball (0 : ℂ) (psFMLS P).radius) :
    Summable fun n : ℕ => ‖P.coeff n * z ^ n‖ := by
  have h := (psFMLS P).summable_norm_apply hz
  convert h using 1
  ext n
  rw [psFMLS_apply_eq]

private lemma hasFPowerSeriesOnBall_mul_ps
    {f g : ℂ → ℂ} {P Q : PowerSeries ℂ} {rP rQ : ENNReal}
    (hP : HasFPowerSeriesOnBall f (psFMLS P) 0 rP)
    (hQ : HasFPowerSeriesOnBall g (psFMLS Q) 0 rQ) :
    HasFPowerSeriesOnBall (fun z => f z * g z) (psFMLS (P * Q)) 0 (min rP rQ) where
  r_le := psFMLS_mul_radius_le hP.r_le hQ.r_le
  r_pos := lt_min hP.r_pos hQ.r_pos
  hasSum := by
    intro z hz
    have hzP : z ∈ EMetric.ball (0 : ℂ) rP :=
      EMetric.ball_subset_ball (min_le_left _ _) hz
    have hzQ : z ∈ EMetric.ball (0 : ℂ) rQ :=
      EMetric.ball_subset_ball (min_le_right _ _) hz
    have hzP_rad : z ∈ EMetric.ball (0 : ℂ) (psFMLS P).radius :=
      EMetric.ball_subset_ball hP.r_le hzP
    have hzQ_rad : z ∈ EMetric.ball (0 : ℂ) (psFMLS Q).radius :=
      EMetric.ball_subset_ball hQ.r_le hzQ
    have hPs : HasSum (fun n : ℕ => P.coeff n * z ^ n) (f z) := by
      simpa [psFMLS_apply_eq, psFMLS, FormalMultilinearSeries.coeff_ofScalars, mul_comm]
        using hP.hasSum hzP
    have hQs : HasSum (fun n : ℕ => Q.coeff n * z ^ n) (g z) := by
      simpa [psFMLS_apply_eq, psFMLS, FormalMultilinearSeries.coeff_ofScalars, mul_comm]
        using hQ.hasSum hzQ
    have hPnorm := summable_norm_coeff_of_apply P hzP_rad
    have hQnorm := summable_norm_coeff_of_apply Q hzQ_rad
    have hmul :=
      hasSum_coeff_mul_of_hasSum P Q z (f z) (g z) hPs hQs hPnorm hQnorm
    simpa [psFMLS_apply_eq, psFMLS, FormalMultilinearSeries.coeff_ofScalars, mul_comm] using hmul

private lemma hasFPowerSeriesAt_mul_ps
    {f g : ℂ → ℂ} {P Q : PowerSeries ℂ}
    (hP : HasFPowerSeriesAt f (psFMLS P) 0)
    (hQ : HasFPowerSeriesAt g (psFMLS Q) 0) :
    HasFPowerSeriesAt (fun z => f z * g z) (psFMLS (P * Q)) 0 := by
  rcases hP with ⟨rP, hP⟩
  rcases hQ with ⟨rQ, hQ⟩
  exact ⟨min rP rQ, hasFPowerSeriesOnBall_mul_ps hP hQ⟩

private theorem hasFPowerSeriesAt_rrJInf_one_rrGPS :
    HasFPowerSeriesAt (fun q : ℂ => rrJInf 1 q)
      (psFMLS (PowerSeries.map (algebraMap ℚ ℂ) rrGPS)) 0 := by
  rcases analyticAt_rrJInf_one_zero with ⟨p, hp⟩
  have hp_eq : p = psFMLS (PowerSeries.map (algebraMap ℚ ℂ) rrGPS) :=
    psFMLS_ext_coeff (fun n => rrJInf_one_taylorCoeff_eq_rrGPS_coeff hp n)
  rwa [← hp_eq]

private theorem hasFPowerSeriesAt_qPochhammer_inf :
    HasFPowerSeriesAt qPochhammer_inf (psFMLS (qPochInfPS ℂ)) 0 := by
  unfold qPochhammer_inf
  change HasFPowerSeriesAt eulerPentagonalInfiniteProduct
    (psFMLS (qPochInfPS ℂ)) 0
  have h : psFMLS (qPochInfPS ℂ) = qPochInfFMLS := by
    rfl
  rw [h]
  exact ⟨1, hasFPowerSeriesOnBall_eulerPentagonalInfiniteProduct⟩

private theorem hasFPowerSeriesAt_pentagonal023_analytic :
    HasFPowerSeriesAt pentagonal023_analytic (psFMLS (pentagonal023SeriesPS ℂ)) 0 := by
  unfold pentagonal023_analytic
  change HasFPowerSeriesAt pentagonal023Analytic
    (psFMLS (pentagonal023SeriesPS ℂ)) 0
  have h : psFMLS (pentagonal023SeriesPS ℂ) = pentagonal023SeriesFMLS := by
    ext n
    rw [psFMLS, FormalMultilinearSeries.ofScalars]
    simp [pentagonal023SeriesFMLS, coeff_pentagonal023SeriesPS]
  rw [h]
  exact ⟨1, hasFPowerSeriesOnBall_pentagonal023Analytic⟩

theorem rogers_ramanujan_G_complex_formal :
    PowerSeries.map (algebraMap ℚ ℂ) rrGPS * qPochInfPS ℂ =
      pentagonal023SeriesPS ℂ := by
  have hprod : HasFPowerSeriesAt
      (fun q : ℂ => rrJInf 1 q * qPochhammer_inf q)
      (psFMLS (PowerSeries.map (algebraMap ℚ ℂ) rrGPS * qPochInfPS ℂ)) 0 :=
    hasFPowerSeriesAt_mul_ps
      hasFPowerSeriesAt_rrJInf_one_rrGPS
      hasFPowerSeriesAt_qPochhammer_inf
  have hpent := hasFPowerSeriesAt_pentagonal023_analytic
  have hevent :
      (fun q : ℂ => rrJInf 1 q * qPochhammer_inf q)
        =ᶠ[𝓝 (0 : ℂ)] pentagonal023_analytic := by
    have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
      Metric.ball_mem_nhds 0 (by norm_num)
    filter_upwards [hball] with q hq
    have hq_norm : ‖q‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hq
    exact rrJInf_one_mul_qPochhammer_inf_eq_pentagonal023_analytic q hq_norm
  have h_unique :
      psFMLS (PowerSeries.map (algebraMap ℚ ℂ) rrGPS * qPochInfPS ℂ) =
        psFMLS (pentagonal023SeriesPS ℂ) :=
    hprod.eq_formalMultilinearSeries_of_eventually hpent hevent
  ext n
  have hcoeff := congrFun (congrArg FormalMultilinearSeries.coeff h_unique) n
  simpa [psFMLS, FormalMultilinearSeries.coeff_ofScalars] using hcoeff

theorem rogersRamanujan_G_formal :
    rrGPS * qPochInfPS ℚ = pentagonal023SeriesPS ℚ :=
  rogers_ramanujan_G_formal_of_complex_identity rogers_ramanujan_G_complex_formal

private theorem hasFPowerSeriesAt_rrJInf_q_rrHPS :
    HasFPowerSeriesAt (fun q : ℂ => rrJInf q q)
      (psFMLS (PowerSeries.map (algebraMap ℚ ℂ) rrHPS)) 0 := by
  rcases analyticAt_rrJInf_q_zero with ⟨p, hp⟩
  have hp_eq : p = psFMLS (PowerSeries.map (algebraMap ℚ ℂ) rrHPS) :=
    psFMLS_ext_coeff (fun n => rrJInf_q_taylorCoeff_eq_rrHPS_coeff hp n)
  rwa [← hp_eq]

private theorem hasFPowerSeriesAt_pentagonal014_analytic :
    HasFPowerSeriesAt
      QseriesFormalization.Pending.RRAnalyticProofH.pentagonal014_analytic
      (psFMLS (pentagonal014SeriesPS ℂ)) 0 := by
  unfold QseriesFormalization.Pending.RRAnalyticProofH.pentagonal014_analytic
  change HasFPowerSeriesAt pentagonal014Analytic
    (psFMLS (pentagonal014SeriesPS ℂ)) 0
  have h : psFMLS (pentagonal014SeriesPS ℂ) = pentagonal014SeriesFMLS := by
    ext n
    rw [psFMLS, FormalMultilinearSeries.ofScalars]
    simp [pentagonal014SeriesFMLS, coeff_pentagonal014SeriesPS]
  rw [h]
  exact ⟨1, hasFPowerSeriesOnBall_pentagonal014Analytic⟩

theorem rogers_ramanujan_H_complex_formal :
    PowerSeries.map (algebraMap ℚ ℂ) rrHPS * qPochInfPS ℂ =
      pentagonal014SeriesPS ℂ := by
  have hprod : HasFPowerSeriesAt
      (fun q : ℂ => rrJInf q q * qPochhammer_inf q)
      (psFMLS (PowerSeries.map (algebraMap ℚ ℂ) rrHPS * qPochInfPS ℂ)) 0 :=
    hasFPowerSeriesAt_mul_ps
      hasFPowerSeriesAt_rrJInf_q_rrHPS
      hasFPowerSeriesAt_qPochhammer_inf
  have hpent := hasFPowerSeriesAt_pentagonal014_analytic
  have hevent :
      (fun q : ℂ => rrJInf q q * qPochhammer_inf q)
        =ᶠ[𝓝 (0 : ℂ)]
          QseriesFormalization.Pending.RRAnalyticProofH.pentagonal014_analytic := by
    have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
      Metric.ball_mem_nhds 0 (by norm_num)
    filter_upwards [hball] with q hq
    have hq_norm : ‖q‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hq
    have h :=
      RRAnalyticProofH.rrJInf_q_mul_qPochhammer_inf_eq_pentagonal014_analytic q hq_norm
    simpa [qPochhammer_inf,
      QseriesFormalization.Pending.RRAnalyticProofH.qPochhammer_inf] using h
  have h_unique :
      psFMLS (PowerSeries.map (algebraMap ℚ ℂ) rrHPS * qPochInfPS ℂ) =
        psFMLS (pentagonal014SeriesPS ℂ) :=
    hprod.eq_formalMultilinearSeries_of_eventually hpent hevent
  ext n
  have hcoeff := congrFun (congrArg FormalMultilinearSeries.coeff h_unique) n
  simpa [psFMLS, FormalMultilinearSeries.coeff_ofScalars] using hcoeff

theorem map_pentagonal014SeriesPS_rat_complex :
    PowerSeries.map (algebraMap ℚ ℂ) (pentagonal014SeriesPS ℚ) =
      pentagonal014SeriesPS ℂ := by
  ext n
  rw [PowerSeries.coeff_map, coeff_pentagonal014SeriesPS, coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hk : pentagonal014Exp k = n <;> simp [hk, negOnePowInt]

theorem rogers_ramanujan_H_formal_of_complex_identity
    (h_complex :
      PowerSeries.map (algebraMap ℚ ℂ) rrHPS * qPochInfPS ℂ =
        pentagonal014SeriesPS ℂ) :
    rrHPS * qPochInfPS ℚ = pentagonal014SeriesPS ℚ := by
  apply PowerSeries.map_injective (algebraMap ℚ ℂ) Rat.cast_injective
  rw [map_mul, map_qPochInfPS (algebraMap ℚ ℂ), h_complex,
    map_pentagonal014SeriesPS_rat_complex]

theorem rogersRamanujan_H_formal :
    rrHPS * qPochInfPS ℚ = pentagonal014SeriesPS ℚ :=
  rogers_ramanujan_H_formal_of_complex_identity rogers_ramanujan_H_complex_formal

theorem rogersRamanujan_ratio_formal :
    rrHPS * rrGPS⁻¹ =
      QseriesFormalization.Pending.Ch13RRCF.rrcf_r := by
  have hq_ne : PowerSeries.constantCoeff (qPochInfPS ℚ) ≠ 0 := by
    rw [constantCoeff_qPochInfPS]
    norm_num
  have hG_ne : PowerSeries.constantCoeff rrGPS ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_rrGPS]
    norm_num
  have h023_ne :
      PowerSeries.constantCoeff (pentagonal023SeriesPS ℚ) ≠ 0 :=
    QseriesFormalization.Pending.Ch13RRCF.constantCoeff_pentagonal023SeriesPS_rat_ne_zero
  have hG_solve :
      rrGPS = pentagonal023SeriesPS ℚ * (qPochInfPS ℚ)⁻¹ := by
    calc
      rrGPS = rrGPS * 1 := by rw [mul_one]
      _ = rrGPS * (qPochInfPS ℚ * (qPochInfPS ℚ)⁻¹) := by
        rw [PowerSeries.mul_inv_cancel _ hq_ne]
      _ = (rrGPS * qPochInfPS ℚ) * (qPochInfPS ℚ)⁻¹ := by ring
      _ = pentagonal023SeriesPS ℚ * (qPochInfPS ℚ)⁻¹ := by
        rw [rogersRamanujan_G_formal]
  have hH_solve :
      rrHPS = pentagonal014SeriesPS ℚ * (qPochInfPS ℚ)⁻¹ := by
    calc
      rrHPS = rrHPS * 1 := by rw [mul_one]
      _ = rrHPS * (qPochInfPS ℚ * (qPochInfPS ℚ)⁻¹) := by
        rw [PowerSeries.mul_inv_cancel _ hq_ne]
      _ = (rrHPS * qPochInfPS ℚ) * (qPochInfPS ℚ)⁻¹ := by ring
      _ = pentagonal014SeriesPS ℚ * (qPochInfPS ℚ)⁻¹ := by
        rw [rogersRamanujan_H_formal]
  have hrrcf_mul :
      QseriesFormalization.Pending.Ch13RRCF.rrcf_r * rrGPS = rrHPS := by
    unfold QseriesFormalization.Pending.Ch13RRCF.rrcf_r
    rw [hG_solve, hH_solve]
    calc
      (pentagonal014SeriesPS ℚ * (pentagonal023SeriesPS ℚ)⁻¹) *
          (pentagonal023SeriesPS ℚ * (qPochInfPS ℚ)⁻¹)
          = pentagonal014SeriesPS ℚ *
              ((pentagonal023SeriesPS ℚ)⁻¹ * pentagonal023SeriesPS ℚ) *
                (qPochInfPS ℚ)⁻¹ := by ring
      _ = pentagonal014SeriesPS ℚ * (qPochInfPS ℚ)⁻¹ := by
        rw [PowerSeries.inv_mul_cancel _ h023_ne]
        ring
  calc
    rrHPS * rrGPS⁻¹ =
        (QseriesFormalization.Pending.Ch13RRCF.rrcf_r * rrGPS) * rrGPS⁻¹ := by
          rw [hrrcf_mul]
    _ = QseriesFormalization.Pending.Ch13RRCF.rrcf_r * (rrGPS * rrGPS⁻¹) := by ring
    _ = QseriesFormalization.Pending.Ch13RRCF.rrcf_r := by
      rw [PowerSeries.mul_inv_cancel _ hG_ne]
      ring

theorem chan_theorem_11_1_of_rrcf_via_CF_eq_ratio
    (h_cf :
      QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_r_via_CF =
        rrHPS * rrGPS⁻¹) :
    QseriesFormalization.Pending.Ch13RRCF.rrcf_r =
      QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_r_via_CF := by
  rw [h_cf, rogersRamanujan_ratio_formal]

end RRFinalAssembly
end Pending
end QseriesFormalization
