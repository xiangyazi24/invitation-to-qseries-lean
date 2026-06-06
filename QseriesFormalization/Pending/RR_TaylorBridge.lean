import QseriesFormalization.Pending.RR_AnalyticProof
import QseriesFormalization.Pending.RR_AnalyticProof_H
import QseriesFormalization.Pending.RogersRamanujan_FormalPS
import QseriesFormalization.Chapter19_JacobiTripleSignChar
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Rogers-Ramanujan Taylor bridge

This file records the Taylor-coefficient bridge currently needed for the
`G`-side Rogers-Ramanujan formal series.  The main theorem identifies every
Taylor coefficient of `q ↦ rrJInf 1 q` at zero with the corresponding
coefficient of the complexified formal series `rrGPS`.
-/

namespace QseriesFormalization
namespace Pending
namespace RRTaylorBridge

open Asymptotics Filter Topology
open scoped ENNReal

open QseriesFormalization.PartII.Ch07
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartI.Ch04
open QseriesFormalization.Pending.RRAnalyticProof
open QseriesFormalization.Pending.RogersRamanujanFormalPS
open QseriesFormalization.Pending.JTPFormalPSPentagonal

noncomputable def qPochInfFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (qPochInfPS ℂ).coeff n)

theorem one_le_qPochInfFMLS_radius :
    (1 : ENNReal) ≤ qPochInfFMLS.radius := by
  rw [show (1 : ENNReal) = ((1 : NNReal) : ENNReal) by simp]
  apply ENNReal.le_of_forall_nnreal_lt
  intro s hs
  rw [ENNReal.coe_lt_coe] at hs
  have hs_norm : ‖((s : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
    exact_mod_cast hs
  have hsum :
      Summable (fun n : ℕ => (qPochInfPS ℂ).coeff n * (((s : ℝ) : ℂ)) ^ n) := by
    refine (QseriesFormalization.PartIV.Ch19.summable_pentagonalSign_mul_pow
      ((s : ℝ) : ℂ) hs_norm).congr ?_
    intro n
    rw [coeff_qPochInfPS_eq_pentagonalSign]
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have hsum_norm := hsum.norm
  have h_eq :
      (fun n : ℕ => ‖qPochInfFMLS n‖ * (s : ℝ) ^ n) =
        (fun n : ℕ => ‖(qPochInfPS ℂ).coeff n * (((s : ℝ) : ℂ)) ^ n‖) := by
    funext n
    rw [qPochInfFMLS, FormalMultilinearSeries.ofScalars_norm]
    rw [norm_mul, norm_pow]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
  rw [h_eq]
  exact hsum_norm

theorem hasFPowerSeriesOnBall_eulerPentagonalInfiniteProduct :
    HasFPowerSeriesOnBall eulerPentagonalInfiniteProduct qPochInfFMLS 0 1 := by
  refine ⟨one_le_qPochInfFMLS_radius, by positivity, ?_⟩
  intro y hy
  rw [zero_add]
  have hy_norm : ‖y‖ < 1 := by
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    have h_ball : y ∈ Metric.ball (0 : ℂ) 1 := by
      rw [h1, Metric.emetric_ball] at hy
      exact hy
    have hdist : dist y (0 : ℂ) < 1 := Metric.mem_ball.mp h_ball
    rwa [dist_zero_right] at hdist
  have hsum :
      Summable (fun n : ℕ => (qPochInfPS ℂ).coeff n * y ^ n) := by
    refine (QseriesFormalization.PartIV.Ch19.summable_pentagonalSign_mul_pow y hy_norm).congr ?_
    intro n
    rw [coeff_qPochInfPS_eq_pentagonalSign]
  have h_eval :=
    QseriesFormalization.PartIV.Ch19.eulerPentagonalInfiniteProduct_eq_tsum_qPochInfPS_coeff
      y hy_norm
  rw [h_eval]
  convert hsum.hasSum using 1
  funext n
  rw [qPochInfFMLS, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]

theorem analyticAt_rrJInf_one_zero :
    AnalyticAt ℂ (fun q : ℂ => rrJInf 1 q) 0 := by
  have h_num : AnalyticAt ℂ pentagonal023_analytic 0 :=
    (hasFPowerSeriesOnBall_pentagonal023Analytic.hasFPowerSeriesAt).analyticAt
  have h_den : AnalyticAt ℂ qPochhammer_inf 0 := by
    unfold qPochhammer_inf
    exact (hasFPowerSeriesOnBall_eulerPentagonalInfiniteProduct.hasFPowerSeriesAt).analyticAt
  have h_den_ne : qPochhammer_inf 0 ≠ 0 := by
    unfold qPochhammer_inf
    have h := eulerPentagonalInfiniteProduct_ne_zero (0 : ℂ) (by simp)
    simpa using h
  have h_quot : AnalyticAt ℂ (fun q : ℂ => pentagonal023_analytic q / qPochhammer_inf q) 0 :=
    h_num.div h_den h_den_ne
  refine h_quot.congr ?_
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 (by norm_num)
  filter_upwards [hball] with q hq
  have hq_norm : ‖q‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hq
  have hden : qPochhammer_inf q ≠ 0 := by
    unfold qPochhammer_inf
    exact eulerPentagonalInfiniteProduct_ne_zero q hq_norm
  have hmain := rrJInf_one_mul_qPochhammer_inf_eq_pentagonal023_analytic q hq_norm
  exact ((eq_div_iff hden).mpr hmain).symm

noncomputable def rrGTermFMLS (n : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun k => (PowerSeries.map (algebraMap ℚ ℂ) (rrGTermPS n)).coeff k)

private lemma fmls_sum_coeff {ι : Type*} (s : Finset ι)
    (p : ι → FormalMultilinearSeries ℂ ℂ ℂ) (k : ℕ) :
    (∑ i ∈ s, p i).coeff k = ∑ i ∈ s, (p i).coeff k := by
  classical
  change ((∑ i ∈ s, p i) k) 1 = ∑ i ∈ s, (p i k) 1
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change ((p a k + (∑ i ∈ s, p i) k) 1) =
        (p a k) 1 + ∑ x ∈ s, (p x k) 1
      rw [ContinuousMultilinearMap.add_apply, ih]

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

private noncomputable def multiplesEquiv (d : ℕ) (hd : 0 < d) :
    ℕ ≃ {k : ℕ // d ∣ k} where
  toFun m := ⟨d * m, ⟨m, rfl⟩⟩
  invFun k := k.1 / d
  left_inv m := Nat.mul_div_right m hd
  right_inv k := by
    ext
    change d * (k.1 / d) = k.1
    rw [mul_comm, Nat.div_mul_cancel k.2]

private noncomputable def geomFactorPS (d : ℕ) (hd : d ≠ 0) : PowerSeries ℂ :=
  PowerSeries.expand d hd (PowerSeries.mk 1 : PowerSeries ℂ)

private lemma hasSum_geomFactorPS_coeff_mul_pow
    (d : ℕ) (hd : d ≠ 0) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (geomFactorPS d hd).coeff k * z ^ k) ((1 - z ^ d)⁻¹) := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  let f : ℕ → ℂ := fun k => (geomFactorPS d hd).coeff k * z ^ k
  have hf_support : Function.support f ⊆ {k : ℕ | d ∣ k} := by
    intro k hk
    by_contra hkd
    have hnot : ¬ d ∣ k := hkd
    exact hk (by
      dsimp [f, geomFactorPS]
      rw [PowerSeries.coeff_expand]
      simp [hnot])
  have hgeom : HasSum (fun m : ℕ => (z ^ d) ^ m) ((1 - z ^ d)⁻¹) := by
    have hnorm : ‖z ^ d‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg z) hz hdpos.ne'
    simpa using hasSum_geometric_of_norm_lt_one hnorm
  have hgeom' :
      HasSum ((f ∘ (fun k : {k : ℕ // d ∣ k} => k.1)) ∘ multiplesEquiv d hdpos)
        ((1 - z ^ d)⁻¹) := by
    convert hgeom using 1
    ext m
    dsimp [f, geomFactorPS, multiplesEquiv]
    rw [PowerSeries.coeff_expand]
    simp [dvd_mul_right, pow_mul]
  have hsub : HasSum (f ∘ (fun k : {k : ℕ // d ∣ k} => k.1)) ((1 - z ^ d)⁻¹) :=
    (multiplesEquiv d hdpos).hasSum_iff.mp hgeom'
  exact (hasSum_subtype_iff_of_support_subset hf_support).mp hsub

private lemma summable_norm_geomFactorPS_coeff_mul_pow
    (d : ℕ) (hd : d ≠ 0) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => ‖(geomFactorPS d hd).coeff k * z ^ k‖) := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  let f : ℕ → ℝ := fun k => ‖(geomFactorPS d hd).coeff k * z ^ k‖
  have hf_support : Function.support f ⊆ {k : ℕ | d ∣ k} := by
    intro k hk
    by_contra hkd
    have hnot : ¬ d ∣ k := hkd
    exact hk (by
      dsimp [f, geomFactorPS]
      rw [PowerSeries.coeff_expand]
      simp [hnot])
  have hgeom : Summable (fun m : ℕ => ‖(z ^ d) ^ m‖) := by
    have hnorm : ‖z ^ d‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg z) hz hdpos.ne'
    exact (summable_geometric_of_norm_lt_one hnorm).norm
  have hsub : Summable (f ∘ (fun k : {k : ℕ // d ∣ k} => k.1)) := by
    rw [← (multiplesEquiv d hdpos).summable_iff]
    convert hgeom using 1
    ext m
    dsimp [f, geomFactorPS, multiplesEquiv]
    rw [PowerSeries.coeff_expand]
    simp [dvd_mul_right, pow_mul]
  rcases hsub with ⟨a, ha⟩
  exact ⟨a, (hasSum_subtype_iff_of_support_subset hf_support).mp ha⟩

private noncomputable def qPochInvProductPS (n : ℕ) : PowerSeries ℂ :=
  ∏ i ∈ Finset.range n, geomFactorPS (i + 1) (Nat.succ_ne_zero i)

private lemma hasSum_and_summable_norm_qPochInvProductPS_coeff_mul_pow
    (n : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (qPochInvProductPS n).coeff k * z ^ k)
        (∏ i ∈ Finset.range n, (1 - z ^ (i + 1))⁻¹) ∧
      Summable (fun k : ℕ => ‖(qPochInvProductPS n).coeff k * z ^ k‖) := by
  induction n with
  | zero =>
      constructor
      · simpa [qPochInvProductPS] using
          (hasSum_single (0 : ℕ)
            (f := fun k : ℕ => (1 : PowerSeries ℂ).coeff k * z ^ k)
            (by intro b hb; simp [PowerSeries.coeff_one, hb]))
      · refine (hasSum_single (0 : ℕ)
          (f := fun k : ℕ => ‖(1 : PowerSeries ℂ).coeff k * z ^ k‖) ?_).summable
        intro b hb
        simp [PowerSeries.coeff_one, hb]
  | succ n ih =>
      rw [qPochInvProductPS, Finset.prod_range_succ, Finset.prod_range_succ]
      exact ⟨
        hasSum_coeff_mul_of_hasSum
          (qPochInvProductPS n) (geomFactorPS (n + 1) (Nat.succ_ne_zero n)) z
          (∏ i ∈ Finset.range n, (1 - z ^ (i + 1))⁻¹)
          ((1 - z ^ (n + 1))⁻¹) ih.1
          (hasSum_geomFactorPS_coeff_mul_pow (n + 1) (Nat.succ_ne_zero n) z hz)
          ih.2
          (summable_norm_geomFactorPS_coeff_mul_pow (n + 1) (Nat.succ_ne_zero n) z hz),
        summable_norm_coeff_mul_of_summable_norm
          (qPochInvProductPS n) (geomFactorPS (n + 1) (Nat.succ_ne_zero n)) z
          ih.2
          (summable_norm_geomFactorPS_coeff_mul_pow (n + 1) (Nat.succ_ne_zero n) z hz)⟩

private lemma hasSum_qPochInvProductPS_coeff_mul_pow
    (n : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (qPochInvProductPS n).coeff k * z ^ k)
      (∏ i ∈ Finset.range n, (1 - z ^ (i + 1))⁻¹) :=
  (hasSum_and_summable_norm_qPochInvProductPS_coeff_mul_pow n z hz).1

private lemma geomFactor_mul (d : ℕ) (hd : d ≠ 0) :
    geomFactorPS d hd * (1 - (PowerSeries.X : PowerSeries ℂ) ^ d) = 1 := by
  have hbase : (PowerSeries.mk 1 : PowerSeries ℂ) * (1 - PowerSeries.X) = 1 :=
    PowerSeries.mk_one_mul_one_sub_eq_one ℂ
  have h := congrArg (PowerSeries.expand d hd) hbase
  simpa [geomFactorPS, map_mul, map_sub, map_one, PowerSeries.expand_X] using h

private lemma constantCoeff_qPochPS_complex (n : ℕ) :
    PowerSeries.constantCoeff (qPochhammer (PowerSeries.X : PowerSeries ℂ) n) = 1 := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih => simp [qPochhammer, ih, PowerSeries.constantCoeff_X]

private lemma qPochInvProduct_mul (n : ℕ) :
    qPochInvProductPS n * qPochhammer (PowerSeries.X : PowerSeries ℂ) n = 1 := by
  induction n with
  | zero => simp [qPochInvProductPS, qPochhammer]
  | succ n ih =>
      rw [qPochInvProductPS, Finset.prod_range_succ]
      change (qPochInvProductPS n * geomFactorPS (n + 1) (Nat.succ_ne_zero n)) *
          (qPochhammer (PowerSeries.X : PowerSeries ℂ) n *
            (1 - (PowerSeries.X : PowerSeries ℂ) ^ (n + 1))) = 1
      rw [show (qPochInvProductPS n * geomFactorPS (n + 1) (Nat.succ_ne_zero n)) *
          (qPochhammer (PowerSeries.X : PowerSeries ℂ) n *
            (1 - (PowerSeries.X : PowerSeries ℂ) ^ (n + 1))) =
          (qPochInvProductPS n * qPochhammer (PowerSeries.X : PowerSeries ℂ) n) *
            (geomFactorPS (n + 1) (Nat.succ_ne_zero n) *
              (1 - (PowerSeries.X : PowerSeries ℂ) ^ (n + 1))) by ring]
      rw [ih, geomFactor_mul]
      simp

private lemma qPochInvProduct_eq_inv (n : ℕ) :
    qPochInvProductPS n = (qPochhammer (PowerSeries.X : PowerSeries ℂ) n)⁻¹ := by
  symm
  rw [PowerSeries.inv_eq_iff_mul_eq_one]
  · exact qPochInvProduct_mul n
  · rw [constantCoeff_qPochPS_complex n]
    norm_num

private lemma map_qPochPS_complex (n : ℕ) :
    PowerSeries.map (algebraMap ℚ ℂ) (qPochPS n) =
      qPochhammer (PowerSeries.X : PowerSeries ℂ) n := by
  induction n with
  | zero => simp [qPochPS, qPochhammer]
  | succ n ih =>
      change PowerSeries.map (algebraMap ℚ ℂ)
          (qPochPS n * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (n + 1))) =
        qPochhammer (PowerSeries.X : PowerSeries ℂ) n *
          (1 - (PowerSeries.X : PowerSeries ℂ) ^ (n + 1))
      rw [map_mul, ih]
      simp

private lemma map_inv_qPochPS_complex (n : ℕ) :
    PowerSeries.map (algebraMap ℚ ℂ) ((qPochPS n)⁻¹) = qPochInvProductPS n := by
  rw [qPochInvProduct_eq_inv]
  symm
  rw [PowerSeries.inv_eq_iff_mul_eq_one]
  · calc
      PowerSeries.map (algebraMap ℚ ℂ) ((qPochPS n)⁻¹) *
          qPochhammer (PowerSeries.X : PowerSeries ℂ) n
          = PowerSeries.map (algebraMap ℚ ℂ) ((qPochPS n)⁻¹) *
              PowerSeries.map (algebraMap ℚ ℂ) (qPochPS n) := by rw [map_qPochPS_complex]
      _ = PowerSeries.map (algebraMap ℚ ℂ) ((qPochPS n)⁻¹ * qPochPS n) := by rw [map_mul]
      _ = 1 := by
        rw [PowerSeries.inv_mul_cancel]
        · simp
        · rw [constantCoeff_qPochPS]
          norm_num
  · rw [constantCoeff_qPochPS_complex n]
    norm_num

private lemma map_rrGTermPS_complex (n : ℕ) :
    PowerSeries.map (algebraMap ℚ ℂ) (rrGTermPS n) =
      (PowerSeries.X : PowerSeries ℂ) ^ (n * n) * qPochInvProductPS n := by
  unfold rrGTermPS
  rw [map_mul, map_pow, map_inv_qPochPS_complex]
  simp

private lemma hasSum_X_pow_mul_coeff (P : PowerSeries ℂ) (z p : ℂ) (s : ℕ)
    (hP : HasSum (fun k : ℕ => P.coeff k * z ^ k) p) :
    HasSum (fun k : ℕ => ((PowerSeries.X : PowerSeries ℂ) ^ s * P).coeff k * z ^ k)
      (z ^ s * p) := by
  let F : ℕ → ℂ := fun k => ((PowerSeries.X : PowerSeries ℂ) ^ s * P).coeff k * z ^ k
  have hshift : HasSum (fun n : ℕ => F (n + s)) (z ^ s * p) := by
    have hmul : HasSum (fun n : ℕ => (P.coeff n * z ^ n) * z ^ s) (p * z ^ s) :=
      hP.mul_right (z ^ s)
    have hmul' : HasSum (fun n : ℕ => (P.coeff n * z ^ n) * z ^ s) (z ^ s * p) := by
      simpa [mul_comm] using hmul
    refine hmul'.congr_fun ?_
    intro n
    dsimp [F]
    rw [PowerSeries.coeff_X_pow_mul, pow_add]
    ring
  have hzero : (∑ i ∈ Finset.range s, F i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    dsimp [F]
    rw [PowerSeries.coeff_X_pow_mul']
    have hi_lt : i < s := Finset.mem_range.mp hi
    rw [if_neg (Nat.not_le_of_gt hi_lt)]
    simp
  have hfull := (hasSum_nat_add_iff (f := F) s).mp hshift
  simpa [hzero] using hfull

private lemma qPochhammer_eq_prod_range {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    qPochhammer q n = ∏ i ∈ Finset.range n, (1 - q ^ (i + 1)) := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
      rw [qPochhammer_succ, ih, Finset.prod_range_succ]

private lemma rrJTerm_one_eq_zpow_mul_qPochInvProduct (z : ℂ) (n : ℕ) :
    rrJTerm 1 z n = z ^ (n * n) * ∏ i ∈ Finset.range n, (1 - z ^ (i + 1))⁻¹ := by
  rw [rrJTerm, qPochhammer_eq_prod_range]
  simp [div_eq_mul_inv, Finset.prod_inv_distrib]

private lemma hasSum_map_rrGTermPS_coeff_mul_pow
    (n : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (PowerSeries.map (algebraMap ℚ ℂ) (rrGTermPS n)).coeff k * z ^ k)
      (rrJTerm 1 z n) := by
  have hInv := hasSum_qPochInvProductPS_coeff_mul_pow n z hz
  have hShift := hasSum_X_pow_mul_coeff (qPochInvProductPS n) z
    (∏ i ∈ Finset.range n, (1 - z ^ (i + 1))⁻¹) (n * n) hInv
  rw [rrJTerm_one_eq_zpow_mul_qPochInvProduct]
  simpa [map_rrGTermPS_complex] using hShift

theorem hasFPowerSeriesAt_rrJTerm_one (n : ℕ) :
    HasFPowerSeriesAt (fun q : ℂ => rrJTerm 1 q n) (rrGTermFMLS n) 0 := by
  rw [hasFPowerSeriesAt_iff']
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  filter_upwards [hball] with z hz
  have hz_norm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have h := hasSum_map_rrGTermPS_coeff_mul_pow n z hz_norm
  convert h using 1
  ext k
  simp [rrGTermFMLS, smul_eq_mul, mul_comm]

private lemma coeff_eq_zero_of_isBigO_norm_pow
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {N k : ℕ}
    (hp : HasFPowerSeriesAt f p 0)
    (hO : f =O[𝓝 (0 : ℂ)] fun z : ℂ => ‖z‖ ^ N)
    (hk : k < N) :
    p.coeff k = 0 := by
  suffices hmap : ∀ y : ℂ, p k (fun _ : Fin k => y) = 0 by
    exact hmap 1
  revert hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hkN y
      have psum_eq : p.partialSum (k + 1) = fun y : ℂ => p k fun _ : Fin k => y := by
        funext z
        refine Finset.sum_eq_single k (fun b hb hbk => ?_) (fun hk_not_mem => ?_)
        · have hb_lt : b < k := by
            have hb_le : b ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
            exact hb_le.lt_of_ne hbk
          exact ih b hb_lt (lt_trans hb_lt hkN) z
        · exact False.elim (hk_not_mem (Finset.mem_range.mpr (lt_add_one k)))
      have hpowO :
          (fun z : ℂ => ‖z‖ ^ N) =O[𝓝 (0 : ℂ)] fun z : ℂ => ‖z‖ ^ (k + 1) := by
        by_cases hEq : N = k + 1
        · simpa [hEq] using
            (isBigO_refl (fun z : ℂ => ‖z‖ ^ (k + 1)) (𝓝 (0 : ℂ)))
        · have hlt : k + 1 < N := by omega
          exact (isLittleO_norm_pow_norm_pow (E' := ℂ) hlt).isBigO
      have hfO :
          (fun z : ℂ => f (0 + z)) =O[𝓝 (0 : ℂ)] fun z : ℂ => ‖z‖ ^ (k + 1) := by
        simpa using hO.trans hpowO
      have hdiff :
          (fun z : ℂ => f (0 + z) - p k (fun _ : Fin k => z))
            =O[𝓝 (0 : ℂ)] fun z : ℂ => ‖z‖ ^ (k + 1) := by
        simpa [psum_eq] using hp.isBigO_sub_partialSum_pow (k + 1)
      have hterm :
          (fun z : ℂ => p k (fun _ : Fin k => z))
            =O[𝓝 (0 : ℂ)] fun z : ℂ => ‖z‖ ^ (k + 1) := by
        have h := hfO.sub hdiff
        simpa [sub_sub_cancel] using h
      exact hterm.continuousMultilinearMap_apply_eq_zero y

private lemma rrJInf_one_sub_inv_one_sub_eq_tsum_tail
    (q : ℂ) (hq : ‖q‖ < 1) :
    rrJInf 1 q - (1 - q)⁻¹ =
      ∑' n : ℕ, rrJTerm 1 q (n + 2) := by
  have hsum := hasSum_rrJTerm 1 q hq
  have htail := (hasSum_nat_add_iff' (f := rrJTerm 1 q) 2).mpr hsum
  have hq_ne : 1 - q ≠ 0 := by
    have hq1 : q ≠ 1 := by
      intro h
      rw [h, norm_one] at hq
      exact not_lt_of_ge le_rfl hq
    exact sub_ne_zero.mpr hq1.symm
  have h0 : rrJTerm 1 q 0 = 1 := by simp [rrJTerm, qPochhammer]
  have h1 : rrJTerm 1 q 1 = q / (1 - q) := by
    simp [rrJTerm, qPochhammer]
  have hpartial :
      (∑ x ∈ Finset.range 2, rrJTerm 1 q x) = (1 - q)⁻¹ := by
    simp [h0, h1, Finset.sum_range_succ]
    field_simp [hq_ne]
    ring
  have htail' :
      HasSum (fun n : ℕ => rrJTerm 1 q (n + 2))
        (rrJInf 1 q - (1 - q)⁻¹) := by
    simpa [hpartial] using htail
  exact htail'.tsum_eq.symm

private lemma rrJInf_one_sub_inv_one_sub_isBigO :
    (fun q : ℂ => rrJInf 1 q - (1 - q)⁻¹)
      =O[𝓝 (0 : ℂ)] fun q : ℂ => ‖q‖ ^ 4 := by
  let A : ℕ → ℝ := fun n => (4 : ℝ) * ((1 / 2 : ℝ) ^ n)
  have hA_summable : Summable A := by
    exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  refine IsBigO.of_bound (∑' n : ℕ, A n) ?_
  have hball : Metric.ball (0 : ℂ) (1 / 8 : ℝ) ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  filter_upwards [hball] with q hq_ball
  have hq_lt_eighth : ‖q‖ < (1 / 8 : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm] using hq_ball
  have hq_le_eighth : ‖q‖ ≤ (1 / 8 : ℝ) := hq_lt_eighth.le
  have hq_lt_one : ‖q‖ < 1 := by nlinarith
  rw [rrJInf_one_sub_inv_one_sub_eq_tsum_tail q hq_lt_one]
  have hnorm_summable : Summable fun n : ℕ => ‖rrJTerm 1 q (n + 2)‖ :=
    (summable_norm_rrJTerm 1 q hq_lt_one).comp_injective (i := fun n => n + 2)
      (fun a b h => Nat.add_right_cancel h)
  have htail_norm :
      ‖∑' n : ℕ, rrJTerm 1 q (n + 2)‖ ≤
        ∑' n : ℕ, ‖rrJTerm 1 q (n + 2)‖ :=
    norm_tsum_le_tsum_norm hnorm_summable
  have hterm :
      ∀ n : ℕ, ‖rrJTerm 1 q (n + 2)‖ ≤ A n * ‖q‖ ^ 4 := by
    intro n
    set m : ℕ := n + 2
    have hm_ge_two : 2 ≤ m := by omega
    have hden0 : (0 : ℝ) < (1 / 2) ^ m := by positivity
    have hbase : (1 / 2 : ℝ) ≤ 1 - ‖q‖ := by nlinarith
    have hden_ge : (1 / 2 : ℝ) ^ m ≤ ‖qPochhammer q m‖ := by
      have h1 : (1 / 2 : ℝ) ^ m ≤ (1 - ‖q‖) ^ m := by
        exact pow_le_pow_left₀ (by norm_num) hbase m
      exact le_trans h1 (norm_qPochhammer_ge q hq_lt_one m)
    have hpow_extra_for_n : ‖q‖ ^ (m * m - 4) ≤ (1 / 8 : ℝ) ^ n := by
      have hq_nonneg : 0 ≤ ‖q‖ := norm_nonneg q
      have hq_le_one : ‖q‖ ≤ 1 := by nlinarith
      have hn_le : n ≤ m * m - 4 := by
        subst m
        have h : (n + 2) * (n + 2) = n * n + 4 * n + 4 := by ring
        omega
      calc
        ‖q‖ ^ (m * m - 4) ≤ ‖q‖ ^ n :=
          pow_le_pow_of_le_one hq_nonneg hq_le_one hn_le
        _ ≤ (1 / 8 : ℝ) ^ n :=
          pow_le_pow_left₀ hq_nonneg hq_le_eighth n
    have hpow_split : ‖q‖ ^ (m * m) = ‖q‖ ^ 4 * ‖q‖ ^ (m * m - 4) := by
      rw [← pow_add]
      congr 1
      have hm_sq : 4 ≤ m * m := by nlinarith
      omega
    rw [norm_rrJTerm_eq]
    simp only [norm_one, one_pow, one_mul]
    calc
      ‖q‖ ^ (m * m) / ‖qPochhammer q m‖
          ≤ ‖q‖ ^ (m * m) / ((1 / 2 : ℝ) ^ m) := by
            exact div_le_div_of_nonneg_left (by positivity) hden0 hden_ge
      _ = ‖q‖ ^ 4 * ‖q‖ ^ (m * m - 4) / ((1 / 2 : ℝ) ^ m) := by
            rw [hpow_split]
      _ ≤ A n * ‖q‖ ^ 4 := by
            by_cases hn0 : n = 0
            · subst n
              subst m
              change ‖q‖ ^ 4 * ‖q‖ ^ (2 * 2 - 4) / ((1 / 2 : ℝ) ^ 2) ≤
                (4 * (1 / 2 : ℝ) ^ 0) * ‖q‖ ^ 4
              norm_num
              ring_nf
              exact le_rfl
            · have hn_pos : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
              have hm_ge_three : 3 ≤ m := by omega
              have hm_le_extra : m ≤ m * m - 4 := by
                apply Nat.le_sub_of_add_le
                have hlin : m + 4 ≤ 3 * m := by omega
                have hmul : 3 * m ≤ m * m :=
                  Nat.mul_le_mul_right m hm_ge_three
                exact le_trans hlin hmul
              have hpow_extra_m : ‖q‖ ^ (m * m - 4) ≤ (1 / 8 : ℝ) ^ m := by
                have hq_nonneg : 0 ≤ ‖q‖ := norm_nonneg q
                have hq_le_one : ‖q‖ ≤ 1 := by nlinarith
                calc
                  ‖q‖ ^ (m * m - 4) ≤ ‖q‖ ^ m :=
                    pow_le_pow_of_le_one hq_nonneg hq_le_one hm_le_extra
                  _ ≤ (1 / 8 : ℝ) ^ m :=
                    pow_le_pow_left₀ hq_nonneg hq_le_eighth m
              calc
                ‖q‖ ^ 4 * ‖q‖ ^ (m * m - 4) / ((1 / 2 : ℝ) ^ m)
                    ≤ ‖q‖ ^ 4 * ((1 / 8 : ℝ) ^ m) / ((1 / 2 : ℝ) ^ m) := by
                      exact div_le_div_of_nonneg_right
                        (mul_le_mul_of_nonneg_left hpow_extra_m (by positivity))
                        (by positivity)
                  _ = ‖q‖ ^ 4 * ((1 / 4 : ℝ) ^ m) := by
                        calc
                          ‖q‖ ^ 4 * (1 / 8 : ℝ) ^ m / (1 / 2 : ℝ) ^ m
                              = ‖q‖ ^ 4 *
                                  (((1 / 8 : ℝ) ^ m) / ((1 / 2 : ℝ) ^ m)) := by ring
                          _ = ‖q‖ ^ 4 * (((1 / 8 : ℝ) / (1 / 2 : ℝ)) ^ m) := by
                                rw [← div_pow]
                          _ = ‖q‖ ^ 4 * ((1 / 4 : ℝ) ^ m) := by norm_num
                  _ ≤ A n * ‖q‖ ^ 4 := by
                        have hconst : (1 / 4 : ℝ) ^ m ≤ 4 * (1 / 2 : ℝ) ^ n := by
                          subst m
                          calc
                            (1 / 4 : ℝ) ^ (n + 2)
                                = (1 / 16 : ℝ) * (1 / 4 : ℝ) ^ n := by
                                  rw [pow_add]
                                  ring
                            _ ≤ (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ n := by
                                  exact mul_le_mul_of_nonneg_left
                                    (pow_le_pow_left₀ (by norm_num) (by norm_num) n)
                                    (by norm_num)
                            _ ≤ 4 * (1 / 2 : ℝ) ^ n := by
                                  exact mul_le_mul_of_nonneg_right
                                    (by norm_num : (1 / 16 : ℝ) ≤ 4)
                                    (by positivity)
                        change ‖q‖ ^ 4 * (1 / 4 : ℝ) ^ m ≤
                          (4 * (1 / 2 : ℝ) ^ n) * ‖q‖ ^ 4
                        calc
                          ‖q‖ ^ 4 * (1 / 4 : ℝ) ^ m
                              ≤ ‖q‖ ^ 4 * (4 * (1 / 2 : ℝ) ^ n) := by
                                exact mul_le_mul_of_nonneg_left hconst
                                  (by positivity)
                          _ = (4 * (1 / 2 : ℝ) ^ n) * ‖q‖ ^ 4 := by ring
  have hsum_le :
      (∑' n : ℕ, ‖rrJTerm 1 q (n + 2)‖) ≤
        ∑' n : ℕ, A n * ‖q‖ ^ 4 :=
    hnorm_summable.tsum_le_tsum hterm (hA_summable.mul_right _)
  have hsum_eval : (∑' n : ℕ, A n * ‖q‖ ^ 4) = (∑' n : ℕ, A n) * ‖q‖ ^ 4 := by
    rw [tsum_mul_right]
  calc
    ‖∑' n : ℕ, rrJTerm 1 q (n + 2)‖
        ≤ ∑' n : ℕ, ‖rrJTerm 1 q (n + 2)‖ := htail_norm
    _ ≤ ∑' n : ℕ, A n * ‖q‖ ^ 4 := hsum_le
    _ = (∑' n : ℕ, A n) * ‖q‖ ^ 4 := hsum_eval
    _ = (∑' n : ℕ, A n) * ‖(‖q‖ ^ 4 : ℝ)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖q‖ ^ 4)]

private lemma rrJInf_one_sub_partial_eq_tsum_tail
    (N : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    rrJInf 1 q - (∑ n ∈ Finset.range N, rrJTerm 1 q n) =
      ∑' m : ℕ, rrJTerm 1 q (m + N) := by
  have hsum := hasSum_rrJTerm 1 q hq
  have htail := (hasSum_nat_add_iff' (f := rrJTerm 1 q) N).mpr hsum
  exact htail.tsum_eq.symm

private lemma rrJInf_one_sub_partial_isBigO (N : ℕ) (hN : 0 < N) :
    (fun q : ℂ => rrJInf 1 q - ∑ n ∈ Finset.range N, rrJTerm 1 q n)
      =O[𝓝 (0 : ℂ)] fun q : ℂ => ‖q‖ ^ N := by
  let A : ℕ → ℝ := fun m => (2 : ℝ) ^ N * ((1 / 4 : ℝ) ^ m)
  have hA_summable : Summable A := by
    exact (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left _
  refine IsBigO.of_bound (∑' m : ℕ, A m) ?_
  have hball : Metric.ball (0 : ℂ) (1 / 8 : ℝ) ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  filter_upwards [hball] with q hq_ball
  have hq_lt_eighth : ‖q‖ < (1 / 8 : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm] using hq_ball
  have hq_le_eighth : ‖q‖ ≤ (1 / 8 : ℝ) := hq_lt_eighth.le
  have hq_lt_one : ‖q‖ < 1 := by nlinarith
  rw [rrJInf_one_sub_partial_eq_tsum_tail N q hq_lt_one]
  have hnorm_summable : Summable fun m : ℕ => ‖rrJTerm 1 q (m + N)‖ :=
    (summable_norm_rrJTerm 1 q hq_lt_one).comp_injective (i := fun m => m + N)
      (fun a b h => Nat.add_right_cancel h)
  have htail_norm :
      ‖∑' m : ℕ, rrJTerm 1 q (m + N)‖ ≤
        ∑' m : ℕ, ‖rrJTerm 1 q (m + N)‖ :=
    norm_tsum_le_tsum_norm hnorm_summable
  have hterm : ∀ m : ℕ, ‖rrJTerm 1 q (m + N)‖ ≤ A m * ‖q‖ ^ N := by
    intro m
    set r : ℕ := m + N
    have hr_ge_N : N ≤ r := by omega
    have hr_pos : 0 < r := lt_of_lt_of_le hN hr_ge_N
    have hden_pos : (0 : ℝ) < (1 / 2) ^ r := by positivity
    have hbase : (1 / 2 : ℝ) ≤ 1 - ‖q‖ := by nlinarith
    have hden_ge : (1 / 2 : ℝ) ^ r ≤ ‖qPochhammer q r‖ := by
      have h1 : (1 / 2 : ℝ) ^ r ≤ (1 - ‖q‖) ^ r := by
        exact pow_le_pow_left₀ (by norm_num) hbase r
      exact le_trans h1 (norm_qPochhammer_ge q hq_lt_one r)
    have hpow_extra_exp : m ≤ r * r - N := by
      subst r
      have hle : m + N ≤ (m + N) * (m + N) := by
        exact Nat.le_mul_of_pos_left (m + N) (lt_of_lt_of_le hN (by omega : N ≤ m + N))
      omega
    have hpow_extra : ‖q‖ ^ (r * r - N) ≤ (1 / 8 : ℝ) ^ m := by
      have hq_nonneg : 0 ≤ ‖q‖ := norm_nonneg q
      have hq_le_one : ‖q‖ ≤ 1 := by nlinarith
      calc
        ‖q‖ ^ (r * r - N) ≤ ‖q‖ ^ m :=
          pow_le_pow_of_le_one hq_nonneg hq_le_one hpow_extra_exp
        _ ≤ (1 / 8 : ℝ) ^ m :=
          pow_le_pow_left₀ hq_nonneg hq_le_eighth m
    have hpow_split : ‖q‖ ^ (r * r) = ‖q‖ ^ N * ‖q‖ ^ (r * r - N) := by
      rw [← pow_add]
      congr 1
      have hN_le_rr : N ≤ r * r :=
        le_trans hr_ge_N (Nat.le_mul_of_pos_left r hr_pos)
      omega
    rw [norm_rrJTerm_eq]
    simp only [norm_one, one_pow, one_mul]
    calc
      ‖q‖ ^ (r * r) / ‖qPochhammer q r‖
          ≤ ‖q‖ ^ (r * r) / ((1 / 2 : ℝ) ^ r) := by
            exact div_le_div_of_nonneg_left (by positivity) hden_pos hden_ge
      _ = ‖q‖ ^ N * ‖q‖ ^ (r * r - N) / ((1 / 2 : ℝ) ^ r) := by
            rw [hpow_split]
      _ ≤ ‖q‖ ^ N * ((1 / 8 : ℝ) ^ m) / ((1 / 2 : ℝ) ^ r) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow_extra (by positivity))
              (by positivity)
      _ = A m * ‖q‖ ^ N := by
            dsimp [A]
            subst r
            rw [div_eq_mul_inv, ← inv_pow]
            norm_num
            rw [pow_add]
            have hpow : (1 / 8 : ℝ) ^ m * 2 ^ m = (1 / 4 : ℝ) ^ m := by
              rw [← mul_pow]
              norm_num
            calc
              ‖q‖ ^ N * (1 / 8 : ℝ) ^ m * (2 ^ m * 2 ^ N)
                  = ‖q‖ ^ N * ((1 / 8 : ℝ) ^ m * 2 ^ m) * 2 ^ N := by ring
              _ = ‖q‖ ^ N * (1 / 4 : ℝ) ^ m * 2 ^ N := by rw [hpow]
              _ = 2 ^ N * (1 / 4 : ℝ) ^ m * ‖q‖ ^ N := by ring
  have hsum_le :
      (∑' m : ℕ, ‖rrJTerm 1 q (m + N)‖) ≤
        ∑' m : ℕ, A m * ‖q‖ ^ N :=
    hnorm_summable.tsum_le_tsum hterm (hA_summable.mul_right _)
  have hsum_eval : (∑' m : ℕ, A m * ‖q‖ ^ N) = (∑' m : ℕ, A m) * ‖q‖ ^ N := by
    rw [tsum_mul_right]
  calc
    ‖∑' m : ℕ, rrJTerm 1 q (m + N)‖
        ≤ ∑' m : ℕ, ‖rrJTerm 1 q (m + N)‖ := htail_norm
    _ ≤ ∑' m : ℕ, A m * ‖q‖ ^ N := hsum_le
    _ = (∑' m : ℕ, A m) * ‖q‖ ^ N := hsum_eval
    _ = (∑' m : ℕ, A m) * ‖(‖q‖ ^ N : ℝ)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖q‖ ^ N)]

private lemma inv_one_sub_taylor :
    HasFPowerSeriesAt (fun q : ℂ => (1 - q)⁻¹)
      (formalMultilinearSeries_geometric ℂ ℂ) 0 :=
  ⟨1, hasFPowerSeriesOnBall_inv_one_sub ℂ ℂ⟩

private lemma hasFPowerSeriesAt_sum_rrJTerm_one (N : ℕ) :
    HasFPowerSeriesAt
      (fun q : ℂ => ∑ n ∈ Finset.range N, rrJTerm 1 q n)
      (∑ n ∈ Finset.range N, rrGTermFMLS n) 0 := by
  induction N with
  | zero =>
      simpa using (hasFPowerSeriesAt_const (c := (0 : ℂ)) (e := (0 : ℂ)))
  | succ N ih =>
      have hN := hasFPowerSeriesAt_rrJTerm_one N
      simpa [Finset.sum_range_succ, Pi.add_apply] using ih.add hN

private lemma rrGPS_complex_coeff_eq_sum (k : ℕ) :
    (PowerSeries.map (algebraMap ℚ ℂ) rrGPS).coeff k =
      ∑ n ∈ Finset.range (k + 1), (rrGTermFMLS n).coeff k := by
  rw [PowerSeries.coeff_map]
  unfold rrGPS
  rw [PowerSeries.coeff_mk, map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  simp [rrGTermFMLS, PowerSeries.coeff_map]

theorem rrJInf_one_taylorCoeff_eq_rrGPS_coeff
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt (fun q : ℂ => rrJInf 1 q) p 0)
    (k : ℕ) :
    p.coeff k = (PowerSeries.map (algebraMap ℚ ℂ) rrGPS).coeff k := by
  let P : FormalMultilinearSeries ℂ ℂ ℂ :=
    ∑ n ∈ Finset.range (k + 1), rrGTermFMLS n
  have hpartial :
      HasFPowerSeriesAt
        (fun q : ℂ => ∑ n ∈ Finset.range (k + 1), rrJTerm 1 q n) P 0 := by
    simpa [P] using hasFPowerSeriesAt_sum_rrJTerm_one (k + 1)
  have hdiff :
      HasFPowerSeriesAt
        (fun q : ℂ => rrJInf 1 q - ∑ n ∈ Finset.range (k + 1), rrJTerm 1 q n)
        (p - P) 0 := by
    simpa [Pi.sub_apply] using hp.sub hpartial
  have hzero :
      (p - P).coeff k = 0 :=
    coeff_eq_zero_of_isBigO_norm_pow hdiff
      (rrJInf_one_sub_partial_isBigO (k + 1) (Nat.succ_pos k))
      (Nat.lt_succ_self k)
  change p.coeff k - P.coeff k = 0 at hzero
  have hp_eq : p.coeff k = P.coeff k := sub_eq_zero.mp hzero
  calc
    p.coeff k = P.coeff k := hp_eq
    _ = ∑ n ∈ Finset.range (k + 1), (rrGTermFMLS n).coeff k := by
      simp [P, fmls_sum_coeff]
    _ = (PowerSeries.map (algebraMap ℚ ℂ) rrGPS).coeff k :=
      (rrGPS_complex_coeff_eq_sum k).symm

theorem exists_rrJInf_one_taylor_coeffs_agree :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun q : ℂ => rrJInf 1 q) p 0 ∧
        ∀ n : ℕ, p.coeff n = (PowerSeries.map (algebraMap ℚ ℂ) rrGPS).coeff n := by
  rcases analyticAt_rrJInf_one_zero with ⟨p, hp⟩
  exact ⟨p, hp, fun n => rrJInf_one_taylorCoeff_eq_rrGPS_coeff hp n⟩

private theorem rrJInf_one_taylor_coeff_eq_one_of_lt_four
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt (fun q : ℂ => rrJInf 1 q) p 0)
    {n : ℕ} (hn : n < 4) :
    p.coeff n = 1 := by
  have htail :
      HasFPowerSeriesAt
        (fun q : ℂ => rrJInf 1 q - (1 - q)⁻¹)
        (p - formalMultilinearSeries_geometric ℂ ℂ) 0 :=
    hp.sub inv_one_sub_taylor
  have hzero :
      (p - formalMultilinearSeries_geometric ℂ ℂ).coeff n = 0 :=
    coeff_eq_zero_of_isBigO_norm_pow htail rrJInf_one_sub_inv_one_sub_isBigO hn
  have hgeom :
      (formalMultilinearSeries_geometric ℂ ℂ).coeff n = 1 := by
    rw [formalMultilinearSeries_geometric_eq_ofScalars]
    simp
  change p.coeff n - (formalMultilinearSeries_geometric ℂ ℂ).coeff n = 0 at hzero
  rw [hgeom] at hzero
  linear_combination hzero

theorem rrJInf_one_taylorCoeff_eq_rrGPS_coeff_of_lt_four
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt (fun q : ℂ => rrJInf 1 q) p 0)
    {n : ℕ} (hn : n < 4) :
    p.coeff n = ((rrGPS).coeff n : ℂ) := by
  have hp1 := rrJInf_one_taylor_coeff_eq_one_of_lt_four hp hn
  interval_cases n <;>
    simp [hp1, coeff_zero_rrGPS, coeff_one_rrGPS, coeff_two_rrGPS, coeff_three_rrGPS]

theorem exists_rrJInf_one_taylor_coeffs_agree_to_order_four :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun q : ℂ => rrJInf 1 q) p 0 ∧
        ∀ n : ℕ, n < 4 → p.coeff n = ((rrGPS).coeff n : ℂ) := by
  rcases analyticAt_rrJInf_one_zero with ⟨p, hp⟩
  exact ⟨p, hp, fun n hn => rrJInf_one_taylorCoeff_eq_rrGPS_coeff_of_lt_four hp hn⟩

/-! ## H-side Taylor bridge -/

theorem analyticAt_rrJInf_q_zero :
    AnalyticAt ℂ (fun q : ℂ => rrJInf q q) 0 := by
  have h_num :
      AnalyticAt ℂ
        QseriesFormalization.Pending.RRAnalyticProofH.pentagonal014_analytic 0 :=
    (hasFPowerSeriesOnBall_pentagonal014Analytic.hasFPowerSeriesAt).analyticAt
  have h_den :
      AnalyticAt ℂ
        QseriesFormalization.Pending.RRAnalyticProofH.qPochhammer_inf 0 := by
    unfold QseriesFormalization.Pending.RRAnalyticProofH.qPochhammer_inf
    exact (hasFPowerSeriesOnBall_eulerPentagonalInfiniteProduct.hasFPowerSeriesAt).analyticAt
  have h_den_ne :
      QseriesFormalization.Pending.RRAnalyticProofH.qPochhammer_inf 0 ≠ 0 := by
    unfold QseriesFormalization.Pending.RRAnalyticProofH.qPochhammer_inf
    have h := eulerPentagonalInfiniteProduct_ne_zero (0 : ℂ) (by simp)
    simpa using h
  have h_quot :
      AnalyticAt ℂ
        (fun q : ℂ =>
          QseriesFormalization.Pending.RRAnalyticProofH.pentagonal014_analytic q /
            QseriesFormalization.Pending.RRAnalyticProofH.qPochhammer_inf q) 0 :=
    h_num.div h_den h_den_ne
  refine h_quot.congr ?_
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  filter_upwards [hball] with q hq
  have hq_norm : ‖q‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hq
  have hden :
      QseriesFormalization.Pending.RRAnalyticProofH.qPochhammer_inf q ≠ 0 := by
    unfold QseriesFormalization.Pending.RRAnalyticProofH.qPochhammer_inf
    exact eulerPentagonalInfiniteProduct_ne_zero q hq_norm
  have hmain :=
    RRAnalyticProofH.rrJInf_q_mul_qPochhammer_inf_eq_pentagonal014_analytic q hq_norm
  exact ((eq_div_iff hden).mpr hmain).symm

noncomputable def rrHTermFMLS (n : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun k => (PowerSeries.map (algebraMap ℚ ℂ) (rrHTermPS n)).coeff k)

private lemma map_rrHTermPS_complex (n : ℕ) :
    PowerSeries.map (algebraMap ℚ ℂ) (rrHTermPS n) =
      (PowerSeries.X : PowerSeries ℂ) ^ (n * (n + 1)) * qPochInvProductPS n := by
  unfold rrHTermPS
  rw [map_mul, map_pow, map_inv_qPochPS_complex]
  simp

private lemma rrJTerm_q_eq_zpow_mul_qPochInvProduct (z : ℂ) (n : ℕ) :
    rrJTerm z z n = z ^ (n * (n + 1)) * ∏ i ∈ Finset.range n, (1 - z ^ (i + 1))⁻¹ := by
  rw [rrJTerm, qPochhammer_eq_prod_range]
  have hpow : z ^ n * z ^ (n * n) = z ^ (n * (n + 1)) := by
    rw [← pow_add]
    congr 1
    ring
  rw [hpow]
  simp [div_eq_mul_inv, Finset.prod_inv_distrib]

private lemma hasSum_map_rrHTermPS_coeff_mul_pow
    (n : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (PowerSeries.map (algebraMap ℚ ℂ) (rrHTermPS n)).coeff k * z ^ k)
      (rrJTerm z z n) := by
  have hInv := hasSum_qPochInvProductPS_coeff_mul_pow n z hz
  have hShift := hasSum_X_pow_mul_coeff (qPochInvProductPS n) z
    (∏ i ∈ Finset.range n, (1 - z ^ (i + 1))⁻¹) (n * (n + 1)) hInv
  rw [rrJTerm_q_eq_zpow_mul_qPochInvProduct]
  simpa [map_rrHTermPS_complex] using hShift

theorem hasFPowerSeriesAt_rrJTerm_q (n : ℕ) :
    HasFPowerSeriesAt (fun q : ℂ => rrJTerm q q n) (rrHTermFMLS n) 0 := by
  rw [hasFPowerSeriesAt_iff']
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  filter_upwards [hball] with z hz
  have hz_norm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have h := hasSum_map_rrHTermPS_coeff_mul_pow n z hz_norm
  convert h using 1
  ext k
  simp [rrHTermFMLS, smul_eq_mul, mul_comm]

private lemma rrJInf_q_sub_partial_eq_tsum_tail
    (N : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    rrJInf q q - (∑ n ∈ Finset.range N, rrJTerm q q n) =
      ∑' m : ℕ, rrJTerm q q (m + N) := by
  have hsum := hasSum_rrJTerm q q hq
  have htail := (hasSum_nat_add_iff' (f := rrJTerm q q) N).mpr hsum
  exact htail.tsum_eq.symm

private lemma rrJInf_q_sub_partial_isBigO (N : ℕ) (hN : 0 < N) :
    (fun q : ℂ => rrJInf q q - ∑ n ∈ Finset.range N, rrJTerm q q n)
      =O[𝓝 (0 : ℂ)] fun q : ℂ => ‖q‖ ^ N := by
  let A : ℕ → ℝ := fun m => (2 : ℝ) ^ N * ((1 / 4 : ℝ) ^ m)
  have hA_summable : Summable A := by
    exact (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left _
  refine IsBigO.of_bound (∑' m : ℕ, A m) ?_
  have hball : Metric.ball (0 : ℂ) (1 / 8 : ℝ) ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  filter_upwards [hball] with q hq_ball
  have hq_lt_eighth : ‖q‖ < (1 / 8 : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm] using hq_ball
  have hq_le_eighth : ‖q‖ ≤ (1 / 8 : ℝ) := hq_lt_eighth.le
  have hq_lt_one : ‖q‖ < 1 := by nlinarith
  rw [rrJInf_q_sub_partial_eq_tsum_tail N q hq_lt_one]
  have hnorm_summable : Summable fun m : ℕ => ‖rrJTerm q q (m + N)‖ :=
    (summable_norm_rrJTerm q q hq_lt_one).comp_injective (i := fun m => m + N)
      (fun a b h => Nat.add_right_cancel h)
  have htail_norm :
      ‖∑' m : ℕ, rrJTerm q q (m + N)‖ ≤
        ∑' m : ℕ, ‖rrJTerm q q (m + N)‖ :=
    norm_tsum_le_tsum_norm hnorm_summable
  have hterm : ∀ m : ℕ, ‖rrJTerm q q (m + N)‖ ≤ A m * ‖q‖ ^ N := by
    intro m
    set r : ℕ := m + N
    have hr_ge_N : N ≤ r := by omega
    have hr_pos : 0 < r := lt_of_lt_of_le hN hr_ge_N
    have hden_pos : (0 : ℝ) < (1 / 2) ^ r := by positivity
    have hbase : (1 / 2 : ℝ) ≤ 1 - ‖q‖ := by nlinarith
    have hden_ge : (1 / 2 : ℝ) ^ r ≤ ‖qPochhammer q r‖ := by
      have h1 : (1 / 2 : ℝ) ^ r ≤ (1 - ‖q‖) ^ r := by
        exact pow_le_pow_left₀ (by norm_num) hbase r
      exact le_trans h1 (norm_qPochhammer_ge q hq_lt_one r)
    have hpow_extra_exp : m ≤ r * r + r - N := by
      subst r
      have hle : m + N ≤ (m + N) * (m + N) + (m + N) := by omega
      omega
    have hpow_extra : ‖q‖ ^ (r * r + r - N) ≤ (1 / 8 : ℝ) ^ m := by
      have hq_nonneg : 0 ≤ ‖q‖ := norm_nonneg q
      have hq_le_one : ‖q‖ ≤ 1 := by nlinarith
      calc
        ‖q‖ ^ (r * r + r - N) ≤ ‖q‖ ^ m :=
          pow_le_pow_of_le_one hq_nonneg hq_le_one hpow_extra_exp
        _ ≤ (1 / 8 : ℝ) ^ m :=
          pow_le_pow_left₀ hq_nonneg hq_le_eighth m
    have hpow_split : ‖q‖ ^ (r * r + r) = ‖q‖ ^ N * ‖q‖ ^ (r * r + r - N) := by
      rw [← pow_add]
      congr 1
      have hN_le : N ≤ r * r + r := by
        exact le_trans hr_ge_N (by omega)
      omega
    rw [norm_rrJTerm_eq]
    calc
      ‖q‖ ^ r * ‖q‖ ^ (r * r) / ‖qPochhammer q r‖
          = ‖q‖ ^ (r * r + r) / ‖qPochhammer q r‖ := by
            rw [← pow_add]
            congr 2
            ring
      _ ≤ ‖q‖ ^ (r * r + r) / ((1 / 2 : ℝ) ^ r) := by
            exact div_le_div_of_nonneg_left (by positivity) hden_pos hden_ge
      _ = ‖q‖ ^ N * ‖q‖ ^ (r * r + r - N) / ((1 / 2 : ℝ) ^ r) := by
            rw [hpow_split]
      _ ≤ ‖q‖ ^ N * ((1 / 8 : ℝ) ^ m) / ((1 / 2 : ℝ) ^ r) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow_extra (by positivity))
              (by positivity)
      _ = A m * ‖q‖ ^ N := by
            dsimp [A]
            subst r
            rw [div_eq_mul_inv, ← inv_pow]
            norm_num
            rw [pow_add]
            have hpow : (1 / 8 : ℝ) ^ m * 2 ^ m = (1 / 4 : ℝ) ^ m := by
              rw [← mul_pow]
              norm_num
            calc
              ‖q‖ ^ N * (1 / 8 : ℝ) ^ m * (2 ^ m * 2 ^ N)
                  = ‖q‖ ^ N * ((1 / 8 : ℝ) ^ m * 2 ^ m) * 2 ^ N := by ring
              _ = ‖q‖ ^ N * (1 / 4 : ℝ) ^ m * 2 ^ N := by rw [hpow]
              _ = 2 ^ N * (1 / 4 : ℝ) ^ m * ‖q‖ ^ N := by ring
  have hsum_le :
      (∑' m : ℕ, ‖rrJTerm q q (m + N)‖) ≤
        ∑' m : ℕ, A m * ‖q‖ ^ N :=
    hnorm_summable.tsum_le_tsum hterm (hA_summable.mul_right _)
  have hsum_eval : (∑' m : ℕ, A m * ‖q‖ ^ N) = (∑' m : ℕ, A m) * ‖q‖ ^ N := by
    rw [tsum_mul_right]
  calc
    ‖∑' m : ℕ, rrJTerm q q (m + N)‖
        ≤ ∑' m : ℕ, ‖rrJTerm q q (m + N)‖ := htail_norm
    _ ≤ ∑' m : ℕ, A m * ‖q‖ ^ N := hsum_le
    _ = (∑' m : ℕ, A m) * ‖q‖ ^ N := hsum_eval
    _ = (∑' m : ℕ, A m) * ‖(‖q‖ ^ N : ℝ)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖q‖ ^ N)]

private lemma hasFPowerSeriesAt_sum_rrJTerm_q (N : ℕ) :
    HasFPowerSeriesAt
      (fun q : ℂ => ∑ n ∈ Finset.range N, rrJTerm q q n)
      (∑ n ∈ Finset.range N, rrHTermFMLS n) 0 := by
  induction N with
  | zero =>
      simpa using (hasFPowerSeriesAt_const (c := (0 : ℂ)) (e := (0 : ℂ)))
  | succ N ih =>
      have hN := hasFPowerSeriesAt_rrJTerm_q N
      simpa [Finset.sum_range_succ, Pi.add_apply] using ih.add hN

private lemma rrHPS_complex_coeff_eq_sum (k : ℕ) :
    (PowerSeries.map (algebraMap ℚ ℂ) rrHPS).coeff k =
      ∑ n ∈ Finset.range (k + 1), (rrHTermFMLS n).coeff k := by
  rw [PowerSeries.coeff_map]
  unfold rrHPS
  rw [PowerSeries.coeff_mk, map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  simp [rrHTermFMLS, PowerSeries.coeff_map]

theorem rrJInf_q_taylorCoeff_eq_rrHPS_coeff
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt (fun q : ℂ => rrJInf q q) p 0)
    (k : ℕ) :
    p.coeff k = (PowerSeries.map (algebraMap ℚ ℂ) rrHPS).coeff k := by
  let P : FormalMultilinearSeries ℂ ℂ ℂ :=
    ∑ n ∈ Finset.range (k + 1), rrHTermFMLS n
  have hpartial :
      HasFPowerSeriesAt
        (fun q : ℂ => ∑ n ∈ Finset.range (k + 1), rrJTerm q q n) P 0 := by
    simpa [P] using hasFPowerSeriesAt_sum_rrJTerm_q (k + 1)
  have hdiff :
      HasFPowerSeriesAt
        (fun q : ℂ => rrJInf q q - ∑ n ∈ Finset.range (k + 1), rrJTerm q q n)
        (p - P) 0 := by
    simpa [Pi.sub_apply] using hp.sub hpartial
  have hzero :
      (p - P).coeff k = 0 :=
    coeff_eq_zero_of_isBigO_norm_pow hdiff
      (rrJInf_q_sub_partial_isBigO (k + 1) (Nat.succ_pos k))
      (Nat.lt_succ_self k)
  change p.coeff k - P.coeff k = 0 at hzero
  have hp_eq : p.coeff k = P.coeff k := sub_eq_zero.mp hzero
  calc
    p.coeff k = P.coeff k := hp_eq
    _ = ∑ n ∈ Finset.range (k + 1), (rrHTermFMLS n).coeff k := by
      simp [P, fmls_sum_coeff]
    _ = (PowerSeries.map (algebraMap ℚ ℂ) rrHPS).coeff k :=
      (rrHPS_complex_coeff_eq_sum k).symm

theorem exists_rrJInf_q_taylor_coeffs_agree :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun q : ℂ => rrJInf q q) p 0 ∧
        ∀ n : ℕ, p.coeff n = (PowerSeries.map (algebraMap ℚ ℂ) rrHPS).coeff n := by
  rcases analyticAt_rrJInf_q_zero with ⟨p, hp⟩
  exact ⟨p, hp, fun n => rrJInf_q_taylorCoeff_eq_rrHPS_coeff hp n⟩

end RRTaylorBridge
end Pending
end QseriesFormalization
