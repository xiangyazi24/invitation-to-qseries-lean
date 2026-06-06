import QseriesFormalization.Pending.RamanujanQuinticJTP
import QseriesFormalization.Pending.RR_TaylorBridge
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Pending: Chan §16 Theorem 16.1 — the "Most Beautiful Identity"

Chan, *An Invitation to q-Series*, Theorem 16.1 (`for |q| < 1`):

  ∑_{n=0}^{∞} p(5n+4) q^n  =  5 · (q^5; q^5)_∞^5 / (q;q)_∞^6.

This file states Chan's identity in two forms:

1. **Analytic form** over `ℂ` (matching the book's hypothesis `|q| < 1`),
   in terms of `tsum` and `tprod`.
2. **Formal-power-series form** in `R⟦X⟧` (using Chapter19's
   `partitionGenFun R`, `qPochInfPS R`, and `PowerSeries.expand 5`).

The formal-power-series form is proved by importing the existing rational
quintic proof and transporting it through `ℤ`; the analytic form remains an
explicit honest stub.  This file lives in `Pending/` and is **NOT** imported
by `QseriesFormalization.lean`, so the main repo's `0 sorry` property is
preserved.

When Chan's MBI is later proved in the actual `Chapter16.lean` file,
this `Pending/` stub should be deleted.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch16

open PowerSeries
open Filter Topology
open scoped ENNReal

open QseriesFormalization.PartI.Ch04
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.RRTaylorBridge

private noncomputable def mbiLHSPS : PowerSeries ℂ :=
  PowerSeries.mk
    (fun n : ℕ =>
      (QseriesFormalization.PartIV.Ch19.partitionGenFun ℂ).coeff (5 * n + 4))

private noncomputable def mbiEtaQuotient (q : ℂ) : ℂ :=
  5 * (eulerPentagonalInfiniteProduct (q ^ 5)) ^ 5 /
    (eulerPentagonalInfiniteProduct q) ^ 6

private noncomputable def psFMLS (P : PowerSeries ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => P.coeff n)

private lemma psFMLS_apply_eq (P : PowerSeries ℂ) (z : ℂ) (n : ℕ) :
    psFMLS P n (fun _ : Fin n => z) = P.coeff n * z ^ n := by
  rw [psFMLS, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]

private lemma psFMLS_ext {P Q : PowerSeries ℂ}
    (h : psFMLS P = psFMLS Q) : P = Q := by
  ext n
  have hcoeff := congrFun (congrArg FormalMultilinearSeries.coeff h) n
  simpa [psFMLS, FormalMultilinearSeries.coeff_ofScalars] using hcoeff

private lemma psFMLS_smul (c : ℂ) (P : PowerSeries ℂ) :
    c • psFMLS P = psFMLS (c • P) := by
  rw [psFMLS, psFMLS]
  rw [← FormalMultilinearSeries.ofScalars_smul ℂ (fun n => P.coeff n) c]
  ext n
  simp

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

private lemma summable_norm_coeff_of_apply
    (P : PowerSeries ℂ) {z : ℂ}
    (hz : z ∈ EMetric.ball (0 : ℂ) (psFMLS P).radius) :
    Summable fun n : ℕ => ‖P.coeff n * z ^ n‖ := by
  have h := (psFMLS P).summable_norm_apply hz
  convert h using 1
  ext n
  rw [psFMLS_apply_eq]

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

private lemma hasFPowerSeriesAt_pow_ps
    {f : ℂ → ℂ} {P : PowerSeries ℂ}
    (hP : HasFPowerSeriesAt f (psFMLS P) 0) :
    ∀ m : ℕ, HasFPowerSeriesAt (fun z => (f z) ^ m) (psFMLS (P ^ m)) 0
  | 0 => by
      rw [hasFPowerSeriesAt_iff']
      filter_upwards [Filter.univ_mem] with z _hz
      simpa [psFMLS, PowerSeries.coeff_one, FormalMultilinearSeries.ofScalars_apply_eq,
        smul_eq_mul] using
        (hasSum_single (0 : ℕ)
          (f := fun n : ℕ => if n = 0 then z ^ n else 0)
          (by intro b hb; simp [hb]))
  | m + 1 => by
      simpa [pow_succ] using
        hasFPowerSeriesAt_mul_ps (hasFPowerSeriesAt_pow_ps hP m) hP

private lemma norm_lt_one_of_mem_emetric_unit_ball {q : ℂ}
    (hq : q ∈ EMetric.ball (0 : ℂ) (1 : ENNReal)) :
    ‖q‖ < 1 := by
  have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
  have h_ball : q ∈ Metric.ball (0 : ℂ) 1 := by
    rw [h1, Metric.emetric_ball] at hq
    exact hq
  have hdist : dist q (0 : ℂ) < 1 := Metric.mem_ball.mp h_ball
  rwa [dist_zero_right] at hdist

private theorem hasFPowerSeriesAt_euler :
    HasFPowerSeriesAt eulerPentagonalInfiniteProduct
      (psFMLS (qPochInfPS ℂ)) 0 := by
  have h : psFMLS (qPochInfPS ℂ) = qPochInfFMLS := rfl
  rw [h]
  exact ⟨1, hasFPowerSeriesOnBall_eulerPentagonalInfiniteProduct⟩

private noncomputable def multiplesEquiv (d : ℕ) (hd : 0 < d) :
    ℕ ≃ {k : ℕ // d ∣ k} where
  toFun m := ⟨d * m, ⟨m, rfl⟩⟩
  invFun k := k.1 / d
  left_inv m := Nat.mul_div_right m hd
  right_inv k := by
    ext
    change d * (k.1 / d) = k.1
    rw [mul_comm, Nat.div_mul_cancel k.2]

private lemma hasSum_expand_coeff_mul_pow
    (P : PowerSeries ℂ) (d : ℕ) (hd : d ≠ 0) (z a : ℂ)
    (h : HasSum (fun n : ℕ => P.coeff n * (z ^ d) ^ n) a) :
    HasSum (fun k : ℕ => (PowerSeries.expand d hd P).coeff k * z ^ k) a := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  let f : ℕ → ℂ := fun k => (PowerSeries.expand d hd P).coeff k * z ^ k
  have hf_support : Function.support f ⊆ {k : ℕ | d ∣ k} := by
    intro k hk
    by_contra hkd
    have hnot : ¬ d ∣ k := hkd
    exact hk (by
      dsimp [f]
      rw [PowerSeries.coeff_expand, if_neg hnot]
      simp)
  have hsub : HasSum (f ∘ (fun k : {k : ℕ // d ∣ k} => k.1)) a := by
    rw [← (multiplesEquiv d hdpos).hasSum_iff]
    convert h using 1
    ext m
    dsimp [f, multiplesEquiv]
    rw [PowerSeries.coeff_expand]
    have hdiv : d ∣ d * m := dvd_mul_right d m
    simp [hdiv, Nat.mul_div_right m hdpos, pow_mul]
  exact (hasSum_subtype_iff_of_support_subset hf_support).mp hsub

private theorem hasFPowerSeriesAt_euler_fifth :
    HasFPowerSeriesAt
      (fun z : ℂ => eulerPentagonalInfiniteProduct (z ^ 5))
      (psFMLS (PowerSeries.expand 5 (by decide) (qPochInfPS ℂ))) 0 := by
  rw [hasFPowerSeriesAt_iff]
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  filter_upwards [hball] with z hz
  have hz_norm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hz5_norm : ‖z ^ 5‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg z) hz_norm (by norm_num)
  have hz5_mem : z ^ 5 ∈ EMetric.ball (0 : ℂ) (1 : ENNReal) := by
    have hz5_met : z ^ 5 ∈ Metric.ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz5_norm
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    rw [h1, Metric.emetric_ball]
    exact hz5_met
  have hsum0 := hasFPowerSeriesOnBall_eulerPentagonalInfiniteProduct.hasSum hz5_mem
  have hsum1 :
      HasSum (fun n : ℕ => (qPochInfPS ℂ).coeff n * (z ^ 5) ^ n)
        (eulerPentagonalInfiniteProduct (z ^ 5)) := by
    simpa [qPochInfFMLS, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
      zero_add, mul_comm] using hsum0
  have hsum2 :=
    hasSum_expand_coeff_mul_pow (qPochInfPS ℂ) 5 (by decide) z
      (eulerPentagonalInfiniteProduct (z ^ 5)) hsum1
  simpa [psFMLS, FormalMultilinearSeries.coeff_ofScalars, zero_add, mul_comm] using hsum2

private noncomputable def mbiEtaQuotientTaylorPS : PowerSeries ℂ :=
  PowerSeries.mk (fun n => iteratedDeriv n mbiEtaQuotient 0 / n.factorial)

private lemma analyticAt_euler_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ eulerPentagonalInfiniteProduct z := by
  have hzmet : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzmem : z ∈ EMetric.ball (0 : ℂ) (1 : ENNReal) := by
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    rw [h1, Metric.emetric_ball]
    exact hzmet
  exact hasFPowerSeriesOnBall_eulerPentagonalInfiniteProduct.analyticAt_of_mem hzmem

private lemma analyticAt_mbiEtaQuotient_zero :
    AnalyticAt ℂ mbiEtaQuotient 0 := by
  have hE : AnalyticAt ℂ eulerPentagonalInfiniteProduct (0 : ℂ) :=
    analyticAt_euler_of_norm_lt_one (by norm_num)
  have hE5 : AnalyticAt ℂ eulerPentagonalInfiniteProduct ((0 : ℂ) ^ 5) :=
    analyticAt_euler_of_norm_lt_one (by norm_num)
  have hpowfun : AnalyticAt ℂ (fun w : ℂ => w ^ 5) (0 : ℂ) := by fun_prop
  have hnum : AnalyticAt ℂ
      (fun w : ℂ => (eulerPentagonalInfiniteProduct (w ^ 5)) ^ 5) (0 : ℂ) := by
    exact ((hE5.comp (f := fun w : ℂ => w ^ 5) hpowfun).pow 5)
  have hden : AnalyticAt ℂ
      (fun w : ℂ => (eulerPentagonalInfiniteProduct w) ^ 6) (0 : ℂ) := hE.pow 6
  have hden_ne : (eulerPentagonalInfiniteProduct (0 : ℂ)) ^ 6 ≠ 0 := by
    exact pow_ne_zero 6 (eulerPentagonalInfiniteProduct_ne_zero 0 (by norm_num))
  unfold mbiEtaQuotient
  exact (analyticAt_const.mul hnum).div hden hden_ne

private theorem hasFPowerSeriesAt_mbiEtaQuotient_taylor :
    HasFPowerSeriesAt mbiEtaQuotient (psFMLS mbiEtaQuotientTaylorPS) 0 := by
  have h := analyticAt_mbiEtaQuotient_zero.hasFPowerSeriesAt
  simpa [psFMLS, mbiEtaQuotientTaylorPS, PowerSeries.coeff_mk] using h

private theorem most_beautiful_identity_cleared_complex :
    mbiLHSPS * (qPochInfPS ℂ)^6 =
      (5 : ℂ) •
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℂ))^5 := by
  have hmbi :
      (PowerSeries.mk
          (fun n : ℕ => (partitionGenFun ℂ).coeff (5 * n + 4)) : ℂ⟦X⟧)
        = (5 : ℂ) •
          ((PowerSeries.expand 5 (by decide) (qPochInfPS ℂ)) ^ 5 *
           (partitionGenFun ℂ) ^ 6) := by
    have hmap :=
      congrArg (PowerSeries.map (algebraMap ℚ ℂ))
        QseriesFormalization.Pending.RamanujanQuinticJTP.most_beautiful_identity
    convert hmap using 1
    · ext n
      rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      have hcoeff :=
        congrArg (fun f : ℂ⟦X⟧ => f.coeff (5 * n + 4))
          (map_partitionGenFun (algebraMap ℚ ℂ))
      simpa [PowerSeries.coeff_map] using hcoeff.symm
    · simp [map_mul, map_pow, PowerSeries.map_expand, map_qPochInfPS,
        map_partitionGenFun]
      rw [show (PowerSeries.map (algebraMap ℚ ℂ)) (5 : ℚ⟦X⟧) =
          (PowerSeries.C : ℂ →+* ℂ⟦X⟧) 5 by
        rw [show (5 : ℚ⟦X⟧) = (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 5 by
          rw [PowerSeries.C_eq_algebraMap]
          rfl]
        rw [PowerSeries.map_C]
        norm_num]
      rw [PowerSeries.smul_eq_C_mul]
  have hpow :
      (partitionGenFun ℂ)^6 * (qPochInfPS ℂ)^6 = (1 : PowerSeries ℂ) := by
    have hmul : partitionGenFun ℂ * qPochInfPS ℂ = (1 : PowerSeries ℂ) :=
      partitionGenFun_mul_qPochInfPS ℂ
    rw [← mul_pow, hmul, one_pow]
  change
    (PowerSeries.mk
        (fun n : ℕ => (partitionGenFun ℂ).coeff (5 * n + 4)) : ℂ⟦X⟧) *
        (qPochInfPS ℂ)^6 =
      (5 : ℂ) •
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℂ))^5
  calc
    (PowerSeries.mk
        (fun n : ℕ => (partitionGenFun ℂ).coeff (5 * n + 4)) : ℂ⟦X⟧) *
        (qPochInfPS ℂ)^6
        = ((5 : ℂ) •
            ((PowerSeries.expand 5 (by decide) (qPochInfPS ℂ)) ^ 5 *
             (partitionGenFun ℂ) ^ 6)) * (qPochInfPS ℂ)^6 := by
          rw [hmbi]
    _ = (5 : ℂ) •
          ((PowerSeries.expand 5 (by decide) (qPochInfPS ℂ)) ^ 5 *
            ((partitionGenFun ℂ)^6 * (qPochInfPS ℂ)^6)) := by
          norm_num [nsmul_eq_mul]
          ring
    _ = (5 : ℂ) •
          ((PowerSeries.expand 5 (by decide) (qPochInfPS ℂ)) ^ 5 * 1) := by
          rw [hpow]
    _ = (5 : ℂ) •
          (PowerSeries.expand 5 (by decide) (qPochInfPS ℂ)) ^ 5 := by
          rw [mul_one]

private theorem mbiEtaQuotientTaylorPS_mul_den :
    mbiEtaQuotientTaylorPS * (qPochInfPS ℂ)^6 =
      (5 : ℂ) •
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℂ))^5 := by
  let Eps : PowerSeries ℂ := qPochInfPS ℂ
  let E5ps : PowerSeries ℂ := PowerSeries.expand 5 (by decide) (qPochInfPS ℂ)
  have hEpow6 :
      HasFPowerSeriesAt
        (fun z : ℂ => (eulerPentagonalInfiniteProduct z)^6)
        (psFMLS (Eps^6)) 0 := by
    simpa [Eps] using hasFPowerSeriesAt_pow_ps hasFPowerSeriesAt_euler 6
  have hleft :
      HasFPowerSeriesAt
        (fun z : ℂ => mbiEtaQuotient z * (eulerPentagonalInfiniteProduct z)^6)
        (psFMLS (mbiEtaQuotientTaylorPS * Eps^6)) 0 :=
    hasFPowerSeriesAt_mul_ps hasFPowerSeriesAt_mbiEtaQuotient_taylor hEpow6
  have hE5pow5 :
      HasFPowerSeriesAt
        (fun z : ℂ => (eulerPentagonalInfiniteProduct (z^5))^5)
        (psFMLS (E5ps^5)) 0 := by
    simpa [E5ps] using hasFPowerSeriesAt_pow_ps hasFPowerSeriesAt_euler_fifth 5
  have hright :
      HasFPowerSeriesAt
        (fun z : ℂ => 5 * (eulerPentagonalInfiniteProduct (z^5))^5)
        (psFMLS ((5 : ℂ) • E5ps^5)) 0 := by
    have h := hE5pow5.const_smul (c := (5 : ℂ))
    simpa [Pi.smul_apply, smul_eq_mul, psFMLS_smul, E5ps] using h
  have hevent :
      (fun z : ℂ => mbiEtaQuotient z * (eulerPentagonalInfiniteProduct z)^6)
        =ᶠ[𝓝 (0 : ℂ)]
      (fun z : ℂ => 5 * (eulerPentagonalInfiniteProduct (z^5))^5) := by
    have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
      Metric.ball_mem_nhds 0 (by norm_num)
    filter_upwards [hball] with z hz
    have hz_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have hE_ne : eulerPentagonalInfiniteProduct z ≠ 0 :=
      eulerPentagonalInfiniteProduct_ne_zero z hz_norm
    unfold mbiEtaQuotient
    field_simp [hE_ne]
  have h_unique :
      psFMLS (mbiEtaQuotientTaylorPS * Eps^6) =
        psFMLS ((5 : ℂ) • E5ps^5) :=
    hleft.eq_formalMultilinearSeries_of_eventually hright hevent
  simpa [Eps, E5ps] using psFMLS_ext h_unique

private theorem mbiEtaQuotientTaylorPS_eq_lhs :
    mbiEtaQuotientTaylorPS = mbiLHSPS := by
  have hformal := most_beautiful_identity_cleared_complex
  have hanalytic := mbiEtaQuotientTaylorPS_mul_den
  have hmul :
      mbiEtaQuotientTaylorPS * (qPochInfPS ℂ)^6 =
        mbiLHSPS * (qPochInfPS ℂ)^6 := by
    rw [hanalytic, hformal]
  exact ((isUnit_qPochInfPS ℂ).pow 6).mul_left_inj.mp hmul

private theorem hasFPowerSeriesAt_mbiEtaQuotient_lhs :
    HasFPowerSeriesAt mbiEtaQuotient (psFMLS mbiLHSPS) 0 := by
  simpa [mbiEtaQuotientTaylorPS_eq_lhs] using
    hasFPowerSeriesAt_mbiEtaQuotient_taylor

private theorem differentiableOn_mbiEtaQuotient_closedBall
    (R : NNReal) (hR : (R : ℝ) < 1) :
    DifferentiableOn ℂ mbiEtaQuotient (Metric.closedBall (0 : ℂ) (R : ℝ)) := by
  intro z hz
  have hz_norm : ‖z‖ < 1 := by
    have hzr : dist z (0 : ℂ) ≤ (R : ℝ) := by
      simpa [Metric.mem_closedBall] using hz
    rw [dist_zero_right] at hzr
    exact lt_of_le_of_lt hzr hR
  have hz5_norm : ‖z ^ 5‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg z) hz_norm (by norm_num)
  have hE : AnalyticAt ℂ eulerPentagonalInfiniteProduct z :=
    analyticAt_euler_of_norm_lt_one hz_norm
  have hE5 : AnalyticAt ℂ eulerPentagonalInfiniteProduct (z ^ 5) :=
    analyticAt_euler_of_norm_lt_one hz5_norm
  have hpowfun : AnalyticAt ℂ (fun w : ℂ => w ^ 5) z := by fun_prop
  have hnum : AnalyticAt ℂ
      (fun w : ℂ => (eulerPentagonalInfiniteProduct (w ^ 5)) ^ 5) z := by
    exact ((hE5.comp (f := fun w : ℂ => w ^ 5) hpowfun).pow 5)
  have hden : AnalyticAt ℂ
      (fun w : ℂ => (eulerPentagonalInfiniteProduct w) ^ 6) z := hE.pow 6
  have hden_ne : (eulerPentagonalInfiniteProduct z) ^ 6 ≠ 0 := by
    exact pow_ne_zero 6 (eulerPentagonalInfiniteProduct_ne_zero z hz_norm)
  have hH : AnalyticAt ℂ mbiEtaQuotient z := by
    unfold mbiEtaQuotient
    exact (analyticAt_const.mul hnum).div hden hden_ne
  exact hH.differentiableAt.differentiableWithinAt

private theorem hasFPowerSeriesOnBall_mbiEtaQuotient_lhs
    (R : NNReal) (hRpos : 0 < R) (hR : (R : ℝ) < 1) :
    HasFPowerSeriesOnBall mbiEtaQuotient (psFMLS mbiLHSPS) 0 (R : ENNReal) := by
  rcases hasFPowerSeriesAt_mbiEtaQuotient_lhs with ⟨r0, h0⟩
  have hcauchy :
      HasFPowerSeriesOnBall mbiEtaQuotient
        (cauchyPowerSeries mbiEtaQuotient 0 R) 0 (R : ENNReal) :=
    (differentiableOn_mbiEtaQuotient_closedBall R hR).hasFPowerSeriesOnBall hRpos
  exact h0.exchange_radius hcauchy

private theorem hasProd_pow {f : ℕ → ℂ} {a : ℂ}
    (hf : HasProd f a) :
    ∀ m : ℕ, HasProd (fun n : ℕ => (f n) ^ m) (a ^ m)
  | 0 => by
      simpa using (hasProd_one : HasProd (fun _ : ℕ => (1 : ℂ)) 1)
  | m + 1 => by
      have hmul := hf.mul (hasProd_pow hf m)
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul

private lemma tprod_euler_factor_pow
    (q : ℂ) (hq : ‖q‖ < 1) (m : ℕ) :
    (∏' n : ℕ, (1 - q ^ (n + 1)) ^ m) =
      (eulerPentagonalInfiniteProduct q) ^ m := by
  have h := hasProd_pow (hasProd_eulerPentagonalProductFactor q hq) m
  have h' : HasProd (fun n : ℕ => (1 - q ^ (n + 1)) ^ m)
      ((eulerPentagonalInfiniteProduct q) ^ m) := by
    simpa [eulerPentagonalProductFactor] using h
  exact h'.tprod_eq

private lemma tprod_euler_fifth_factor_pow
    (q : ℂ) (hq : ‖q‖ < 1) (m : ℕ) :
    (∏' n : ℕ, (1 - q ^ (5 * (n + 1))) ^ m) =
      (eulerPentagonalInfiniteProduct (q ^ 5)) ^ m := by
  have hq5 : ‖q ^ 5‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  calc
    (∏' n : ℕ, (1 - q ^ (5 * (n + 1))) ^ m)
        = ∏' n : ℕ, (1 - (q ^ 5) ^ (n + 1)) ^ m := by
          refine tprod_congr fun n => ?_
          rw [← pow_mul]
    _ = (eulerPentagonalInfiniteProduct (q ^ 5)) ^ m :=
          tprod_euler_factor_pow (q ^ 5) hq5 m

private theorem map_mbi_lhs_int (R : Type*) [CommRing R] :
    PowerSeries.map (Int.castRingHom R)
      (PowerSeries.mk
        (fun n : ℕ =>
          (QseriesFormalization.PartIV.Ch19.partitionGenFun ℤ).coeff (5 * n + 4))
        : ℤ⟦X⟧)
      =
    (PowerSeries.mk
      (fun n : ℕ =>
        (QseriesFormalization.PartIV.Ch19.partitionGenFun R).coeff (5 * n + 4))
      : R⟦X⟧) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  have hmap :=
    congrArg (fun f : R⟦X⟧ => f.coeff (5 * n + 4))
      (QseriesFormalization.PartIV.Ch19.map_partitionGenFun (Int.castRingHom R))
  simpa [PowerSeries.coeff_map] using hmap

private theorem map_mbi_rhs_int (R : Type*) [CommRing R] :
    PowerSeries.map (Int.castRingHom R)
      ((5 : ℤ) •
        ((PowerSeries.expand 5 (by decide)
            (QseriesFormalization.PartIV.Ch19.qPochInfPS ℤ)) ^ 5 *
         (QseriesFormalization.PartIV.Ch19.partitionGenFun ℤ) ^ 6))
      =
    (5 : R) •
      ((PowerSeries.expand 5 (by decide)
          (QseriesFormalization.PartIV.Ch19.qPochInfPS R)) ^ 5 *
       (QseriesFormalization.PartIV.Ch19.partitionGenFun R) ^ 6) := by
  let A : ℤ⟦X⟧ :=
    (PowerSeries.expand 5 (by decide)
        (QseriesFormalization.PartIV.Ch19.qPochInfPS ℤ)) ^ 5 *
      (QseriesFormalization.PartIV.Ch19.partitionGenFun ℤ) ^ 6
  let B : R⟦X⟧ :=
    (PowerSeries.expand 5 (by decide)
        (QseriesFormalization.PartIV.Ch19.qPochInfPS R)) ^ 5 *
      (QseriesFormalization.PartIV.Ch19.partitionGenFun R) ^ 6
  have hcore : PowerSeries.map (Int.castRingHom R) A = B := by
    simp [A, B, PowerSeries.map_expand,
      QseriesFormalization.PartIV.Ch19.map_qPochInfPS,
      QseriesFormalization.PartIV.Ch19.map_partitionGenFun]
  change PowerSeries.map (Int.castRingHom R) ((5 : ℤ) • A) = (5 : R) • B
  rw [map_zsmul, hcore]
  ext n
  rw [PowerSeries.coeff_smul]
  simp

private theorem most_beautiful_identity_formal_int :
    (PowerSeries.mk
        (fun n : ℕ =>
          (QseriesFormalization.PartIV.Ch19.partitionGenFun ℤ).coeff (5 * n + 4))
      : ℤ⟦X⟧)
      = (5 : ℤ) •
        ((PowerSeries.expand 5 (by decide)
            (QseriesFormalization.PartIV.Ch19.qPochInfPS ℤ)) ^ 5 *
         (QseriesFormalization.PartIV.Ch19.partitionGenFun ℤ) ^ 6) := by
  apply PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [map_mbi_lhs_int ℚ, map_mbi_rhs_int ℚ]
  exact QseriesFormalization.Pending.RamanujanQuinticJTP.most_beautiful_identity

/-- **Most Beautiful Identity, formal power series form.**

In `R⟦X⟧` (any commutative ring), Chan's Theorem 16.1 is the equality

  (LHS) ∑_{n ≥ 0} p(5n+4) · X^n
       =
  (RHS) 5 · (expand 5 ((qPochInfPS R)))^5 · (partitionGenFun R)^6
       =  5 · (q^5;q^5)_∞^5 · ((q;q)_∞)^{-6}

at the level of formal power series.  The left-hand side is a 5-section
of `partitionGenFun R`, picking only the coefficients at positions
`5n + 4`.

The proof requires (a) a 5-section / power-series decomposition lemma
and (b) the algebraic core identity relating `expand 5 (qPochInfPS R)^5`
to the 5-section of `partitionGenFun`.  Neither is in the repo yet. -/
theorem most_beautiful_identity_formal
    (R : Type*) [CommRing R] :
    (PowerSeries.mk
        (fun n : ℕ =>
          (QseriesFormalization.PartIV.Ch19.partitionGenFun R).coeff (5 * n + 4))
      : R⟦X⟧)
      = (5 : R) •
        ((PowerSeries.expand 5 (by decide)
            (QseriesFormalization.PartIV.Ch19.qPochInfPS R)) ^ 5 *
         (QseriesFormalization.PartIV.Ch19.partitionGenFun R) ^ 6) := by
  have h :=
    congrArg (PowerSeries.map (Int.castRingHom R)) most_beautiful_identity_formal_int
  rw [map_mbi_lhs_int R, map_mbi_rhs_int R] at h
  exact h

/-- The formal power series whose analytic evaluation should be
`∑ p(5n+4) q^n`. -/
noncomputable def mostBeautifulIdentityLHSPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk
    (fun n : ℕ =>
      (QseriesFormalization.PartIV.Ch19.partitionGenFun R).coeff (5 * n + 4))

/-- The formal power series whose analytic evaluation should be the product side
of Chan's Most Beautiful Identity. -/
noncomputable def mostBeautifulIdentityRHSPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  (5 : R) •
    ((PowerSeries.expand 5 (by decide)
        (QseriesFormalization.PartIV.Ch19.qPochInfPS R)) ^ 5 *
     (QseriesFormalization.PartIV.Ch19.partitionGenFun R) ^ 6)

/-- The formal theorem rewritten using the two named formal power series. -/
theorem mostBeautifulIdentityLHSPS_eq_RHSPS
    (R : Type*) [CommRing R] :
    mostBeautifulIdentityLHSPS R = mostBeautifulIdentityRHSPS R := by
  simpa [mostBeautifulIdentityLHSPS, mostBeautifulIdentityRHSPS]
    using most_beautiful_identity_formal R

/-- The left analytic series is the coefficient `tsum` of the formal 5-section.

This part is not an analytic convergence gap: it is just coefficient
identification for `partitionGenFun`. -/
theorem most_beautiful_identity_lhs_eq_coeff_tsum
    (q : ℂ) :
    (∑' n : ℕ,
      (QseriesFormalization.Ch01.partitionCount (5 * n + 4) : ℂ) * q ^ n)
      =
    ∑' n : ℕ, (mostBeautifulIdentityLHSPS ℂ).coeff n * q ^ n := by
  apply tsum_congr
  intro n
  simp [mostBeautifulIdentityLHSPS,
    QseriesFormalization.PartIV.Ch19.coeff_partitionGenFun,
    QseriesFormalization.Ch01.partitionCount]

/-- Formal coefficient equality gives equality of the corresponding coefficient
`tsum`s at any complex value.  This uses only `tsum_congr`; it does not assert
or prove convergence of either coefficient series. -/
theorem most_beautiful_identity_coeff_tsum_eq
    (q : ℂ) :
    (∑' n : ℕ, (mostBeautifulIdentityLHSPS ℂ).coeff n * q ^ n)
      =
    ∑' n : ℕ, (mostBeautifulIdentityRHSPS ℂ).coeff n * q ^ n := by
  apply tsum_congr
  intro n
  have hcoeff :=
    congrArg (fun f : ℂ⟦X⟧ => f.coeff n)
      (mostBeautifulIdentityLHSPS_eq_RHSPS ℂ)
  exact congrArg (fun c : ℂ => c * q ^ n) hcoeff

/-- Conditional analytic bridge for Chan's Most Beautiful Identity.

Once the product side is proved to be the analytic evaluation of
`mostBeautifulIdentityRHSPS ℂ`, the formal power-series identity already proves
the analytic identity. -/
theorem most_beautiful_identity_analytic_of_rhs_coeff_tsum
    (q : ℂ) (_hq : ‖q‖ < 1)
    (hRHS :
      (∑' n : ℕ, (mostBeautifulIdentityRHSPS ℂ).coeff n * q ^ n)
        =
      5 * (∏' n : ℕ, (1 - q ^ (5 * (n + 1)))^5) /
          (∏' n : ℕ, (1 - q ^ (n + 1))^6)) :
    (∑' n : ℕ,
      (QseriesFormalization.Ch01.partitionCount (5 * n + 4) : ℂ) * q ^ n)
      =
    5 * (∏' n : ℕ, (1 - q ^ (5 * (n + 1)))^5) /
        (∏' n : ℕ, (1 - q ^ (n + 1))^6) := by
  calc
    (∑' n : ℕ,
      (QseriesFormalization.Ch01.partitionCount (5 * n + 4) : ℂ) * q ^ n)
        = ∑' n : ℕ, (mostBeautifulIdentityLHSPS ℂ).coeff n * q ^ n :=
          most_beautiful_identity_lhs_eq_coeff_tsum q
    _ = ∑' n : ℕ, (mostBeautifulIdentityRHSPS ℂ).coeff n * q ^ n :=
          most_beautiful_identity_coeff_tsum_eq q
    _ = 5 * (∏' n : ℕ, (1 - q ^ (5 * (n + 1)))^5) /
        (∏' n : ℕ, (1 - q ^ (n + 1))^6) := hRHS

/-- **Most Beautiful Identity, analytic form (Chan's stated theorem).**

For `q ∈ ℂ` with `‖q‖ < 1`,

  ∑_{n ≥ 0} p(5n+4) · q^n  =  5 · ∏_{n ≥ 1} (1 - q^{5n})^5 / (1 - q^n)^6.

The infinite product converges in `ℂ` for `‖q‖ < 1`, as does the series
on the left.  Both equal numerical objects, and Chan's identity is their
equality at every such `q`.

Proving this from the formal-PS form `most_beautiful_identity_formal`
has now been reduced to one specific analytic evaluation bridge: the
coefficient `tsum` of
`mostBeautifulIdentityRHSPS ℂ =
  5 • ((expand 5 qPochInfPS)^5 * partitionGenFun^6)`
must be shown equal to
`5 * ∏ (1 - q^(5n))^5 / ∏ (1 - q^n)^6`.

That missing bridge requires analytic convergence/evaluation facts for
`partitionGenFun ℂ` as the reciprocal of `(q;q)_∞`, compatibility with
`PowerSeries.expand 5`, and Cauchy-product/power evaluation of the formal
RHS.  The current imports provide formal identities and an Euler-product
bridge for `qPochInfPS` in nearby files, but not this combined
`partitionGenFun`/inverse/power bridge. -/
theorem most_beautiful_identity_analytic
    (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ,
      (QseriesFormalization.Ch01.partitionCount (5 * n + 4) : ℂ) * q ^ n)
      =
    5 * (∏' n : ℕ, (1 - q ^ (5 * (n + 1)))^5) /
        (∏' n : ℕ, (1 - q ^ (n + 1))^6) := by
  refine most_beautiful_identity_analytic_of_rhs_coeff_tsum q hq ?_
  let R : NNReal := ⟨(‖q‖ + 1) / 2, by positivity⟩
  have hRpos : 0 < R := by
    change 0 < (‖q‖ + 1) / 2
    nlinarith [norm_nonneg q]
  have hqR : ‖q‖ < (R : ℝ) := by
    change ‖q‖ < (‖q‖ + 1) / 2
    nlinarith [hq]
  have hRlt : (R : ℝ) < 1 := by
    change (‖q‖ + 1) / 2 < 1
    nlinarith [hq]
  have hqmem : q ∈ EMetric.ball (0 : ℂ) (R : ENNReal) := by
    have hqmet : q ∈ Metric.ball (0 : ℂ) (R : ℝ) := by
      simpa [Metric.mem_ball, dist_zero_right] using hqR
    have hRenn : (R : ENNReal) = ENNReal.ofReal (R : ℝ) := by simp
    rw [hRenn, Metric.emetric_ball]
    exact hqmet
  have hseries :=
    (hasFPowerSeriesOnBall_mbiEtaQuotient_lhs R hRpos hRlt).hasSum hqmem
  have hsumLHS :
      HasSum
        (fun n : ℕ => (mostBeautifulIdentityLHSPS ℂ).coeff n * q ^ n)
        (mbiEtaQuotient q) := by
    change HasSum (fun n : ℕ => mbiLHSPS.coeff n * q ^ n) (mbiEtaQuotient q)
    have hseries' :
        HasSum (fun n : ℕ => mbiLHSPS.coeff n * q ^ n) (mbiEtaQuotient (0 + q)) :=
      hseries.congr_fun (fun n => by rw [psFMLS_apply_eq])
    simpa [zero_add] using hseries'
  calc
    (∑' n : ℕ, (mostBeautifulIdentityRHSPS ℂ).coeff n * q ^ n)
        = ∑' n : ℕ, (mostBeautifulIdentityLHSPS ℂ).coeff n * q ^ n :=
          (most_beautiful_identity_coeff_tsum_eq q).symm
    _ = mbiEtaQuotient q := hsumLHS.tsum_eq
    _ = 5 * (∏' n : ℕ, (1 - q ^ (5 * (n + 1)))^5) /
        (∏' n : ℕ, (1 - q ^ (n + 1))^6) := by
          unfold mbiEtaQuotient
          rw [tprod_euler_fifth_factor_pow q hq 5,
            tprod_euler_factor_pow q hq 6]

end Ch16
end Pending
end QseriesFormalization
