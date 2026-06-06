import Mathlib.RingTheory.PowerSeries.Expand
import QseriesFormalization.Pending.ASD_EtaProducts
import QseriesFormalization.Chapter04

/-!
# Formal power-series shells for the mod-7 JTP specialisations

This file mirrors the completed mod-5 path in
`Pending/JTP_FormalPS_Pentagonal.lean` and `Pending/ASD_EtaProducts.lean`.
It keeps all declarations local to this new pending file.
-/

namespace QseriesFormalization
namespace Pending
namespace JTPFormalPSMod7

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

open JTPFormalPSPentagonal
open ASDEtaProducts

/-! ## Analytic mod-7 AP factors -/

/-- The analytic factor `1 - q^(r + 7n)`. -/
def rrMod7Factor (q : ℂ) (r : ℕ) (n : ℕ) : ℂ :=
  1 - q ^ (r + 7 * n)

@[simp] theorem rrMod7Factor_def (q : ℂ) (r n : ℕ) :
    rrMod7Factor q r n = 1 - q ^ (r + 7 * n) := rfl

private theorem summable_norm_rrMod7_tail (q : ℂ) (hq : ‖q‖ < 1) (r : ℕ) :
    Summable fun n : ℕ => ‖-q ^ r * (q ^ 7) ^ n‖ := by
  have hq7 : ‖q ^ 7‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  exact PartI.Ch02.summable_norm_mul_geometric_complex (-(q ^ r)) (q ^ 7) hq7

/-- The `r`-th mod-7 residue factor family is multipliable for `‖q‖ < 1`. -/
theorem multipliable_rrMod7Factor (q : ℂ) (hq : ‖q‖ < 1) (r : ℕ) :
    Multipliable fun n : ℕ => rrMod7Factor q r n := by
  have h := multipliable_one_add_of_summable (summable_norm_rrMod7_tail q hq r)
  refine h.congr fun n => ?_
  simp only [rrMod7Factor]
  rw [show q ^ (r + 7 * n) = q ^ r * (q ^ 7) ^ n by
    rw [pow_add, pow_mul]]
  ring

theorem tprod_rrMod7Factor_zero (r : ℕ) (hr : 1 ≤ r) :
    (∏' n : ℕ, rrMod7Factor (0 : ℂ) r n) = 1 := by
  have hfac :
      (fun n : ℕ => rrMod7Factor (0 : ℂ) r n) = fun _ : ℕ => (1 : ℂ) := by
    funext n
    have hne : r + 7 * n ≠ 0 := by omega
    have hpow : (0 : ℂ) ^ (r + 7 * n) = 0 := zero_pow hne
    simp [rrMod7Factor, hpow]
  rw [hfac]
  simp

/-! ## Formal AP products -/

/-- `(q^a,q^b,q^7;q^7)_∞` as a formal power series. -/
noncomputable def mod7ProductPS
    (a b : ℕ) (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R a 7 * qPochAPPS R b 7 * qPochAPPS R 7 7

/-- The per-`n` triple factor for `(q^a,q^b,q^7;q^7)_∞`. -/
noncomputable def mod7TripleFactorPS
    (a b : ℕ) (R : Type*) [CommRing R] (n : ℕ) : R⟦X⟧ :=
  apFactorPS R a 7 n * apFactorPS R b 7 n * apFactorPS R 7 7 n

/-- HasProd form of a mod-7 triple product. -/
theorem hasProd_mod7TripleFactorPS
    (a b : ℕ) (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    HasProd (fun n : ℕ => mod7TripleFactorPS a b R n)
      (mod7ProductPS a b R) := by
  unfold mod7ProductPS mod7TripleFactorPS
  exact ((hasProd_qPochAPPS R a 7 (by norm_num)).mul
    (hasProd_qPochAPPS R b 7 (by norm_num))).mul
    (hasProd_qPochAPPS R 7 7 (by norm_num))

/-- Tprod form of a mod-7 triple product. -/
theorem mod7ProductPS_eq_tprod
    (a b : ℕ) (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] :
    mod7ProductPS a b R = ∏' n : ℕ, mod7TripleFactorPS a b R n :=
  (hasProd_mod7TripleFactorPS a b R).tprod_eq.symm

/-- `(q^3,q^4,q^7;q^7)_∞`. -/
noncomputable abbrev mod7Product034PS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  mod7ProductPS 3 4 R

/-- `(q^2,q^5,q^7;q^7)_∞`. -/
noncomputable abbrev mod7Product025PS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  mod7ProductPS 2 5 R

/-- `(q,q^6,q^7;q^7)_∞`. -/
noncomputable abbrev mod7Product016PS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  mod7ProductPS 1 6 R

/-! ## Formal bilateral theta coefficients -/

/-- The allowed odd `c` values in the exponents `(7k² - ck)/2`. -/
def ThetaCValid (c : ℤ) : Prop := c = 1 ∨ c = 3 ∨ c = 5

private theorem thetaCValid_pos {c : ℤ} (hc : ThetaCValid c) : 0 < c := by
  rcases hc with rfl | rfl | rfl <;> norm_num

private theorem thetaCValid_le_five {c : ℤ} (hc : ThetaCValid c) : c ≤ 5 := by
  rcases hc with rfl | rfl | rfl <;> norm_num

private theorem thetaCValid_odd {c : ℤ} (hc : ThetaCValid c) : Odd c := by
  rcases hc with rfl | rfl | rfl <;> norm_num

/-- The integer exponent `(7k² - ck)/2`, coerced to `Nat`. -/
def theta7Exp (c : ℤ) (k : ℤ) : ℕ :=
  (k * (7 * k - c) / 2).toNat

/-- Coefficient of `X^n` in `∑ (-1)^k X^((7k²-ck)/2)`. -/
def theta7Coeff (c : ℤ) (R : Type*) [CommRing R] (n : ℕ) : R :=
  ∑ k ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ),
    if theta7Exp c k = n then negOnePowInt R k else 0

/-- Formal series `∑ (-1)^k X^((7k²-ck)/2)`. -/
noncomputable def theta7SeriesPS (c : ℤ) (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk (theta7Coeff c R)

@[simp] theorem coeff_theta7SeriesPS
    (c : ℤ) (R : Type*) [CommRing R] (n : ℕ) :
    (theta7SeriesPS c R).coeff n = theta7Coeff c R n := by
  unfold theta7SeriesPS
  rw [PowerSeries.coeff_mk]

lemma theta7Exp_nonneg_int {c : ℤ} (hc : ThetaCValid c) (k : ℤ) :
    0 ≤ k * (7 * k - c) / 2 := by
  have hc0 : 0 < c := thetaCValid_pos hc
  have hc5 : c ≤ 5 := thetaCValid_le_five hc
  have hnum : 0 ≤ k * (7 * k - c) := by
    by_cases hk : 0 ≤ k
    · by_cases hk0 : k = 0
      · simp [hk0]
      · have hkpos : 1 ≤ k := by omega
        have hfac : 0 ≤ 7 * k - c := by nlinarith
        exact mul_nonneg hk hfac
    · have hk_nonpos : k ≤ 0 := by omega
      have hfac : 7 * k - c ≤ 0 := by nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos hk_nonpos hfac
  exact Int.ediv_nonneg hnum (by norm_num)

lemma int_coe_theta7Exp {c : ℤ} (hc : ThetaCValid c) (k : ℤ) :
    (theta7Exp c k : ℤ) = k * (7 * k - c) / 2 := by
  unfold theta7Exp
  exact Int.toNat_of_nonneg (theta7Exp_nonneg_int hc k)

lemma theta7Exp_bound_pos {c : ℤ} (hc : ThetaCValid c) (k : ℤ) (hk : 0 ≤ k) :
    k ≤ k * (7 * k - c) / 2 := by
  rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)]
  have hc5 : c ≤ 5 := thetaCValid_le_five hc
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hkpos : 1 ≤ k := by omega
    nlinarith

lemma theta7Exp_bound_neg {c : ℤ} (hc : ThetaCValid c) (k : ℤ) (hk : k ≤ 0) :
    -k ≤ k * (7 * k - c) / 2 := by
  rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)]
  have hc0 : 0 < c := thetaCValid_pos hc
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hkneg : k ≤ -1 := by omega
    nlinarith

lemma theta7Exp_mem_Icc_of_eq {c : ℤ} (hc : ThetaCValid c)
    {k : ℤ} {n : ℕ} (h : theta7Exp c k = n) :
    k ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ) := by
  rw [Finset.mem_Icc]
  have hn : (n : ℤ) = k * (7 * k - c) / 2 := by
    rw [← h]
    exact int_coe_theta7Exp hc k
  constructor
  · by_cases hk : 0 ≤ k
    · have hn_nonneg : (0 : ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
      omega
    · have hk_nonpos : k ≤ 0 := by omega
      have hneg : -k ≤ (n : ℤ) := by
        rw [hn]
        exact theta7Exp_bound_neg hc k hk_nonpos
      omega
  · by_cases hk : 0 ≤ k
    · have hle : k ≤ (n : ℤ) := by
        rw [hn]
        exact theta7Exp_bound_pos hc k hk
      omega
    · have hk_nonpos : k ≤ 0 := by omega
      have hn_nonneg : (0 : ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
      omega

lemma theta7Exp_pos_of_ne_zero {c : ℤ} (hc : ThetaCValid c) {k : ℤ}
    (hk : k ≠ 0) :
    0 < theta7Exp c k := by
  by_cases hk_nonneg : 0 ≤ k
  · have hk_one : (1 : ℤ) ≤ k := by omega
    have hle_int : (1 : ℤ) ≤ (theta7Exp c k : ℤ) := by
      rw [int_coe_theta7Exp hc]
      exact le_trans hk_one (theta7Exp_bound_pos hc k hk_nonneg)
    have hle_nat : 1 ≤ theta7Exp c k := by exact_mod_cast hle_int
    omega
  · have hk_nonpos : k ≤ 0 := by omega
    have hk_one : (1 : ℤ) ≤ -k := by omega
    have hle_int : (1 : ℤ) ≤ (theta7Exp c k : ℤ) := by
      rw [int_coe_theta7Exp hc]
      exact le_trans hk_one (theta7Exp_bound_neg hc k hk_nonpos)
    have hle_nat : 1 ≤ theta7Exp c k := by exact_mod_cast hle_int
    omega

/-! ## Bilateral theta analytic-to-formal bridge -/

noncomputable def theta7ThetaTerm (c : ℤ) (q : ℂ) (k : ℤ) : ℂ :=
  negOnePowInt ℂ k * q ^ theta7Exp c k

noncomputable def theta7ThetaNat (c : ℤ) (q : ℂ) : ℂ :=
  ∑' k : ℤ, theta7ThetaTerm c q k

noncomputable def theta7Analytic (c : ℤ) (q : ℂ) : ℂ :=
  ∑' k : ℤ, (-1 : ℂ) ^ k * q ^ (k * (7 * k - c) / 2)

lemma theta7_zpow_term_eq_thetaTerm {c : ℤ} (hc : ThetaCValid c) (q : ℂ) (k : ℤ) :
    (-1 : ℂ) ^ k * q ^ (k * (7 * k - c) / 2) =
      theta7ThetaTerm c q k := by
  rw [theta7ThetaTerm]
  rw [← negOnePowInt_complex_eq_zpow k]
  rw [← int_coe_theta7Exp hc k]
  rw [zpow_natCast]

theorem theta7Analytic_eq_thetaNat {c : ℤ} (hc : ThetaCValid c) (q : ℂ) :
    theta7Analytic c q = theta7ThetaNat c q := by
  unfold theta7Analytic theta7ThetaNat
  exact tsum_congr fun k => theta7_zpow_term_eq_thetaTerm hc q k

theorem summable_theta7ThetaTerm {c : ℤ} (hc : ThetaCValid c) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun k : ℤ => theta7ThetaTerm c q k := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hgeom : Summable fun n : ℕ => ‖q‖ ^ n := by
    have hnorm : ‖(‖q‖ : ℝ)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg q)]
      exact hq
    simpa using summable_geometric_of_norm_lt_one hnorm
  constructor
  · refine Summable.of_norm_bounded hgeom ?_
    intro n
    have hle_int : (n : ℤ) ≤ (theta7Exp c (n : ℤ) : ℤ) := by
      rw [int_coe_theta7Exp hc]
      exact theta7Exp_bound_pos hc (n : ℤ) (by exact_mod_cast Nat.zero_le n)
    have hle_nat : n ≤ theta7Exp c (n : ℤ) := by exact_mod_cast hle_int
    calc
      ‖theta7ThetaTerm c q (n : ℤ)‖ = ‖q‖ ^ theta7Exp c (n : ℤ) := by
        rw [theta7ThetaTerm, norm_mul, norm_negOnePowInt_complex, one_mul, norm_pow]
      _ ≤ ‖q‖ ^ n := pow_le_pow_of_le_one (norm_nonneg q) (le_of_lt hq) hle_nat
  · refine Summable.of_norm_bounded hgeom ?_
    intro n
    have hle_int : (n : ℤ) ≤ (theta7Exp c (-(n : ℤ)) : ℤ) := by
      have h := theta7Exp_bound_neg hc (-(n : ℤ)) (by omega)
      rw [← int_coe_theta7Exp hc (-(n : ℤ))] at h
      simpa using h
    have hle_nat : n ≤ theta7Exp c (-(n : ℤ)) := by exact_mod_cast hle_int
    calc
      ‖theta7ThetaTerm c q (-(n : ℤ))‖ = ‖q‖ ^ theta7Exp c (-(n : ℤ)) := by
        rw [theta7ThetaTerm, norm_mul, norm_negOnePowInt_complex, one_mul, norm_pow]
      _ ≤ ‖q‖ ^ n := pow_le_pow_of_le_one (norm_nonneg q) (le_of_lt hq) hle_nat

theorem theta7_fiber_tsum_eq_coeff_mul_pow
    {c : ℤ} (hc : ThetaCValid c) (q : ℂ) (n : ℕ) :
    (∑' k : ↑(theta7Exp c ⁻¹' ({n} : Set ℕ)), theta7ThetaTerm c q k) =
      theta7Coeff c ℂ n * q ^ n := by
  rw [tsum_subtype]
  rw [tsum_eq_sum (s := Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ))]
  · rw [theta7Coeff, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases h : theta7Exp c k = n
    · rw [Set.indicator_of_mem]
      · simp [h, theta7ThetaTerm]
      · simpa using h
    · have hnot : k ∉ theta7Exp c ⁻¹' ({n} : Set ℕ) := by
        simpa using h
      rw [Set.indicator_of_notMem hnot]
      simp [h]
  · intro k hk
    rw [Set.indicator_of_notMem]
    intro hmem
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hmem
    exact hk (theta7Exp_mem_Icc_of_eq hc hmem)

theorem hasSum_theta7Coeff_mul_pow {c : ℤ} (hc : ThetaCValid c) (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => theta7Coeff c ℂ n * q ^ n)
      (theta7ThetaNat c q) := by
  unfold theta7ThetaNat
  have h := (summable_theta7ThetaTerm hc q hq).hasSum
  convert h.tsum_fiberwise (theta7Exp c) using 1
  ext n
  exact (theta7_fiber_tsum_eq_coeff_mul_pow hc q n).symm

noncomputable def theta7SeriesFMLS (c : ℤ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (theta7Coeff c ℂ)

theorem one_le_theta7SeriesFMLS_radius {c : ℤ} (hc : ThetaCValid c) :
    (1 : ENNReal) ≤ (theta7SeriesFMLS c).radius := by
  rw [show (1 : ENNReal) = ((1 : NNReal) : ENNReal) by simp]
  apply ENNReal.le_of_forall_nnreal_lt
  intro s hs
  rw [ENNReal.coe_lt_coe] at hs
  have hq_norm : ‖((s : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
    exact_mod_cast hs
  have h_sum := (hasSum_theta7Coeff_mul_pow hc ((s : ℝ) : ℂ) hq_norm).summable
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have h_sum_norm := h_sum.norm
  have h_eq :
      (fun n : ℕ => ‖(theta7SeriesFMLS c) n‖ * (s : ℝ) ^ n) =
        (fun n : ℕ => ‖theta7Coeff c ℂ n * (((s : ℝ) : ℂ)) ^ n‖) := by
    funext n
    rw [theta7SeriesFMLS, FormalMultilinearSeries.ofScalars_norm]
    rw [norm_mul, norm_pow]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
  rw [h_eq]
  exact h_sum_norm

theorem hasFPowerSeriesOnBall_theta7ThetaNat {c : ℤ} (hc : ThetaCValid c) :
    HasFPowerSeriesOnBall (theta7ThetaNat c) (theta7SeriesFMLS c) 0 1 := by
  refine ⟨one_le_theta7SeriesFMLS_radius hc, by positivity, ?_⟩
  intro y hy
  rw [zero_add]
  have hy_norm : ‖y‖ < 1 := by
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    have h_ball : y ∈ Metric.ball (0 : ℂ) 1 := by
      rw [h1, Metric.emetric_ball] at hy
      exact hy
    have h2 : dist y (0 : ℂ) < 1 := Metric.mem_ball.mp h_ball
    rwa [dist_zero_right] at h2
  have h := hasSum_theta7Coeff_mul_pow hc y hy_norm
  convert h using 1
  funext n
  rw [theta7SeriesFMLS, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]

theorem hasFPowerSeriesOnBall_theta7Analytic {c : ℤ} (hc : ThetaCValid c) :
    HasFPowerSeriesOnBall (theta7Analytic c) (theta7SeriesFMLS c) 0 1 := by
  exact (hasFPowerSeriesOnBall_theta7ThetaNat hc).congr fun q _ =>
    (theta7Analytic_eq_thetaNat hc q).symm

private theorem int_two_dvd_j_mul_seven_j_add {c : ℤ} (hc : ThetaCValid c) (j : ℤ) :
    (2 : ℤ) ∣ j * (7 * j + c) := by
  rcases Int.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (7 * j + c), by rw [hm]; ring⟩
  · rcases thetaCValid_odd hc with ⟨t, ht⟩
    exact ⟨j * (7 * m + t + 4), by rw [hm, ht]; ring⟩

private theorem theta7_zpow_Y_seven_j_add
    {c : ℤ} (hc : ThetaCValid c) (Y q : ℂ) (hYq : Y ^ 2 = q) (j : ℤ) :
    Y ^ (j * (7 * j + c)) = q ^ (j * (7 * j + c) / 2) := by
  have hdiv : (2 : ℤ) ∣ j * (7 * j + c) := int_two_dvd_j_mul_seven_j_add hc j
  have hmul : 2 * (j * (7 * j + c) / 2) = j * (7 * j + c) := by
    rw [show 2 * (j * (7 * j + c) / 2) = (j * (7 * j + c) / 2) * 2 by ring]
    exact Int.ediv_mul_cancel hdiv
  calc
    Y ^ (j * (7 * j + c)) = Y ^ (2 * (j * (7 * j + c) / 2)) := by rw [hmul]
    _ = (Y ^ (2 : ℤ)) ^ (j * (7 * j + c) / 2) := by rw [zpow_mul]
    _ = (Y ^ 2) ^ (j * (7 * j + c) / 2) := by rfl
    _ = q ^ (j * (7 * j + c) / 2) := by rw [hYq]

theorem theta7_minus_eq_plus_tsum (c : ℤ) (q : ℂ) :
    theta7Analytic c q =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (7 * j + c) / 2) := by
  unfold theta7Analytic
  rw [← (Equiv.neg ℤ).tsum_eq
    (fun j : ℤ => (-1 : ℂ) ^ j * q ^ (j * (7 * j - c) / 2))]
  exact tsum_congr fun j => by
    simp only [Equiv.neg_apply]
    have hsign : (-1 : ℂ) ^ (-j) = (-1 : ℂ) ^ j := by
      by_cases h : Even j <;> simp [neg_one_zpow_eq_ite, h]
    rw [hsign]
    congr 1
    ring_nf

theorem theta7_plus_tsum_eq_jacobiSeries
    {c : ℤ} (hc : ThetaCValid c) (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) :
    (PartI.Ch02.jacobiInfiniteSeries (Y ^ 7) (-(Y ^ c)) : ℂ) =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (7 * j + c) / 2) := by
  rw [PartI.Ch02.jacobiInfiniteSeries]
  refine tsum_congr fun j => ?_
  have h1 : (-(Y ^ c) : ℂ) ^ j = (-1) ^ j * (Y ^ c) ^ j := by
    rw [show (-(Y ^ c) : ℂ) = (-1 : ℂ) * (Y ^ c) by ring]
    rw [mul_zpow]
  have hYc : ((Y : ℂ) ^ c) ^ j = Y ^ (c * j) := by
    rw [← zpow_mul]
  have h2 : ((Y : ℂ) ^ 7) ^ (j ^ 2) = Y ^ (7 * (j * j)) := by
    rw [show j ^ 2 = j * j from by ring]
    rw [show ((Y : ℂ) ^ 7) ^ (j * j) = (Y ^ (7 : ℤ)) ^ (j * j) from rfl]
    rw [← zpow_mul]
  rw [h1, hYc, h2]
  rw [show ((-1 : ℂ) ^ j * Y ^ (c * j)) * Y ^ (7 * (j * j)) =
          (-1) ^ j * (Y ^ (c * j) * Y ^ (7 * (j * j))) from by ring]
  rw [← zpow_add₀ hYne]
  have h_exp : (c * j + 7 * (j * j) : ℤ) = j * (7 * j + c) := by ring
  rw [h_exp, theta7_zpow_Y_seven_j_add hc Y q hYq j]

/-! ## Analytic JTP specialisations for modulus 7 -/

private lemma Y_pow_seven_even (Y q : ℂ) (hYq : Y ^ 2 = q) (m : ℕ) :
    (Y ^ 7) ^ (2 * m) = q ^ (7 * m) := by
  rw [← pow_mul, show 7 * (2 * m) = 2 * (7 * m) from by ring, pow_mul, hYq]

private lemma Y_pow_seven_odd_base (Y q : ℂ) (hYq : Y ^ 2 = q) (n : ℕ) :
    (Y ^ 7) ^ (2 * (n + 1) - 1) = Y * q ^ (7 * n + 3) := by
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 from by omega]
  rw [pow_succ, Y_pow_seven_even Y q hYq n]
  have hY7 : (Y : ℂ) ^ 7 = Y * (Y ^ 2) ^ 3 := by ring
  rw [hY7, hYq]
  rw [show q ^ (7 * n + 3) = q ^ (7 * n) * q ^ 3 from by rw [← pow_add]]
  ring

private lemma norm_Y_pow_7_lt_one (Y q : ℂ) (hYq : Y ^ 2 = q) (hq : ‖q‖ < 1) :
    ‖Y ^ 7‖ < 1 := by
  have hY_sq : ‖Y‖ ^ 2 = ‖q‖ := by
    rw [← norm_pow, hYq]
  have hY_nn : 0 ≤ ‖Y‖ := norm_nonneg _
  have hY_lt : ‖Y‖ < 1 := by
    have h := hq
    rw [← hY_sq] at h
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by simpa using h)
  rw [norm_pow]
  exact pow_lt_one₀ hY_nn hY_lt (by norm_num)

private theorem jacobiProductNatFactor_C1_substitution
    (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) (n : ℕ) :
    PartI.Ch02.jacobiProductNatFactor (Y ^ 7) (-(Y ^ (1 : ℤ))) n =
      rrMod7Factor q 7 n * rrMod7Factor q 4 n * rrMod7Factor q 3 n := by
  have hEven : (Y ^ 7) ^ (2 * (n + 1)) = q ^ (7 + 7 * n) := by
    rw [Y_pow_seven_even Y q hYq (n + 1)]
    congr 1
    ring
  have hOddBase := Y_pow_seven_odd_base Y q hYq n
  simp only [PartI.Ch02.jacobiProductNatFactor, PartI.Ch02.jacobiProductEvenFactor,
    PartI.Ch02.jacobiProductOddFactor, rrMod7Factor]
  rw [hEven, hOddBase]
  simp only [zpow_one]
  have h_inv : (-Y : ℂ)⁻¹ = -Y⁻¹ := by rw [neg_inv]
  rw [h_inv]
  have h_term2 : -Y * (Y * q ^ (7 * n + 3)) = -q ^ (7 * n + 4) := by
    have hYY : Y * Y = q := by rw [← sq, hYq]
    have h_succ : q ^ (7 * n + 4) = q * q ^ (7 * n + 3) := by
      rw [show 7 * n + 4 = 1 + (7 * n + 3) from by omega, pow_add, pow_one]
    rw [show -Y * (Y * q ^ (7 * n + 3)) = -(Y * Y) * q ^ (7 * n + 3) from by ring]
    rw [hYY, h_succ]
    ring
  have h_term3 : -Y⁻¹ * (Y * q ^ (7 * n + 3)) = -q ^ (7 * n + 3) := by
    field_simp
  rw [h_term2, h_term3]
  rw [show (7 * n + 4 : ℕ) = 4 + 7 * n from by omega,
      show (7 * n + 3 : ℕ) = 3 + 7 * n from by omega]
  ring

private theorem jacobiProductNatFactor_C3_substitution
    (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) (n : ℕ) :
    PartI.Ch02.jacobiProductNatFactor (Y ^ 7) (-(Y ^ (3 : ℤ))) n =
      rrMod7Factor q 7 n * rrMod7Factor q 5 n * rrMod7Factor q 2 n := by
  have hEven : (Y ^ 7) ^ (2 * (n + 1)) = q ^ (7 + 7 * n) := by
    rw [Y_pow_seven_even Y q hYq (n + 1)]
    congr 1
    ring
  have hOddBase := Y_pow_seven_odd_base Y q hYq n
  simp only [PartI.Ch02.jacobiProductNatFactor, PartI.Ch02.jacobiProductEvenFactor,
    PartI.Ch02.jacobiProductOddFactor, rrMod7Factor]
  rw [hEven, hOddBase]
  norm_num only [zpow_ofNat]
  have hY4 : (Y : ℂ) ^ 4 = q ^ 2 := by
    rw [show (Y : ℂ) ^ 4 = (Y ^ 2) ^ 2 from by ring, hYq]
  have h_term2 : -Y ^ 3 * (Y * q ^ (7 * n + 3)) = -q ^ (7 * n + 5) := by
    have : -Y ^ 3 * (Y * q ^ (7 * n + 3)) = -(Y ^ 4) * q ^ (7 * n + 3) := by ring
    rw [this, hY4]
    rw [show q ^ (7 * n + 5) = q ^ 2 * q ^ (7 * n + 3) from by
      rw [← pow_add]; congr 1; omega]
    ring
  have hq_ne_zero : q ≠ 0 := by
    intro hq_eq
    apply hYne
    have : Y ^ 2 = 0 := hq_eq ▸ hYq
    exact (pow_eq_zero_iff (n := 2) (by norm_num : (2 : ℕ) ≠ 0)).mp this
  have h_term3 : (-(Y ^ 3) : ℂ)⁻¹ * (Y * q ^ (7 * n + 3)) =
      -q ^ (7 * n + 2) := by
    have h_inv_Y3 : (-(Y ^ 3) : ℂ)⁻¹ = -(Y ^ 3)⁻¹ := by rw [neg_inv]
    rw [h_inv_Y3]
    have h_step : -(Y ^ 3)⁻¹ * (Y * q ^ (7 * n + 3)) =
        -((Y ^ 2)⁻¹ * q ^ (7 * n + 3)) := by
      field_simp
    rw [h_step, hYq]
    rw [show q ^ (7 * n + 3) = q * q ^ (7 * n + 2) from by
      rw [show 7 * n + 3 = (7 * n + 2) + 1 from by omega, pow_succ]
      ring]
    field_simp
  rw [h_term2, h_term3]
  rw [show (7 * n + 5 : ℕ) = 5 + 7 * n from by omega,
      show (7 * n + 2 : ℕ) = 2 + 7 * n from by omega]
  ring

private theorem jacobiProductNatFactor_C5_substitution
    (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) (n : ℕ) :
    PartI.Ch02.jacobiProductNatFactor (Y ^ 7) (-(Y ^ (5 : ℤ))) n =
      rrMod7Factor q 7 n * rrMod7Factor q 6 n * rrMod7Factor q 1 n := by
  have hEven : (Y ^ 7) ^ (2 * (n + 1)) = q ^ (7 + 7 * n) := by
    rw [Y_pow_seven_even Y q hYq (n + 1)]
    congr 1
    ring
  have hOddBase := Y_pow_seven_odd_base Y q hYq n
  simp only [PartI.Ch02.jacobiProductNatFactor, PartI.Ch02.jacobiProductEvenFactor,
    PartI.Ch02.jacobiProductOddFactor, rrMod7Factor]
  rw [hEven, hOddBase]
  norm_num only [zpow_ofNat]
  have hY6 : (Y : ℂ) ^ 6 = q ^ 3 := by
    rw [show (Y : ℂ) ^ 6 = (Y ^ 2) ^ 3 from by ring, hYq]
  have hY4 : (Y : ℂ) ^ 4 = q ^ 2 := by
    rw [show (Y : ℂ) ^ 4 = (Y ^ 2) ^ 2 from by ring, hYq]
  have h_term2 : -Y ^ 5 * (Y * q ^ (7 * n + 3)) = -q ^ (7 * n + 6) := by
    have : -Y ^ 5 * (Y * q ^ (7 * n + 3)) = -(Y ^ 6) * q ^ (7 * n + 3) := by ring
    rw [this, hY6]
    rw [show q ^ (7 * n + 6) = q ^ 3 * q ^ (7 * n + 3) from by
      rw [← pow_add]; congr 1; omega]
    ring
  have hq_ne_zero : q ≠ 0 := by
    intro hq_eq
    apply hYne
    have : Y ^ 2 = 0 := hq_eq ▸ hYq
    exact (pow_eq_zero_iff (n := 2) (by norm_num : (2 : ℕ) ≠ 0)).mp this
  have h_term3 : (-(Y ^ 5) : ℂ)⁻¹ * (Y * q ^ (7 * n + 3)) =
      -q ^ (7 * n + 1) := by
    have h_inv_Y5 : (-(Y ^ 5) : ℂ)⁻¹ = -(Y ^ 5)⁻¹ := by rw [neg_inv]
    rw [h_inv_Y5]
    have h_step : -(Y ^ 5)⁻¹ * (Y * q ^ (7 * n + 3)) =
        -((Y ^ 4)⁻¹ * q ^ (7 * n + 3)) := by
      field_simp
    rw [h_step, hY4]
    rw [show q ^ (7 * n + 3) = q ^ 2 * q ^ (7 * n + 1) from by
      rw [← pow_add]; congr 1; omega]
    field_simp
  rw [h_term2, h_term3]
  rw [show (7 * n + 6 : ℕ) = 6 + 7 * n from by omega,
      show (7 * n + 1 : ℕ) = 1 + 7 * n from by omega]
  ring

/-- Analytic product `(q^a,q^b,q^7;q^7)_∞`, ordered as the JTP product side. -/
noncomputable def mod7ProductAnalytic (a b : ℕ) (q : ℂ) : ℂ :=
  (∏' n : ℕ, rrMod7Factor q 7 n) *
    (∏' n : ℕ, rrMod7Factor q b n) *
    (∏' n : ℕ, rrMod7Factor q a n)

private theorem jacobiInfiniteProduct_C1_eq_mod7_triple
    (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) (hq : ‖q‖ < 1) :
    PartI.Ch02.jacobiInfiniteProduct (Y ^ 7) (-(Y ^ (1 : ℤ))) =
      mod7ProductAnalytic 3 4 q := by
  have hP7 := (multipliable_rrMod7Factor q hq 7).hasProd
  have hP4 := (multipliable_rrMod7Factor q hq 4).hasProd
  have hP3 := (multipliable_rrMod7Factor q hq 3).hasProd
  have hP_triple : HasProd
      (fun n : ℕ => rrMod7Factor q 7 n * rrMod7Factor q 4 n * rrMod7Factor q 3 n)
      (mod7ProductAnalytic 3 4 q) := by
    unfold mod7ProductAnalytic
    exact (hP7.mul hP4).mul hP3
  have hP_eq : HasProd
      (fun n : ℕ => PartI.Ch02.jacobiProductNatFactor (Y ^ 7) (-(Y ^ (1 : ℤ))) n)
      (mod7ProductAnalytic 3 4 q) := by
    refine hP_triple.congr_fun fun n => ?_
    exact jacobiProductNatFactor_C1_substitution q Y hYne hYq n
  rw [PartI.Ch02.jacobiInfiniteProduct_eq_tprod_natFactor]
  exact hP_eq.tprod_eq

private theorem jacobiInfiniteProduct_C3_eq_mod7_triple
    (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) (hq : ‖q‖ < 1) :
    PartI.Ch02.jacobiInfiniteProduct (Y ^ 7) (-(Y ^ (3 : ℤ))) =
      mod7ProductAnalytic 2 5 q := by
  have hP7 := (multipliable_rrMod7Factor q hq 7).hasProd
  have hP5 := (multipliable_rrMod7Factor q hq 5).hasProd
  have hP2 := (multipliable_rrMod7Factor q hq 2).hasProd
  have hP_triple : HasProd
      (fun n : ℕ => rrMod7Factor q 7 n * rrMod7Factor q 5 n * rrMod7Factor q 2 n)
      (mod7ProductAnalytic 2 5 q) := by
    unfold mod7ProductAnalytic
    exact (hP7.mul hP5).mul hP2
  have hP_eq : HasProd
      (fun n : ℕ => PartI.Ch02.jacobiProductNatFactor (Y ^ 7) (-(Y ^ (3 : ℤ))) n)
      (mod7ProductAnalytic 2 5 q) := by
    refine hP_triple.congr_fun fun n => ?_
    exact jacobiProductNatFactor_C3_substitution q Y hYne hYq n
  rw [PartI.Ch02.jacobiInfiniteProduct_eq_tprod_natFactor]
  exact hP_eq.tprod_eq

private theorem jacobiInfiniteProduct_C5_eq_mod7_triple
    (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) (hq : ‖q‖ < 1) :
    PartI.Ch02.jacobiInfiniteProduct (Y ^ 7) (-(Y ^ (5 : ℤ))) =
      mod7ProductAnalytic 1 6 q := by
  have hP7 := (multipliable_rrMod7Factor q hq 7).hasProd
  have hP6 := (multipliable_rrMod7Factor q hq 6).hasProd
  have hP1 := (multipliable_rrMod7Factor q hq 1).hasProd
  have hP_triple : HasProd
      (fun n : ℕ => rrMod7Factor q 7 n * rrMod7Factor q 6 n * rrMod7Factor q 1 n)
      (mod7ProductAnalytic 1 6 q) := by
    unfold mod7ProductAnalytic
    exact (hP7.mul hP6).mul hP1
  have hP_eq : HasProd
      (fun n : ℕ => PartI.Ch02.jacobiProductNatFactor (Y ^ 7) (-(Y ^ (5 : ℤ))) n)
      (mod7ProductAnalytic 1 6 q) := by
    refine hP_triple.congr_fun fun n => ?_
    exact jacobiProductNatFactor_C5_substitution q Y hYne hYq n
  rw [PartI.Ch02.jacobiInfiniteProduct_eq_tprod_natFactor]
  exact hP_eq.tprod_eq

theorem theta7ThetaNat_zero {c : ℤ} (hc : ThetaCValid c) :
    theta7ThetaNat c 0 = 1 := by
  unfold theta7ThetaNat
  rw [tsum_eq_single (0 : ℤ)]
  · simp [theta7ThetaTerm, theta7Exp, negOnePowInt]
  · intro k hk
    rw [theta7ThetaTerm]
    rw [zero_pow (theta7Exp_pos_of_ne_zero hc hk).ne', mul_zero]

theorem theta7Analytic_zero {c : ℤ} (hc : ThetaCValid c) :
    theta7Analytic c 0 = 1 := by
  rw [theta7Analytic_eq_thetaNat hc, theta7ThetaNat_zero hc]

theorem mod7ProductAnalytic_zero (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    mod7ProductAnalytic a b 0 = 1 := by
  unfold mod7ProductAnalytic
  rw [tprod_rrMod7Factor_zero 7 (by norm_num),
    tprod_rrMod7Factor_zero b hb,
    tprod_rrMod7Factor_zero a ha]
  ring

theorem mod7ProductAnalytic_eq_theta7Analytic_c1
    (q : ℂ) (hq : ‖q‖ < 1) :
    mod7ProductAnalytic 3 4 q = theta7Analytic 1 q := by
  by_cases hq_zero : q = 0
  · subst q
    rw [mod7ProductAnalytic_zero 3 4 (by norm_num) (by norm_num),
      theta7Analytic_zero (by left; rfl)]
  · obtain ⟨Y, hYq⟩ := IsAlgClosed.exists_pow_nat_eq q (n := 2) (by norm_num)
    have hYne : Y ≠ 0 := by
      intro hY_zero
      apply hq_zero
      rw [← hYq, hY_zero]
      ring
    have hY7_norm : ‖Y ^ 7‖ < 1 := norm_Y_pow_7_lt_one Y q hYq hq
    have hz_ne : (-(Y ^ (1 : ℤ)) : ℂ) ≠ 0 := by
      simp [hYne]
    rw [theta7_minus_eq_plus_tsum]
    rw [← theta7_plus_tsum_eq_jacobiSeries (c := 1) (by left; rfl) q Y hYne hYq]
    rw [← PartI.Ch02.jacobiTripleProduct (Y ^ 7) (-(Y ^ (1 : ℤ))) hY7_norm hz_ne]
    exact (jacobiInfiniteProduct_C1_eq_mod7_triple q Y hYne hYq hq).symm

theorem mod7ProductAnalytic_eq_theta7Analytic_c3
    (q : ℂ) (hq : ‖q‖ < 1) :
    mod7ProductAnalytic 2 5 q = theta7Analytic 3 q := by
  by_cases hq_zero : q = 0
  · subst q
    rw [mod7ProductAnalytic_zero 2 5 (by norm_num) (by norm_num),
      theta7Analytic_zero (by right; left; rfl)]
  · obtain ⟨Y, hYq⟩ := IsAlgClosed.exists_pow_nat_eq q (n := 2) (by norm_num)
    have hYne : Y ≠ 0 := by
      intro hY_zero
      apply hq_zero
      rw [← hYq, hY_zero]
      ring
    have hY7_norm : ‖Y ^ 7‖ < 1 := norm_Y_pow_7_lt_one Y q hYq hq
    have hz_ne : (-(Y ^ (3 : ℤ)) : ℂ) ≠ 0 := by
      norm_num only [zpow_ofNat]
      exact neg_ne_zero.mpr (pow_ne_zero 3 hYne)
    rw [theta7_minus_eq_plus_tsum]
    rw [← theta7_plus_tsum_eq_jacobiSeries (c := 3) (by right; left; rfl) q Y hYne hYq]
    rw [← PartI.Ch02.jacobiTripleProduct (Y ^ 7) (-(Y ^ (3 : ℤ))) hY7_norm hz_ne]
    exact (jacobiInfiniteProduct_C3_eq_mod7_triple q Y hYne hYq hq).symm

theorem mod7ProductAnalytic_eq_theta7Analytic_c5
    (q : ℂ) (hq : ‖q‖ < 1) :
    mod7ProductAnalytic 1 6 q = theta7Analytic 5 q := by
  by_cases hq_zero : q = 0
  · subst q
    rw [mod7ProductAnalytic_zero 1 6 (by norm_num) (by norm_num),
      theta7Analytic_zero (by right; right; rfl)]
  · obtain ⟨Y, hYq⟩ := IsAlgClosed.exists_pow_nat_eq q (n := 2) (by norm_num)
    have hYne : Y ≠ 0 := by
      intro hY_zero
      apply hq_zero
      rw [← hYq, hY_zero]
      ring
    have hY7_norm : ‖Y ^ 7‖ < 1 := norm_Y_pow_7_lt_one Y q hYq hq
    have hz_ne : (-(Y ^ (5 : ℤ)) : ℂ) ≠ 0 := by
      norm_num only [zpow_ofNat]
      exact neg_ne_zero.mpr (pow_ne_zero 5 hYne)
    rw [theta7_minus_eq_plus_tsum]
    rw [← theta7_plus_tsum_eq_jacobiSeries (c := 5) (by right; right; rfl) q Y hYne hYq]
    rw [← PartI.Ch02.jacobiTripleProduct (Y ^ 7) (-(Y ^ (5 : ℤ))) hY7_norm hz_ne]
    exact (jacobiInfiniteProduct_C5_eq_mod7_triple q Y hYne hYq hq).symm

/-! ## Product coefficient Taylor bridge -/

lemma partial_prod_mod7TripleFactorPS_coeff_stable
    (a b : ℕ) (R : Type*) [CommRing R] (k N : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hN : k ≤ N) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range (N + 1), mod7TripleFactorPS a b R n) =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N, mod7TripleFactorPS a b R n) := by
  rw [Finset.prod_range_succ]
  change PowerSeries.coeff k
      ((∏ n ∈ Finset.range N, mod7TripleFactorPS a b R n) *
        (apFactorPS R a 7 N * apFactorPS R b 7 N * apFactorPS R 7 7 N)) =
    PowerSeries.coeff k (∏ n ∈ Finset.range N, mod7TripleFactorPS a b R n)
  let P : R⟦X⟧ := ∏ n ∈ Finset.range N, mod7TripleFactorPS a b R n
  calc
    PowerSeries.coeff k
        (P * (apFactorPS R a 7 N * apFactorPS R b 7 N * apFactorPS R 7 7 N))
        = PowerSeries.coeff k
          (((P * apFactorPS R a 7 N) * apFactorPS R b 7 N) *
            apFactorPS R 7 7 N) := by
          ring_nf
    _ = PowerSeries.coeff k ((P * apFactorPS R a 7 N) * apFactorPS R b 7 N) :=
          coeff_mul_apFactorPS_eq_of_lt R
            ((P * apFactorPS R a 7 N) * apFactorPS R b 7 N) k 7 7 N (by omega)
    _ = PowerSeries.coeff k (P * apFactorPS R a 7 N) :=
          coeff_mul_apFactorPS_eq_of_lt R (P * apFactorPS R a 7 N) k b 7 N
            (by omega)
    _ = PowerSeries.coeff k P :=
          coeff_mul_apFactorPS_eq_of_lt R P k a 7 N (by omega)

theorem partial_prod_mod7TripleFactorPS_coeff_eq
    (a b : ℕ) (R : Type*) [CommRing R] (k N M : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hkN : k ≤ N) (hNM : N ≤ M) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range M, mod7TripleFactorPS a b R n) =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N, mod7TripleFactorPS a b R n) := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M _ ih =>
      rw [partial_prod_mod7TripleFactorPS_coeff_stable a b R k M ha hb (by omega), ih]

theorem coeff_mod7ProductPS_eq_coeff_partial
    (a b : ℕ) (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] (k : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (mod7ProductPS a b R).coeff k =
      (∏ n ∈ Finset.range (k + 1), mod7TripleFactorPS a b R n).coeff k := by
  have h_tendsto : Tendsto
      (fun N : ℕ => ∏ n ∈ Finset.range N, mod7TripleFactorPS a b R n) atTop
      (𝓝 (mod7ProductPS a b R)) :=
    (hasProd_mod7TripleFactorPS a b R).tendsto_prod_nat
  have h_coeff_tendsto : Tendsto
      (fun N : ℕ => PowerSeries.coeff k
        (∏ n ∈ Finset.range N, mod7TripleFactorPS a b R n)) atTop
      (𝓝 (PowerSeries.coeff k (mod7ProductPS a b R))) :=
    ((PowerSeries.WithPiTopology.continuous_coeff R k).tendsto _).comp h_tendsto
  have h_const_tendsto : Tendsto
      (fun N : ℕ => PowerSeries.coeff k
        (∏ n ∈ Finset.range N, mod7TripleFactorPS a b R n)) atTop
      (𝓝 (PowerSeries.coeff k
        (∏ n ∈ Finset.range (k + 1), mod7TripleFactorPS a b R n))) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨k + 1, fun N hN =>
      (partial_prod_mod7TripleFactorPS_coeff_eq a b R k (k + 1) N ha hb
        (by omega) hN).symm⟩
  exact tendsto_nhds_unique h_coeff_tendsto h_const_tendsto

theorem tendsto_mod7ProductAnalytic_partial
    (a b : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto
      (fun N : ℕ => ∏ n ∈ Finset.range N,
        rrMod7Factor q 7 n * rrMod7Factor q b n * rrMod7Factor q a n)
      atTop (𝓝 (mod7ProductAnalytic a b q)) := by
  have h7 := (multipliable_rrMod7Factor q hq 7).tendsto_prod_tprod_nat
  have hb := (multipliable_rrMod7Factor q hq b).tendsto_prod_tprod_nat
  have ha := (multipliable_rrMod7Factor q hq a).tendsto_prod_tprod_nat
  simpa [mod7ProductAnalytic, Finset.prod_mul_distrib, mul_assoc]
    using ((h7.mul hb).mul ha)

lemma norm_coeff_mul_mod7TripleFactorPS_complex_le
    (a b : ℕ) (P : ℂ⟦X⟧) (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ k : ℕ, ‖P.coeff k‖ ≤ B) (k N : ℕ) :
    ‖(P * mod7TripleFactorPS a b ℂ N).coeff k‖ ≤ 8 * B := by
  have hP1 : ∀ k : ℕ, ‖(P * apFactorPS ℂ a 7 N).coeff k‖ ≤ 2 * B :=
    fun k => norm_coeff_mul_apFactorPS_complex_le P B hB hP k a 7 N
  have hP2 : ∀ k : ℕ,
      ‖((P * apFactorPS ℂ a 7 N) * apFactorPS ℂ b 7 N).coeff k‖ ≤
        2 * (2 * B) :=
    fun k => norm_coeff_mul_apFactorPS_complex_le
      (P * apFactorPS ℂ a 7 N) (2 * B) (by nlinarith) hP1 k b 7 N
  calc
    ‖(P * mod7TripleFactorPS a b ℂ N).coeff k‖ =
        ‖(((P * apFactorPS ℂ a 7 N) * apFactorPS ℂ b 7 N) *
          apFactorPS ℂ 7 7 N).coeff k‖ := by
        congr 1
        rw [mod7TripleFactorPS]
        ring_nf
    _ ≤ 2 * (2 * (2 * B)) :=
        norm_coeff_mul_apFactorPS_complex_le
          ((P * apFactorPS ℂ a 7 N) * apFactorPS ℂ b 7 N)
          (2 * (2 * B)) (by nlinarith) hP2 k 7 7 N
    _ = 8 * B := by ring

lemma norm_coeff_partial_mod7TripleFactorPS_complex_le
    (a b N k : ℕ) :
    ‖(∏ n ∈ Finset.range N, mod7TripleFactorPS a b ℂ n).coeff k‖ ≤
      (8 : ℝ) ^ N := by
  revert k
  induction N with
  | zero =>
      intro k
      by_cases hk : k = 0 <;> simp [hk]
  | succ N ih =>
      intro k
      rw [Finset.prod_range_succ]
      calc
        ‖((∏ n ∈ Finset.range N, mod7TripleFactorPS a b ℂ n) *
            mod7TripleFactorPS a b ℂ N).coeff k‖
            ≤ 8 * (8 : ℝ) ^ N :=
          norm_coeff_mul_mod7TripleFactorPS_complex_le a b
            (∏ n ∈ Finset.range N, mod7TripleFactorPS a b ℂ n)
            ((8 : ℝ) ^ N) (by positivity) (fun j => ih j) k N
        _ = (8 : ℝ) ^ (N + 1) := by
          rw [pow_succ]
          ring

lemma norm_coeff_mod7ProductPS_complex_le
    (a b k : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ‖(mod7ProductPS a b ℂ).coeff k‖ ≤ (8 : ℝ) ^ (k + 1) := by
  rw [coeff_mod7ProductPS_eq_coeff_partial a b ℂ k ha hb]
  exact norm_coeff_partial_mod7TripleFactorPS_complex_le a b (k + 1) k

lemma norm_coeff_partial_mod7TripleFactorPS_complex_le_uniform
    (a b N k : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ‖(∏ n ∈ Finset.range N, mod7TripleFactorPS a b ℂ n).coeff k‖ ≤
      (8 : ℝ) ^ (k + 1) := by
  by_cases hN : N ≤ k + 1
  · exact le_trans (norm_coeff_partial_mod7TripleFactorPS_complex_le a b N k)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 8) hN)
  · have hle : k + 1 ≤ N := Nat.le_of_not_ge hN
    rw [partial_prod_mod7TripleFactorPS_coeff_eq a b ℂ k (k + 1) N ha hb
      (by omega) hle]
    exact norm_coeff_partial_mod7TripleFactorPS_complex_le a b (k + 1) k

lemma hasSum_coeff_mul_mod7TripleFactorPS_complex
    (a b : ℕ) (P : ℂ⟦X⟧) (q p : ℂ) (N : ℕ)
    (hP : HasSum (fun k : ℕ => P.coeff k * q ^ k) p) :
    HasSum (fun k : ℕ => (P * mod7TripleFactorPS a b ℂ N).coeff k * q ^ k)
      (p * (rrMod7Factor q 7 N * rrMod7Factor q b N * rrMod7Factor q a N)) := by
  have h1 := hasSum_coeff_mul_apFactorPS_complex P q p a 7 N hP
  have h2 := hasSum_coeff_mul_apFactorPS_complex (P * apFactorPS ℂ a 7 N) q
    (p * (1 - q ^ (a + 7 * N))) b 7 N h1
  have h3 := hasSum_coeff_mul_apFactorPS_complex
    ((P * apFactorPS ℂ a 7 N) * apFactorPS ℂ b 7 N) q
    ((p * (1 - q ^ (a + 7 * N))) * (1 - q ^ (b + 7 * N))) 7 7 N h2
  convert h3 using 1
  · ext k
    rw [mod7TripleFactorPS]
    ring_nf
  · simp [rrMod7Factor]
    ring

lemma hasSum_coeff_partial_mod7TripleFactorPS_complex
    (a b : ℕ) (q : ℂ) (N : ℕ) :
    HasSum (fun k : ℕ =>
        (∏ n ∈ Finset.range N, mod7TripleFactorPS a b ℂ n).coeff k * q ^ k)
      (∏ n ∈ Finset.range N,
        rrMod7Factor q 7 n * rrMod7Factor q b n * rrMod7Factor q a n) := by
  induction N with
  | zero =>
      simpa using (hasSum_single (0 : ℕ)
        (f := fun k : ℕ => ((1 : ℂ⟦X⟧).coeff k) * q ^ k)
        (by
          intro j hj
          simp [PowerSeries.coeff_one, hj]))
  | succ N ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      exact hasSum_coeff_mul_mod7TripleFactorPS_complex a b
        (∏ n ∈ Finset.range N, mod7TripleFactorPS a b ℂ n) q
        (∏ n ∈ Finset.range N,
          rrMod7Factor q 7 n * rrMod7Factor q b n * rrMod7Factor q a n) N ih

lemma summable_mod7Product_bound_of_norm_lt_one_sixteenth
    {q : ℂ} (hq : ‖q‖ < (1 / 16 : ℝ)) :
    Summable fun k : ℕ => (8 : ℝ) ^ (k + 1) * ‖q‖ ^ k :=
  summable_pentagonalProduct_bound_of_norm_lt_one_sixteenth hq

theorem hasSum_mod7ProductPS_coeff_mul_pow_of_norm_lt_one_sixteenth
    (a b : ℕ) (q : ℂ) (hq : ‖q‖ < (1 / 16 : ℝ)) (ha : 0 < a) (hb : 0 < b) :
    HasSum (fun k : ℕ => (mod7ProductPS a b ℂ).coeff k * q ^ k)
      (mod7ProductAnalytic a b q) := by
  let f : ℕ → ℕ → ℂ := fun N k =>
    (∏ n ∈ Finset.range N, mod7TripleFactorPS a b ℂ n).coeff k * q ^ k
  let g : ℕ → ℂ := fun k => (mod7ProductPS a b ℂ).coeff k * q ^ k
  let bound : ℕ → ℝ := fun k => (8 : ℝ) ^ (k + 1) * ‖q‖ ^ k
  have hbound_sum : Summable bound :=
    summable_mod7Product_bound_of_norm_lt_one_sixteenth hq
  have hab : ∀ k : ℕ, Tendsto (fun N : ℕ => f N k) atTop (𝓝 (g k)) := by
    intro k
    apply tendsto_nhds_of_eventually_eq
    refine Filter.eventually_atTop.mpr ⟨k + 1, ?_⟩
    intro N hN
    dsimp [f, g]
    rw [partial_prod_mod7TripleFactorPS_coeff_eq a b ℂ k (k + 1) N ha hb
      (by omega) hN]
    rw [← coeff_mod7ProductPS_eq_coeff_partial a b ℂ k ha hb]
  have h_bound : ∀ᶠ N in atTop, ∀ k : ℕ, ‖f N k‖ ≤ bound k :=
    Filter.Eventually.of_forall fun N => by
      intro k
      dsimp [f, bound]
      rw [norm_mul, norm_pow]
      gcongr
      exact norm_coeff_partial_mod7TripleFactorPS_complex_le_uniform a b N k ha hb
  have h_tsum : Tendsto (fun N : ℕ => ∑' k : ℕ, f N k) atTop
      (𝓝 (∑' k : ℕ, g k)) :=
    tendsto_tsum_of_dominated_convergence hbound_sum hab h_bound
  have h_finite : ∀ N : ℕ, (∑' k : ℕ, f N k) =
      ∏ n ∈ Finset.range N,
        rrMod7Factor q 7 n * rrMod7Factor q b n * rrMod7Factor q a n := by
    intro N
    exact (hasSum_coeff_partial_mod7TripleFactorPS_complex a b q N).tsum_eq
  have hq_unit : ‖q‖ < 1 := by nlinarith [hq]
  have h_partial := tendsto_mod7ProductAnalytic_partial a b q hq_unit
  have h_tsum_analytic : Tendsto (fun N : ℕ => ∑' k : ℕ, f N k) atTop
      (𝓝 (mod7ProductAnalytic a b q)) :=
    Filter.Tendsto.congr (fun N => (h_finite N).symm) h_partial
  have h_eq : (∑' k : ℕ, g k) = mod7ProductAnalytic a b q :=
    tendsto_nhds_unique h_tsum h_tsum_analytic
  have hg_summable : Summable g := by
    refine hbound_sum.of_norm_bounded ?_
    intro k
    dsimp [g, bound]
    rw [norm_mul, norm_pow]
    gcongr
    exact norm_coeff_mod7ProductPS_complex_le a b k ha hb
  simpa [g, h_eq] using hg_summable.hasSum

noncomputable def mod7ProductCoeffFMLS (a b : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (mod7ProductPS a b ℂ).coeff n)

theorem one_sixteenth_le_mod7ProductCoeffFMLS_radius
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((1 / 16 : NNReal) : ENNReal) ≤ (mod7ProductCoeffFMLS a b).radius := by
  refine FormalMultilinearSeries.le_radius_of_bound
    (mod7ProductCoeffFMLS a b) 8 (r := (1 / 16 : NNReal)) ?_
  intro n
  rw [mod7ProductCoeffFMLS, FormalMultilinearSeries.ofScalars_norm]
  calc
    ‖(mod7ProductPS a b ℂ).coeff n‖ * ((1 / 16 : NNReal) : ℝ) ^ n
        ≤ (8 : ℝ) ^ (n + 1) * ((1 / 16 : NNReal) : ℝ) ^ n := by
        gcongr
        exact norm_coeff_mod7ProductPS_complex_le a b n ha hb
    _ = 8 * ((1 / 2 : ℝ) ^ n) := by
        rw [pow_succ]
        rw [show (8 : ℝ) ^ n * 8 * ((1 / 16 : NNReal) : ℝ) ^ n =
          8 * (((8 : ℝ) * ((1 / 16 : NNReal) : ℝ)) ^ n) by
            rw [mul_pow]
            ring]
        norm_num
    _ ≤ 8 := by
        have hpow : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith

theorem hasFPowerSeriesOnBall_mod7ProductAnalytic_productCoeff_small
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    HasFPowerSeriesOnBall (mod7ProductAnalytic a b) (mod7ProductCoeffFMLS a b) 0
      ((1 / 16 : NNReal) : ENNReal) := by
  refine ⟨one_sixteenth_le_mod7ProductCoeffFMLS_radius a b ha hb, by norm_num, ?_⟩
  intro y hy
  rw [zero_add]
  have hy_norm : ‖y‖ < (1 / 16 : ℝ) := by
    have h_radius : (((1 / 16 : NNReal) : ENNReal) =
        ENNReal.ofReal (1 / 16 : ℝ)) := by
      rw [ENNReal.coe_nnreal_eq]
      congr
    have h_ball : y ∈ Metric.ball (0 : ℂ) (1 / 16 : ℝ) := by
      rw [h_radius, Metric.emetric_ball] at hy
      exact hy
    have hdist : dist y (0 : ℂ) < (1 / 16 : ℝ) := Metric.mem_ball.mp h_ball
    rwa [dist_zero_right] at hdist
  have h := hasSum_mod7ProductPS_coeff_mul_pow_of_norm_lt_one_sixteenth
    a b y hy_norm ha hb
  convert h using 1
  funext n
  rw [mod7ProductCoeffFMLS, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]

theorem hasFPowerSeriesOnBall_mod7ProductAnalytic_theta
    {a b : ℕ} {c : ℤ} (hc : ThetaCValid c)
    (hanalytic : ∀ q : ℂ, ‖q‖ < 1 → mod7ProductAnalytic a b q = theta7Analytic c q) :
    HasFPowerSeriesOnBall (mod7ProductAnalytic a b) (theta7SeriesFMLS c) 0 1 := by
  refine (hasFPowerSeriesOnBall_theta7Analytic hc).congr ?_
  intro q hq
  exact (hanalytic q (norm_lt_one_of_mem_emetric_unit_ball hq)).symm

theorem mod7ProductCoeffFMLS_eq_theta7SeriesFMLS
    {a b : ℕ} {c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : ThetaCValid c)
    (hanalytic : ∀ q : ℂ, ‖q‖ < 1 → mod7ProductAnalytic a b q = theta7Analytic c q) :
    mod7ProductCoeffFMLS a b = theta7SeriesFMLS c := by
  have h_prod : HasFPowerSeriesAt (mod7ProductAnalytic a b)
      (mod7ProductCoeffFMLS a b) 0 :=
    ⟨((1 / 16 : NNReal) : ENNReal),
      hasFPowerSeriesOnBall_mod7ProductAnalytic_productCoeff_small a b ha hb⟩
  have h_series : HasFPowerSeriesAt (mod7ProductAnalytic a b)
      (theta7SeriesFMLS c) 0 :=
    ⟨1, hasFPowerSeriesOnBall_mod7ProductAnalytic_theta hc hanalytic⟩
  exact h_prod.eq_formalMultilinearSeries h_series

theorem mod7ProductPS_eq_theta7SeriesPS_complex_of_analytic
    {a b : ℕ} {c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : ThetaCValid c)
    (hanalytic : ∀ q : ℂ, ‖q‖ < 1 → mod7ProductAnalytic a b q = theta7Analytic c q) :
    mod7ProductPS a b ℂ = theta7SeriesPS c ℂ := by
  have h_unique :=
    mod7ProductCoeffFMLS_eq_theta7SeriesFMLS ha hb hc hanalytic
  ext n
  have h_coeff : (mod7ProductPS a b ℂ).coeff n = theta7Coeff c ℂ n := by
    have h_prod_coeff : (mod7ProductCoeffFMLS a b).coeff n =
        (mod7ProductPS a b ℂ).coeff n := by
      simp [mod7ProductCoeffFMLS]
    have h_series_coeff : (theta7SeriesFMLS c).coeff n = theta7Coeff c ℂ n := by
      simp [theta7SeriesFMLS]
    rw [← h_prod_coeff, ← h_series_coeff, h_unique]
  rw [h_coeff, coeff_theta7SeriesPS]

/-- `(q^3,q^4,q^7;q^7)_∞ = ∑ (-1)^k q^((7k²-k)/2)` over `ℂ⟦X⟧`. -/
theorem mod7Product034PS_eq_theta7SeriesPS_complex :
    mod7Product034PS ℂ = theta7SeriesPS 1 ℂ :=
  mod7ProductPS_eq_theta7SeriesPS_complex_of_analytic
    (a := 3) (b := 4) (c := 1) (by norm_num) (by norm_num) (by left; rfl)
    mod7ProductAnalytic_eq_theta7Analytic_c1

/-- `(q^2,q^5,q^7;q^7)_∞ = ∑ (-1)^k q^((7k²-3k)/2)` over `ℂ⟦X⟧`. -/
theorem mod7Product025PS_eq_theta7SeriesPS_complex :
    mod7Product025PS ℂ = theta7SeriesPS 3 ℂ :=
  mod7ProductPS_eq_theta7SeriesPS_complex_of_analytic
    (a := 2) (b := 5) (c := 3) (by norm_num) (by norm_num) (by right; left; rfl)
    mod7ProductAnalytic_eq_theta7Analytic_c3

/-- `(q,q^6,q^7;q^7)_∞ = ∑ (-1)^k q^((7k²-5k)/2)` over `ℂ⟦X⟧`. -/
theorem mod7Product016PS_eq_theta7SeriesPS_complex :
    mod7Product016PS ℂ = theta7SeriesPS 5 ℂ :=
  mod7ProductPS_eq_theta7SeriesPS_complex_of_analytic
    (a := 1) (b := 6) (c := 5) (by norm_num) (by norm_num) (by right; right; rfl)
    mod7ProductAnalytic_eq_theta7Analytic_c5

/-! ## Rational forms -/

private theorem map_mod7TripleFactorPS_int
    (a b : ℕ) (R : Type*) [CommRing R] (n : ℕ) :
    PowerSeries.map (Int.castRingHom R) (mod7TripleFactorPS a b ℤ n) =
      mod7TripleFactorPS a b R n := by
  simp [mod7TripleFactorPS, apFactorPS, PowerSeries.map_X]

private theorem map_mod7ProductPS_int
    (a b : ℕ) (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] (ha : 0 < a) (hb : 0 < b) :
    PowerSeries.map (Int.castRingHom R) (mod7ProductPS a b ℤ) =
      mod7ProductPS a b R := by
  ext k
  rw [PowerSeries.coeff_map, coeff_mod7ProductPS_eq_coeff_partial a b ℤ k ha hb,
    coeff_mod7ProductPS_eq_coeff_partial a b R k ha hb]
  rw [← PowerSeries.coeff_map]
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro n _hn
  exact map_mod7TripleFactorPS_int a b R n

private theorem map_theta7SeriesPS_int
    (c : ℤ) (R : Type*) [CommRing R] :
    PowerSeries.map (Int.castRingHom R) (theta7SeriesPS c ℤ) =
      theta7SeriesPS c R := by
  ext n
  rw [PowerSeries.coeff_map, coeff_theta7SeriesPS, coeff_theta7SeriesPS]
  unfold theta7Coeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hk : theta7Exp c k = n <;> simp [hk, negOnePowInt]

theorem mod7ProductPS_eq_theta7SeriesPS_int_of_complex
    {a b : ℕ} {c : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hcomplex : mod7ProductPS a b ℂ = theta7SeriesPS c ℂ) :
    mod7ProductPS a b ℤ = theta7SeriesPS c ℤ := by
  ext n
  have h := congrArg (fun φ : ℂ⟦X⟧ => φ.coeff n) (by
    calc
      PowerSeries.map (Int.castRingHom ℂ) (mod7ProductPS a b ℤ)
          = mod7ProductPS a b ℂ := map_mod7ProductPS_int a b ℂ ha hb
      _ = theta7SeriesPS c ℂ := hcomplex
      _ = PowerSeries.map (Int.castRingHom ℂ) (theta7SeriesPS c ℤ) :=
          (map_theta7SeriesPS_int c ℂ).symm)
  exact Int.cast_injective (by simpa [PowerSeries.coeff_map] using h)

theorem mod7ProductPS_eq_theta7SeriesPS_rat_of_complex
    {a b : ℕ} {c : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hcomplex : mod7ProductPS a b ℂ = theta7SeriesPS c ℂ) :
    mod7ProductPS a b ℚ = theta7SeriesPS c ℚ := by
  have hint := mod7ProductPS_eq_theta7SeriesPS_int_of_complex ha hb hcomplex
  calc
    mod7ProductPS a b ℚ
        = PowerSeries.map (Int.castRingHom ℚ) (mod7ProductPS a b ℤ) :=
          (map_mod7ProductPS_int a b ℚ ha hb).symm
    _ = PowerSeries.map (Int.castRingHom ℚ) (theta7SeriesPS c ℤ) := by rw [hint]
    _ = theta7SeriesPS c ℚ := map_theta7SeriesPS_int c ℚ

theorem mod7Product034PS_eq_theta7SeriesPS_rat :
    mod7Product034PS ℚ = theta7SeriesPS 1 ℚ :=
  mod7ProductPS_eq_theta7SeriesPS_rat_of_complex
    (a := 3) (b := 4) (c := 1) (by norm_num) (by norm_num)
    mod7Product034PS_eq_theta7SeriesPS_complex

theorem mod7Product025PS_eq_theta7SeriesPS_rat :
    mod7Product025PS ℚ = theta7SeriesPS 3 ℚ :=
  mod7ProductPS_eq_theta7SeriesPS_rat_of_complex
    (a := 2) (b := 5) (c := 3) (by norm_num) (by norm_num)
    mod7Product025PS_eq_theta7SeriesPS_complex

theorem mod7Product016PS_eq_theta7SeriesPS_rat :
    mod7Product016PS ℚ = theta7SeriesPS 5 ℚ :=
  mod7ProductPS_eq_theta7SeriesPS_rat_of_complex
    (a := 1) (b := 6) (c := 5) (by norm_num) (by norm_num)
    mod7Product016PS_eq_theta7SeriesPS_complex

/-! ## Hirschhorn §3.7.2: the mod-49 H/J/K eta products -/

/-- Hirschhorn's `H(q^7) = (q^21,q^28,q^49;q^49)_∞`. -/
noncomputable def asd7HProductPS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 21 49 * qPochAPPS R 28 49 * qPochAPPS R 49 49

/-- Hirschhorn's `J(q^7) = (q^14,q^35,q^49;q^49)_∞`. -/
noncomputable def asd7JProductPS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 14 49 * qPochAPPS R 35 49 * qPochAPPS R 49 49

/-- Hirschhorn's `K(q^7) = (q^7,q^42,q^49;q^49)_∞`. -/
noncomputable def asd7KProductPS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 7 49 * qPochAPPS R 42 49 * qPochAPPS R 49 49

/-- Theta side of `H(q^7)`: `∑ (-1)^k X^((49k²-7k)/2)`. -/
noncomputable def asd7HSeriesPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 7 (by decide) (theta7SeriesPS 1 R)

/-- Theta side of `J(q^7)`: `∑ (-1)^k X^((49k²-21k)/2)`. -/
noncomputable def asd7JSeriesPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 7 (by decide) (theta7SeriesPS 3 R)

/-- Theta side of `K(q^7)`: `∑ (-1)^k X^((49k²-35k)/2)`. -/
noncomputable def asd7KSeriesPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 7 (by decide) (theta7SeriesPS 5 R)

@[simp] theorem coeff_asd7HSeriesPS (R : Type*) [CommRing R] (n : ℕ) :
    (asd7HSeriesPS R).coeff n =
      if 7 ∣ n then theta7Coeff 1 R (n / 7) else 0 := by
  rw [asd7HSeriesPS, PowerSeries.coeff_expand]
  by_cases hdiv : 7 ∣ n <;> simp [hdiv]

@[simp] theorem coeff_asd7JSeriesPS (R : Type*) [CommRing R] (n : ℕ) :
    (asd7JSeriesPS R).coeff n =
      if 7 ∣ n then theta7Coeff 3 R (n / 7) else 0 := by
  rw [asd7JSeriesPS, PowerSeries.coeff_expand]
  by_cases hdiv : 7 ∣ n <;> simp [hdiv]

@[simp] theorem coeff_asd7KSeriesPS (R : Type*) [CommRing R] (n : ℕ) :
    (asd7KSeriesPS R).coeff n =
      if 7 ∣ n then theta7Coeff 5 R (n / 7) else 0 := by
  rw [asd7KSeriesPS, PowerSeries.coeff_expand]
  by_cases hdiv : 7 ∣ n <;> simp [hdiv]

theorem expand_mod7Product034PS
    (R : Type*) [CommRing R] [TopologicalSpace R] [T2Space R] :
    PowerSeries.expand 7 (by decide) (mod7Product034PS R) =
      asd7HProductPS R := by
  unfold mod7Product034PS mod7ProductPS asd7HProductPS
  rw [map_mul, map_mul]
  rw [expand_qPochAPPS R 7 3 7 (by decide) (by norm_num),
    expand_qPochAPPS R 7 4 7 (by decide) (by norm_num),
    expand_qPochAPPS R 7 7 7 (by decide) (by norm_num)]

theorem expand_mod7Product025PS
    (R : Type*) [CommRing R] [TopologicalSpace R] [T2Space R] :
    PowerSeries.expand 7 (by decide) (mod7Product025PS R) =
      asd7JProductPS R := by
  unfold mod7Product025PS mod7ProductPS asd7JProductPS
  rw [map_mul, map_mul]
  rw [expand_qPochAPPS R 7 2 7 (by decide) (by norm_num),
    expand_qPochAPPS R 7 5 7 (by decide) (by norm_num),
    expand_qPochAPPS R 7 7 7 (by decide) (by norm_num)]

theorem expand_mod7Product016PS
    (R : Type*) [CommRing R] [TopologicalSpace R] [T2Space R] :
    PowerSeries.expand 7 (by decide) (mod7Product016PS R) =
      asd7KProductPS R := by
  unfold mod7Product016PS mod7ProductPS asd7KProductPS
  rw [map_mul, map_mul]
  rw [expand_qPochAPPS R 7 1 7 (by decide) (by norm_num),
    expand_qPochAPPS R 7 6 7 (by decide) (by norm_num),
    expand_qPochAPPS R 7 7 7 (by decide) (by norm_num)]

theorem asd7HProductPS_eq_asd7HSeriesPS_complex :
    asd7HProductPS ℂ = asd7HSeriesPS ℂ := by
  rw [← expand_mod7Product034PS ℂ]
  unfold asd7HSeriesPS
  rw [mod7Product034PS_eq_theta7SeriesPS_complex]

theorem asd7JProductPS_eq_asd7JSeriesPS_complex :
    asd7JProductPS ℂ = asd7JSeriesPS ℂ := by
  rw [← expand_mod7Product025PS ℂ]
  unfold asd7JSeriesPS
  rw [mod7Product025PS_eq_theta7SeriesPS_complex]

theorem asd7KProductPS_eq_asd7KSeriesPS_complex :
    asd7KProductPS ℂ = asd7KSeriesPS ℂ := by
  rw [← expand_mod7Product016PS ℂ]
  unfold asd7KSeriesPS
  rw [mod7Product016PS_eq_theta7SeriesPS_complex]

theorem asd7HProductPS_eq_asd7HSeriesPS_rat :
    asd7HProductPS ℚ = asd7HSeriesPS ℚ := by
  rw [← expand_mod7Product034PS ℚ]
  unfold asd7HSeriesPS
  rw [mod7Product034PS_eq_theta7SeriesPS_rat]

theorem asd7JProductPS_eq_asd7JSeriesPS_rat :
    asd7JProductPS ℚ = asd7JSeriesPS ℚ := by
  rw [← expand_mod7Product025PS ℚ]
  unfold asd7JSeriesPS
  rw [mod7Product025PS_eq_theta7SeriesPS_rat]

theorem asd7KProductPS_eq_asd7KSeriesPS_rat :
    asd7KProductPS ℚ = asd7KSeriesPS ℚ := by
  rw [← expand_mod7Product016PS ℚ]
  unfold asd7KSeriesPS
  rw [mod7Product016PS_eq_theta7SeriesPS_rat]

end JTPFormalPSMod7
end Pending
end QseriesFormalization
