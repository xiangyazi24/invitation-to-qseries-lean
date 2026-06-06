import QseriesFormalization.Pending.RR_FinalAssembly

/-!
# Chan Theorem 11.1

This file closes the formal-power-series version of Chan's Theorem 11.1:
the Rogers-Ramanujan continued-fraction limit agrees with the product-form
Rogers-Ramanujan ratio.
-/

namespace QseriesFormalization
namespace Pending
namespace ChanTheorem111

open PowerSeries
open QseriesFormalization.Pending.RogersRamanujanFormalPS
open QseriesFormalization.Pending.Ch11RRCFConvergent
open QseriesFormalization.Pending.Ch13RRCF
open QseriesFormalization.Pending.RRFinalAssembly

/-- The shifted Rogers-Ramanujan summand
`X^(n^2 + m n)/(X;X)_n`.  Thus `m = 0` is the `G` summand and
`m = 1` is the `H` summand. -/
noncomputable def rrJShiftTermPS (m n : ℕ) : ℚ⟦X⟧ :=
  X ^ (n * n + m * n) * (qPochPS n)⁻¹

/-- The shifted Rogers-Ramanujan series
`J_m = Σ_n X^(n^2 + m n)/(X;X)_n`, defined coefficientwise by the
usual X-adic finite cutoff. -/
noncomputable def rrJShiftPS (m : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun k =>
    ∑ n ∈ Finset.range (k + 1), (rrJShiftTermPS m n).coeff k

theorem rrJShiftTermPS_coeff_eq_zero (m n k : ℕ)
    (hk : k < n * n + m * n) :
    (rrJShiftTermPS m n).coeff k = 0 := by
  unfold rrJShiftTermPS
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  rcases ij with ⟨i, j⟩
  rw [Finset.mem_antidiagonal] at hij
  have hi : i < n * n + m * n := by omega
  rw [PowerSeries.coeff_X_pow, if_neg (by omega)]
  simp

theorem rrJShiftPS_zero :
    rrJShiftPS 0 = rrGPS := by
  ext k
  unfold rrJShiftPS rrGPS rrJShiftTermPS rrGTermPS
  simp only [PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  ring

theorem rrJShiftPS_one :
    rrJShiftPS 1 = rrHPS := by
  ext k
  unfold rrJShiftPS rrHPS rrJShiftTermPS rrHTermPS
  simp only [PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  ring

private theorem constantCoeff_one_sub_X_pow_succ_ne_zero (n : ℕ) :
    constantCoeff (1 - X ^ (n + 1) : ℚ⟦X⟧) ≠ 0 := by
  rw [map_sub, map_one, map_pow, constantCoeff_X, zero_pow (Nat.succ_ne_zero n),
      sub_zero]
  norm_num

private theorem qPochPS_succ (n : ℕ) :
    qPochPS (n + 1) = qPochPS n * (1 - X ^ (n + 1) : ℚ⟦X⟧) := by
  unfold qPochPS
  rw [qPochhammer_succ]

/-- Termwise shifted RR functional equation, after dropping the zero `n = 0`
term from `J_m - J_{m+1}`. -/
theorem rrJShiftTermPS_succ_sub (m n : ℕ) :
    rrJShiftTermPS m (n + 1) - rrJShiftTermPS (m + 1) (n + 1) =
      X ^ (m + 1) * rrJShiftTermPS (m + 2) n := by
  unfold rrJShiftTermPS
  rw [qPochPS_succ n, PowerSeries.mul_inv_rev]
  have hcancel :
      (1 - X ^ (n + 1) : ℚ⟦X⟧) * (1 - X ^ (n + 1) : ℚ⟦X⟧)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (constantCoeff_one_sub_X_pow_succ_ne_zero n)
  have hexp :
      (n + 1) * (n + 1) + (m + 1) * (n + 1) =
        ((n + 1) * (n + 1) + m * (n + 1)) + (n + 1) := by
    ring
  calc
    X ^ ((n + 1) * (n + 1) + m * (n + 1)) *
          ((1 - X ^ (n + 1) : ℚ⟦X⟧)⁻¹ * (qPochPS n)⁻¹) -
        X ^ ((n + 1) * (n + 1) + (m + 1) * (n + 1)) *
          ((1 - X ^ (n + 1) : ℚ⟦X⟧)⁻¹ * (qPochPS n)⁻¹)
        =
        X ^ ((n + 1) * (n + 1) + m * (n + 1)) *
          ((1 - X ^ (n + 1) : ℚ⟦X⟧) *
            (1 - X ^ (n + 1) : ℚ⟦X⟧)⁻¹) * (qPochPS n)⁻¹ := by
          rw [hexp, pow_add]
          ring_nf
    _ = X ^ (m + 1) * (X ^ (n * n + (m + 2) * n) * (qPochPS n)⁻¹) := by
          rw [hcancel]
          rw [show (n + 1) * (n + 1) + m * (n + 1) =
              (m + 1) + (n * n + (m + 2) * n) by ring]
          rw [pow_add]
          ring

/-- Finite cutoff of the shifted RR series. -/
noncomputable def rrJShiftPartialPS (m N : ℕ) : ℚ⟦X⟧ :=
  ∑ n ∈ Finset.range (N + 1), rrJShiftTermPS m n

@[simp] theorem rrJShiftTermPS_zero (m : ℕ) :
    rrJShiftTermPS m 0 = 1 := by
  unfold rrJShiftTermPS qPochPS
  rw [show 0 * 0 + m * 0 = 0 by ring, pow_zero, qPochhammer_zero, inv_one, mul_one]

theorem rrJShiftPartialPS_succ (m N : ℕ) :
    rrJShiftPartialPS m (N + 1) =
      rrJShiftPartialPS m N + rrJShiftTermPS m (N + 1) := by
  unfold rrJShiftPartialPS
  rw [Finset.sum_range_succ]

theorem rrJShiftPartialPS_succ_sub (m N : ℕ) :
    rrJShiftPartialPS m (N + 1) - rrJShiftPartialPS (m + 1) (N + 1) =
      X ^ (m + 1) * rrJShiftPartialPS (m + 2) N := by
  induction N with
  | zero =>
      rw [rrJShiftPartialPS_succ, rrJShiftPartialPS_succ]
      unfold rrJShiftPartialPS
      rw [Finset.sum_range_one, Finset.sum_range_one]
      rw [rrJShiftTermPS_zero, rrJShiftTermPS_zero]
      rw [show (1 : ℚ⟦X⟧) + rrJShiftTermPS m (0 + 1) -
            (1 + rrJShiftTermPS (m + 1) (0 + 1)) =
            rrJShiftTermPS m (0 + 1) - rrJShiftTermPS (m + 1) (0 + 1) by ring]
      rw [rrJShiftTermPS_succ_sub]
      rw [Finset.sum_range_one]
  | succ N ih =>
      rw [rrJShiftPartialPS_succ m (N + 1),
          rrJShiftPartialPS_succ (m + 1) (N + 1),
          rrJShiftPartialPS_succ (m + 2) N]
      rw [show rrJShiftPartialPS m (N + 1) + rrJShiftTermPS m (N + 1 + 1) -
            (rrJShiftPartialPS (m + 1) (N + 1) +
              rrJShiftTermPS (m + 1) (N + 1 + 1)) =
            (rrJShiftPartialPS m (N + 1) - rrJShiftPartialPS (m + 1) (N + 1)) +
              (rrJShiftTermPS m ((N + 1) + 1) -
                rrJShiftTermPS (m + 1) ((N + 1) + 1)) by ring]
      rw [ih, rrJShiftTermPS_succ_sub]
      ring

theorem coeff_rrJShiftPS_eq_partial (m k : ℕ) :
    (rrJShiftPS m).coeff k = (rrJShiftPartialPS m k).coeff k := by
  unfold rrJShiftPS rrJShiftPartialPS
  rw [PowerSeries.coeff_mk, map_sum]

theorem rrJShiftPartialPS_coeff_eq_of_le (m k N : ℕ) (hkN : k ≤ N) :
    (rrJShiftPartialPS m N).coeff k = (rrJShiftPartialPS m k).coeff k := by
  induction N, hkN using Nat.le_induction with
  | base => rfl
  | succ N hle ih =>
      rw [rrJShiftPartialPS_succ, map_add, ih]
      have hterm : (rrJShiftTermPS m (N + 1)).coeff k = 0 := by
        apply rrJShiftTermPS_coeff_eq_zero
        have hlt : k < N + 1 := by omega
        have hle_exp : N + 1 ≤ (N + 1) * (N + 1) + m * (N + 1) := by
          have hsq : N + 1 ≤ (N + 1) * (N + 1) := Nat.le_mul_self (N + 1)
          omega
        omega
      rw [hterm, add_zero]

private theorem coeff_X_pow_mul_rrJShiftPS_eq_partial_of_le (m k N : ℕ)
    (hN : k - (m + 1) ≤ N) :
    (X ^ (m + 1) * rrJShiftPS (m + 2)).coeff k =
      (X ^ (m + 1) * rrJShiftPartialPS (m + 2) N).coeff k := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hmk : m + 1 ≤ k
  · rw [if_pos hmk]
    rw [PowerSeries.coeff_X_pow_mul', if_pos hmk]
    rw [coeff_rrJShiftPS_eq_partial]
    rw [rrJShiftPartialPS_coeff_eq_of_le (m + 2) (k - (m + 1)) N hN]
  · rw [if_neg hmk]
    rw [PowerSeries.coeff_X_pow_mul', if_neg hmk]

theorem rrJShiftPS_functional_eq (m : ℕ) :
    rrJShiftPS m = rrJShiftPS (m + 1) + X ^ (m + 1) * rrJShiftPS (m + 2) := by
  ext k
  by_cases hk0 : k = 0
  · subst k
    unfold rrJShiftPS
    simp [PowerSeries.coeff_mk]
  · rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨N, rfl⟩
    rw [map_add]
    rw [coeff_rrJShiftPS_eq_partial m (N + 1),
        coeff_rrJShiftPS_eq_partial (m + 1) (N + 1),
        coeff_X_pow_mul_rrJShiftPS_eq_partial_of_le m (N + 1) N (by omega)]
    have hpart := congrArg (fun f : ℚ⟦X⟧ => f.coeff (N + 1))
      (rrJShiftPartialPS_succ_sub m N)
    have hpart' :
        (rrJShiftPartialPS m (N + 1)).coeff (N + 1) -
          (rrJShiftPartialPS (m + 1) (N + 1)).coeff (N + 1) =
            (X ^ (m + 1) * rrJShiftPartialPS (m + 2) N).coeff (N + 1) := by
      simpa [map_sub] using hpart
    linarith

private def tri (n : ℕ) : ℕ := (n + 1) * (n + 2) / 2

private lemma tri_succ (n : ℕ) :
    tri n + (n + 2) = tri (n + 1) := by
  unfold tri
  change (n + 1) * (n + 2) / 2 + (n + 2) = (n + 2) * (n + 3) / 2
  have h1 : 2 ∣ (n + 1) * (n + 2) := (Nat.even_mul_succ_self (n + 1)).two_dvd
  have h2 : 2 ∣ (n + 2) * (n + 3) := (Nat.even_mul_succ_self (n + 2)).two_dvd
  have heq : (n + 2) * (n + 3) = 2 * (n + 2) + (n + 1) * (n + 2) := by ring
  omega

/-- The error after clearing denominators in the `n`-th continued-fraction
convergent has exact X-adic order at least the triangular number `tri n`. -/
theorem rrJShift_convergent_error (n : ℕ) :
    rrJShiftPS 1 * rrcf_APS n - rrJShiftPS 0 * rrcf_BPS n =
      ((-1) ^ (n + 1) : ℚ⟦X⟧) * X ^ tri n * rrJShiftPS (n + 2) := by
  refine Nat.twoStepInduction
    (P := fun n => rrJShiftPS 1 * rrcf_APS n - rrJShiftPS 0 * rrcf_BPS n =
      ((-1) ^ (n + 1) : ℚ⟦X⟧) * X ^ tri n * rrJShiftPS (n + 2))
    ?h0 ?h1 ?hstep n
  · change rrJShiftPS 1 * rrcf_APS 0 - rrJShiftPS 0 * rrcf_BPS 0 =
      ((-1) ^ (0 + 1) : ℚ⟦X⟧) * X ^ tri 0 * rrJShiftPS (0 + 2)
    rw [rrcf_APS_zero, rrcf_BPS_zero, mul_one, mul_one]
    rw [rrJShiftPS_functional_eq 0]
    unfold tri
    ring
  · change rrJShiftPS 1 * rrcf_APS 1 - rrJShiftPS 0 * rrcf_BPS 1 =
      ((-1) ^ (1 + 1) : ℚ⟦X⟧) * X ^ tri 1 * rrJShiftPS (1 + 2)
    rw [rrcf_APS_one, rrcf_BPS_one, mul_one]
    rw [rrJShiftPS_functional_eq 0, rrJShiftPS_functional_eq 1]
    unfold tri
    ring
  · intro n ih ih1
    rw [rrcf_APS_succ_succ n, rrcf_BPS_succ_succ n]
    calc
      rrJShiftPS 1 * (rrcf_APS (n + 1) + X ^ (n + 2) * rrcf_APS n) -
          rrJShiftPS 0 * (rrcf_BPS (n + 1) + X ^ (n + 2) * rrcf_BPS n)
          =
          (rrJShiftPS 1 * rrcf_APS (n + 1) -
            rrJShiftPS 0 * rrcf_BPS (n + 1)) +
            X ^ (n + 2) *
              (rrJShiftPS 1 * rrcf_APS n - rrJShiftPS 0 * rrcf_BPS n) := by
            ring
      _ =
          ((-1) ^ (n + 2) : ℚ⟦X⟧) * X ^ tri (n + 1) * rrJShiftPS (n + 3) +
            X ^ (n + 2) *
              (((-1) ^ (n + 1) : ℚ⟦X⟧) * X ^ tri n * rrJShiftPS (n + 2)) := by
            rw [ih1, ih]
      _ =
          ((-1) ^ (n + 1) : ℚ⟦X⟧) * X ^ tri (n + 1) *
            (rrJShiftPS (n + 2) - rrJShiftPS (n + 3)) := by
            rw [← tri_succ n, pow_add]
            ring
      _ =
          ((-1) ^ (n + 1) : ℚ⟦X⟧) * X ^ tri (n + 1) *
            (X ^ (n + 3) * rrJShiftPS (n + 4)) := by
            have hfun := rrJShiftPS_functional_eq (n + 2)
            rw [hfun]
            ring
      _ =
          ((-1) ^ ((n + 2) + 1) : ℚ⟦X⟧) * X ^ tri (n + 2) *
            rrJShiftPS ((n + 2) + 2) := by
            rw [← tri_succ (n + 1), pow_add]
            ring

private theorem constantCoeff_rrGPS_ne_zero :
    constantCoeff rrGPS ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_rrGPS]
  norm_num

private theorem constantCoeff_rrcf_APS_ne_zero (n : ℕ) :
    constantCoeff (rrcf_APS n) ≠ 0 := by
  rw [constantCoeff_rrcf_APS]
  norm_num

theorem rrHPS_mul_APS_sub_rrGPS_mul_BPS_dvd (n : ℕ) :
    (X ^ tri n : ℚ⟦X⟧) ∣ (rrHPS * rrcf_APS n - rrGPS * rrcf_BPS n) := by
  have herr : rrHPS * rrcf_APS n - rrGPS * rrcf_BPS n =
      ((-1) ^ (n + 1) : ℚ⟦X⟧) * X ^ tri n * rrJShiftPS (n + 2) := by
    simpa [rrJShiftPS_one, rrJShiftPS_zero] using rrJShift_convergent_error n
  refine ⟨(((-1) ^ (n + 1) : ℚ⟦X⟧) * rrJShiftPS (n + 2)), ?_⟩
  rw [herr]
  ring

theorem ratio_sub_rrcf_RPS_dvd (n : ℕ) :
    (X ^ tri n : ℚ⟦X⟧) ∣ (rrHPS * rrGPS⁻¹ - rrcf_RPS n) := by
  have hGA_ne :
      constantCoeff (rrGPS * rrcf_APS n) ≠ 0 := by
    rw [map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_rrGPS,
        constantCoeff_rrcf_APS]
    norm_num
  have hG_inv : rrGPS⁻¹ * rrGPS = 1 :=
    PowerSeries.inv_mul_cancel _ constantCoeff_rrGPS_ne_zero
  have hA_inv : (rrcf_APS n)⁻¹ * rrcf_APS n = 1 :=
    PowerSeries.inv_mul_cancel _ (constantCoeff_rrcf_APS_ne_zero n)
  have hunit :
      (rrGPS * rrcf_APS n) * (rrGPS * rrcf_APS n)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ hGA_ne
  rcases rrHPS_mul_APS_sub_rrGPS_mul_BPS_dvd n with ⟨w, hw⟩
  refine ⟨w * (rrGPS * rrcf_APS n)⁻¹, ?_⟩
  calc
    rrHPS * rrGPS⁻¹ - rrcf_RPS n
        = (rrHPS * rrGPS⁻¹ - rrcf_RPS n) *
            ((rrGPS * rrcf_APS n) * (rrGPS * rrcf_APS n)⁻¹) := by
          rw [hunit, mul_one]
    _ = ((rrHPS * rrGPS⁻¹ - rrcf_RPS n) * rrGPS * rrcf_APS n) *
          (rrGPS * rrcf_APS n)⁻¹ := by
          ring
    _ = (rrHPS * rrcf_APS n - rrGPS * rrcf_BPS n) *
          (rrGPS * rrcf_APS n)⁻¹ := by
          unfold rrcf_RPS
          calc
            ((rrHPS * rrGPS⁻¹ - rrcf_BPS n * (rrcf_APS n)⁻¹) *
                  rrGPS * rrcf_APS n) * (rrGPS * rrcf_APS n)⁻¹
                =
                (rrHPS * (rrGPS⁻¹ * rrGPS) * rrcf_APS n -
                    rrcf_BPS n * ((rrcf_APS n)⁻¹ * rrcf_APS n) * rrGPS) *
                  (rrGPS * rrcf_APS n)⁻¹ := by
                  ring
            _ = (rrHPS * rrcf_APS n - rrGPS * rrcf_BPS n) *
                  (rrGPS * rrcf_APS n)⁻¹ := by
                  rw [hG_inv, hA_inv]
                  ring
    _ = (X ^ tri n * w) * (rrGPS * rrcf_APS n)⁻¹ := by
          rw [hw]
    _ = X ^ tri n * (w * (rrGPS * rrcf_APS n)⁻¹) := by
          ring

private lemma coeff_lt_tri_of_le (n k : ℕ) (hk : k ≤ n) :
    k < tri n := by
  unfold tri
  have h_even : 2 ∣ (n + 1) * (n + 2) := (Nat.even_mul_succ_self (n + 1)).two_dvd
  have h_ge : 2 * (n + 1) ≤ (n + 1) * (n + 2) := by
    have : (n + 1) * (n + 2) = (n + 1) * 2 + (n + 1) * n := by ring
    omega
  omega

theorem coeff_ratio_eq_rrcf_RPS_of_le (n k : ℕ) (hk : k ≤ n) :
    (rrHPS * rrGPS⁻¹).coeff k = (rrcf_RPS n).coeff k := by
  have hdvd := ratio_sub_rrcf_RPS_dvd n
  have hlt : k < tri n := coeff_lt_tri_of_le n k hk
  have hzero : (rrHPS * rrGPS⁻¹ - rrcf_RPS n).coeff k = 0 := by
    rw [PowerSeries.X_pow_dvd_iff] at hdvd
    exact hdvd k hlt
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

theorem rrcf_r_via_CF_eq_rrHPS_mul_rrGPS_inv :
    rrcf_r_via_CF = rrHPS * rrGPS⁻¹ := by
  ext k
  rw [coeff_rrcf_r_via_CF]
  exact (coeff_ratio_eq_rrcf_RPS_of_le k k le_rfl).symm

theorem chan_theorem_11_1 : rrcf_r = rrcf_r_via_CF := by
  rw [← rogersRamanujan_ratio_formal]
  exact rrcf_r_via_CF_eq_rrHPS_mul_rrGPS_inv.symm

end ChanTheorem111

/-- Chan Theorem 11.1, exposed directly in the `Pending` namespace. -/
theorem chan_theorem_11_1 :
    Ch13RRCF.rrcf_r = Ch11RRCFConvergent.rrcf_r_via_CF :=
  ChanTheorem111.chan_theorem_11_1

end Pending
end QseriesFormalization
