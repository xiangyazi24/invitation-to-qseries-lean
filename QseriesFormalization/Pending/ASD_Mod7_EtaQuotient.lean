import QseriesFormalization.Pending.JTP_FormalPS_Mod7
import QseriesFormalization.Pending.Chapter17_ASD_Mod7
import QseriesFormalization.Pending.Chapter17_ASD_Mod7_Full
import QseriesFormalization.Pending.ASD_EtaProducts

/-!
# ASD mod-7 eta-product section identifications

This file mirrors the completed mod-5 section-identification path in
`Pending.ASD_EtaProducts` for Hirschhorn's modulus-7 dissection.
-/

namespace QseriesFormalization
namespace Pending
namespace ASDMod7EtaQuotient

open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartIV.Ch17
open QseriesFormalization.Pending.Hirschhorn7
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.JTPFormalPSMod7
open QseriesFormalization.Pending.ASDMod7Full

/-! ## Integral-to-`ZMod 7` forms of the mod-7 theta product identities -/

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

theorem mod7ProductPS_eq_theta7SeriesPS_zmod7_of_complex
    {a b : ℕ} {c : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hcomplex : mod7ProductPS a b ℂ = theta7SeriesPS c ℂ) :
    mod7ProductPS a b (ZMod 7) = theta7SeriesPS c (ZMod 7) := by
  have hint := mod7ProductPS_eq_theta7SeriesPS_int_of_complex ha hb hcomplex
  calc
    mod7ProductPS a b (ZMod 7)
        = PowerSeries.map (Int.castRingHom (ZMod 7)) (mod7ProductPS a b ℤ) :=
          (map_mod7ProductPS_int a b (ZMod 7) ha hb).symm
    _ = PowerSeries.map (Int.castRingHom (ZMod 7)) (theta7SeriesPS c ℤ) := by
          rw [hint]
    _ = theta7SeriesPS c (ZMod 7) := map_theta7SeriesPS_int c (ZMod 7)

theorem mod7Product034PS_eq_theta7SeriesPS_zmod7 :
    mod7Product034PS (ZMod 7) = theta7SeriesPS 1 (ZMod 7) :=
  mod7ProductPS_eq_theta7SeriesPS_zmod7_of_complex
    (a := 3) (b := 4) (c := 1) (by norm_num) (by norm_num)
    mod7Product034PS_eq_theta7SeriesPS_complex

theorem mod7Product025PS_eq_theta7SeriesPS_zmod7 :
    mod7Product025PS (ZMod 7) = theta7SeriesPS 3 (ZMod 7) :=
  mod7ProductPS_eq_theta7SeriesPS_zmod7_of_complex
    (a := 2) (b := 5) (c := 3) (by norm_num) (by norm_num)
    mod7Product025PS_eq_theta7SeriesPS_complex

theorem mod7Product016PS_eq_theta7SeriesPS_zmod7 :
    mod7Product016PS (ZMod 7) = theta7SeriesPS 5 (ZMod 7) :=
  mod7ProductPS_eq_theta7SeriesPS_zmod7_of_complex
    (a := 1) (b := 6) (c := 5) (by norm_num) (by norm_num)
    mod7Product016PS_eq_theta7SeriesPS_complex

theorem asd7HProductPS_eq_asd7HSeriesPS_zmod7 :
    asd7HProductPS (ZMod 7) = asd7HSeriesPS (ZMod 7) := by
  rw [← expand_mod7Product034PS (ZMod 7)]
  unfold asd7HSeriesPS
  rw [mod7Product034PS_eq_theta7SeriesPS_zmod7]

theorem asd7JProductPS_eq_asd7JSeriesPS_zmod7 :
    asd7JProductPS (ZMod 7) = asd7JSeriesPS (ZMod 7) := by
  rw [← expand_mod7Product025PS (ZMod 7)]
  unfold asd7JSeriesPS
  rw [mod7Product025PS_eq_theta7SeriesPS_zmod7]

theorem asd7KProductPS_eq_asd7KSeriesPS_zmod7 :
    asd7KProductPS (ZMod 7) = asd7KSeriesPS (ZMod 7) := by
  rw [← expand_mod7Product016PS (ZMod 7)]
  unfold asd7KSeriesPS
  rw [mod7Product016PS_eq_theta7SeriesPS_zmod7]

/-! ## Coefficient matching helpers -/

private theorem even_int_theta7_num {c : ℤ} (hc : ThetaCValid c) (k : ℤ) :
    Even (k * (7 * k - c)) := by
  rcases Int.even_or_odd k with hk | hk
  · exact hk.mul_right _
  · refine Even.mul_left ?_ k
    rcases hk with ⟨a, ha⟩
    rcases hc with rfl | rfl | rfl
    · rw [ha]; exact ⟨7 * a + 3, by ring⟩
    · rw [ha]; exact ⟨7 * a + 2, by ring⟩
    · rw [ha]; exact ⟨7 * a + 1, by ring⟩

private theorem two_mul_int_theta7_div_two {c : ℤ} (hc : ThetaCValid c) (k : ℤ) :
    2 * (k * (7 * k - c) / 2) = k * (7 * k - c) := by
  exact Int.two_mul_ediv_two_of_even (even_int_theta7_num hc k)

private theorem theta7Exp_injective {c : ℤ} (hc : ThetaCValid c) {a b : ℤ}
    (h : theta7Exp c a = theta7Exp c b) : a = b := by
  have hcast : ((theta7Exp c a : ℕ) : ℤ) =
      ((theta7Exp c b : ℕ) : ℤ) := by
    exact_mod_cast h
  rw [int_coe_theta7Exp hc, int_coe_theta7Exp hc] at hcast
  have hmul := congrArg (fun z : ℤ => 2 * z) hcast
  change 2 * (a * (7 * a - c) / 2) =
    2 * (b * (7 * b - c) / 2) at hmul
  rw [two_mul_int_theta7_div_two hc, two_mul_int_theta7_div_two hc] at hmul
  have hfac : (a - b) * (7 * (a + b) - c) = 0 := by
    nlinarith
  have hsecond : 7 * (a + b) - c ≠ 0 := by
    rcases hc with rfl | rfl | rfl <;> omega
  rcases mul_eq_zero.mp hfac with hab | hbad
  · omega
  · exact (hsecond hbad).elim

private theorem theta7Coeff_eq_of_exp {c : ℤ} (hc : ThetaCValid c)
    (m : ℕ) (k : ℤ) (hk : theta7Exp c k = m) :
    theta7Coeff c (ZMod 7) m = negOnePowInt (ZMod 7) k := by
  unfold theta7Coeff
  calc
    (∑ l ∈ Finset.Icc (-(m + 1 : ℤ)) (m + 1 : ℤ),
        if theta7Exp c l = m then negOnePowInt (ZMod 7) l else 0)
        = (if theta7Exp c k = m then negOnePowInt (ZMod 7) k else 0) := by
          apply Finset.sum_eq_single k
          · intro l _hl hlne
            by_cases hleq : theta7Exp c l = m
            · have hlk : l = k := theta7Exp_injective hc (hleq.trans hk.symm)
              exact (hlne hlk).elim
            · simp [hleq]
          · intro hknot
            exact (hknot (theta7Exp_mem_Icc_of_eq hc hk)).elim
    _ = negOnePowInt (ZMod 7) k := by rw [if_pos hk]

private theorem theta7Coeff_eq_zero_of_no_exp {c : ℤ}
    (m : ℕ) (h : ∀ k : ℤ, theta7Exp c k ≠ m) :
    theta7Coeff c (ZMod 7) m = 0 := by
  unfold theta7Coeff
  apply Finset.sum_eq_zero
  intro k _hk
  simp [h k]

private theorem theta7Exp_one_neg_nat (a : ℕ) :
    theta7Exp 1 (-(a : ℤ)) = a * (7 * a + 1) / 2 := by
  rw [← Int.natCast_inj]
  rw [int_coe_theta7Exp (by left; rfl)]
  norm_num
  ring_nf

private theorem theta7Exp_one_nat (a : ℕ) :
    theta7Exp 1 (a : ℤ) = a * (7 * a - 1) / 2 := by
  rw [← Int.natCast_inj]
  rw [int_coe_theta7Exp (by left; rfl)]
  by_cases ha : a = 0
  · simp [ha]
  · have hsub : ((7 * a - 1 : ℕ) : ℤ) = 7 * (a : ℤ) - 1 := by omega
    norm_num
    rw [hsub]

private theorem even_nat_mul_seven_mul_add_one (a : ℕ) :
    Even (a * (7 * a + 1)) := by
  rcases Nat.even_or_odd a with ha | ha
  · exact ha.mul_right _
  · refine Even.mul_left ?_ a
    rcases ha with ⟨t, ht⟩
    rw [ht]
    exact ⟨7 * t + 4, by ring⟩

private theorem even_nat_mul_seven_mul_sub_one (a : ℕ) :
    Even (a * (7 * a - 1)) := by
  rcases Nat.even_or_odd a with ha | ha
  · exact ha.mul_right _
  · refine Even.mul_left ?_ a
    rcases ha with ⟨t, ht⟩
    rw [ht]
    exact ⟨7 * t + 3, by omega⟩

private theorem seven_mul_theta7Exp_one_neg_nat_formula (a : ℕ) :
    7 * (a * (7 * a + 1) / 2) = (7 * a) * (7 * a + 1) / 2 := by
  obtain ⟨q, hq⟩ := even_nat_mul_seven_mul_add_one a
  have hprod : (7 * a) * (7 * a + 1) = 7 * (a * (7 * a + 1)) := by ring
  rw [hprod, hq]
  omega

private theorem seven_mul_theta7Exp_one_nat_formula (a : ℕ) :
    7 * (a * (7 * a - 1) / 2) = (7 * a - 1) * (7 * a) / 2 := by
  by_cases ha0 : a = 0
  · simp [ha0]
  obtain ⟨q, hq⟩ := even_nat_mul_seven_mul_sub_one a
  have hprod : (7 * a - 1) * (7 * a) = 7 * (a * (7 * a - 1)) := by
    apply Nat.cast_injective (R := ℤ)
    push_cast
    have h1 : ((7 * a - 1 : ℕ) : ℤ) = 7 * (a : ℤ) - 1 := by omega
    rw [h1]
    ring
  rw [hprod, hq]
  omega

private theorem natCast_zmod7_eq_mod (n : ℕ) :
    (n : ZMod 7) = ((n % 7 : ℕ) : ZMod 7) := by
  conv_lhs => rw [← Nat.mod_add_div n 7]
  push_cast
  have : (7 : ZMod 7) = 0 := by decide
  rw [this]
  ring

private theorem triangular_cast_eq_mod7 (k : ℕ) :
    (((k * (k + 1) / 2 : ℕ) : ZMod 7)) =
      4 * (k : ZMod 7) * ((k : ZMod 7) + 1) := by
  have h2T : 2 * (k * (k + 1) / 2) = k * (k + 1) := two_mul_triangular k
  have h_cast : (2 : ZMod 7) * ((k * (k + 1) / 2 : ℕ) : ZMod 7) =
      ((k : ZMod 7)) * ((k : ZMod 7) + 1) := by
    have h1 : ((2 * (k * (k + 1) / 2) : ℕ) : ZMod 7) =
        ((k * (k + 1) : ℕ) : ZMod 7) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 7) h2T
    push_cast at h1
    exact h1
  have h2_inv : (4 : ZMod 7) * 2 = 1 := by decide
  calc
    ((k * (k + 1) / 2 : ℕ) : ZMod 7)
        = 1 * ((k * (k + 1) / 2 : ℕ) : ZMod 7) := (one_mul _).symm
    _ = (4 * 2) * ((k * (k + 1) / 2 : ℕ) : ZMod 7) := by rw [h2_inv]
    _ = 4 * (2 * ((k * (k + 1) / 2 : ℕ) : ZMod 7)) := by ring
    _ = 4 * ((k : ZMod 7) * ((k : ZMod 7) + 1)) := by rw [h_cast]
    _ = 4 * (k : ZMod 7) * ((k : ZMod 7) + 1) := by ring

private theorem triangular_index_mod7_eq_zero (j : ℕ)
    (h : (((j * (j + 1) / 2 : ℕ) : ZMod 7) = 0)) :
    j % 7 = 0 ∨ j % 7 = 6 := by
  rw [triangular_cast_eq_mod7] at h
  have hj : (j : ZMod 7) = ((j % 7 : ℕ) : ZMod 7) := natCast_zmod7_eq_mod j
  rw [hj] at h
  have hlt : j % 7 < 7 := Nat.mod_lt j (by decide)
  interval_cases j % 7 <;> norm_num at h ⊢
  all_goals exact absurd h (by decide)

private theorem neg_one_pow_zmod7_seven_mul (a : ℕ) :
    (-1 : ZMod 7) ^ (7 * a) = (-1 : ZMod 7) ^ a := by
  rw [neg_one_pow_eq_pow_mod_two (R := ZMod 7) (7 * a),
    neg_one_pow_eq_pow_mod_two (R := ZMod 7) a]
  have h : (7 * a) % 2 = a % 2 := by omega
  rw [h]

private theorem neg_one_pow_zmod7_seven_mul_sub_one (a : ℕ) (ha : 0 < a) :
    (-1 : ZMod 7) ^ (7 * a - 1) = -((-1 : ZMod 7) ^ a) := by
  rw [neg_one_pow_eq_pow_mod_two (R := ZMod 7) (7 * a - 1)]
  have h : (7 * a - 1) % 2 = (a + 1) % 2 := by omega
  rw [h]
  rw [← neg_one_pow_eq_pow_mod_two (R := ZMod 7) (a + 1)]
  rw [pow_succ]
  ring

private theorem jacobi_seven_mul_sign_zero_family (a : ℕ) :
    ((((-1 : ℤ) ^ (7 * a) * (2 * (7 * a) + 1) : ℤ) : ZMod 7)) =
      negOnePowInt (ZMod 7) (-(a : ℤ)) := by
  simp [negOnePowInt]
  rw [neg_one_pow_zmod7_seven_mul a]
  have hcoeff : (2 : ZMod 7) * (7 * (a : ZMod 7)) + 1 = 1 := by
    have h7 : (7 : ZMod 7) = 0 := by decide
    rw [show (7 : ZMod 7) * a = 7 * a by rfl, h7, zero_mul]
    ring
  rw [hcoeff, mul_one]

private theorem jacobi_seven_mul_sign_six_family (a : ℕ) (ha : 0 < a) :
    ((((-1 : ℤ) ^ (7 * a - 1) * (2 * (7 * a - 1) + 1) : ℤ) : ZMod 7)) =
      negOnePowInt (ZMod 7) (a : ℤ) := by
  simp [negOnePowInt]
  rw [neg_one_pow_zmod7_seven_mul_sub_one a ha]
  have hcoeff : (2 : ZMod 7) * (7 * (a : ZMod 7) - 1) + 1 = -1 := by
    have h7 : (7 : ZMod 7) = 0 := by decide
    rw [h7, zero_mul]
    norm_num
  rw [hcoeff]
  ring

private theorem jacobiTripleSign_seven_mul_eq_theta7Coeff_one_zmod7 (m : ℕ) :
    ((jacobiTripleSign (7 * m) : ℤ) : ZMod 7) =
      theta7Coeff 1 (ZMod 7) m := by
  by_cases htri : ∃ j ≤ 7 * m, 7 * m = j * (j + 1) / 2
  · obtain ⟨j, _hjle, hj⟩ := htri
    rw [hj, jacobiTripleSign_triangular]
    have htri_zmod : (((j * (j + 1) / 2 : ℕ) : ZMod 7) = 0) := by
      rw [← hj]
      push_cast
      change (7 : ZMod 7) * (m : ZMod 7) = 0
      have h7 : (7 : ZMod 7) = 0 := by decide
      rw [h7, zero_mul]
    rcases triangular_index_mod7_eq_zero j htri_zmod with hjmod | hjmod
    · let a := j / 7
      have hj_eq : j = 7 * a := by
        calc
          j = j % 7 + 7 * (j / 7) := (Nat.mod_add_div j 7).symm
          _ = 0 + 7 * a := by rw [hjmod]
          _ = 7 * a := by omega
      have hexp : theta7Exp 1 (-(a : ℤ)) = m := by
        rw [theta7Exp_one_neg_nat]
        apply Eq.symm
        exact Nat.eq_of_mul_eq_mul_left (n := 7) (by decide) (by
          rw [seven_mul_theta7Exp_one_neg_nat_formula]
          have hj_formula : (7 * a) * (7 * a + 1) / 2 = j * (j + 1) / 2 := by
            rw [← hj_eq]
          rw [hj_formula]
          exact hj)
      rw [theta7Coeff_eq_of_exp (by left; rfl) m (-(a : ℤ)) hexp]
      rw [hj_eq]
      exact jacobi_seven_mul_sign_zero_family a
    · let a := j / 7 + 1
      have ha : 0 < a := by omega
      have hj_eq : j = 7 * a - 1 := by
        calc
          j = j % 7 + 7 * (j / 7) := (Nat.mod_add_div j 7).symm
          _ = 6 + 7 * (j / 7) := by rw [hjmod]
          _ = 7 * a - 1 := by omega
      have hexp : theta7Exp 1 (a : ℤ) = m := by
        rw [theta7Exp_one_nat]
        apply Eq.symm
        exact Nat.eq_of_mul_eq_mul_left (n := 7) (by decide) (by
          rw [seven_mul_theta7Exp_one_nat_formula]
          have hj_formula : (7 * a - 1) * (7 * a) / 2 = j * (j + 1) / 2 := by
            rw [← hj_eq]
            have hs : 7 * a = j + 1 := by omega
            rw [hs]
          rw [hj_formula]
          exact hj)
      rw [theta7Coeff_eq_of_exp (by left; rfl) m (a : ℤ) hexp]
      rw [hj_eq]
      have hcast_sub : ((7 * a - 1 : ℕ) : ZMod 7) = 7 * (a : ZMod 7) - 1 := by
        have hs : 7 * a - 1 + 1 = 7 * a := by omega
        have hs_cast : (((7 * a - 1 + 1 : ℕ) : ZMod 7) =
            ((7 * a : ℕ) : ZMod 7)) := by
          exact congrArg (fun n : ℕ => (n : ZMod 7)) hs
        push_cast at hs_cast
        linear_combination hs_cast
      push_cast
      rw [hcast_sub]
      simpa using jacobi_seven_mul_sign_six_family a ha
  · push_neg at htri
    rw [jacobiTripleSign_of_not_triangular (7 * m) htri]
    simp only [Int.cast_zero]
    symm
    apply theta7Coeff_eq_zero_of_no_exp
    intro k hk
    cases k with
    | ofNat a =>
        change theta7Exp 1 (a : ℤ) = m at hk
        rw [theta7Exp_one_nat] at hk
        by_cases ha : a = 0
        · subst a
          simp at hk
          subst m
          exact htri 0 (by simp) (by simp)
        ·
          have hj : 7 * m = (7 * a - 1) * (7 * a) / 2 := by
            rw [← seven_mul_theta7Exp_one_nat_formula, hk]
          have hsucc : 7 * a - 1 + 1 = 7 * a := by omega
          have hjle : 7 * a - 1 ≤ 7 * m := by
            rw [hj]
            rw [← hsucc]
            exact k_le_triangular (7 * a - 1)
          have hjtri : 7 * m = (7 * a - 1) * (7 * a - 1 + 1) / 2 := by
            rwa [hsucc]
          exact htri (7 * a - 1) hjle hjtri
    | negSucc n =>
        let a := n + 1
        have hk' : theta7Exp 1 (-(a : ℤ)) = m := by
          change theta7Exp 1 (Int.negSucc n) = m
          exact hk
        rw [theta7Exp_one_neg_nat] at hk'
        have hj : 7 * m = (7 * a) * (7 * a + 1) / 2 := by
          rw [← seven_mul_theta7Exp_one_neg_nat_formula, hk']
        have hjle : 7 * a ≤ 7 * m := by
          rw [hj]
          exact k_le_triangular (7 * a)
        exact htri (7 * a) hjle hj

theorem ASD7_0_eq_asd7HSeriesPS_zmod7 :
    ASD7 0 = asd7HSeriesPS (ZMod 7) := by
  ext n
  rw [ASD7, coeff_section7]
  by_cases hdiv : 7 ∣ n
  · have hnmod : n % 7 = 0 := Nat.mod_eq_zero_of_dvd hdiv
    rw [if_pos hnmod]
    rw [QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS,
      coeff_jacobiThetaPS]
    rw [coeff_asd7HSeriesPS, if_pos hdiv]
    have hn : 7 * (n / 7) = n := Nat.mul_div_cancel' hdiv
    calc
      ((jacobiTripleSign n : ℤ) : ZMod 7)
          = ((jacobiTripleSign (7 * (n / 7)) : ℤ) : ZMod 7) := by rw [hn]
      _ = theta7Coeff 1 (ZMod 7) (n / 7) :=
          jacobiTripleSign_seven_mul_eq_theta7Coeff_one_zmod7 (n / 7)
  · have hnmod : n % 7 ≠ 0 := by
      intro hnmod
      exact hdiv (Nat.dvd_of_mod_eq_zero hnmod)
    rw [if_neg hnmod]
    rw [coeff_asd7HSeriesPS, if_neg hdiv]

theorem ASD7_0_eq_asd7HProductPS_zmod7 :
    ASD7 0 = asd7HProductPS (ZMod 7) := by
  rw [ASD7_0_eq_asd7HSeriesPS_zmod7, asd7HProductPS_eq_asd7HSeriesPS_zmod7]

/-! ## The residue-1 component: `ASD7 1 = -3q J(q^7)` -/

noncomputable abbrev asd7JShiftedProductPS : (ZMod 7)⟦X⟧ :=
  -(3 : (ZMod 7)⟦X⟧) * PowerSeries.X * asd7JProductPS (ZMod 7)

private theorem theta7Exp_three_neg_nat (a : ℕ) :
    theta7Exp 3 (-(a : ℤ)) = a * (7 * a + 3) / 2 := by
  rw [← Int.natCast_inj]
  rw [int_coe_theta7Exp (by right; left; rfl)]
  norm_num
  ring_nf

private theorem theta7Exp_three_nat (a : ℕ) :
    theta7Exp 3 (a : ℤ) = a * (7 * a - 3) / 2 := by
  rw [← Int.natCast_inj]
  rw [int_coe_theta7Exp (by right; left; rfl)]
  by_cases ha : a = 0
  · simp [ha]
  · have hsub : ((7 * a - 3 : ℕ) : ℤ) = 7 * (a : ℤ) - 3 := by omega
    norm_num
    rw [hsub]

private theorem even_nat_mul_seven_mul_add_three (a : ℕ) :
    Even (a * (7 * a + 3)) := by
  rcases Nat.even_or_odd a with ha | ha
  · exact ha.mul_right _
  · refine Even.mul_left ?_ a
    rcases ha with ⟨t, ht⟩
    rw [ht]
    exact ⟨7 * t + 5, by ring⟩

private theorem even_nat_mul_seven_mul_sub_three (a : ℕ) :
    Even (a * (7 * a - 3)) := by
  rcases Nat.even_or_odd a with ha | ha
  · exact ha.mul_right _
  · refine Even.mul_left ?_ a
    rcases ha with ⟨t, ht⟩
    rw [ht]
    exact ⟨7 * t + 2, by omega⟩

private theorem seven_mul_theta7Exp_three_neg_nat_formula (a : ℕ) :
    7 * (a * (7 * a + 3) / 2) + 1 = (7 * a + 1) * (7 * a + 2) / 2 := by
  obtain ⟨q, hq⟩ := even_nat_mul_seven_mul_add_three a
  have hprod : (7 * a + 1) * (7 * a + 2) = 7 * (a * (7 * a + 3)) + 2 := by
    ring
  rw [hprod, hq]
  omega

private theorem seven_mul_theta7Exp_three_nat_formula (a : ℕ) (ha : 0 < a) :
    7 * (a * (7 * a - 3) / 2) + 1 = (7 * a - 2) * (7 * a - 1) / 2 := by
  obtain ⟨q, hq⟩ := even_nat_mul_seven_mul_sub_three a
  have hprod : (7 * a - 2) * (7 * a - 1) =
      7 * (a * (7 * a - 3)) + 2 := by
    apply Nat.cast_injective (R := ℤ)
    push_cast
    have h1 : ((7 * a - 2 : ℕ) : ℤ) = 7 * (a : ℤ) - 2 := by omega
    have h2 : ((7 * a - 1 : ℕ) : ℤ) = 7 * (a : ℤ) - 1 := by omega
    have h3 : ((7 * a - 3 : ℕ) : ℤ) = 7 * (a : ℤ) - 3 := by omega
    rw [h1, h2, h3]
    ring
  rw [hprod, hq]
  omega

private theorem triangular_index_mod7_eq_one (j : ℕ)
    (h : (((j * (j + 1) / 2 : ℕ) : ZMod 7) = 1)) :
    j % 7 = 1 ∨ j % 7 = 5 := by
  rw [triangular_cast_eq_mod7] at h
  have hj : (j : ZMod 7) = ((j % 7 : ℕ) : ZMod 7) := natCast_zmod7_eq_mod j
  rw [hj] at h
  have hlt : j % 7 < 7 := Nat.mod_lt j (by decide)
  interval_cases j % 7 <;> norm_num at h ⊢
  all_goals exact absurd h (by decide)

private theorem neg_one_pow_zmod7_seven_mul_add_one (a : ℕ) :
    (-1 : ZMod 7) ^ (7 * a + 1) = -((-1 : ZMod 7) ^ a) := by
  rw [neg_one_pow_eq_pow_mod_two (R := ZMod 7) (7 * a + 1)]
  have h : (7 * a + 1) % 2 = (a + 1) % 2 := by omega
  rw [h]
  rw [← neg_one_pow_eq_pow_mod_two (R := ZMod 7) (a + 1)]
  rw [pow_succ]
  ring

private theorem neg_one_pow_zmod7_seven_mul_sub_two (a : ℕ) (ha : 0 < a) :
    (-1 : ZMod 7) ^ (7 * a - 2) = (-1 : ZMod 7) ^ a := by
  rw [neg_one_pow_eq_pow_mod_two (R := ZMod 7) (7 * a - 2),
    neg_one_pow_eq_pow_mod_two (R := ZMod 7) a]
  have h : (7 * a - 2) % 2 = a % 2 := by omega
  rw [h]

private theorem jacobi_seven_mul_sign_one_family (a : ℕ) :
    ((((-1 : ℤ) ^ (7 * a + 1) * (2 * (7 * a + 1) + 1) : ℤ) : ZMod 7)) =
      -(3 : ZMod 7) * negOnePowInt (ZMod 7) (-(a : ℤ)) := by
  simp [negOnePowInt]
  rw [neg_one_pow_zmod7_seven_mul_add_one a]
  have hcoeff : (2 : ZMod 7) * (7 * (a : ZMod 7) + 1) + 1 = 3 := by
    have h7 : (7 : ZMod 7) = 0 := by decide
    rw [h7, zero_mul]
    norm_num
  rw [hcoeff]
  ring

private theorem jacobi_seven_mul_sign_five_family (a : ℕ) (ha : 0 < a) :
    ((((-1 : ℤ) ^ (7 * a - 2) * (2 * (7 * a - 2) + 1) : ℤ) : ZMod 7)) =
      -(3 : ZMod 7) * negOnePowInt (ZMod 7) (a : ℤ) := by
  simp [negOnePowInt]
  rw [neg_one_pow_zmod7_seven_mul_sub_two a ha]
  have hcoeff : (2 : ZMod 7) * (7 * (a : ZMod 7) - 2) + 1 = -3 := by
    have h7 : (7 : ZMod 7) = 0 := by decide
    rw [h7, zero_mul]
    norm_num
  rw [hcoeff]
  ring

private theorem jacobiTripleSign_seven_mul_add_one_eq_theta7Coeff_three_zmod7
    (m : ℕ) :
    ((jacobiTripleSign (7 * m + 1) : ℤ) : ZMod 7) =
      -(3 : ZMod 7) * theta7Coeff 3 (ZMod 7) m := by
  by_cases htri : ∃ j ≤ 7 * m + 1, 7 * m + 1 = j * (j + 1) / 2
  · obtain ⟨j, _hjle, hj⟩ := htri
    rw [hj, jacobiTripleSign_triangular]
    have htri_zmod : (((j * (j + 1) / 2 : ℕ) : ZMod 7) = 1) := by
      rw [← hj]
      push_cast
      change (7 : ZMod 7) * (m : ZMod 7) + 1 = 1
      have h7 : (7 : ZMod 7) = 0 := by decide
      rw [h7, zero_mul, zero_add]
    rcases triangular_index_mod7_eq_one j htri_zmod with hjmod | hjmod
    · let a := j / 7
      have hj_eq : j = 7 * a + 1 := by
        calc
          j = j % 7 + 7 * (j / 7) := (Nat.mod_add_div j 7).symm
          _ = 1 + 7 * a := by rw [hjmod]
          _ = 7 * a + 1 := by omega
      have hexp : theta7Exp 3 (-(a : ℤ)) = m := by
        rw [theta7Exp_three_neg_nat]
        apply Eq.symm
        exact Nat.eq_of_mul_eq_mul_left (n := 7) (by decide) (by
          have hformula := seven_mul_theta7Exp_three_neg_nat_formula a
          have hj_formula :
              (7 * a + 1) * (7 * a + 2) / 2 = j * (j + 1) / 2 := by
            rw [← hj_eq]
            have hs : 7 * a + 2 = j + 1 := by omega
            rw [hs]
          omega)
      rw [theta7Coeff_eq_of_exp (by right; left; rfl) m (-(a : ℤ)) hexp]
      rw [hj_eq]
      exact jacobi_seven_mul_sign_one_family a
    · let a := j / 7 + 1
      have ha : 0 < a := by omega
      have hj_eq : j = 7 * a - 2 := by
        calc
          j = j % 7 + 7 * (j / 7) := (Nat.mod_add_div j 7).symm
          _ = 5 + 7 * (j / 7) := by rw [hjmod]
          _ = 7 * a - 2 := by omega
      have hexp : theta7Exp 3 (a : ℤ) = m := by
        rw [theta7Exp_three_nat]
        apply Eq.symm
        exact Nat.eq_of_mul_eq_mul_left (n := 7) (by decide) (by
          have hformula := seven_mul_theta7Exp_three_nat_formula a ha
          have hj_formula :
              (7 * a - 2) * (7 * a - 1) / 2 = j * (j + 1) / 2 := by
            rw [← hj_eq]
            have hs : 7 * a - 1 = j + 1 := by omega
            rw [hs]
          omega)
      rw [theta7Coeff_eq_of_exp (by right; left; rfl) m (a : ℤ) hexp]
      rw [hj_eq]
      push_cast
      have hcast_sub_two : ((7 * a - 2 : ℕ) : ZMod 7) = 7 * (a : ZMod 7) - 2 := by
        have hs : 7 * a - 2 + 2 = 7 * a := by omega
        have hs_cast : (((7 * a - 2 + 2 : ℕ) : ZMod 7) =
            ((7 * a : ℕ) : ZMod 7)) := by
          exact congrArg (fun n : ℕ => (n : ZMod 7)) hs
        push_cast at hs_cast
        linear_combination hs_cast
      rw [hcast_sub_two]
      simpa using jacobi_seven_mul_sign_five_family a ha
  · push_neg at htri
    rw [jacobiTripleSign_of_not_triangular (7 * m + 1) htri]
    simp only [Int.cast_zero]
    have hcoeff_zero : theta7Coeff 3 (ZMod 7) m = 0 := by
      apply theta7Coeff_eq_zero_of_no_exp
      intro k hk
      cases k with
      | ofNat a =>
          change theta7Exp 3 (a : ℤ) = m at hk
          rw [theta7Exp_three_nat] at hk
          by_cases ha : a = 0
          · subst a
            simp at hk
            subst m
            exact htri 1 (by simp) (by simp)
          ·
            have ha_pos : 0 < a := by omega
            have hj : 7 * m + 1 = (7 * a - 2) * (7 * a - 1) / 2 := by
              rw [← seven_mul_theta7Exp_three_nat_formula a ha_pos, hk]
            have hsucc : 7 * a - 2 + 1 = 7 * a - 1 := by omega
            have hjle : 7 * a - 2 ≤ 7 * m + 1 := by
              rw [hj]
              rw [← hsucc]
              exact k_le_triangular (7 * a - 2)
            have hjtri :
                7 * m + 1 = (7 * a - 2) * (7 * a - 2 + 1) / 2 := by
              rwa [hsucc]
            exact htri (7 * a - 2) hjle hjtri
      | negSucc n =>
          let a := n + 1
          have hk' : theta7Exp 3 (-(a : ℤ)) = m := by
            change theta7Exp 3 (Int.negSucc n) = m
            exact hk
          rw [theta7Exp_three_neg_nat] at hk'
          have hj : 7 * m + 1 = (7 * a + 1) * (7 * a + 2) / 2 := by
            rw [← seven_mul_theta7Exp_three_neg_nat_formula, hk']
          have hsucc : 7 * a + 1 + 1 = 7 * a + 2 := by omega
          have hjle : 7 * a + 1 ≤ 7 * m + 1 := by
            rw [hj]
            rw [← hsucc]
            exact k_le_triangular (7 * a + 1)
          have hjtri :
              7 * m + 1 = (7 * a + 1) * (7 * a + 1 + 1) / 2 := by
            rwa [hsucc]
          exact htri (7 * a + 1) hjle hjtri
    rw [hcoeff_zero]
    ring

private theorem neg_three_ps_zmod7_eq_C :
    (-(3 : (ZMod 7)⟦X⟧)) = PowerSeries.C (-(3 : ZMod 7)) := by
  rw [show (3 : (ZMod 7)⟦X⟧) = PowerSeries.C (3 : ZMod 7) by
    exact (map_natCast (PowerSeries.C : ZMod 7 →+* (ZMod 7)⟦X⟧) 3).symm]
  rw [map_neg]

theorem ASD7_1_eq_asd7JShiftedSeriesPS_zmod7 :
    ASD7 1 = -(3 : (ZMod 7)⟦X⟧) * PowerSeries.X * asd7JSeriesPS (ZMod 7) := by
  ext n
  cases n with
  | zero =>
      rw [ASD7, coeff_section7]
      simp
  | succ n =>
      rw [ASD7, coeff_section7]
      rw [mul_assoc, neg_three_ps_zmod7_eq_C, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul]
      by_cases hres : (n + 1) % 7 = 1
      · rw [if_pos hres]
        rw [QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS,
          coeff_jacobiThetaPS]
        have hnmod : n % 7 = 0 := by omega
        have hdiv : 7 ∣ n := Nat.dvd_of_mod_eq_zero hnmod
        rw [coeff_asd7JSeriesPS, if_pos hdiv]
        have hn : 7 * (n / 7) = n := Nat.mul_div_cancel' hdiv
        calc
          ((jacobiTripleSign (n + 1) : ℤ) : ZMod 7)
              = ((jacobiTripleSign (7 * (n / 7) + 1) : ℤ) : ZMod 7) := by
                rw [hn]
          _ = -(3 : ZMod 7) * theta7Coeff 3 (ZMod 7) (n / 7) :=
              jacobiTripleSign_seven_mul_add_one_eq_theta7Coeff_three_zmod7 (n / 7)
      · rw [if_neg hres]
        have hnotdiv : ¬ 7 ∣ n := by omega
        rw [coeff_asd7JSeriesPS, if_neg hnotdiv, mul_zero]

theorem ASD7_1_eq_asd7JShiftedProductPS_zmod7 :
    ASD7 1 = asd7JShiftedProductPS := by
  rw [ASD7_1_eq_asd7JShiftedSeriesPS_zmod7]
  unfold asd7JShiftedProductPS
  rw [asd7JProductPS_eq_asd7JSeriesPS_zmod7]

/-! ## The residue-3 component: `ASD7 3 = 5q^3 K(q^7)` -/

noncomputable abbrev asd7KShiftedProductPS : (ZMod 7)⟦X⟧ :=
  (5 : (ZMod 7)⟦X⟧) * PowerSeries.X ^ 3 * asd7KProductPS (ZMod 7)

private theorem theta7Exp_five_neg_nat (a : ℕ) :
    theta7Exp 5 (-(a : ℤ)) = a * (7 * a + 5) / 2 := by
  rw [← Int.natCast_inj]
  rw [int_coe_theta7Exp (by right; right; rfl)]
  norm_num
  ring_nf

private theorem theta7Exp_five_nat (a : ℕ) :
    theta7Exp 5 (a : ℤ) = a * (7 * a - 5) / 2 := by
  rw [← Int.natCast_inj]
  rw [int_coe_theta7Exp (by right; right; rfl)]
  by_cases ha : a = 0
  · simp [ha]
  · have hsub : ((7 * a - 5 : ℕ) : ℤ) = 7 * (a : ℤ) - 5 := by omega
    norm_num
    rw [hsub]

private theorem even_nat_mul_seven_mul_add_five (a : ℕ) :
    Even (a * (7 * a + 5)) := by
  rcases Nat.even_or_odd a with ha | ha
  · exact ha.mul_right _
  · refine Even.mul_left ?_ a
    rcases ha with ⟨t, ht⟩
    rw [ht]
    exact ⟨7 * t + 6, by ring⟩

private theorem even_nat_mul_seven_mul_sub_five (a : ℕ) :
    Even (a * (7 * a - 5)) := by
  rcases Nat.even_or_odd a with ha | ha
  · exact ha.mul_right _
  · refine Even.mul_left ?_ a
    rcases ha with ⟨t, ht⟩
    rw [ht]
    exact ⟨7 * t + 1, by omega⟩

private theorem seven_mul_theta7Exp_five_neg_nat_formula (a : ℕ) :
    7 * (a * (7 * a + 5) / 2) + 3 = (7 * a + 2) * (7 * a + 3) / 2 := by
  obtain ⟨q, hq⟩ := even_nat_mul_seven_mul_add_five a
  have hprod : (7 * a + 2) * (7 * a + 3) = 7 * (a * (7 * a + 5)) + 6 := by
    ring
  rw [hprod, hq]
  omega

private theorem seven_mul_theta7Exp_five_nat_formula (a : ℕ) (ha : 0 < a) :
    7 * (a * (7 * a - 5) / 2) + 3 = (7 * a - 3) * (7 * a - 2) / 2 := by
  obtain ⟨q, hq⟩ := even_nat_mul_seven_mul_sub_five a
  have hprod : (7 * a - 3) * (7 * a - 2) =
      7 * (a * (7 * a - 5)) + 6 := by
    apply Nat.cast_injective (R := ℤ)
    push_cast
    have h1 : ((7 * a - 3 : ℕ) : ℤ) = 7 * (a : ℤ) - 3 := by omega
    have h2 : ((7 * a - 2 : ℕ) : ℤ) = 7 * (a : ℤ) - 2 := by omega
    have h3 : ((7 * a - 5 : ℕ) : ℤ) = 7 * (a : ℤ) - 5 := by omega
    rw [h1, h2, h3]
    ring
  rw [hprod, hq]
  omega

private theorem triangular_index_mod7_eq_three (j : ℕ)
    (h : (((j * (j + 1) / 2 : ℕ) : ZMod 7) = 3)) :
    j % 7 = 2 ∨ j % 7 = 4 := by
  rw [triangular_cast_eq_mod7] at h
  have hj : (j : ZMod 7) = ((j % 7 : ℕ) : ZMod 7) := natCast_zmod7_eq_mod j
  rw [hj] at h
  have hlt : j % 7 < 7 := Nat.mod_lt j (by decide)
  interval_cases j % 7 <;> norm_num at h ⊢
  all_goals exact absurd h (by decide)

private theorem neg_one_pow_zmod7_seven_mul_add_two (a : ℕ) :
    (-1 : ZMod 7) ^ (7 * a + 2) = (-1 : ZMod 7) ^ a := by
  rw [neg_one_pow_eq_pow_mod_two (R := ZMod 7) (7 * a + 2),
    neg_one_pow_eq_pow_mod_two (R := ZMod 7) a]
  have h : (7 * a + 2) % 2 = a % 2 := by omega
  rw [h]

private theorem neg_one_pow_zmod7_seven_mul_sub_three (a : ℕ) (ha : 0 < a) :
    (-1 : ZMod 7) ^ (7 * a - 3) = -((-1 : ZMod 7) ^ a) := by
  rw [neg_one_pow_eq_pow_mod_two (R := ZMod 7) (7 * a - 3)]
  have h : (7 * a - 3) % 2 = (a + 1) % 2 := by omega
  rw [h]
  rw [← neg_one_pow_eq_pow_mod_two (R := ZMod 7) (a + 1)]
  rw [pow_succ]
  ring

private theorem jacobi_seven_mul_sign_two_family (a : ℕ) :
    ((((-1 : ℤ) ^ (7 * a + 2) * (2 * (7 * a + 2) + 1) : ℤ) : ZMod 7)) =
      (5 : ZMod 7) * negOnePowInt (ZMod 7) (-(a : ℤ)) := by
  simp [negOnePowInt]
  rw [neg_one_pow_zmod7_seven_mul_add_two a]
  have hcoeff : (2 : ZMod 7) * (7 * (a : ZMod 7) + 2) + 1 = 5 := by
    have h7 : (7 : ZMod 7) = 0 := by decide
    rw [h7, zero_mul]
    norm_num
  rw [hcoeff]
  ring

private theorem jacobi_seven_mul_sign_four_family (a : ℕ) (ha : 0 < a) :
    ((((-1 : ℤ) ^ (7 * a - 3) * (2 * (7 * a - 3) + 1) : ℤ) : ZMod 7)) =
      (5 : ZMod 7) * negOnePowInt (ZMod 7) (a : ℤ) := by
  simp [negOnePowInt]
  rw [neg_one_pow_zmod7_seven_mul_sub_three a ha]
  have hcoeff : (2 : ZMod 7) * (7 * (a : ZMod 7) - 3) + 1 = -5 := by
    have h7 : (7 : ZMod 7) = 0 := by decide
    rw [h7, zero_mul]
    norm_num
  rw [hcoeff]
  ring

private theorem jacobiTripleSign_seven_mul_add_three_eq_theta7Coeff_five_zmod7
    (m : ℕ) :
    ((jacobiTripleSign (7 * m + 3) : ℤ) : ZMod 7) =
      (5 : ZMod 7) * theta7Coeff 5 (ZMod 7) m := by
  by_cases htri : ∃ j ≤ 7 * m + 3, 7 * m + 3 = j * (j + 1) / 2
  · obtain ⟨j, _hjle, hj⟩ := htri
    rw [hj, jacobiTripleSign_triangular]
    have htri_zmod : (((j * (j + 1) / 2 : ℕ) : ZMod 7) = 3) := by
      rw [← hj]
      push_cast
      change (7 : ZMod 7) * (m : ZMod 7) + 3 = 3
      have h7 : (7 : ZMod 7) = 0 := by decide
      rw [h7, zero_mul, zero_add]
    rcases triangular_index_mod7_eq_three j htri_zmod with hjmod | hjmod
    · let a := j / 7
      have hj_eq : j = 7 * a + 2 := by
        calc
          j = j % 7 + 7 * (j / 7) := (Nat.mod_add_div j 7).symm
          _ = 2 + 7 * a := by rw [hjmod]
          _ = 7 * a + 2 := by omega
      have hexp : theta7Exp 5 (-(a : ℤ)) = m := by
        rw [theta7Exp_five_neg_nat]
        apply Eq.symm
        exact Nat.eq_of_mul_eq_mul_left (n := 7) (by decide) (by
          have hformula := seven_mul_theta7Exp_five_neg_nat_formula a
          have hj_formula :
              (7 * a + 2) * (7 * a + 3) / 2 = j * (j + 1) / 2 := by
            rw [← hj_eq]
            have hs : 7 * a + 3 = j + 1 := by omega
            rw [hs]
          omega)
      rw [theta7Coeff_eq_of_exp (by right; right; rfl) m (-(a : ℤ)) hexp]
      rw [hj_eq]
      exact jacobi_seven_mul_sign_two_family a
    · let a := j / 7 + 1
      have ha : 0 < a := by omega
      have hj_eq : j = 7 * a - 3 := by
        calc
          j = j % 7 + 7 * (j / 7) := (Nat.mod_add_div j 7).symm
          _ = 4 + 7 * (j / 7) := by rw [hjmod]
          _ = 7 * a - 3 := by omega
      have hexp : theta7Exp 5 (a : ℤ) = m := by
        rw [theta7Exp_five_nat]
        apply Eq.symm
        exact Nat.eq_of_mul_eq_mul_left (n := 7) (by decide) (by
          have hformula := seven_mul_theta7Exp_five_nat_formula a ha
          have hj_formula :
              (7 * a - 3) * (7 * a - 2) / 2 = j * (j + 1) / 2 := by
            rw [← hj_eq]
            have hs : 7 * a - 2 = j + 1 := by omega
            rw [hs]
          omega)
      rw [theta7Coeff_eq_of_exp (by right; right; rfl) m (a : ℤ) hexp]
      rw [hj_eq]
      push_cast
      have hcast_sub_three :
          ((7 * a - 3 : ℕ) : ZMod 7) = 7 * (a : ZMod 7) - 3 := by
        have hs : 7 * a - 3 + 3 = 7 * a := by omega
        have hs_cast : (((7 * a - 3 + 3 : ℕ) : ZMod 7) =
            ((7 * a : ℕ) : ZMod 7)) := by
          exact congrArg (fun n : ℕ => (n : ZMod 7)) hs
        push_cast at hs_cast
        linear_combination hs_cast
      rw [hcast_sub_three]
      simpa using jacobi_seven_mul_sign_four_family a ha
  · push_neg at htri
    rw [jacobiTripleSign_of_not_triangular (7 * m + 3) htri]
    simp only [Int.cast_zero]
    have hcoeff_zero : theta7Coeff 5 (ZMod 7) m = 0 := by
      apply theta7Coeff_eq_zero_of_no_exp
      intro k hk
      cases k with
      | ofNat a =>
          change theta7Exp 5 (a : ℤ) = m at hk
          rw [theta7Exp_five_nat] at hk
          by_cases ha : a = 0
          · subst a
            simp at hk
            subst m
            exact htri 2 (by simp) (by simp)
          ·
            have ha_pos : 0 < a := by omega
            have hj : 7 * m + 3 = (7 * a - 3) * (7 * a - 2) / 2 := by
              rw [← seven_mul_theta7Exp_five_nat_formula a ha_pos, hk]
            have hsucc : 7 * a - 3 + 1 = 7 * a - 2 := by omega
            have hjle : 7 * a - 3 ≤ 7 * m + 3 := by
              rw [hj]
              rw [← hsucc]
              exact k_le_triangular (7 * a - 3)
            have hjtri :
                7 * m + 3 = (7 * a - 3) * (7 * a - 3 + 1) / 2 := by
              rwa [hsucc]
            exact htri (7 * a - 3) hjle hjtri
      | negSucc n =>
          let a := n + 1
          have hk' : theta7Exp 5 (-(a : ℤ)) = m := by
            change theta7Exp 5 (Int.negSucc n) = m
            exact hk
          rw [theta7Exp_five_neg_nat] at hk'
          have hj : 7 * m + 3 = (7 * a + 2) * (7 * a + 3) / 2 := by
            rw [← seven_mul_theta7Exp_five_neg_nat_formula, hk']
          have hsucc : 7 * a + 2 + 1 = 7 * a + 3 := by omega
          have hjle : 7 * a + 2 ≤ 7 * m + 3 := by
            rw [hj]
            rw [← hsucc]
            exact k_le_triangular (7 * a + 2)
          have hjtri :
              7 * m + 3 = (7 * a + 2) * (7 * a + 2 + 1) / 2 := by
            rwa [hsucc]
          exact htri (7 * a + 2) hjle hjtri
    rw [hcoeff_zero]
    ring

private theorem five_ps_zmod7_eq_C :
    (5 : (ZMod 7)⟦X⟧) = PowerSeries.C (5 : ZMod 7) := by
  exact (map_natCast (PowerSeries.C : ZMod 7 →+* (ZMod 7)⟦X⟧) 5).symm

theorem ASD7_3_eq_asd7KShiftedSeriesPS_zmod7 :
    ASD7 3 = (5 : (ZMod 7)⟦X⟧) * PowerSeries.X ^ 3 * asd7KSeriesPS (ZMod 7) := by
  ext n
  cases n with
  | zero =>
      rw [ASD7, coeff_section7]
      rw [mul_assoc, five_ps_zmod7_eq_C, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X_pow_mul']
      norm_num
  | succ n =>
      cases n with
      | zero =>
          rw [ASD7, coeff_section7]
          rw [mul_assoc, five_ps_zmod7_eq_C, PowerSeries.coeff_C_mul,
            PowerSeries.coeff_X_pow_mul']
          norm_num
      | succ n =>
          cases n with
          | zero =>
              rw [ASD7, coeff_section7]
              rw [mul_assoc, five_ps_zmod7_eq_C, PowerSeries.coeff_C_mul,
                PowerSeries.coeff_X_pow_mul']
              norm_num
          | succ n =>
              rw [ASD7, coeff_section7]
              rw [mul_assoc, five_ps_zmod7_eq_C, PowerSeries.coeff_C_mul]
              change (if (n + 3) % 7 = 3 then ((qPochInfPS (ZMod 7)) ^ 3).coeff (n + 3)
                else 0) =
                (5 : ZMod 7) * ((PowerSeries.X ^ 3 * asd7KSeriesPS (ZMod 7)).coeff (n + 3))
              rw [PowerSeries.coeff_X_pow_mul]
              by_cases hres : (n + 3) % 7 = 3
              · rw [if_pos hres]
                rw [QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS,
                  coeff_jacobiThetaPS]
                have hnmod : n % 7 = 0 := by omega
                have hdiv : 7 ∣ n := Nat.dvd_of_mod_eq_zero hnmod
                rw [coeff_asd7KSeriesPS, if_pos hdiv]
                have hn : 7 * (n / 7) = n := Nat.mul_div_cancel' hdiv
                calc
                  ((jacobiTripleSign (n + 3) : ℤ) : ZMod 7)
                      = ((jacobiTripleSign (7 * (n / 7) + 3) : ℤ) : ZMod 7) := by
                        rw [hn]
                  _ = (5 : ZMod 7) * theta7Coeff 5 (ZMod 7) (n / 7) :=
                      jacobiTripleSign_seven_mul_add_three_eq_theta7Coeff_five_zmod7 (n / 7)
              · rw [if_neg hres]
                have hnotdiv : ¬ 7 ∣ n := by omega
                rw [coeff_asd7KSeriesPS, if_neg hnotdiv, mul_zero]

theorem ASD7_3_eq_asd7KShiftedProductPS_zmod7 :
    ASD7 3 = asd7KShiftedProductPS := by
  rw [ASD7_3_eq_asd7KShiftedSeriesPS_zmod7]
  unfold asd7KShiftedProductPS
  rw [asd7KProductPS_eq_asd7KSeriesPS_zmod7]

/-! ## Unconditional ASD mod-7 eta-quotient congruences -/

/-- **ASD `7n`** (unconditional), section form. -/
theorem partition_section_0_eq_eta_product :
    section_kr (ZMod 7) 7 0 P7 =
      section_kr (ZMod 7) 7 0 ((asd7HProductPS (ZMod 7)) ^ 2) * P7 := by
  rw [partition_section_0_eq_over_Q7]
  unfold N0
  rw [ASD7_0_eq_asd7HProductPS_zmod7]

/-- **ASD `7n+1`** (unconditional), section form. -/
theorem partition_section_1_eq_eta_product :
    section_kr (ZMod 7) 7 1 P7 =
      section_kr (ZMod 7) 7 1
        ((2 : (ZMod 7)⟦X⟧) * asd7HProductPS (ZMod 7) *
          asd7JShiftedProductPS) * P7 := by
  rw [partition_section_1_eq_over_Q7]
  unfold N1
  rw [ASD7_0_eq_asd7HProductPS_zmod7, ASD7_1_eq_asd7JShiftedProductPS_zmod7]

/-- **ASD `7n+2`** (unconditional), section form. -/
theorem partition_section_2_eq_eta_product :
    section_kr (ZMod 7) 7 2 P7 =
      section_kr (ZMod 7) 7 2 (asd7JShiftedProductPS ^ 2) * P7 := by
  rw [partition_section_2_eq_over_Q7]
  unfold N2
  rw [ASD7_1_eq_asd7JShiftedProductPS_zmod7]

/-- **ASD `7n+3`** (unconditional), section form. -/
theorem partition_section_3_eq_eta_product :
    section_kr (ZMod 7) 7 3 P7 =
      section_kr (ZMod 7) 7 3
        ((2 : (ZMod 7)⟦X⟧) * asd7HProductPS (ZMod 7) *
          asd7KShiftedProductPS) * P7 := by
  rw [partition_section_3_eq_over_Q7]
  unfold N3
  rw [ASD7_0_eq_asd7HProductPS_zmod7, ASD7_3_eq_asd7KShiftedProductPS_zmod7]

/-- **ASD `7n+4`** (unconditional), section form. -/
theorem partition_section_4_eq_eta_product :
    section_kr (ZMod 7) 7 4 P7 =
      section_kr (ZMod 7) 7 4
        ((2 : (ZMod 7)⟦X⟧) * asd7JShiftedProductPS *
          asd7KShiftedProductPS) * P7 := by
  rw [partition_section_4_eq_over_Q7]
  unfold N4
  rw [ASD7_1_eq_asd7JShiftedProductPS_zmod7, ASD7_3_eq_asd7KShiftedProductPS_zmod7]

/-- **ASD `7n+5`** (unconditional): the clean zero section. -/
theorem partition_section_5_eq_zero_eta_product :
    section_kr (ZMod 7) 7 5 P7 = 0 :=
  partition_section_5_eq_zero

/-- **ASD `7n+6`** (unconditional), section form. -/
theorem partition_section_6_eq_eta_product :
    section_kr (ZMod 7) 7 6 P7 =
      section_kr (ZMod 7) 7 6 (asd7KShiftedProductPS ^ 2) * P7 := by
  rw [partition_section_6_eq_over_Q7]
  unfold N6
  rw [ASD7_3_eq_asd7KShiftedProductPS_zmod7]

end ASDMod7EtaQuotient
end Pending
end QseriesFormalization
