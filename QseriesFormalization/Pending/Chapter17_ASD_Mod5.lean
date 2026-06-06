import QseriesFormalization.Chapter17_PerTermAnalysis
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal

/-!
# Chapter 17 — Atkin-Swinnerton-Dyer congruences mod 5

This file records the mod-5 dissection used in Hirschhorn §3.6.
In `(ZMod 5)⟦X⟧`, Jacobi's cube identity shows that `(q;q)_∞^3`
has only residue `0` and residue `1` terms modulo `5`: triangular
exponents have residues `{0,1,3}`, but the `3` residue occurs exactly
when the Jacobi coefficient `2k+1` is zero in `ZMod 5`.
-/

namespace QseriesFormalization
namespace Pending
namespace ASDMod5

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartIV.Ch17
open QseriesFormalization.PartI.Ch04Franklin

/-- The 5-residue section of a formal power series over `R`: keep only
coefficients at indices `≡ r (mod 5)`, set the rest to zero. -/
noncomputable def section5 (R : Type*) [CommRing R] (r : ℕ) (φ : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk (fun n => if n % 5 = r then φ.coeff n else 0)

@[simp] theorem coeff_section5 (R : Type*) [CommRing R] (r : ℕ) (φ : R⟦X⟧)
    (n : ℕ) :
    (section5 R r φ).coeff n = if n % 5 = r then φ.coeff n else 0 := by
  rw [section5, PowerSeries.coeff_mk]

/-- A series is supported on one residue class modulo `5`. -/
def IsRes5 {R : Type*} [CommRing R] (r : ℕ) (φ : R⟦X⟧) : Prop :=
  ∀ n, n % 5 ≠ r → φ.coeff n = 0

theorem coeff_section5_of_ne (R : Type*) [CommRing R] (r : ℕ) (φ : R⟦X⟧)
    (n : ℕ) (h : n % 5 ≠ r) : (section5 R r φ).coeff n = 0 := by
  rw [coeff_section5, if_neg h]

theorem isRes5_section5 {R : Type*} [CommRing R] (r : ℕ) (φ : R⟦X⟧) :
    IsRes5 r (section5 R r φ) := by
  intro n hn
  exact coeff_section5_of_ne R r φ n hn

theorem natCast_zmod5_eq_mod (n : ℕ) :
    (n : ZMod 5) = ((n % 5 : ℕ) : ZMod 5) := by
  conv_lhs => rw [← Nat.mod_add_div n 5]
  push_cast
  have h5 : (5 : ZMod 5) = 0 := by decide
  rw [h5]
  ring

theorem zmod5_natCast_inj_of_lt {a b : ℕ} (ha : a < 5) (hb : b < 5)
    (h : ((a : ℕ) : ZMod 5) = ((b : ℕ) : ZMod 5)) : a = b := by
  interval_cases a <;> interval_cases b <;>
    first | rfl | exact absurd h (by decide)

/-- Off residues `0` and `1`, the Jacobi cube coefficient is zero in `ZMod 5`. -/
theorem jacobiTripleSign_zmod5_eq_zero_of_not_residue_zero_one
    (n : ℕ) (h0 : n % 5 ≠ 0) (h1 : n % 5 ≠ 1) :
    ((jacobiTripleSign n : ℤ) : ZMod 5) = 0 := by
  by_cases hzero : jacobiTripleSign n = 0
  · rw [hzero]
    simp
  obtain ⟨k, _hk_le, hk_eq, hk_sign⟩ :=
    QseriesFormalization.PartIV.Ch17.jacobiTripleSign_ne_zero_extract n hzero
  rw [hk_sign]
  by_cases h2k1 : (2 * (k : ZMod 5) + 1 : ZMod 5) = 0
  · push_cast
    rw [h2k1]
    ring
  · exfalso
    have hn_tri : (n : ZMod 5) = triangularMod5 (k : ZMod 5) := by
      rw [hk_eq, triangular_cast_eq_triangularMod5]
    rw [natCast_zmod5_eq_mod] at hn_tri
    have hlt : n % 5 < 5 := Nat.mod_lt n (by decide)
    rcases triangular_when_jacobi_nonzero (k : ZMod 5) h2k1 with htri | htri
    · rw [htri] at hn_tri
      exact h0 (zmod5_natCast_inj_of_lt hlt (by decide : 0 < (5 : ℕ)) hn_tri)
    · rw [htri] at hn_tri
      exact h1 (zmod5_natCast_inj_of_lt hlt (by decide : 1 < (5 : ℕ)) hn_tri)

/-- Off residues `0`, `1`, and `2`, the Euler pentagonal coefficient is zero
in `ZMod 5`. -/
theorem pentagonalSign_zmod5_eq_zero_of_not_residue_zero_one_two
    (n : ℕ) (h0 : n % 5 ≠ 0) (h1 : n % 5 ≠ 1) (h2 : n % 5 ≠ 2) :
    ((pentagonalSign n : ℤ) : ZMod 5) = 0 := by
  by_cases hzero : pentagonalSign n = 0
  · rw [hzero]
    simp
  obtain ⟨k, _hk_le, hk_side, hk_sign⟩ :=
    QseriesFormalization.PartIV.Ch17.pentagonalSign_ne_zero_extract n hzero
  rw [hk_sign]
  exfalso
  rcases hk_side with hk_minus | ⟨_hk_pos_plus, hk_plus⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simp at hk_minus
      subst n
      exact h0 rfl
    · have hn_pent :
          (n : ZMod 5) = pentagonalMod5Minus (k : ZMod 5) := by
        rw [hk_minus, pentagonal_minus_cast_eq_pentagonalMod5Minus k hk_pos]
      rw [natCast_zmod5_eq_mod] at hn_pent
      have hlt : n % 5 < 5 := Nat.mod_lt n (by decide)
      rcases pentagonalMod5Minus_range (k : ZMod 5) with hp | hp | hp
      · rw [hp] at hn_pent
        exact h0 (zmod5_natCast_inj_of_lt hlt (by decide : 0 < (5 : ℕ)) hn_pent)
      · rw [hp] at hn_pent
        exact h1 (zmod5_natCast_inj_of_lt hlt (by decide : 1 < (5 : ℕ)) hn_pent)
      · rw [hp] at hn_pent
        exact h2 (zmod5_natCast_inj_of_lt hlt (by decide : 2 < (5 : ℕ)) hn_pent)
  · have hn_pent :
        (n : ZMod 5) = pentagonalMod5 (k : ZMod 5) := by
      rw [hk_plus, pentagonal_plus_cast_eq_pentagonalMod5]
    rw [natCast_zmod5_eq_mod] at hn_pent
    have hlt : n % 5 < 5 := Nat.mod_lt n (by decide)
    rcases pentagonalMod5_range (k : ZMod 5) with hp | hp | hp
    · rw [hp] at hn_pent
      exact h0 (zmod5_natCast_inj_of_lt hlt (by decide : 0 < (5 : ℕ)) hn_pent)
    · rw [hp] at hn_pent
      exact h1 (zmod5_natCast_inj_of_lt hlt (by decide : 1 < (5 : ℕ)) hn_pent)
    · rw [hp] at hn_pent
      exact h2 (zmod5_natCast_inj_of_lt hlt (by decide : 2 < (5 : ℕ)) hn_pent)

/-- The residue-`r` component of `(qPochInfPS (ZMod 5))^3`. -/
noncomputable def A (r : ℕ) : (ZMod 5)⟦X⟧ :=
  section5 (ZMod 5) r ((qPochInfPS (ZMod 5)) ^ 3)

theorem isRes5_A (r : ℕ) : IsRes5 r (A r) := by
  exact isRes5_section5 r ((qPochInfPS (ZMod 5)) ^ 3)

/-- Hirschhorn §3.6, equation (3.6.4) in residue-section form:
`(q;q)_∞^3` over `ZMod 5` is the sum of its residue `0` and residue `1`
parts.  These are the formal counterparts of `F(q^5)` and `-3q G(q^5)`. -/
theorem qPochInfPS_cube_decompose_mod_5 :
    (qPochInfPS (ZMod 5)) ^ 3 = A 0 + A 1 := by
  ext n
  have hB2 :
      ((qPochInfPS (ZMod 5)) ^ 3).coeff n =
        ((jacobiTripleSign n : ℤ) : ZMod 5) := by
    rw [QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS]
    rw [coeff_jacobiThetaPS]
  have hRHS :
      (A 0 + A 1 : (ZMod 5)⟦X⟧).coeff n =
        (if n % 5 = 0 then ((qPochInfPS (ZMod 5)) ^ 3).coeff n else 0) +
        (if n % 5 = 1 then ((qPochInfPS (ZMod 5)) ^ 3).coeff n else 0) := by
    simp only [A, section5, map_add, coeff_mk]
  rw [hRHS]
  have h_zero_off :
      n % 5 ≠ 0 → n % 5 ≠ 1 →
        ((qPochInfPS (ZMod 5)) ^ 3).coeff n = 0 := by
    intro h0 h1
    rw [hB2]
    exact jacobiTripleSign_zmod5_eq_zero_of_not_residue_zero_one n h0 h1
  have hlt : n % 5 < 5 := Nat.mod_lt n (by decide)
  interval_cases n % 5 <;> simp_all

theorem coeff_A_sum_eq_zero_of_not_residue_zero_one
    (n : ℕ) (h0 : n % 5 ≠ 0) (h1 : n % 5 ≠ 1) :
    (A 0 + A 1 : (ZMod 5)⟦X⟧).coeff n = 0 := by
  simp [A, coeff_section5, h0, h1]

theorem coeff_qPochInfPS_zmod5_eq_zero_of_not_residue_zero_one_two
    (n : ℕ) (h0 : n % 5 ≠ 0) (h1 : n % 5 ≠ 1) (h2 : n % 5 ≠ 2) :
    (qPochInfPS (ZMod 5)).coeff n = 0 := by
  rw [coeff_qPochInfPS_eq_pentagonalSign]
  exact pentagonalSign_zmod5_eq_zero_of_not_residue_zero_one_two n h0 h1 h2

/-- The dissection gives the vanishing needed for Ramanujan's mod-5
congruence: the `5n+4` coefficient of `(q;q)_∞^4` is zero in `ZMod 5`. -/
theorem coeff_qPochInfPS_pow_four_at_5n_plus_4_eq_zero (n : ℕ) :
    ((qPochInfPS (ZMod 5)) ^ 4).coeff (5 * n + 4) = 0 := by
  have h_pow4 :
      (qPochInfPS (ZMod 5)) ^ 4 = (A 0 + A 1) * qPochInfPS (ZMod 5) := by
    calc
      (qPochInfPS (ZMod 5)) ^ 4
          = (qPochInfPS (ZMod 5)) ^ 3 * qPochInfPS (ZMod 5) := by ring
      _ = (A 0 + A 1) * qPochInfPS (ZMod 5) := by
        rw [qPochInfPS_cube_decompose_mod_5]
  rw [h_pow4, PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  have hmod : ((i % 5 + j % 5) % 5) = 4 := by
    calc
      (i % 5 + j % 5) % 5 = (i + j) % 5 := (Nat.add_mod i j 5).symm
      _ = (5 * n + 4) % 5 := by rw [hij]
      _ = 4 := by omega
  by_cases hi : i % 5 = 0 ∨ i % 5 = 1
  · by_cases hj : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2
    · exfalso
      rcases hi with hi0 | hi1
      · rcases hj with hj0 | hj12
        · rw [hi0, hj0] at hmod
          norm_num at hmod
        · rcases hj12 with hj1 | hj2
          · rw [hi0, hj1] at hmod
            norm_num at hmod
          · rw [hi0, hj2] at hmod
            norm_num at hmod
      · rcases hj with hj0 | hj12
        · rw [hi1, hj0] at hmod
          norm_num at hmod
        · rcases hj12 with hj1 | hj2
          · rw [hi1, hj1] at hmod
            norm_num at hmod
          · rw [hi1, hj2] at hmod
            norm_num at hmod
    · push_neg at hj
      rw [coeff_qPochInfPS_zmod5_eq_zero_of_not_residue_zero_one_two j hj.1 hj.2.1 hj.2.2,
        mul_zero]
  · push_neg at hi
    rw [coeff_A_sum_eq_zero_of_not_residue_zero_one i hi.1 hi.2, zero_mul]

/-- Ramanujan's first congruence, obtained from the residue-4 vanishing. -/
theorem ramanujan_5_dvd_p_5n_plus_4 :
    ∀ n, 5 ∣ QseriesFormalization.Ch01.partitionCount (5 * n + 4) := by
  intro n
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply (ZMod.natCast_eq_zero_iff _ 5).mp
  refine ramanujan_from_pochInf_vanishes 5 (by decide) 4 (by decide) ?_ n
  intro m
  exact coeff_qPochInfPS_pow_four_at_5n_plus_4_eq_zero m

theorem ramanujan_partition_5n_plus_4_eq_zero_mod_5 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (5 * n + 4) : ℕ) : ZMod 5) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 5).mpr (ramanujan_5_dvd_p_5n_plus_4 n)

end ASDMod5
end Pending
end QseriesFormalization
