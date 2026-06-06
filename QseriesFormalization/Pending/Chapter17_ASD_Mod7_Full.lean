import QseriesFormalization.Pending.Chapter17_ASD_Mod7
import QseriesFormalization.Chapter19_Section5

/-!
# Chapter 17 — Full mod-7 ASD residue extraction

This file continues `Pending.Chapter17_ASD_Mod7`.  It keeps the
Atkin--Swinnerton-Dyer mod-7 dissection in terms of the already-proved section
components

* `ASD7 0`, the residue-0 component of `(q;q)_∞^3`;
* `ASD7 1`, the residue-1 component of `(q;q)_∞^3`;
* `ASD7 3`, the residue-3 component of `(q;q)_∞^3`.

After Frobenius, the denominator-cleared form of Hirschhorn §3.7 is

`partitionGenFun * expand 7 qPochInfPS = (ASD7 0 + ASD7 1 + ASD7 3)^2`

in `(ZMod 7)⟦X⟧`.  Applying the compressed `7`-section operator gives the
seven generating-function congruences, with the right-hand side still written
in section-component form.  The residue-5 section vanishes.
-/

namespace QseriesFormalization
namespace Pending
namespace ASDMod7Full

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Hirschhorn7

/-- Extracting a residue class through multiplication by an expanded series.

The right factor has only exponents divisible by `p`, so the compressed
`p`-section of `f * expand p g` is the product of the compressed section of `f`
and `g`. -/
theorem section_kr_mul_expand (R : Type*) [CommRing R] (p : ℕ) (hp : p ≠ 0)
    (f g : R⟦X⟧) (r : ℕ) (hr : r < p) :
    section_kr R p r (f * PowerSeries.expand p hp g) =
      section_kr R p r f * g := by
  ext n
  rw [coeff_section_kr]
  rw [coeff_mul_expand_of_lt R p hp f g n r hr]
  rw [PowerSeries.coeff_mul]
  rw [← Finset.Nat.sum_antidiagonal_swap
    (f := fun ij : ℕ × ℕ =>
      (section_kr R p r f).coeff ij.1 * g.coeff ij.2)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  rw [coeff_section_kr]
  simp

noncomputable abbrev Q7 : (ZMod 7)⟦X⟧ :=
  qPochInfPS (ZMod 7)

noncomputable abbrev D7 : (ZMod 7)⟦X⟧ :=
  PowerSeries.expand 7 (by decide) Q7

noncomputable abbrev P7 : (ZMod 7)⟦X⟧ :=
  partitionGenFun (ZMod 7)

noncomputable abbrev S7 : (ZMod 7)⟦X⟧ :=
  ASD7 0 + ASD7 1 + ASD7 3

/-- Frobenius identifies the expanded Euler product with the seventh power. -/
theorem D7_eq_Q7_pow_seven : D7 = Q7 ^ 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact PowerSeries.expand_eq_pow_zmod 7 (by decide) Q7

/-- The ASD section sum is `(q;q)_∞^3`. -/
theorem S7_eq_Q7_cube : S7 = Q7 ^ 3 := by
  exact qPochInfPS_cube_decompose_mod_7.symm

/-- Denominator-cleared Hirschhorn §3.7 identity over `ZMod 7`. -/
theorem partitionGenFun_mul_D7_eq_S7_sq :
    P7 * D7 = S7 ^ 2 := by
  calc
    P7 * D7 = P7 * Q7 ^ 7 := by rw [D7_eq_Q7_pow_seven]
    _ = (P7 * Q7) * Q7 ^ 6 := by ring
    _ = Q7 ^ 6 := by rw [partitionGenFun_mul_qPochInfPS (ZMod 7)]; ring
    _ = (Q7 ^ 3) ^ 2 := by ring
    _ = S7 ^ 2 := by rw [S7_eq_Q7_cube]

/-- Residue extraction of the denominator-cleared identity. -/
theorem section_partitionGenFun_mul_Q7_eq_section_S7_sq (r : ℕ) (hr : r < 7) :
    section_kr (ZMod 7) 7 r P7 * Q7 =
      section_kr (ZMod 7) 7 r (S7 ^ 2) := by
  have h := congrArg (section_kr (ZMod 7) 7 r) partitionGenFun_mul_D7_eq_S7_sq
  rw [section_kr_mul_expand (ZMod 7) 7 (by decide) P7 Q7 r hr] at h
  exact h

/-- Multiplication adds mod-7 supports. -/
theorem isRes7_mul {R : Type*} [CommRing R] {r s : ℕ} {φ ψ : R⟦X⟧}
    (hφ : IsRes7 r φ) (hψ : IsRes7 s ψ) :
    IsRes7 ((r + s) % 7) (φ * ψ) := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  by_cases hi : i % 7 = r
  · by_cases hj : j % 7 = s
    · exfalso
      apply hn
      rw [← hij, Nat.add_mod, hi, hj]
    · change φ.coeff i * ψ.coeff j = 0
      rw [hψ j hj, mul_zero]
  · change φ.coeff i * ψ.coeff j = 0
    rw [hφ i hi, zero_mul]

/-- Powers multiply the support residue. -/
theorem isRes7_pow {R : Type*} [CommRing R] {r : ℕ} {φ : R⟦X⟧}
    (hφ : IsRes7 r φ) :
    ∀ m, IsRes7 ((m * r) % 7) (φ ^ m)
  | 0 => by
      intro n hn
      rw [pow_zero]
      by_cases hn0 : n = 0
      · subst hn0
        simp at hn
      · rw [PowerSeries.coeff_one]
        simp [hn0]
  | m + 1 => by
      have hm := isRes7_pow hφ m
      simpa [Nat.succ_mul, Nat.add_mod, Nat.mod_mod, pow_succ]
        using isRes7_mul hm hφ

/-- Multiplication by a scalar power series does not change mod-7 support. -/
theorem isRes7_natCast_mul {R : Type*} [CommRing R] (c r : ℕ) {φ : R⟦X⟧}
    (hφ : IsRes7 r φ) :
    IsRes7 r ((c : R⟦X⟧) * φ) := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  by_cases hi : i = 0
  · subst hi
    have hj : j = n := by omega
    rw [hj, hφ n hn, mul_zero]
  · have hcoeff : ((c : R⟦X⟧).coeff i) = 0 := by
      rw [show (c : R⟦X⟧) = (PowerSeries.C : R →+* R⟦X⟧) (c : R) by
        exact (map_natCast (PowerSeries.C : R →+* R⟦X⟧) c).symm]
      rw [PowerSeries.coeff_C]
      simp [hi]
    rw [hcoeff, zero_mul]

/-- A compressed section vanishes on a series supported on a different residue. -/
theorem section_kr_eq_zero_of_isRes7_ne {R : Type*} [CommRing R]
    {target r : ℕ} (htarget : target < 7) {φ : R⟦X⟧}
    (htr : target ≠ r) (hφ : IsRes7 r φ) :
    section_kr R 7 target φ = 0 := by
  ext n
  rw [coeff_section_kr, map_zero]
  apply hφ
  have hmod : (7 * n + target) % 7 = target := by omega
  rw [hmod]
  exact htr

noncomputable abbrev N0 : (ZMod 7)⟦X⟧ :=
  (ASD7 0) ^ 2

noncomputable abbrev N1 : (ZMod 7)⟦X⟧ :=
  (2 : (ZMod 7)⟦X⟧) * ASD7 0 * ASD7 1

noncomputable abbrev N2 : (ZMod 7)⟦X⟧ :=
  (ASD7 1) ^ 2

noncomputable abbrev N3 : (ZMod 7)⟦X⟧ :=
  (2 : (ZMod 7)⟦X⟧) * ASD7 0 * ASD7 3

noncomputable abbrev N4 : (ZMod 7)⟦X⟧ :=
  (2 : (ZMod 7)⟦X⟧) * ASD7 1 * ASD7 3

noncomputable abbrev N6 : (ZMod 7)⟦X⟧ :=
  (ASD7 3) ^ 2

/-- Quadratic expansion of the ASD numerator. -/
theorem S7_sq_expand :
    S7 ^ 2 = N0 + N1 + N2 + N3 + N4 + N6 := by
  simp only [S7, N0, N1, N2, N3, N4, N6]
  ring

theorem isRes7_N0 : IsRes7 0 N0 := by
  simpa [N0] using isRes7_pow (isRes7_ASD7 0) 2

theorem isRes7_N1 : IsRes7 1 N1 := by
  have hprod : IsRes7 1 (ASD7 0 * ASD7 1) := by
    simpa using isRes7_mul (isRes7_ASD7 0) (isRes7_ASD7 1)
  simpa [N1, mul_assoc] using isRes7_natCast_mul (R := ZMod 7) 2 1 hprod

theorem isRes7_N2 : IsRes7 2 N2 := by
  simpa [N2] using isRes7_pow (isRes7_ASD7 1) 2

theorem isRes7_N3 : IsRes7 3 N3 := by
  have hprod : IsRes7 3 (ASD7 0 * ASD7 3) := by
    simpa using isRes7_mul (isRes7_ASD7 0) (isRes7_ASD7 3)
  simpa [N3, mul_assoc] using isRes7_natCast_mul (R := ZMod 7) 2 3 hprod

theorem isRes7_N4 : IsRes7 4 N4 := by
  have hprod : IsRes7 4 (ASD7 1 * ASD7 3) := by
    simpa using isRes7_mul (isRes7_ASD7 1) (isRes7_ASD7 3)
  simpa [N4, mul_assoc] using isRes7_natCast_mul (R := ZMod 7) 2 4 hprod

theorem isRes7_N6 : IsRes7 6 N6 := by
  simpa [N6] using isRes7_pow (isRes7_ASD7 3) 2

theorem section_S7_sq_0 :
    section_kr (ZMod 7) 7 0 (S7 ^ 2) = section_kr (ZMod 7) 7 0 N0 := by
  rw [S7_sq_expand]
  simp only [section_kr_add]
  rw [section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 0) (r := 1)
      (by decide) (by decide) isRes7_N1,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 0) (r := 2)
      (by decide) (by decide) isRes7_N2,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 0) (r := 3)
      (by decide) (by decide) isRes7_N3,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 0) (r := 4)
      (by decide) (by decide) isRes7_N4,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 0) (r := 6)
      (by decide) (by decide) isRes7_N6]
  ring

theorem section_S7_sq_1 :
    section_kr (ZMod 7) 7 1 (S7 ^ 2) = section_kr (ZMod 7) 7 1 N1 := by
  rw [S7_sq_expand]
  simp only [section_kr_add]
  rw [section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 1) (r := 0)
      (by decide) (by decide) isRes7_N0,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 1) (r := 2)
      (by decide) (by decide) isRes7_N2,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 1) (r := 3)
      (by decide) (by decide) isRes7_N3,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 1) (r := 4)
      (by decide) (by decide) isRes7_N4,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 1) (r := 6)
      (by decide) (by decide) isRes7_N6]
  ring

theorem section_S7_sq_2 :
    section_kr (ZMod 7) 7 2 (S7 ^ 2) = section_kr (ZMod 7) 7 2 N2 := by
  rw [S7_sq_expand]
  simp only [section_kr_add]
  rw [section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 2) (r := 0)
      (by decide) (by decide) isRes7_N0,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 2) (r := 1)
      (by decide) (by decide) isRes7_N1,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 2) (r := 3)
      (by decide) (by decide) isRes7_N3,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 2) (r := 4)
      (by decide) (by decide) isRes7_N4,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 2) (r := 6)
      (by decide) (by decide) isRes7_N6]
  ring

theorem section_S7_sq_3 :
    section_kr (ZMod 7) 7 3 (S7 ^ 2) = section_kr (ZMod 7) 7 3 N3 := by
  rw [S7_sq_expand]
  simp only [section_kr_add]
  rw [section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 3) (r := 0)
      (by decide) (by decide) isRes7_N0,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 3) (r := 1)
      (by decide) (by decide) isRes7_N1,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 3) (r := 2)
      (by decide) (by decide) isRes7_N2,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 3) (r := 4)
      (by decide) (by decide) isRes7_N4,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 3) (r := 6)
      (by decide) (by decide) isRes7_N6]
  ring

theorem section_S7_sq_4 :
    section_kr (ZMod 7) 7 4 (S7 ^ 2) = section_kr (ZMod 7) 7 4 N4 := by
  rw [S7_sq_expand]
  simp only [section_kr_add]
  rw [section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 4) (r := 0)
      (by decide) (by decide) isRes7_N0,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 4) (r := 1)
      (by decide) (by decide) isRes7_N1,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 4) (r := 2)
      (by decide) (by decide) isRes7_N2,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 4) (r := 3)
      (by decide) (by decide) isRes7_N3,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 4) (r := 6)
      (by decide) (by decide) isRes7_N6]
  ring

theorem section_S7_sq_5 :
    section_kr (ZMod 7) 7 5 (S7 ^ 2) = 0 := by
  rw [S7_sq_expand]
  simp only [section_kr_add]
  rw [section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 5) (r := 0)
      (by decide) (by decide) isRes7_N0,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 5) (r := 1)
      (by decide) (by decide) isRes7_N1,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 5) (r := 2)
      (by decide) (by decide) isRes7_N2,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 5) (r := 3)
      (by decide) (by decide) isRes7_N3,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 5) (r := 4)
      (by decide) (by decide) isRes7_N4,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 5) (r := 6)
      (by decide) (by decide) isRes7_N6]
  ring

theorem section_S7_sq_6 :
    section_kr (ZMod 7) 7 6 (S7 ^ 2) = section_kr (ZMod 7) 7 6 N6 := by
  rw [S7_sq_expand]
  simp only [section_kr_add]
  rw [section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 6) (r := 0)
      (by decide) (by decide) isRes7_N0,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 6) (r := 1)
      (by decide) (by decide) isRes7_N1,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 6) (r := 2)
      (by decide) (by decide) isRes7_N2,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 6) (r := 3)
      (by decide) (by decide) isRes7_N3,
    section_kr_eq_zero_of_isRes7_ne (R := ZMod 7) (target := 6) (r := 4)
      (by decide) (by decide) isRes7_N4]
  ring

/-- The `7n` generating-function congruence, denominator-cleared by `(q;q)_∞`. -/
theorem partition_section_0_mul_Q7 :
    section_kr (ZMod 7) 7 0 P7 * Q7 =
      section_kr (ZMod 7) 7 0 N0 := by
  rw [section_partitionGenFun_mul_Q7_eq_section_S7_sq 0 (by decide),
    section_S7_sq_0]

/-- The `7n+1` generating-function congruence, denominator-cleared by `(q;q)_∞`. -/
theorem partition_section_1_mul_Q7 :
    section_kr (ZMod 7) 7 1 P7 * Q7 =
      section_kr (ZMod 7) 7 1 N1 := by
  rw [section_partitionGenFun_mul_Q7_eq_section_S7_sq 1 (by decide),
    section_S7_sq_1]

/-- The `7n+2` generating-function congruence, denominator-cleared by `(q;q)_∞`. -/
theorem partition_section_2_mul_Q7 :
    section_kr (ZMod 7) 7 2 P7 * Q7 =
      section_kr (ZMod 7) 7 2 N2 := by
  rw [section_partitionGenFun_mul_Q7_eq_section_S7_sq 2 (by decide),
    section_S7_sq_2]

/-- The `7n+3` generating-function congruence, denominator-cleared by `(q;q)_∞`. -/
theorem partition_section_3_mul_Q7 :
    section_kr (ZMod 7) 7 3 P7 * Q7 =
      section_kr (ZMod 7) 7 3 N3 := by
  rw [section_partitionGenFun_mul_Q7_eq_section_S7_sq 3 (by decide),
    section_S7_sq_3]

/-- The `7n+4` generating-function congruence, denominator-cleared by `(q;q)_∞`. -/
theorem partition_section_4_mul_Q7 :
    section_kr (ZMod 7) 7 4 P7 * Q7 =
      section_kr (ZMod 7) 7 4 N4 := by
  rw [section_partitionGenFun_mul_Q7_eq_section_S7_sq 4 (by decide),
    section_S7_sq_4]

/-- The `7n+5` section vanishes after multiplication by `(q;q)_∞`. -/
theorem partition_section_5_mul_Q7 :
    section_kr (ZMod 7) 7 5 P7 * Q7 = 0 := by
  rw [section_partitionGenFun_mul_Q7_eq_section_S7_sq 5 (by decide),
    section_S7_sq_5]

/-- The `7n+6` generating-function congruence, denominator-cleared by `(q;q)_∞`. -/
theorem partition_section_6_mul_Q7 :
    section_kr (ZMod 7) 7 6 P7 * Q7 =
      section_kr (ZMod 7) 7 6 N6 := by
  rw [section_partitionGenFun_mul_Q7_eq_section_S7_sq 6 (by decide),
    section_S7_sq_6]

/-- `P7` is the formal inverse of `Q7`. -/
theorem Q7_mul_P7 : Q7 * P7 = 1 := by
  exact qPochInfPS_mul_partitionGenFun (ZMod 7)

/-- The `7n` generating-function congruence in divided form. -/
theorem partition_section_0_eq_over_Q7 :
    section_kr (ZMod 7) 7 0 P7 =
      section_kr (ZMod 7) 7 0 N0 * P7 := by
  calc
    section_kr (ZMod 7) 7 0 P7 =
        section_kr (ZMod 7) 7 0 P7 * 1 := by rw [mul_one]
    _ = section_kr (ZMod 7) 7 0 P7 * (Q7 * P7) := by
        rw [Q7_mul_P7]
    _ = (section_kr (ZMod 7) 7 0 P7 * Q7) * P7 := by ring
    _ = section_kr (ZMod 7) 7 0 N0 * P7 := by
        rw [partition_section_0_mul_Q7]

/-- The `7n+1` generating-function congruence in divided form. -/
theorem partition_section_1_eq_over_Q7 :
    section_kr (ZMod 7) 7 1 P7 =
      section_kr (ZMod 7) 7 1 N1 * P7 := by
  calc
    section_kr (ZMod 7) 7 1 P7 =
        section_kr (ZMod 7) 7 1 P7 * 1 := by rw [mul_one]
    _ = section_kr (ZMod 7) 7 1 P7 * (Q7 * P7) := by
        rw [Q7_mul_P7]
    _ = (section_kr (ZMod 7) 7 1 P7 * Q7) * P7 := by ring
    _ = section_kr (ZMod 7) 7 1 N1 * P7 := by
        rw [partition_section_1_mul_Q7]

/-- The `7n+2` generating-function congruence in divided form. -/
theorem partition_section_2_eq_over_Q7 :
    section_kr (ZMod 7) 7 2 P7 =
      section_kr (ZMod 7) 7 2 N2 * P7 := by
  calc
    section_kr (ZMod 7) 7 2 P7 =
        section_kr (ZMod 7) 7 2 P7 * 1 := by rw [mul_one]
    _ = section_kr (ZMod 7) 7 2 P7 * (Q7 * P7) := by
        rw [Q7_mul_P7]
    _ = (section_kr (ZMod 7) 7 2 P7 * Q7) * P7 := by ring
    _ = section_kr (ZMod 7) 7 2 N2 * P7 := by
        rw [partition_section_2_mul_Q7]

/-- The `7n+3` generating-function congruence in divided form. -/
theorem partition_section_3_eq_over_Q7 :
    section_kr (ZMod 7) 7 3 P7 =
      section_kr (ZMod 7) 7 3 N3 * P7 := by
  calc
    section_kr (ZMod 7) 7 3 P7 =
        section_kr (ZMod 7) 7 3 P7 * 1 := by rw [mul_one]
    _ = section_kr (ZMod 7) 7 3 P7 * (Q7 * P7) := by
        rw [Q7_mul_P7]
    _ = (section_kr (ZMod 7) 7 3 P7 * Q7) * P7 := by ring
    _ = section_kr (ZMod 7) 7 3 N3 * P7 := by
        rw [partition_section_3_mul_Q7]

/-- The `7n+4` generating-function congruence in divided form. -/
theorem partition_section_4_eq_over_Q7 :
    section_kr (ZMod 7) 7 4 P7 =
      section_kr (ZMod 7) 7 4 N4 * P7 := by
  calc
    section_kr (ZMod 7) 7 4 P7 =
        section_kr (ZMod 7) 7 4 P7 * 1 := by rw [mul_one]
    _ = section_kr (ZMod 7) 7 4 P7 * (Q7 * P7) := by
        rw [Q7_mul_P7]
    _ = (section_kr (ZMod 7) 7 4 P7 * Q7) * P7 := by ring
    _ = section_kr (ZMod 7) 7 4 N4 * P7 := by
        rw [partition_section_4_mul_Q7]

/-- The `7n+5` generating-function congruence in divided form. -/
theorem partition_section_5_eq_zero :
    section_kr (ZMod 7) 7 5 P7 = 0 := by
  calc
    section_kr (ZMod 7) 7 5 P7 =
        section_kr (ZMod 7) 7 5 P7 * 1 := by rw [mul_one]
    _ = section_kr (ZMod 7) 7 5 P7 * (Q7 * P7) := by
        rw [Q7_mul_P7]
    _ = (section_kr (ZMod 7) 7 5 P7 * Q7) * P7 := by ring
    _ = 0 := by rw [partition_section_5_mul_Q7]; ring

/-- The `7n+6` generating-function congruence in divided form. -/
theorem partition_section_6_eq_over_Q7 :
    section_kr (ZMod 7) 7 6 P7 =
      section_kr (ZMod 7) 7 6 N6 * P7 := by
  calc
    section_kr (ZMod 7) 7 6 P7 =
        section_kr (ZMod 7) 7 6 P7 * 1 := by rw [mul_one]
    _ = section_kr (ZMod 7) 7 6 P7 * (Q7 * P7) := by
        rw [Q7_mul_P7]
    _ = (section_kr (ZMod 7) 7 6 P7 * Q7) * P7 := by ring
    _ = section_kr (ZMod 7) 7 6 N6 * P7 := by
        rw [partition_section_6_mul_Q7]

/-- Coefficient form of the `7n+5` sanity-check vanishing. -/
theorem partition_7n_plus_5_eq_zero_mod_7 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (7 * n + 5) : ℕ) : ZMod 7) = 0 := by
  have hcoeff := congrArg (fun φ : (ZMod 7)⟦X⟧ => φ.coeff n) partition_section_5_eq_zero
  have hcoeff' : (section_kr (ZMod 7) 7 5 P7).coeff n = 0 := by
    simpa using hcoeff
  rw [P7, coeff_section_kr, coeff_partitionGenFun] at hcoeff'
  simpa [QseriesFormalization.Ch01.partitionCount] using hcoeff'

end ASDMod7Full
end Pending
end QseriesFormalization
