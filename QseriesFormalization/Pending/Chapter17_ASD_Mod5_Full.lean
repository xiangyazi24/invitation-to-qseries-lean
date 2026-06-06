import QseriesFormalization.Pending.Chapter17_ASD_Mod5
import QseriesFormalization.Chapter19_Section5

/-!
# Chapter 17 — Full mod-5 ASD residue extraction

This file continues `Pending.Chapter17_ASD_Mod5`.  It keeps the
Atkin--Swinnerton-Dyer mod-5 dissection in terms of the already-proved section
components

* `A 0`, the residue-0 component of `(q;q)_∞^3`;
* `A 1`, the residue-1 component of `(q;q)_∞^3`.

After Frobenius, the denominator-cleared form of Hirschhorn §3.6 is

`partitionGenFun * (expand 5 qPochInfPS)^2 = (A 0 + A 1)^3`

in `(ZMod 5)⟦X⟧`.  Applying the compressed `5`-section operator gives the five
generating-function congruences, with the right-hand side still written in
section-component form.
-/

namespace QseriesFormalization
namespace Pending
namespace ASDMod5Full

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.ASDMod5

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

noncomputable abbrev Q5 : (ZMod 5)⟦X⟧ :=
  qPochInfPS (ZMod 5)

noncomputable abbrev D5 : (ZMod 5)⟦X⟧ :=
  PowerSeries.expand 5 (by decide) Q5

noncomputable abbrev P5 : (ZMod 5)⟦X⟧ :=
  partitionGenFun (ZMod 5)

noncomputable abbrev S5 : (ZMod 5)⟦X⟧ :=
  A 0 + A 1

/-- Frobenius identifies the expanded Euler product with the fifth power. -/
theorem D5_eq_Q5_pow_five : D5 = Q5 ^ 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact PowerSeries.expand_eq_pow_zmod 5 (by decide) Q5

/-- The ASD section sum is `(q;q)_∞^3`. -/
theorem S5_eq_Q5_cube : S5 = Q5 ^ 3 := by
  exact qPochInfPS_cube_decompose_mod_5.symm

/-- Denominator-cleared Hirschhorn §3.6 identity over `ZMod 5`. -/
theorem partitionGenFun_mul_D5_sq_eq_S5_cube :
    P5 * D5 ^ 2 = S5 ^ 3 := by
  calc
    P5 * D5 ^ 2 = P5 * (Q5 ^ 5) ^ 2 := by rw [D5_eq_Q5_pow_five]
    _ = P5 * Q5 ^ 10 := by ring
    _ = (P5 * Q5) * Q5 ^ 9 := by ring
    _ = Q5 ^ 9 := by rw [partitionGenFun_mul_qPochInfPS (ZMod 5)]; ring
    _ = (Q5 ^ 3) ^ 3 := by ring
    _ = S5 ^ 3 := by rw [S5_eq_Q5_cube]

/-- The squared expanded denominator is the expansion of `(q;q)_∞²`. -/
theorem D5_sq_eq_expand_Q5_sq :
    D5 ^ 2 = PowerSeries.expand 5 (by decide) (Q5 ^ 2) := by
  change (PowerSeries.expand 5 (by decide) Q5) ^ 2 =
    PowerSeries.expand 5 (by decide) (Q5 ^ 2)
  rw [show Q5 ^ 2 = Q5 * Q5 by ring, sq]
  change PowerSeries.expand 5 (by decide) Q5 * PowerSeries.expand 5 (by decide) Q5 =
    PowerSeries.expand 5 (by decide) (Q5 * Q5)
  rw [← map_mul]

/-- Residue extraction of the denominator-cleared identity. -/
theorem section_partitionGenFun_mul_Q5_sq_eq_section_S5_cube (r : ℕ) (hr : r < 5) :
    section_kr (ZMod 5) 5 r P5 * Q5 ^ 2 =
      section_kr (ZMod 5) 5 r (S5 ^ 3) := by
  have h := congrArg (section_kr (ZMod 5) 5 r) partitionGenFun_mul_D5_sq_eq_S5_cube
  rw [D5_sq_eq_expand_Q5_sq] at h
  rw [section_kr_mul_expand (ZMod 5) 5 (by decide) P5 (Q5 ^ 2) r hr] at h
  exact h

/-- Multiplication adds mod-5 supports. -/
theorem isRes5_mul {R : Type*} [CommRing R] {r s : ℕ} {φ ψ : R⟦X⟧}
    (hφ : IsRes5 r φ) (hψ : IsRes5 s ψ) :
    IsRes5 ((r + s) % 5) (φ * ψ) := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  by_cases hi : i % 5 = r
  · by_cases hj : j % 5 = s
    · exfalso
      apply hn
      rw [← hij, Nat.add_mod, hi, hj]
    · change φ.coeff i * ψ.coeff j = 0
      rw [hψ j hj, mul_zero]
  · change φ.coeff i * ψ.coeff j = 0
    rw [hφ i hi, zero_mul]

/-- Powers multiply the support residue. -/
theorem isRes5_pow {R : Type*} [CommRing R] {r : ℕ} {φ : R⟦X⟧}
    (hφ : IsRes5 r φ) :
    ∀ m, IsRes5 ((m * r) % 5) (φ ^ m)
  | 0 => by
      intro n hn
      rw [pow_zero]
      by_cases hn0 : n = 0
      · subst hn0
        simp at hn
      · rw [PowerSeries.coeff_one]
        simp [hn0]
  | m + 1 => by
      have hm := isRes5_pow hφ m
      simpa [Nat.succ_mul, Nat.add_mod, Nat.mod_mod, pow_succ]
        using isRes5_mul hm hφ

/-- Multiplication by a scalar power series does not change mod-5 support. -/
theorem isRes5_natCast_mul {R : Type*} [CommRing R] (c r : ℕ) {φ : R⟦X⟧}
    (hφ : IsRes5 r φ) :
    IsRes5 r ((c : R⟦X⟧) * φ) := by
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
theorem section_kr_eq_zero_of_isRes5_ne {R : Type*} [CommRing R]
    {target r : ℕ} (htarget : target < 5) {φ : R⟦X⟧}
    (htr : target ≠ r) (hφ : IsRes5 r φ) :
    section_kr R 5 target φ = 0 := by
  ext n
  rw [coeff_section_kr, map_zero]
  apply hφ
  have hmod : (5 * n + target) % 5 = target := by omega
  rw [hmod]
  exact htr

noncomputable abbrev N0 : (ZMod 5)⟦X⟧ :=
  (A 0) ^ 3

noncomputable abbrev N1 : (ZMod 5)⟦X⟧ :=
  (3 : (ZMod 5)⟦X⟧) * (A 0) ^ 2 * A 1

noncomputable abbrev N2 : (ZMod 5)⟦X⟧ :=
  (3 : (ZMod 5)⟦X⟧) * A 0 * (A 1) ^ 2

noncomputable abbrev N3 : (ZMod 5)⟦X⟧ :=
  (A 1) ^ 3

/-- Cubic expansion of the ASD numerator. -/
theorem S5_cube_expand :
    S5 ^ 3 = N0 + N1 + N2 + N3 := by
  simp only [S5, N0, N1, N2, N3]
  ring

theorem isRes5_N0 : IsRes5 0 N0 := by
  simpa [N0] using isRes5_pow (isRes5_A 0) 3

theorem isRes5_N1 : IsRes5 1 N1 := by
  have hA0sq : IsRes5 0 ((A 0) ^ 2) := by
    simpa using isRes5_pow (isRes5_A 0) 2
  have hprod : IsRes5 1 ((A 0) ^ 2 * A 1) := by
    simpa using isRes5_mul hA0sq (isRes5_A 1)
  simpa [N1, mul_assoc] using isRes5_natCast_mul (R := ZMod 5) 3 1 hprod

theorem isRes5_N2 : IsRes5 2 N2 := by
  have hA1sq : IsRes5 2 ((A 1) ^ 2) := by
    simpa using isRes5_pow (isRes5_A 1) 2
  have hprod : IsRes5 2 (A 0 * (A 1) ^ 2) := by
    simpa using isRes5_mul (isRes5_A 0) hA1sq
  simpa [N2, mul_assoc] using isRes5_natCast_mul (R := ZMod 5) 3 2 hprod

theorem isRes5_N3 : IsRes5 3 N3 := by
  simpa [N3] using isRes5_pow (isRes5_A 1) 3

theorem section_S5_cube_0 :
    section_kr (ZMod 5) 5 0 (S5 ^ 3) = section_kr (ZMod 5) 5 0 N0 := by
  rw [S5_cube_expand]
  simp only [section_kr_add]
  rw [section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 0) (r := 1)
      (by decide) (by decide) isRes5_N1,
    section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 0) (r := 2)
      (by decide) (by decide) isRes5_N2,
    section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 0) (r := 3)
      (by decide) (by decide) isRes5_N3]
  ring

theorem section_S5_cube_1 :
    section_kr (ZMod 5) 5 1 (S5 ^ 3) = section_kr (ZMod 5) 5 1 N1 := by
  rw [S5_cube_expand]
  simp only [section_kr_add]
  rw [section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 1) (r := 0)
      (by decide) (by decide) isRes5_N0,
    section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 1) (r := 2)
      (by decide) (by decide) isRes5_N2,
    section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 1) (r := 3)
      (by decide) (by decide) isRes5_N3]
  ring

theorem section_S5_cube_2 :
    section_kr (ZMod 5) 5 2 (S5 ^ 3) = section_kr (ZMod 5) 5 2 N2 := by
  rw [S5_cube_expand]
  simp only [section_kr_add]
  rw [section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 2) (r := 0)
      (by decide) (by decide) isRes5_N0,
    section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 2) (r := 1)
      (by decide) (by decide) isRes5_N1,
    section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 2) (r := 3)
      (by decide) (by decide) isRes5_N3]
  ring

theorem section_S5_cube_3 :
    section_kr (ZMod 5) 5 3 (S5 ^ 3) = section_kr (ZMod 5) 5 3 N3 := by
  rw [S5_cube_expand]
  simp only [section_kr_add]
  rw [section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 3) (r := 0)
      (by decide) (by decide) isRes5_N0,
    section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 3) (r := 1)
      (by decide) (by decide) isRes5_N1,
    section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 3) (r := 2)
      (by decide) (by decide) isRes5_N2]
  ring

theorem section_S5_cube_4 :
    section_kr (ZMod 5) 5 4 (S5 ^ 3) = 0 := by
  rw [S5_cube_expand]
  simp only [section_kr_add]
  rw [section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 4) (r := 0)
      (by decide) (by decide) isRes5_N0,
    section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 4) (r := 1)
      (by decide) (by decide) isRes5_N1,
    section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 4) (r := 2)
      (by decide) (by decide) isRes5_N2,
    section_kr_eq_zero_of_isRes5_ne (R := ZMod 5) (target := 4) (r := 3)
      (by decide) (by decide) isRes5_N3]
  ring

/-- The `5n` generating-function congruence, denominator-cleared by `(q;q)_∞²`. -/
theorem partition_section_0_mul_Q5_sq :
    section_kr (ZMod 5) 5 0 P5 * Q5 ^ 2 =
      section_kr (ZMod 5) 5 0 N0 := by
  rw [section_partitionGenFun_mul_Q5_sq_eq_section_S5_cube 0 (by decide),
    section_S5_cube_0]

/-- The `5n+1` generating-function congruence, denominator-cleared by `(q;q)_∞²`. -/
theorem partition_section_1_mul_Q5_sq :
    section_kr (ZMod 5) 5 1 P5 * Q5 ^ 2 =
      section_kr (ZMod 5) 5 1 N1 := by
  rw [section_partitionGenFun_mul_Q5_sq_eq_section_S5_cube 1 (by decide),
    section_S5_cube_1]

/-- The `5n+2` generating-function congruence, denominator-cleared by `(q;q)_∞²`. -/
theorem partition_section_2_mul_Q5_sq :
    section_kr (ZMod 5) 5 2 P5 * Q5 ^ 2 =
      section_kr (ZMod 5) 5 2 N2 := by
  rw [section_partitionGenFun_mul_Q5_sq_eq_section_S5_cube 2 (by decide),
    section_S5_cube_2]

/-- The `5n+3` generating-function congruence, denominator-cleared by `(q;q)_∞²`. -/
theorem partition_section_3_mul_Q5_sq :
    section_kr (ZMod 5) 5 3 P5 * Q5 ^ 2 =
      section_kr (ZMod 5) 5 3 N3 := by
  rw [section_partitionGenFun_mul_Q5_sq_eq_section_S5_cube 3 (by decide),
    section_S5_cube_3]

/-- The `5n+4` section vanishes after multiplication by `(q;q)_∞²`. -/
theorem partition_section_4_mul_Q5_sq :
    section_kr (ZMod 5) 5 4 P5 * Q5 ^ 2 = 0 := by
  rw [section_partitionGenFun_mul_Q5_sq_eq_section_S5_cube 4 (by decide),
    section_S5_cube_4]

/-- `P5²` is the formal inverse of `Q5²`. -/
theorem Q5_sq_mul_P5_sq : Q5 ^ 2 * P5 ^ 2 = 1 := by
  calc
    Q5 ^ 2 * P5 ^ 2 = (Q5 * P5) ^ 2 := by ring
    _ = 1 := by rw [qPochInfPS_mul_partitionGenFun (ZMod 5)]; ring

/-- The `5n` generating-function congruence in divided form. -/
theorem partition_section_0_eq_over_Q5_sq :
    section_kr (ZMod 5) 5 0 P5 =
      section_kr (ZMod 5) 5 0 N0 * P5 ^ 2 := by
  calc
    section_kr (ZMod 5) 5 0 P5 =
        section_kr (ZMod 5) 5 0 P5 * 1 := by rw [mul_one]
    _ = section_kr (ZMod 5) 5 0 P5 * (Q5 ^ 2 * P5 ^ 2) := by
        rw [Q5_sq_mul_P5_sq]
    _ = (section_kr (ZMod 5) 5 0 P5 * Q5 ^ 2) * P5 ^ 2 := by ring
    _ = section_kr (ZMod 5) 5 0 N0 * P5 ^ 2 := by
        rw [partition_section_0_mul_Q5_sq]

/-- The `5n+1` generating-function congruence in divided form. -/
theorem partition_section_1_eq_over_Q5_sq :
    section_kr (ZMod 5) 5 1 P5 =
      section_kr (ZMod 5) 5 1 N1 * P5 ^ 2 := by
  calc
    section_kr (ZMod 5) 5 1 P5 =
        section_kr (ZMod 5) 5 1 P5 * 1 := by rw [mul_one]
    _ = section_kr (ZMod 5) 5 1 P5 * (Q5 ^ 2 * P5 ^ 2) := by
        rw [Q5_sq_mul_P5_sq]
    _ = (section_kr (ZMod 5) 5 1 P5 * Q5 ^ 2) * P5 ^ 2 := by ring
    _ = section_kr (ZMod 5) 5 1 N1 * P5 ^ 2 := by
        rw [partition_section_1_mul_Q5_sq]

/-- The `5n+2` generating-function congruence in divided form. -/
theorem partition_section_2_eq_over_Q5_sq :
    section_kr (ZMod 5) 5 2 P5 =
      section_kr (ZMod 5) 5 2 N2 * P5 ^ 2 := by
  calc
    section_kr (ZMod 5) 5 2 P5 =
        section_kr (ZMod 5) 5 2 P5 * 1 := by rw [mul_one]
    _ = section_kr (ZMod 5) 5 2 P5 * (Q5 ^ 2 * P5 ^ 2) := by
        rw [Q5_sq_mul_P5_sq]
    _ = (section_kr (ZMod 5) 5 2 P5 * Q5 ^ 2) * P5 ^ 2 := by ring
    _ = section_kr (ZMod 5) 5 2 N2 * P5 ^ 2 := by
        rw [partition_section_2_mul_Q5_sq]

/-- The `5n+3` generating-function congruence in divided form. -/
theorem partition_section_3_eq_over_Q5_sq :
    section_kr (ZMod 5) 5 3 P5 =
      section_kr (ZMod 5) 5 3 N3 * P5 ^ 2 := by
  calc
    section_kr (ZMod 5) 5 3 P5 =
        section_kr (ZMod 5) 5 3 P5 * 1 := by rw [mul_one]
    _ = section_kr (ZMod 5) 5 3 P5 * (Q5 ^ 2 * P5 ^ 2) := by
        rw [Q5_sq_mul_P5_sq]
    _ = (section_kr (ZMod 5) 5 3 P5 * Q5 ^ 2) * P5 ^ 2 := by ring
    _ = section_kr (ZMod 5) 5 3 N3 * P5 ^ 2 := by
        rw [partition_section_3_mul_Q5_sq]

/-- The `5n+4` generating-function congruence in divided form. -/
theorem partition_section_4_eq_zero :
    section_kr (ZMod 5) 5 4 P5 = 0 := by
  calc
    section_kr (ZMod 5) 5 4 P5 =
        section_kr (ZMod 5) 5 4 P5 * 1 := by rw [mul_one]
    _ = section_kr (ZMod 5) 5 4 P5 * (Q5 ^ 2 * P5 ^ 2) := by
        rw [Q5_sq_mul_P5_sq]
    _ = (section_kr (ZMod 5) 5 4 P5 * Q5 ^ 2) * P5 ^ 2 := by ring
    _ = 0 := by rw [partition_section_4_mul_Q5_sq]; ring

/-- Sanity-check restatement of the already-proved Ramanujan mod-5 congruence. -/
theorem partition_5n_plus_4_eq_zero_mod_5 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (5 * n + 4) : ℕ) : ZMod 5) = 0 :=
  ramanujan_partition_5n_plus_4_eq_zero_mod_5 n

end ASDMod5Full
end Pending
end QseriesFormalization
