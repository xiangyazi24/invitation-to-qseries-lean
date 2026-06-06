import QseriesFormalization.Chapter19_JacobiTripleSignChar
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal
import QseriesFormalization.Pending.JTP_FormalPS_Pentagonal

/-!
# Pending proof work for Chan §16 / Hirschhorn §5

This file is intentionally standalone: it does not edit or import the existing
`Pending/Chapter16_MBI.lean` stub.  It develops the mod-5 section bookkeeping
needed for Ramanujan's most beautiful identity.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch16MBIProof

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartI.Ch05 (pentagonalSign)
open QseriesFormalization.Pending.JTPFormalPSPentagonal

/-- The residue-`r` mod 5 section of a formal power series. -/
noncomputable def section5 (R : Type*) [CommRing R] (r : ℕ) (φ : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk (fun n => if n % 5 = r then φ.coeff n else 0)

@[simp] theorem coeff_section5 (R : Type*) [CommRing R] (r : ℕ) (φ : R⟦X⟧)
    (n : ℕ) :
    (section5 R r φ).coeff n = if n % 5 = r then φ.coeff n else 0 := by
  rw [section5, PowerSeries.coeff_mk]

/-- The compressed residue-`r` mod 5 section: coefficient `n` is the
coefficient of the original series at `5n+r`. -/
noncomputable def compressedSection5 (R : Type*) [CommRing R] (r : ℕ)
    (φ : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk (fun n => φ.coeff (5 * n + r))

@[simp] theorem coeff_compressedSection5 (R : Type*) [CommRing R] (r : ℕ)
    (φ : R⟦X⟧) (n : ℕ) :
    (compressedSection5 R r φ).coeff n = φ.coeff (5 * n + r) := by
  rw [compressedSection5, PowerSeries.coeff_mk]

/-- Every power series is the sum of its five residue sections. -/
theorem sum_section5_eq (R : Type*) [CommRing R] (φ : R⟦X⟧) :
    ∑ r ∈ Finset.range 5, section5 R r φ = φ := by
  ext n
  rw [map_sum]
  simp only [coeff_section5]
  rw [Finset.sum_ite_eq (Finset.range 5) (n % 5) (fun _ => φ.coeff n)]
  have : n % 5 ∈ Finset.range 5 := Finset.mem_range.mpr (Nat.mod_lt n (by decide))
  simp [this]

/-- `φ` is supported on one residue class modulo 5. -/
def IsRes5 {R : Type*} [CommRing R] (r : ℕ) (φ : R⟦X⟧) : Prop :=
  ∀ n, n % 5 ≠ r → φ.coeff n = 0

theorem coeff_section5_of_ne (R : Type*) [CommRing R] (r : ℕ) (φ : R⟦X⟧)
    (n : ℕ) (h : n % 5 ≠ r) : (section5 R r φ).coeff n = 0 := by
  rw [coeff_section5, if_neg h]

theorem section5_add (R : Type*) [CommRing R] (r : ℕ) (φ ψ : R⟦X⟧) :
    section5 R r (φ + ψ) = section5 R r φ + section5 R r ψ := by
  ext n
  simp only [coeff_section5, map_add]
  split <;> simp

theorem section5_zero (R : Type*) [CommRing R] (r : ℕ) :
    section5 R r (0 : R⟦X⟧) = 0 := by
  ext n
  simp [coeff_section5]

theorem section5_eq_self_of_isRes5 {R : Type*} [CommRing R]
    (r : ℕ) {φ : R⟦X⟧} (hφ : IsRes5 r φ) :
    section5 R r φ = φ := by
  ext n
  rw [coeff_section5]
  by_cases hn : n % 5 = r
  · simp [hn]
  · simp [hn, hφ n hn]

theorem section5_eq_zero_of_isRes5 {R : Type*} [CommRing R]
    (t r : ℕ) {φ : R⟦X⟧} (htr : t ≠ r) (hφ : IsRes5 r φ) :
    section5 R t φ = 0 := by
  ext n
  rw [coeff_section5]
  by_cases hn : n % 5 = t
  · have hnr : n % 5 ≠ r := by
      intro h
      exact htr (hn.symm.trans h)
    simp [hn, hφ n hnr]
  · simp [hn]

theorem section5_eq_if_of_isRes5 {R : Type*} [CommRing R]
    (t r : ℕ) {φ : R⟦X⟧} (hφ : IsRes5 r φ) :
    section5 R t φ = if t = r then φ else 0 := by
  by_cases htr : t = r
  · subst t
    rw [if_pos rfl]
    exact section5_eq_self_of_isRes5 r hφ
  · rw [if_neg htr]
    exact section5_eq_zero_of_isRes5 t r htr hφ

theorem isRes5_section5 {R : Type*} [CommRing R] (r : ℕ) (φ : R⟦X⟧) :
    IsRes5 r (section5 R r φ) := by
  intro n hn
  exact coeff_section5_of_ne R r φ n hn

theorem isRes5_zero {R : Type*} [CommRing R] (r : ℕ) :
    IsRes5 r (0 : R⟦X⟧) := by
  intro n _hn
  simp

theorem isRes5_add {R : Type*} [CommRing R] {r : ℕ} {φ ψ : R⟦X⟧}
    (hφ : IsRes5 r φ) (hψ : IsRes5 r ψ) :
    IsRes5 r (φ + ψ) := by
  intro n hn
  rw [map_add, hφ n hn, hψ n hn, zero_add]

theorem isRes5_neg {R : Type*} [CommRing R] {r : ℕ} {φ : R⟦X⟧}
    (hφ : IsRes5 r φ) :
    IsRes5 r (-φ) := by
  intro n hn
  rw [map_neg, hφ n hn, neg_zero]

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

/-- Kind-one pentagonal numbers have mod-5 residue in `{0,1,2}`. -/
theorem pentagonal_kind_one_mod_5 (k : ℕ) :
    (((k * (3 * k - 1) / 2 : ℕ) : ZMod 5) = 0) ∨
    (((k * (3 * k - 1) / 2 : ℕ) : ZMod 5) = 1) ∨
    (((k * (3 * k - 1) / 2 : ℕ) : ZMod 5) = 2) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    left
    simp
  have h_even : Even (k * (3 * k - 1)) := by
    rcases Nat.even_or_odd k with hek | hok
    · exact hek.mul_right _
    · refine Even.mul_left ?_ k
      obtain ⟨m, hm⟩ := hok
      have h1 : 3 * k - 1 = 6 * m + 2 := by rw [hm]; omega
      rw [h1]
      exact ⟨3 * m + 1, by ring⟩
  obtain ⟨q, hq⟩ := h_even
  have hq' : k * (3 * k - 1) = 2 * q := by rw [hq]; ring
  have h_div : k * (3 * k - 1) / 2 = q := by
    rw [hq']
    exact Nat.mul_div_cancel_left q (by decide)
  rw [h_div]
  have h_cast_3k : ((3 * k - 1 : ℕ) : ZMod 5) = 3 * (k : ZMod 5) - 1 := by
    have heq : (3 * k - 1 : ℕ) + 1 = 3 * k := by omega
    have h1 : (((3 * k - 1 : ℕ) + 1 : ℕ) : ZMod 5) =
        ((3 * k : ℕ) : ZMod 5) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 5) heq
    push_cast at h1
    linear_combination h1
  have h_2q_cast : (2 : ZMod 5) * (q : ZMod 5) =
      (k : ZMod 5) * (3 * (k : ZMod 5) - 1) := by
    have h2 : ((2 * q : ℕ) : ZMod 5) =
        ((k * (3 * k - 1) : ℕ) : ZMod 5) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 5) hq'.symm
    push_cast at h2
    rw [h_cast_3k] at h2
    linear_combination h2
  have h_q_eq : (q : ZMod 5) =
      3 * ((k : ZMod 5) * (3 * (k : ZMod 5) - 1)) := by
    have h_inv : (3 : ZMod 5) * 2 = 1 := by decide
    calc (q : ZMod 5)
        = 1 * (q : ZMod 5) := (one_mul _).symm
      _ = (3 * 2) * (q : ZMod 5) := by rw [h_inv]
      _ = 3 * (2 * (q : ZMod 5)) := by ring
      _ = 3 * ((k : ZMod 5) * (3 * (k : ZMod 5) - 1)) := by rw [h_2q_cast]
  rw [h_q_eq]
  obtain ⟨k', hk'⟩ : ∃ k' : ZMod 5, (k : ZMod 5) = k' := ⟨(k : ZMod 5), rfl⟩
  rw [hk']
  fin_cases k' <;> decide

/-- Kind-two pentagonal numbers have mod-5 residue in `{0,1,2}`. -/
theorem pentagonal_kind_two_mod_5 (k : ℕ) :
    (((k * (3 * k + 1) / 2 : ℕ) : ZMod 5) = 0) ∨
    (((k * (3 * k + 1) / 2 : ℕ) : ZMod 5) = 1) ∨
    (((k * (3 * k + 1) / 2 : ℕ) : ZMod 5) = 2) := by
  have h_even : Even (k * (3 * k + 1)) := by
    rcases Nat.even_or_odd k with hek | hok
    · exact hek.mul_right _
    · refine Even.mul_left ?_ k
      obtain ⟨m, hm⟩ := hok
      rw [hm]
      exact ⟨3 * m + 2, by ring⟩
  obtain ⟨q, hq⟩ := h_even
  have hq' : k * (3 * k + 1) = 2 * q := by rw [hq]; ring
  have h_div : k * (3 * k + 1) / 2 = q := by
    rw [hq']
    exact Nat.mul_div_cancel_left q (by decide)
  rw [h_div]
  have h_2q_cast : (2 : ZMod 5) * (q : ZMod 5) =
      (k : ZMod 5) * (3 * (k : ZMod 5) + 1) := by
    have h2 : ((2 * q : ℕ) : ZMod 5) =
        ((k * (3 * k + 1) : ℕ) : ZMod 5) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 5) hq'.symm
    push_cast at h2
    linear_combination h2
  have h_q_eq : (q : ZMod 5) =
      3 * ((k : ZMod 5) * (3 * (k : ZMod 5) + 1)) := by
    have h_inv : (3 : ZMod 5) * 2 = 1 := by decide
    calc (q : ZMod 5)
        = 1 * (q : ZMod 5) := (one_mul _).symm
      _ = (3 * 2) * (q : ZMod 5) := by rw [h_inv]
      _ = 3 * (2 * (q : ZMod 5)) := by ring
      _ = 3 * ((k : ZMod 5) * (3 * (k : ZMod 5) + 1)) := by rw [h_2q_cast]
  rw [h_q_eq]
  obtain ⟨k', hk'⟩ : ∃ k' : ZMod 5, (k : ZMod 5) = k' := ⟨(k : ZMod 5), rfl⟩
  rw [hk']
  fin_cases k' <;> decide

theorem pentagonal_kind_one_mod_5_eq_one_imp (k : ℕ)
    (h : (((k * (3 * k - 1) / 2 : ℕ) : ZMod 5) = 1)) :
    (k : ZMod 5) = 1 := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    simpa using h
  have h_even : Even (k * (3 * k - 1)) := by
    rcases Nat.even_or_odd k with hek | hok
    · exact hek.mul_right _
    · refine Even.mul_left ?_ k
      obtain ⟨m, hm⟩ := hok
      have h1 : 3 * k - 1 = 6 * m + 2 := by rw [hm]; omega
      rw [h1]
      exact ⟨3 * m + 1, by ring⟩
  obtain ⟨q, hq⟩ := h_even
  have hq' : k * (3 * k - 1) = 2 * q := by rw [hq]; ring
  have h_div : k * (3 * k - 1) / 2 = q := by
    rw [hq']
    exact Nat.mul_div_cancel_left q (by decide)
  rw [h_div] at h
  have h_cast_3k : ((3 * k - 1 : ℕ) : ZMod 5) = 3 * (k : ZMod 5) - 1 := by
    have heq : (3 * k - 1 : ℕ) + 1 = 3 * k := by omega
    have h1 : (((3 * k - 1 : ℕ) + 1 : ℕ) : ZMod 5) =
        ((3 * k : ℕ) : ZMod 5) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 5) heq
    push_cast at h1
    linear_combination h1
  have h_2q_cast : (2 : ZMod 5) * (q : ZMod 5) =
      (k : ZMod 5) * (3 * (k : ZMod 5) - 1) := by
    have h2 : ((2 * q : ℕ) : ZMod 5) =
        ((k * (3 * k - 1) : ℕ) : ZMod 5) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 5) hq'.symm
    push_cast at h2
    rw [h_cast_3k] at h2
    linear_combination h2
  have h_q_eq : (q : ZMod 5) =
      3 * ((k : ZMod 5) * (3 * (k : ZMod 5) - 1)) := by
    have h_inv : (3 : ZMod 5) * 2 = 1 := by decide
    calc (q : ZMod 5)
        = 1 * (q : ZMod 5) := (one_mul _).symm
      _ = (3 * 2) * (q : ZMod 5) := by rw [h_inv]
      _ = 3 * (2 * (q : ZMod 5)) := by ring
      _ = 3 * ((k : ZMod 5) * (3 * (k : ZMod 5) - 1)) := by rw [h_2q_cast]
  rw [h_q_eq] at h
  obtain ⟨k', hk'⟩ : ∃ k' : ZMod 5, (k : ZMod 5) = k' := ⟨(k : ZMod 5), rfl⟩
  rw [hk'] at h ⊢
  fin_cases k'
  · exact absurd h (by decide)
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem pentagonal_kind_two_mod_5_eq_one_imp (k : ℕ)
    (h : (((k * (3 * k + 1) / 2 : ℕ) : ZMod 5) = 1)) :
    (k : ZMod 5) = 4 := by
  have h_even : Even (k * (3 * k + 1)) := by
    rcases Nat.even_or_odd k with hek | hok
    · exact hek.mul_right _
    · refine Even.mul_left ?_ k
      obtain ⟨m, hm⟩ := hok
      rw [hm]
      exact ⟨3 * m + 2, by ring⟩
  obtain ⟨q, hq⟩ := h_even
  have hq' : k * (3 * k + 1) = 2 * q := by rw [hq]; ring
  have h_div : k * (3 * k + 1) / 2 = q := by
    rw [hq']
    exact Nat.mul_div_cancel_left q (by decide)
  rw [h_div] at h
  have h_2q_cast : (2 : ZMod 5) * (q : ZMod 5) =
      (k : ZMod 5) * (3 * (k : ZMod 5) + 1) := by
    have h2 : ((2 * q : ℕ) : ZMod 5) =
        ((k * (3 * k + 1) : ℕ) : ZMod 5) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 5) hq'.symm
    push_cast at h2
    linear_combination h2
  have h_q_eq : (q : ZMod 5) =
      3 * ((k : ZMod 5) * (3 * (k : ZMod 5) + 1)) := by
    have h_inv : (3 : ZMod 5) * 2 = 1 := by decide
    calc (q : ZMod 5)
        = 1 * (q : ZMod 5) := (one_mul _).symm
      _ = (3 * 2) * (q : ZMod 5) := by rw [h_inv]
      _ = 3 * (2 * (q : ZMod 5)) := by ring
      _ = 3 * ((k : ZMod 5) * (3 * (k : ZMod 5) + 1)) := by rw [h_2q_cast]
  rw [h_q_eq] at h
  obtain ⟨k', hk'⟩ : ∃ k' : ZMod 5, (k : ZMod 5) = k' := ⟨(k : ZMod 5), rfl⟩
  rw [hk'] at h ⊢
  fin_cases k'
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

/-- Nonzero pentagonal-sign coefficients occur only in residues `0,1,2` mod 5. -/
theorem pentagonalSign_mod_5_residue (n : ℕ)
    (h : ((pentagonalSign n : ℤ) : ZMod 5) ≠ 0) :
    (n : ZMod 5) = 0 ∨ (n : ZMod 5) = 1 ∨ (n : ZMod 5) = 2 := by
  unfold pentagonalSign at h
  cases h_find1 :
      (List.range (n + 1)).find? (fun k => decide (n = k * (3 * k - 1) / 2)) with
  | some k =>
      have hpred := (List.find?_eq_some_iff_append.mp h_find1).1
      simp only [decide_eq_true_eq] at hpred
      rw [hpred]
      exact pentagonal_kind_one_mod_5 k
  | none =>
      rw [h_find1] at h
      cases h_find2 : (List.range (n + 1)).find?
          (fun k => decide (0 < k ∧ n = k * (3 * k + 1) / 2)) with
      | some k =>
          have hpred := (List.find?_eq_some_iff_append.mp h_find2).1
          simp only [decide_eq_true_eq] at hpred
          rw [hpred.2]
          exact pentagonal_kind_two_mod_5 k
      | none =>
          rw [h_find2] at h
          simp at h

theorem nat_cast_zmod5_eq_mod (n : ℕ) :
    (n : ZMod 5) = ((n % 5 : ℕ) : ZMod 5) := by
  conv_lhs => rw [← Nat.mod_add_div n 5]
  push_cast
  have h5 : (5 : ZMod 5) = 0 := by decide
  rw [h5]
  ring

theorem nat_mod_five_eq_one_of_zmod5_eq_one (k : ℕ)
    (h : (k : ZMod 5) = 1) : k % 5 = 1 := by
  have hmod := nat_cast_zmod5_eq_mod k
  rw [hmod] at h
  have hlt : k % 5 < 5 := Nat.mod_lt k (by decide)
  interval_cases k % 5 <;> norm_num at h ⊢ <;> contradiction

theorem nat_mod_five_eq_four_of_zmod5_eq_four (k : ℕ)
    (h : (k : ZMod 5) = 4) : k % 5 = 4 := by
  have hmod := nat_cast_zmod5_eq_mod k
  rw [hmod] at h
  have hlt : k % 5 < 5 := Nat.mod_lt k (by decide)
  interval_cases k % 5 <;> norm_num at h ⊢ <;> contradiction

theorem twentyfive_dvd_kind_one_sub_one_of_mod_five_eq_one (k : ℕ)
    (hmod : (k * (3 * k - 1) / 2) % 5 = 1) :
    25 ∣ k * (3 * k - 1) / 2 - 1 := by
  have hcast : (((k * (3 * k - 1) / 2 : ℕ) : ZMod 5) = 1) := by
    rw [nat_cast_zmod5_eq_mod, hmod]
    norm_num
  have hkz := pentagonal_kind_one_mod_5_eq_one_imp k hcast
  have hkmod := nat_mod_five_eq_one_of_zmod5_eq_one k hkz
  let a := k / 5
  have hk : k = 5 * a + 1 := by
    calc
      k = k % 5 + 5 * (k / 5) := (Nat.mod_add_div k 5).symm
      _ = 1 + 5 * a := by rw [hkmod]
      _ = 5 * a + 1 := by omega
  obtain ⟨q, hq⟩ : Even (a * (3 * a + 1)) := by
    rcases Nat.even_or_odd a with he | ho
    · exact he.mul_right _
    · refine Even.mul_left ?_ a
      obtain ⟨m, hm⟩ := ho
      rw [hm]
      exact ⟨3 * m + 2, by ring⟩
  have hprod : k * (3 * k - 1) = 2 * (25 * q + 1) := by
    rw [hk]
    have h3 : 3 * (5 * a + 1) - 1 = 15 * a + 2 := by omega
    rw [h3]
    nlinarith
  have hdiv : k * (3 * k - 1) / 2 = 25 * q + 1 := by
    rw [hprod]
    exact Nat.mul_div_cancel_left (25 * q + 1) (by decide)
  rw [hdiv]
  exact ⟨q, by omega⟩

theorem twentyfive_dvd_kind_two_sub_one_of_mod_five_eq_one (k : ℕ)
    (hmod : (k * (3 * k + 1) / 2) % 5 = 1) :
    25 ∣ k * (3 * k + 1) / 2 - 1 := by
  have hcast : (((k * (3 * k + 1) / 2 : ℕ) : ZMod 5) = 1) := by
    rw [nat_cast_zmod5_eq_mod, hmod]
    norm_num
  have hkz := pentagonal_kind_two_mod_5_eq_one_imp k hcast
  have hkmod := nat_mod_five_eq_four_of_zmod5_eq_four k hkz
  let a := k / 5
  have hk : k = 5 * a + 4 := by
    calc
      k = k % 5 + 5 * (k / 5) := (Nat.mod_add_div k 5).symm
      _ = 4 + 5 * a := by rw [hkmod]
      _ = 5 * a + 4 := by omega
  obtain ⟨q, hq⟩ : Even ((a + 1) * (3 * a + 2)) := by
    have hrewrite : (a + 1) * (3 * a + 2) = (a + 1) * (3 * (a + 1) - 1) := by
      have h3 : 3 * (a + 1) - 1 = 3 * a + 2 := by omega
      rw [h3]
    rw [hrewrite]
    rcases Nat.even_or_odd (a + 1) with he | ho
    · exact he.mul_right _
    · refine Even.mul_left ?_ (a + 1)
      obtain ⟨m, hm⟩ := ho
      have h1 : 3 * (a + 1) - 1 = 6 * m + 2 := by rw [hm]; omega
      rw [h1]
      exact ⟨3 * m + 1, by ring⟩
  have hprod : k * (3 * k + 1) = 2 * (25 * q + 1) := by
    rw [hk]
    have h3 : 3 * (5 * a + 4) + 1 = 15 * a + 13 := by omega
    rw [h3]
    nlinarith
  have hdiv : k * (3 * k + 1) / 2 = 25 * q + 1 := by
    rw [hprod]
    exact Nat.mul_div_cancel_left (25 * q + 1) (by decide)
  rw [hdiv]
  exact ⟨q, by omega⟩

/-- `pentagonalSign` vanishes on residues `3` and `4` modulo 5. -/
theorem pentagonalSign_eq_zero_of_mod_five_eq_three_or_four (n : ℕ)
    (h : n % 5 = 3 ∨ n % 5 = 4) :
    pentagonalSign n = 0 := by
  by_contra hnz
  have hz : ((pentagonalSign n : ℤ) : ZMod 5) ≠ 0 := by
    rcases QseriesFormalization.PartIV.Ch19.pentagonalSign_mem n with hneg | hzero | hpos
    · rw [hneg]
      decide
    · exact (hnz hzero).elim
    · rw [hpos]
      decide
  have hres := pentagonalSign_mod_5_residue n hz
  have hmod := nat_cast_zmod5_eq_mod n
  rcases h with h3 | h4
  · rw [hmod, h3] at hres
    rcases hres with h0 | h1 | h2
    · exact absurd h0 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide)
  · rw [hmod, h4] at hres
    rcases hres with h0 | h1 | h2
    · exact absurd h0 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide)

/-- If a pentagonal-sign coefficient is in residue `1` modulo 5 but not in
residue `1` modulo 25, it vanishes.  This is the support half of
Hirschhorn's `E_1 = -q E(q^25)`. -/
theorem pentagonalSign_eq_zero_of_mod_five_eq_one_not_twentyfive_dvd
    (n : ℕ) (hmod : n % 5 = 1) (hndvd : ¬ 25 ∣ n - 1) :
    pentagonalSign n = 0 := by
  unfold pentagonalSign
  cases h_find1 :
      (List.range (n + 1)).find? (fun k => decide (n = k * (3 * k - 1) / 2)) with
  | some k =>
      exfalso
      have hpred := (List.find?_eq_some_iff_append.mp h_find1).1
      simp only [decide_eq_true_eq] at hpred
      have hkmod : (k * (3 * k - 1) / 2) % 5 = 1 := by
        rw [← hpred]
        exact hmod
      exact hndvd (by
        rw [hpred]
        exact twentyfive_dvd_kind_one_sub_one_of_mod_five_eq_one k hkmod)
  | none =>
      cases h_find2 : (List.range (n + 1)).find?
          (fun k => decide (0 < k ∧ n = k * (3 * k + 1) / 2)) with
      | some k =>
          exfalso
          have hpred := (List.find?_eq_some_iff_append.mp h_find2).1
          simp only [decide_eq_true_eq] at hpred
          have hkmod : (k * (3 * k + 1) / 2) % 5 = 1 := by
            rw [← hpred.2]
            exact hmod
          exact hndvd (by
            rw [hpred.2]
            exact twentyfive_dvd_kind_two_sub_one_of_mod_five_eq_one k hkmod)
      | none =>
          rfl

/-- The `r`-section of `qPochInfPS` is zero for `r = 3,4` mod 5. -/
theorem section5_qPochInfPS_eq_zero_of_three_or_four
    (R : Type*) [CommRing R] (r : ℕ) (hr : r = 3 ∨ r = 4) :
    section5 R r (qPochInfPS R) = 0 := by
  ext n
  rw [coeff_section5]
  by_cases hn : n % 5 = r
  · rw [if_pos hn, coeff_qPochInfPS_eq_pentagonalSign]
    have hmod : n % 5 = 3 ∨ n % 5 = 4 := by
      rcases hr with rfl | rfl <;> simp [hn]
    rw [pentagonalSign_eq_zero_of_mod_five_eq_three_or_four n hmod]
    norm_cast
  · rw [if_neg hn]
    simp

/-- The three nonzero residue sections of Euler's product. -/
noncomputable def E5 (R : Type*) [CommRing R] (r : ℕ) : R⟦X⟧ :=
  section5 R r (qPochInfPS R)

theorem isRes5_E5 (R : Type*) [CommRing R] (r : ℕ) :
    IsRes5 r (E5 R r) :=
  isRes5_section5 r (qPochInfPS R)

/-- Support half of Hirschhorn (5.3.2): the `E_1` section has no coefficient
at exponents `n` with `25 ∤ n - 1`. -/
theorem coeff_E5_one_eq_zero_of_not_twentyfive_dvd
    (R : Type*) [CommRing R] (n : ℕ) (hndvd : ¬ 25 ∣ n - 1) :
    (E5 R 1).coeff n = 0 := by
  rw [E5, coeff_section5]
  by_cases hmod : n % 5 = 1
  · rw [if_pos hmod, coeff_qPochInfPS_eq_pentagonalSign]
    rw [pentagonalSign_eq_zero_of_mod_five_eq_one_not_twentyfive_dvd n hmod hndvd]
    norm_cast
  · rw [if_neg hmod]

/-- Euler's product has only residue sections `0,1,2` modulo 5. -/
theorem qPochInfPS_five_dissection (R : Type*) [CommRing R] :
    qPochInfPS R = E5 R 0 + E5 R 1 + E5 R 2 := by
  calc
    qPochInfPS R = ∑ r ∈ Finset.range 5, section5 R r (qPochInfPS R) :=
      (sum_section5_eq R (qPochInfPS R)).symm
    _ = E5 R 0 + E5 R 1 + E5 R 2 + E5 R 3 + E5 R 4 := by
      simp [E5, Finset.sum_range_succ, add_assoc]
    _ = E5 R 0 + E5 R 1 + E5 R 2 := by
      rw [show E5 R 3 = 0 from section5_qPochInfPS_eq_zero_of_three_or_four R 3 (Or.inl rfl)]
      rw [show E5 R 4 = 0 from section5_qPochInfPS_eq_zero_of_three_or_four R 4 (Or.inr rfl)]
      ring

/-- Triangular exponents have mod-5 residue in `{0,1,3}`. -/
theorem triangular_mod_5_residue (k : ℕ) :
    (((k * (k + 1) / 2 : ℕ) : ZMod 5) = 0) ∨
    (((k * (k + 1) / 2 : ℕ) : ZMod 5) = 1) ∨
    (((k * (k + 1) / 2 : ℕ) : ZMod 5) = 3) := by
  obtain ⟨q, hq⟩ := QseriesFormalization.PartIV.Ch19.two_dvd_mul_succ k
  have hq' : k * (k + 1) = 2 * q := hq
  have h_div : k * (k + 1) / 2 = q := by
    rw [hq']
    exact Nat.mul_div_cancel_left q (by decide)
  rw [h_div]
  have h_2q_cast : (2 : ZMod 5) * (q : ZMod 5) =
      (k : ZMod 5) * ((k : ZMod 5) + 1) := by
    have h2 : ((2 * q : ℕ) : ZMod 5) =
        ((k * (k + 1) : ℕ) : ZMod 5) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 5) hq'.symm
    push_cast at h2
    linear_combination h2
  have h_q_eq : (q : ZMod 5) =
      3 * ((k : ZMod 5) * ((k : ZMod 5) + 1)) := by
    have h_inv : (3 : ZMod 5) * 2 = 1 := by decide
    calc (q : ZMod 5)
        = 1 * (q : ZMod 5) := (one_mul _).symm
      _ = (3 * 2) * (q : ZMod 5) := by rw [h_inv]
      _ = 3 * (2 * (q : ZMod 5)) := by ring
      _ = 3 * ((k : ZMod 5) * ((k : ZMod 5) + 1)) := by rw [h_2q_cast]
  rw [h_q_eq]
  obtain ⟨k', hk'⟩ : ∃ k' : ZMod 5, (k : ZMod 5) = k' := ⟨(k : ZMod 5), rfl⟩
  rw [hk']
  fin_cases k' <;> decide

/-- Nonzero Jacobi-theta coefficients occur only in residues `0,1,3` modulo 5. -/
theorem jacobiTripleSign_mod_5_residue (n : ℕ)
    (h : ((jacobiTripleSign n : ℤ) : ZMod 5) ≠ 0) :
    (n : ZMod 5) = 0 ∨ (n : ZMod 5) = 1 ∨ (n : ZMod 5) = 3 := by
  by_cases htri : ∃ k ≤ n, n = k * (k + 1) / 2
  · obtain ⟨k, _hk_le, hk⟩ := htri
    rw [hk]
    exact triangular_mod_5_residue k
  · push_neg at htri
    rw [QseriesFormalization.PartIV.Ch19.jacobiTripleSign_of_not_triangular n htri] at h
    simp at h

/-- `jacobiThetaPS` has zero 2-section modulo 5 over any commutative ring. -/
theorem section5_jacobiThetaPS_two_eq_zero (R : Type*) [CommRing R] :
    section5 R 2 (jacobiThetaPS R) = 0 := by
  ext n
  rw [coeff_section5]
  by_cases hn : n % 5 = 2
  · rw [if_pos hn, coeff_jacobiThetaPS]
    have hnottri : ∀ k ≤ n, n ≠ k * (k + 1) / 2 := by
      intro k _hk hkn
      have hres := triangular_mod_5_residue k
      have hmod := nat_cast_zmod5_eq_mod n
      have htri_cast : (((k * (k + 1) / 2 : ℕ) : ZMod 5)) = (n : ZMod 5) := by
        rw [← hkn]
      rw [htri_cast, hmod, hn] at hres
      rcases hres with h0 | h1 | h3
      · exact absurd h0 (by decide)
      · exact absurd h1 (by decide)
      · exact absurd h3 (by decide)
    rw [QseriesFormalization.PartIV.Ch19.jacobiTripleSign_of_not_triangular n hnottri]
    norm_cast
  · rw [if_neg hn]
    simp

theorem section5_two_qPochInfPS_cube_eq_zero_rat :
    section5 ℚ 2 ((qPochInfPS ℚ)^3) = 0 := by
  rw [QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS]
  exact section5_jacobiThetaPS_two_eq_zero ℚ

private theorem isRes5_rat_term_three_mul {r : ℕ} {φ : ℚ⟦X⟧}
    (hφ : IsRes5 r φ) :
    IsRes5 r ((3 : ℚ⟦X⟧) * φ) :=
  isRes5_natCast_mul (R := ℚ) 3 r hφ

private theorem isRes5_rat_term_six_mul {r : ℕ} {φ : ℚ⟦X⟧}
    (hφ : IsRes5 r φ) :
    IsRes5 r ((6 : ℚ⟦X⟧) * φ) :=
  isRes5_natCast_mul (R := ℚ) 6 r hφ

set_option maxHeartbeats 1200000 in
theorem section5_two_E5_sum_cube_rat :
    section5 ℚ 2 ((E5 ℚ 0 + E5 ℚ 1 + E5 ℚ 2)^3)
      =
    (3 : ℚ⟦X⟧) * (E5 ℚ 0)^2 * E5 ℚ 2 +
      (3 : ℚ⟦X⟧) * E5 ℚ 0 * (E5 ℚ 1)^2 := by
  let E0 : ℚ⟦X⟧ := E5 ℚ 0
  let E1 : ℚ⟦X⟧ := E5 ℚ 1
  let E2 : ℚ⟦X⟧ := E5 ℚ 2
  have hE0 : IsRes5 0 E0 := by simpa [E0] using isRes5_E5 ℚ 0
  have hE1 : IsRes5 1 E1 := by simpa [E1] using isRes5_E5 ℚ 1
  have hE2 : IsRes5 2 E2 := by simpa [E2] using isRes5_E5 ℚ 2
  have hE0_sq : IsRes5 0 (E0 ^ 2) := by
    simpa using isRes5_pow hE0 2
  have hE1_sq : IsRes5 2 (E1 ^ 2) := by
    simpa using isRes5_pow hE1 2
  have hE2_sq : IsRes5 4 (E2 ^ 2) := by
    simpa using isRes5_pow hE2 2
  have hE0_cu : IsRes5 0 (E0 ^ 3) := by
    simpa using isRes5_pow hE0 3
  have hE1_cu : IsRes5 3 (E1 ^ 3) := by
    simpa using isRes5_pow hE1 3
  have hE2_cu : IsRes5 1 (E2 ^ 3) := by
    simpa using isRes5_pow hE2 3
  have h001 : IsRes5 1 ((3 : ℚ⟦X⟧) * E0 ^ 2 * E1) := by
    have h := isRes5_mul (isRes5_rat_term_three_mul hE0_sq) hE1
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h002 : IsRes5 2 ((3 : ℚ⟦X⟧) * E0 ^ 2 * E2) := by
    have h := isRes5_mul (isRes5_rat_term_three_mul hE0_sq) hE2
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h011 : IsRes5 2 ((3 : ℚ⟦X⟧) * E0 * E1 ^ 2) := by
    have h := isRes5_mul (isRes5_rat_term_three_mul hE0) hE1_sq
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h012 : IsRes5 3 ((6 : ℚ⟦X⟧) * E0 * E1 * E2) := by
    have h01 : IsRes5 1 ((6 : ℚ⟦X⟧) * E0 * E1) := by
      have h := isRes5_mul (isRes5_rat_term_six_mul hE0) hE1
      simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
    have h := isRes5_mul h01 hE2
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h022 : IsRes5 4 ((3 : ℚ⟦X⟧) * E0 * E2 ^ 2) := by
    have h := isRes5_mul (isRes5_rat_term_three_mul hE0) hE2_sq
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h112 : IsRes5 4 ((3 : ℚ⟦X⟧) * E1 ^ 2 * E2) := by
    have h := isRes5_mul (isRes5_rat_term_three_mul hE1_sq) hE2
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h122 : IsRes5 0 ((3 : ℚ⟦X⟧) * E1 * E2 ^ 2) := by
    have h := isRes5_mul (isRes5_rat_term_three_mul hE1) hE2_sq
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  change section5 ℚ 2 ((E0 + E1 + E2)^3) =
    (3 : ℚ⟦X⟧) * E0 ^ 2 * E2 + (3 : ℚ⟦X⟧) * E0 * E1 ^ 2
  have h_expand :
      (E0 + E1 + E2)^3 =
        E0^3 + (3 : ℚ⟦X⟧) * E0^2 * E1 +
        (3 : ℚ⟦X⟧) * E0^2 * E2 +
        (3 : ℚ⟦X⟧) * E0 * E1^2 +
        (6 : ℚ⟦X⟧) * E0 * E1 * E2 +
        (3 : ℚ⟦X⟧) * E0 * E2^2 +
        E1^3 + (3 : ℚ⟦X⟧) * E1^2 * E2 +
        (3 : ℚ⟦X⟧) * E1 * E2^2 + E2^3 := by
    ring
  rw [h_expand]
  simp only [section5_add]
  rw [section5_eq_if_of_isRes5 2 0 hE0_cu,
    section5_eq_if_of_isRes5 2 1 h001,
    section5_eq_if_of_isRes5 2 2 h002,
    section5_eq_if_of_isRes5 2 2 h011,
    section5_eq_if_of_isRes5 2 3 h012,
    section5_eq_if_of_isRes5 2 4 h022,
    section5_eq_if_of_isRes5 2 3 hE1_cu,
    section5_eq_if_of_isRes5 2 4 h112,
    section5_eq_if_of_isRes5 2 0 h122,
    section5_eq_if_of_isRes5 2 1 hE2_cu]
  norm_num

/-- Hirschhorn (5.3.1), over `ℚ⟦X⟧`: `E_0 E_2 = -E_1^2`. -/
theorem E5_zero_mul_two_eq_neg_one_sq_rat :
    E5 ℚ 0 * E5 ℚ 2 = - (E5 ℚ 1)^2 := by
  let E0 : ℚ⟦X⟧ := E5 ℚ 0
  let E1 : ℚ⟦X⟧ := E5 ℚ 1
  let E2 : ℚ⟦X⟧ := E5 ℚ 2
  have hsec_zero : section5 ℚ 2 ((E0 + E1 + E2)^3) = 0 := by
    change section5 ℚ 2 ((E5 ℚ 0 + E5 ℚ 1 + E5 ℚ 2)^3) = 0
    rw [← qPochInfPS_five_dissection ℚ]
    exact section5_two_qPochInfPS_cube_eq_zero_rat
  have hsec_eval : section5 ℚ 2 ((E0 + E1 + E2)^3) =
      (3 : ℚ⟦X⟧) * E0^2 * E2 + (3 : ℚ⟦X⟧) * E0 * E1^2 := by
    simpa [E0, E1, E2] using section5_two_E5_sum_cube_rat
  have hsum : (3 : ℚ⟦X⟧) * E0^2 * E2 + (3 : ℚ⟦X⟧) * E0 * E1^2 = 0 := by
    rw [← hsec_eval]
    exact hsec_zero
  have hprod : ((3 : ℚ⟦X⟧) * E0) * (E0 * E2 + E1^2) = 0 := by
    have hfactor :
        (3 : ℚ⟦X⟧) * E0^2 * E2 + (3 : ℚ⟦X⟧) * E0 * E1^2 =
          ((3 : ℚ⟦X⟧) * E0) * (E0 * E2 + E1^2) := by
      ring
    rwa [hfactor] at hsum
  have h3_ne : (3 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc : ((3 : ℚ⟦X⟧).coeff 0) = (0 : ℚ) := by
      simpa using congrArg (fun φ : ℚ⟦X⟧ => φ.coeff 0) h
    have hcast : (3 : ℚ⟦X⟧) = (PowerSeries.C : ℚ →+* ℚ⟦X⟧) (3 : ℚ) := by
      exact (map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 3).symm
    rw [hcast, PowerSeries.coeff_C] at hc
    norm_num at hc
  have hE0_ne : E0 ≠ 0 := by
    intro h
    have hc : E0.coeff 0 = (0 : ℚ) := by
      simpa using congrArg (fun φ : ℚ⟦X⟧ => φ.coeff 0) h
    have hE0c : E0.coeff 0 = 1 := by
      simp [E0, E5, coeff_zero_qPochInfPS]
    rw [hE0c] at hc
    norm_num at hc
  have hleft_ne : (3 : ℚ⟦X⟧) * E0 ≠ 0 := mul_ne_zero h3_ne hE0_ne
  have hsum0 : E0 * E2 + E1^2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hleft_ne
  change E0 * E2 = -E1^2
  calc
    E0 * E2 = E0 * E2 + E1^2 - E1^2 := by ring
    _ = 0 - E1^2 := by rw [hsum0]
    _ = -E1^2 := by ring

private theorem even_pent_A_succ (a : ℕ) :
    2 ∣ (a + 1) * (3 * a + 2) := by
  induction a with
  | zero => exact ⟨1, by decide⟩
  | succ n ih =>
      obtain ⟨m, hm⟩ := ih
      exact ⟨m + 3 * n + 4, by nlinarith⟩

private theorem even_pent_A (a : ℕ) :
    2 ∣ a * (3 * a - 1) := by
  rcases a with _ | a
  · simp
  · rw [show 3 * (a + 1) - 1 = 3 * a + 2 from by omega]
    exact even_pent_A_succ a

private theorem even_pent_B (a : ℕ) :
    2 ∣ a * (3 * a + 1) := by
  rcases a with _ | n
  · simp
  · induction n with
    | zero => exact ⟨2, by decide⟩
    | succ k ih =>
        obtain ⟨m, hm⟩ := ih
        exact ⟨m + 3 * k + 5, by nlinarith⟩

private theorem pent_A_inj {a b : ℕ}
    (h : a * (3 * a - 1) / 2 = b * (3 * b - 1) / 2) : a = b := by
  rcases a with _ | a <;> rcases b with _ | b
  · rfl
  · exfalso
    simp only [Nat.zero_mul, Nat.zero_div] at h
    obtain ⟨m, hm⟩ := even_pent_A_succ b
    rw [show 3 * (b + 1) - 1 = 3 * b + 2 from by omega] at h
    rw [hm, Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at h
    have : m ≥ 1 := by nlinarith
    omega
  · exfalso
    simp only [Nat.zero_mul, Nat.zero_div] at h
    obtain ⟨m, hm⟩ := even_pent_A_succ a
    rw [show 3 * (a + 1) - 1 = 3 * a + 2 from by omega] at h
    rw [hm, Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at h
    have : m ≥ 1 := by nlinarith
    omega
  · rw [show 3 * (a + 1) - 1 = 3 * a + 2 from by omega,
      show 3 * (b + 1) - 1 = 3 * b + 2 from by omega] at h
    obtain ⟨ma, hma⟩ := even_pent_A_succ a
    obtain ⟨mb, hmb⟩ := even_pent_A_succ b
    rw [hma, hmb, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at h
    have h2 : (a + 1) * (3 * a + 2) = (b + 1) * (3 * b + 2) := by nlinarith
    have h3 : ((a : ℤ) - b) * (3 * ((a : ℤ) + b) + 5) = 0 := by
      push_cast at h2 ⊢
      nlinarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · omega
    · exfalso
      linarith [Int.natCast_nonneg a, Int.natCast_nonneg b]

private theorem pent_B_inj {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : a * (3 * a + 1) / 2 = b * (3 * b + 1) / 2) : a = b := by
  obtain ⟨ma, hma⟩ := even_pent_B a
  obtain ⟨mb, hmb⟩ := even_pent_B b
  rw [hma, hmb, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
    Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at h
  have h2 : a * (3 * a + 1) = b * (3 * b + 1) := by nlinarith
  have h3 : ((a : ℤ) - b) * (3 * ((a : ℤ) + b) + 1) = 0 := by
    push_cast at h2 ⊢
    nlinarith
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact_mod_cast show (a : ℤ) = b by linarith
  · exfalso
    linarith [Int.natCast_nonneg a, Int.natCast_nonneg b]

private theorem pent_B_not_A {k j : ℕ} (hk : 0 < k)
    (h : k * (3 * k + 1) / 2 = j * (3 * j - 1) / 2) : False := by
  rcases j with _ | j
  · simp only [Nat.zero_mul, Nat.zero_div] at h
    obtain ⟨m, hm⟩ := even_pent_B k
    rw [hm, Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at h
    have : m ≥ 1 := by nlinarith
    omega
  · rw [show 3 * (j + 1) - 1 = 3 * j + 2 from by omega] at h
    obtain ⟨mk, hmk⟩ := even_pent_B k
    obtain ⟨mj, hmj⟩ := even_pent_A_succ j
    rw [hmk, hmj, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at h
    have h2 : k * (3 * k + 1) = (j + 1) * (3 * j + 2) := by nlinarith
    by_cases hkj : k ≤ j
    · nlinarith [Nat.mul_le_mul_right (3 * k + 1) (show k ≤ j from hkj)]
    · push_neg at hkj
      by_cases hkj2 : k = j + 1
      · subst hkj2
        nlinarith
      · nlinarith [Nat.mul_le_mul_right (3 * (j + 2) + 1)
          (show j + 2 ≤ k from by omega)]

private theorem pentagonalSign_type_A_local (k : ℕ) :
    pentagonalSign (k * (3 * k - 1) / 2) = (-1 : ℤ) ^ k := by
  simp only [pentagonalSign]
  split
  · rename_i j hj
    have hpred := (List.find?_eq_some_iff_append.mp hj).1
    simp only [decide_eq_true_eq] at hpred
    exact congrArg ((-1 : ℤ) ^ ·) (pent_A_inj hpred.symm)
  · rename_i h_none
    exfalso
    rw [List.find?_eq_none] at h_none
    have hk_le : k ≤ k * (3 * k - 1) / 2 := by
      rcases k with _ | k
      · simp
      · have h3 : 3 * (k + 1) - 1 = 3 * k + 2 := by omega
        have hmul :
            (k + 1) * (3 * (k + 1) - 1) = (k + 1) * (3 * k + 2) := by rw [h3]
        obtain ⟨m, hm⟩ := even_pent_A_succ k
        have hm2 : (k + 1) * (3 * (k + 1) - 1) / 2 = m := by
          rw [hmul, hm]
          omega
        have : m ≥ k + 1 := by nlinarith
        omega
    have := h_none k (List.mem_range.mpr (by omega))
    simp at this

private theorem pentagonalSign_type_B_local (k : ℕ) (hk : 0 < k) :
    pentagonalSign (k * (3 * k + 1) / 2) = (-1 : ℤ) ^ k := by
  simp only [pentagonalSign]
  split
  · rename_i j hj
    have hpred := (List.find?_eq_some_iff_append.mp hj).1
    simp only [decide_eq_true_eq] at hpred
    exact (pent_B_not_A hk hpred).elim
  · split
    · rename_i j hj
      have hpred := (List.find?_eq_some_iff_append.mp hj).1
      simp only [decide_eq_true_eq] at hpred
      exact congrArg ((-1 : ℤ) ^ ·) (pent_B_inj hpred.1 hk hpred.2.symm)
    · rename_i _ h_none
      exfalso
      rw [List.find?_eq_none] at h_none
      have hk_le : k ≤ k * (3 * k + 1) / 2 := by
        obtain ⟨m, hm⟩ := even_pent_B k
        have : k * (3 * k + 1) ≥ 4 * k := by nlinarith
        have : m ≥ 2 * k := by omega
        omega
      have := h_none k (List.mem_range.mpr (by omega))
      simp [hk] at this

private theorem pentA_twentyfive_to_pentB (a : ℕ) (ha : 0 < a) :
    25 * (a * (3 * a - 1) / 2) + 1 =
      (5 * a - 1) * (3 * (5 * a - 1) + 1) / 2 := by
  rcases a with _ | b
  · omega
  obtain ⟨q, hq⟩ := even_pent_A_succ b
  have hA :
      (b + 1) * (3 * (b + 1) - 1) / 2 = q := by
    rw [show 3 * (b + 1) - 1 = 3 * b + 2 from by omega, hq]
    exact Nat.mul_div_cancel_left q (by decide)
  have hprod :
      (5 * (b + 1) - 1) * (3 * (5 * (b + 1) - 1) + 1) =
        2 * (25 * q + 1) := by
    rw [show 5 * (b + 1) - 1 = 5 * b + 4 from by omega,
      show 3 * (5 * b + 4) + 1 = 15 * b + 13 from by omega]
    nlinarith [hq]
  rw [hA, hprod]
  exact (Nat.mul_div_cancel_left (25 * q + 1) (by decide)).symm

private theorem pentB_twentyfive_to_pentA (a : ℕ) :
    25 * (a * (3 * a + 1) / 2) + 1 =
      (5 * a + 1) * (3 * (5 * a + 1) - 1) / 2 := by
  obtain ⟨q, hq⟩ := even_pent_B a
  have hdivB : a * (3 * a + 1) / 2 = q := by
    rw [hq]
    exact Nat.mul_div_cancel_left q (by decide)
  have hprod :
      (5 * a + 1) * (3 * (5 * a + 1) - 1) = 2 * (25 * q + 1) := by
    have h3 : 3 * (5 * a + 1) - 1 = 15 * a + 2 := by omega
    rw [h3]
    nlinarith [hq]
  rw [hdivB, hprod]
  exact (Nat.mul_div_cancel_left (25 * q + 1) (by decide)).symm

private theorem neg_one_pow_five_mul_sub_one (a : ℕ) (ha : 0 < a) :
    (-1 : ℤ) ^ (5 * a - 1) = -((-1 : ℤ) ^ a) := by
  rcases Nat.even_or_odd a with he | ho
  · have heven_a := he
    obtain ⟨t, ht⟩ := he
    have hodd : Odd (5 * a - 1) := by
      refine ⟨5 * t - 1, ?_⟩
      omega
    rw [Even.neg_one_pow heven_a, Odd.neg_one_pow hodd]
  · have hodd_a := ho
    obtain ⟨t, ht⟩ := ho
    have heven : Even (5 * a - 1) := by
      refine ⟨5 * t + 2, ?_⟩
      omega
    rw [Odd.neg_one_pow hodd_a, Even.neg_one_pow heven]
    norm_num

private theorem neg_one_pow_five_mul_add_one (a : ℕ) :
    (-1 : ℤ) ^ (5 * a + 1) = -((-1 : ℤ) ^ a) := by
  rcases Nat.even_or_odd a with he | ho
  · have heven_a := he
    obtain ⟨t, ht⟩ := he
    have hodd : Odd (5 * a + 1) := by
      refine ⟨5 * t, ?_⟩
      omega
    rw [Even.neg_one_pow heven_a, Odd.neg_one_pow hodd]
  · have hodd_a := ho
    obtain ⟨t, ht⟩ := ho
    have heven : Even (5 * a + 1) := by
      refine ⟨5 * t + 3, ?_⟩
      omega
    rw [Odd.neg_one_pow hodd_a, Even.neg_one_pow heven]
    norm_num

private theorem pentA_preimage_of_twentyfive_mul_add_one
    (m k : ℕ) (h : 25 * m + 1 = k * (3 * k - 1) / 2) :
    ∃ a : ℕ, m = a * (3 * a + 1) / 2 := by
  have hcast : (((k * (3 * k - 1) / 2 : ℕ) : ZMod 5) = 1) := by
    rw [← h]
    push_cast
    change (25 : ZMod 5) * (m : ZMod 5) + 1 = 1
    have h25 : (25 : ZMod 5) = 0 := by decide
    rw [h25, zero_mul, zero_add]
  have hkz := pentagonal_kind_one_mod_5_eq_one_imp k hcast
  have hkmod := nat_mod_five_eq_one_of_zmod5_eq_one k hkz
  let a := k / 5
  have hk : k = 5 * a + 1 := by
    calc
      k = k % 5 + 5 * (k / 5) := (Nat.mod_add_div k 5).symm
      _ = 1 + 5 * a := by rw [hkmod]
      _ = 5 * a + 1 := by omega
  refine ⟨a, ?_⟩
  have hmap := pentB_twentyfive_to_pentA a
  rw [hk] at h
  rw [← hmap] at h
  omega

private theorem pentB_preimage_of_twentyfive_mul_add_one
    (m k : ℕ) (h : 25 * m + 1 = k * (3 * k + 1) / 2) :
    ∃ a : ℕ, m = a * (3 * a - 1) / 2 := by
  have hcast : (((k * (3 * k + 1) / 2 : ℕ) : ZMod 5) = 1) := by
    rw [← h]
    push_cast
    change (25 : ZMod 5) * (m : ZMod 5) + 1 = 1
    have h25 : (25 : ZMod 5) = 0 := by decide
    rw [h25, zero_mul, zero_add]
  have hkz := pentagonal_kind_two_mod_5_eq_one_imp k hcast
  have hkmod := nat_mod_five_eq_four_of_zmod5_eq_four k hkz
  let a := k / 5 + 1
  have hk : k = 5 * a - 1 := by
    calc
      k = k % 5 + 5 * (k / 5) := (Nat.mod_add_div k 5).symm
      _ = 4 + 5 * (k / 5) := by rw [hkmod]
      _ = 5 * a - 1 := by omega
  refine ⟨a, ?_⟩
  have ha : 0 < a := by omega
  have hmap := pentA_twentyfive_to_pentB a ha
  rw [hk] at h
  rw [← hmap] at h
  omega

private theorem pentagonalSign_nonzero_of_A (a : ℕ) :
    pentagonalSign (a * (3 * a - 1) / 2) ≠ 0 := by
  rw [pentagonalSign_type_A_local a]
  exact pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0)

private theorem pentagonalSign_nonzero_of_B (a : ℕ) (ha : 0 < a) :
    pentagonalSign (a * (3 * a + 1) / 2) ≠ 0 := by
  rw [pentagonalSign_type_B_local a ha]
  exact pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0)

/-- The sign reindexing behind Hirschhorn (5.3.2). -/
theorem pentagonalSign_twentyfive_mul_add_one (m : ℕ) :
    pentagonalSign (25 * m + 1) = -pentagonalSign m := by
  cases h_findA :
      (List.range (m + 1)).find? (fun k => decide (m = k * (3 * k - 1) / 2)) with
  | some a =>
      have hpred := (List.find?_eq_some_iff_append.mp h_findA).1
      simp only [decide_eq_true_eq] at hpred
      rw [hpred]
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rw [pentagonalSign_type_A_local 1, pentagonalSign_type_A_local 0]
        norm_num
      · rw [pentA_twentyfive_to_pentB a ha,
          pentagonalSign_type_B_local (5 * a - 1) (by omega),
          pentagonalSign_type_A_local a]
        exact neg_one_pow_five_mul_sub_one a ha
  | none =>
      cases h_findB :
          (List.range (m + 1)).find?
            (fun k => decide (0 < k ∧ m = k * (3 * k + 1) / 2)) with
      | some a =>
          have hpred := (List.find?_eq_some_iff_append.mp h_findB).1
          simp only [decide_eq_true_eq] at hpred
          rw [hpred.2, pentB_twentyfive_to_pentA a,
            pentagonalSign_type_A_local (5 * a + 1),
            pentagonalSign_type_B_local a hpred.1]
          exact neg_one_pow_five_mul_add_one a
      | none =>
          have hmzero : pentagonalSign m = 0 := by
            unfold pentagonalSign
            rw [h_findA, h_findB]
          rw [hmzero, neg_zero]
          unfold pentagonalSign
          cases h_findA_n :
              (List.range (25 * m + 1 + 1)).find?
                (fun k => decide (25 * m + 1 = k * (3 * k - 1) / 2)) with
          | some k =>
              exfalso
              have hpred := (List.find?_eq_some_iff_append.mp h_findA_n).1
              simp only [decide_eq_true_eq] at hpred
              obtain ⟨a, ha⟩ :=
                pentA_preimage_of_twentyfive_mul_add_one m k hpred
              have hnonzero : pentagonalSign m ≠ 0 := by
                rw [ha]
                by_cases ha0 : a = 0
                · subst a
                  exact pentagonalSign_nonzero_of_A 0
                · exact pentagonalSign_nonzero_of_B a (Nat.pos_of_ne_zero ha0)
              exact hnonzero hmzero
          | none =>
              cases h_findB_n :
                  (List.range (25 * m + 1 + 1)).find?
                    (fun k => decide
                      (0 < k ∧ 25 * m + 1 = k * (3 * k + 1) / 2)) with
              | some k =>
                  exfalso
                  have hpred := (List.find?_eq_some_iff_append.mp h_findB_n).1
                  simp only [decide_eq_true_eq] at hpred
                  obtain ⟨a, ha⟩ :=
                    pentB_preimage_of_twentyfive_mul_add_one m k hpred.2
                  have hnonzero : pentagonalSign m ≠ 0 := by
                    rw [ha]
                    exact pentagonalSign_nonzero_of_A a
                  exact hnonzero hmzero
              | none =>
                  rfl

/-- Full Hirschhorn (5.3.2): `E_1(q) = -q E(q^25)`. -/
theorem E5_one_eq_neg_X_mul_expand_twentyfive_qPochInfPS
    (R : Type*) [CommRing R] :
    E5 R 1 =
      -PowerSeries.X * PowerSeries.expand 25 (by decide) (qPochInfPS R) := by
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp [E5, coeff_section5]
  · have h_rhs :
        ((-PowerSeries.X : R⟦X⟧) *
            PowerSeries.expand 25 (by decide) (qPochInfPS R)).coeff n =
          -((PowerSeries.expand 25 (by decide) (qPochInfPS R)).coeff (n - 1)) := by
      cases n with
      | zero => exact (hn0 rfl).elim
      | succ d =>
          simp [PowerSeries.coeff_succ_X_mul]
    by_cases hdvd : 25 ∣ n - 1
    · obtain ⟨m, hm⟩ := hdvd
      have hdvd' : 25 ∣ n - 1 := ⟨m, hm⟩
      have hn : n = 25 * m + 1 := by omega
      have hmod : n % 5 = 1 := by
        rw [hn]
        omega
      have hdiv : (n - 1) / 25 = m := by
        rw [hm]
        exact Nat.mul_div_cancel_left m (by decide)
      rw [h_rhs, PowerSeries.coeff_expand, if_pos hdvd', hdiv]
      rw [E5, coeff_section5, if_pos hmod]
      rw [coeff_qPochInfPS_eq_pentagonalSign,
        coeff_qPochInfPS_eq_pentagonalSign]
      rw [hn]
      have hsign :
          (((pentagonalSign (25 * m + 1) : ℤ) : R) =
            -(((pentagonalSign m : ℤ) : R))) := by
        rw [pentagonalSign_twentyfive_mul_add_one]
        simp
      exact hsign
    · rw [coeff_E5_one_eq_zero_of_not_twentyfive_dvd R n hdvd]
      rw [h_rhs, PowerSeries.coeff_expand, if_neg hdvd]
      simp

theorem E5_bracket_collapse_rat :
    (E5 ℚ 0)^2 * (E5 ℚ 2)^2 -
        (3 : ℚ⟦X⟧) * E5 ℚ 0 * (E5 ℚ 1)^2 * E5 ℚ 2 +
        (E5 ℚ 1)^4 =
      (5 : ℚ⟦X⟧) * (E5 ℚ 1)^4 := by
  let E0 : ℚ⟦X⟧ := E5 ℚ 0
  let E1 : ℚ⟦X⟧ := E5 ℚ 1
  let E2 : ℚ⟦X⟧ := E5 ℚ 2
  have h02 : E0 * E2 = -E1^2 := by
    simpa [E0, E1, E2] using E5_zero_mul_two_eq_neg_one_sq_rat
  change E0^2 * E2^2 - (3 : ℚ⟦X⟧) * E0 * E1^2 * E2 + E1^4 =
    (5 : ℚ⟦X⟧) * E1^4
  calc
    E0^2 * E2^2 - (3 : ℚ⟦X⟧) * E0 * E1^2 * E2 + E1^4
        = (E0 * E2)^2 - (3 : ℚ⟦X⟧) * (E0 * E2) * E1^2 + E1^4 := by ring
    _ = (-E1^2)^2 - (3 : ℚ⟦X⟧) * (-E1^2) * E1^2 + E1^4 := by rw [h02]
    _ = (5 : ℚ⟦X⟧) * E1^4 := by ring

theorem E5_one_pow_four_eq_X_pow_four_expand_twentyfive_qPochInfPS_pow_four_rat :
    (E5 ℚ 1)^4 =
      PowerSeries.X ^ 4 *
        (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ))^4 := by
  rw [E5_one_eq_neg_X_mul_expand_twentyfive_qPochInfPS ℚ]
  ring

set_option maxHeartbeats 1200000 in
theorem section5_four_E5_sum_pow_four_rat :
    section5 ℚ 4 ((E5 ℚ 0 + E5 ℚ 1 + E5 ℚ 2)^4)
      =
    (6 : ℚ⟦X⟧) * (E5 ℚ 0)^2 * (E5 ℚ 2)^2 +
      (12 : ℚ⟦X⟧) * E5 ℚ 0 * (E5 ℚ 1)^2 * E5 ℚ 2 +
      (E5 ℚ 1)^4 := by
  let E0 : ℚ⟦X⟧ := E5 ℚ 0
  let E1 : ℚ⟦X⟧ := E5 ℚ 1
  let E2 : ℚ⟦X⟧ := E5 ℚ 2
  have hE0 : IsRes5 0 E0 := by simpa [E0] using isRes5_E5 ℚ 0
  have hE1 : IsRes5 1 E1 := by simpa [E1] using isRes5_E5 ℚ 1
  have hE2 : IsRes5 2 E2 := by simpa [E2] using isRes5_E5 ℚ 2
  have hE0_sq : IsRes5 0 (E0 ^ 2) := by
    simpa using isRes5_pow hE0 2
  have hE1_sq : IsRes5 2 (E1 ^ 2) := by
    simpa using isRes5_pow hE1 2
  have hE2_sq : IsRes5 4 (E2 ^ 2) := by
    simpa using isRes5_pow hE2 2
  have hE0_cu : IsRes5 0 (E0 ^ 3) := by
    simpa using isRes5_pow hE0 3
  have hE1_cu : IsRes5 3 (E1 ^ 3) := by
    simpa using isRes5_pow hE1 3
  have hE2_cu : IsRes5 1 (E2 ^ 3) := by
    simpa using isRes5_pow hE2 3
  have hE0_4 : IsRes5 0 (E0 ^ 4) := by
    simpa using isRes5_pow hE0 4
  have hE1_4 : IsRes5 4 (E1 ^ 4) := by
    simpa using isRes5_pow hE1 4
  have hE2_4 : IsRes5 3 (E2 ^ 4) := by
    simpa using isRes5_pow hE2 4
  have h0001 : IsRes5 1 ((4 : ℚ⟦X⟧) * E0 ^ 3 * E1) := by
    have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 4 0 hE0_cu) hE1
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h0002 : IsRes5 2 ((4 : ℚ⟦X⟧) * E0 ^ 3 * E2) := by
    have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 4 0 hE0_cu) hE2
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h0011 : IsRes5 2 ((6 : ℚ⟦X⟧) * E0 ^ 2 * E1 ^ 2) := by
    have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 6 0 hE0_sq) hE1_sq
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h0012 : IsRes5 3 ((12 : ℚ⟦X⟧) * E0 ^ 2 * E1 * E2) := by
    have h001 : IsRes5 1 ((12 : ℚ⟦X⟧) * E0 ^ 2 * E1) := by
      have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 12 0 hE0_sq) hE1
      simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
    have h := isRes5_mul h001 hE2
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h0022 : IsRes5 4 ((6 : ℚ⟦X⟧) * E0 ^ 2 * E2 ^ 2) := by
    have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 6 0 hE0_sq) hE2_sq
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h0111 : IsRes5 3 ((4 : ℚ⟦X⟧) * E0 * E1 ^ 3) := by
    have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 4 0 hE0) hE1_cu
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h0112 : IsRes5 4 ((12 : ℚ⟦X⟧) * E0 * E1 ^ 2 * E2) := by
    have h011 : IsRes5 2 ((12 : ℚ⟦X⟧) * E0 * E1 ^ 2) := by
      have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 12 0 hE0) hE1_sq
      simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
    have h := isRes5_mul h011 hE2
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h0122 : IsRes5 0 ((12 : ℚ⟦X⟧) * E0 * E1 * E2 ^ 2) := by
    have h01 : IsRes5 1 ((12 : ℚ⟦X⟧) * E0 * E1) := by
      have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 12 0 hE0) hE1
      simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
    have h := isRes5_mul h01 hE2_sq
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h0222 : IsRes5 1 ((4 : ℚ⟦X⟧) * E0 * E2 ^ 3) := by
    have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 4 0 hE0) hE2_cu
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h1112 : IsRes5 0 ((4 : ℚ⟦X⟧) * E1 ^ 3 * E2) := by
    have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 4 3 hE1_cu) hE2
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h1122 : IsRes5 1 ((6 : ℚ⟦X⟧) * E1 ^ 2 * E2 ^ 2) := by
    have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 6 2 hE1_sq) hE2_sq
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have h1222 : IsRes5 2 ((4 : ℚ⟦X⟧) * E1 * E2 ^ 3) := by
    have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 4 1 hE1) hE2_cu
    simpa [Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  change section5 ℚ 4 ((E0 + E1 + E2)^4) =
    (6 : ℚ⟦X⟧) * E0 ^ 2 * E2 ^ 2 +
      (12 : ℚ⟦X⟧) * E0 * E1 ^ 2 * E2 + E1 ^ 4
  have h_expand :
      (E0 + E1 + E2)^4 =
        E0^4 + (4 : ℚ⟦X⟧) * E0^3 * E1 +
        (4 : ℚ⟦X⟧) * E0^3 * E2 +
        (6 : ℚ⟦X⟧) * E0^2 * E1^2 +
        (12 : ℚ⟦X⟧) * E0^2 * E1 * E2 +
        (6 : ℚ⟦X⟧) * E0^2 * E2^2 +
        (4 : ℚ⟦X⟧) * E0 * E1^3 +
        (12 : ℚ⟦X⟧) * E0 * E1^2 * E2 +
        (12 : ℚ⟦X⟧) * E0 * E1 * E2^2 +
        (4 : ℚ⟦X⟧) * E0 * E2^3 +
        E1^4 + (4 : ℚ⟦X⟧) * E1^3 * E2 +
        (6 : ℚ⟦X⟧) * E1^2 * E2^2 +
        (4 : ℚ⟦X⟧) * E1 * E2^3 + E2^4 := by
    ring
  rw [h_expand]
  simp only [section5_add]
  rw [section5_eq_if_of_isRes5 4 0 hE0_4,
    section5_eq_if_of_isRes5 4 1 h0001,
    section5_eq_if_of_isRes5 4 2 h0002,
    section5_eq_if_of_isRes5 4 2 h0011,
    section5_eq_if_of_isRes5 4 3 h0012,
    section5_eq_if_of_isRes5 4 4 h0022,
    section5_eq_if_of_isRes5 4 3 h0111,
    section5_eq_if_of_isRes5 4 4 h0112,
    section5_eq_if_of_isRes5 4 0 h0122,
    section5_eq_if_of_isRes5 4 1 h0222,
    section5_eq_if_of_isRes5 4 4 hE1_4,
    section5_eq_if_of_isRes5 4 0 h1112,
    section5_eq_if_of_isRes5 4 1 h1122,
    section5_eq_if_of_isRes5 4 2 h1222,
    section5_eq_if_of_isRes5 4 3 hE2_4]
  norm_num

theorem section5_four_qPochInfPS_pow_four_rat :
    section5 ℚ 4 ((qPochInfPS ℚ)^4) =
      -(5 : ℚ⟦X⟧) * (E5 ℚ 1)^4 := by
  let E0 : ℚ⟦X⟧ := E5 ℚ 0
  let E1 : ℚ⟦X⟧ := E5 ℚ 1
  let E2 : ℚ⟦X⟧ := E5 ℚ 2
  have h02 : E0 * E2 = -E1^2 := by
    simpa [E0, E1, E2] using E5_zero_mul_two_eq_neg_one_sq_rat
  change section5 ℚ 4 ((qPochInfPS ℚ)^4) = -(5 : ℚ⟦X⟧) * E1^4
  rw [qPochInfPS_five_dissection ℚ]
  change section5 ℚ 4 ((E0 + E1 + E2)^4) = -(5 : ℚ⟦X⟧) * E1^4
  rw [section5_four_E5_sum_pow_four_rat]
  calc
    (6 : ℚ⟦X⟧) * E0 ^ 2 * E2 ^ 2 +
        (12 : ℚ⟦X⟧) * E0 * E1 ^ 2 * E2 + E1 ^ 4
        = (6 : ℚ⟦X⟧) * (E0 * E2)^2 +
          (12 : ℚ⟦X⟧) * (E0 * E2) * E1^2 + E1^4 := by ring
    _ = (6 : ℚ⟦X⟧) * (-E1^2)^2 +
          (12 : ℚ⟦X⟧) * (-E1^2) * E1^2 + E1^4 := by rw [h02]
    _ = -(5 : ℚ⟦X⟧) * E1^4 := by ring

theorem E5_bracket_eq_five_X_pow_four_expand_twentyfive_qPochInfPS_pow_four_rat :
    (E5 ℚ 0)^2 * (E5 ℚ 2)^2 -
        (3 : ℚ⟦X⟧) * E5 ℚ 0 * (E5 ℚ 1)^2 * E5 ℚ 2 +
        (E5 ℚ 1)^4 =
      (5 : ℚ⟦X⟧) * PowerSeries.X ^ 4 *
        (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ))^4 := by
  rw [E5_bracket_collapse_rat,
    E5_one_pow_four_eq_X_pow_four_expand_twentyfive_qPochInfPS_pow_four_rat]
  ring

theorem section5_four_qPochInfPS_pow_four_eq_neg_five_X_pow_four_expand_twentyfive_qPochInfPS_pow_four_rat :
    section5 ℚ 4 ((qPochInfPS ℚ)^4) =
      -(5 : ℚ⟦X⟧) * PowerSeries.X ^ 4 *
        (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ))^4 := by
  rw [section5_four_qPochInfPS_pow_four_rat,
    E5_one_pow_four_eq_X_pow_four_expand_twentyfive_qPochInfPS_pow_four_rat]
  ring

/-- The rationalized denominator core from the mod-5 dissection:
`E_0^5 + 11 E_1^5 + E_2^5`.  The remaining Route A eta-product gap is the
identity `E5DenominatorCoreRat * E(q^25) = E(q^5)^6`. -/
noncomputable def E5DenominatorCoreRat : ℚ⟦X⟧ :=
  (E5 ℚ 0)^5 + (11 : ℚ⟦X⟧) * (E5 ℚ 1)^5 + (E5 ℚ 2)^5

/-- The rationalizer numerator, reduced using `E_0 E_2 = -E_1^2`. -/
noncomputable def E5RationalizerRat : ℚ⟦X⟧ :=
  (E5 ℚ 2)^4 - E5 ℚ 1 * (E5 ℚ 2)^3 +
    (2 : ℚ⟦X⟧) * (E5 ℚ 1)^2 * (E5 ℚ 2)^2 -
    (3 : ℚ⟦X⟧) * (E5 ℚ 1)^3 * E5 ℚ 2 +
    (5 : ℚ⟦X⟧) * (E5 ℚ 1)^4 -
    (3 : ℚ⟦X⟧) * E5 ℚ 0 * (E5 ℚ 1)^3 +
    (2 : ℚ⟦X⟧) * (E5 ℚ 0)^2 * (E5 ℚ 1)^2 -
    (E5 ℚ 0)^3 * E5 ℚ 1 +
    (E5 ℚ 0)^4

theorem isRes5_E5DenominatorCoreRat :
    IsRes5 0 E5DenominatorCoreRat := by
  let E0 : ℚ⟦X⟧ := E5 ℚ 0
  let E1 : ℚ⟦X⟧ := E5 ℚ 1
  let E2 : ℚ⟦X⟧ := E5 ℚ 2
  have hE0 : IsRes5 0 E0 := by simpa [E0] using isRes5_E5 ℚ 0
  have hE1 : IsRes5 1 E1 := by simpa [E1] using isRes5_E5 ℚ 1
  have hE2 : IsRes5 2 E2 := by simpa [E2] using isRes5_E5 ℚ 2
  have hE0_5 : IsRes5 0 (E0 ^ 5) := by
    simpa using isRes5_pow hE0 5
  have hE1_5 : IsRes5 0 (E1 ^ 5) := by
    simpa using isRes5_pow hE1 5
  have hE2_5 : IsRes5 0 (E2 ^ 5) := by
    simpa using isRes5_pow hE2 5
  have h11E1_5 : IsRes5 0 ((11 : ℚ⟦X⟧) * E1 ^ 5) :=
    isRes5_natCast_mul (R := ℚ) 11 0 hE1_5
  change IsRes5 0 (E0 ^ 5 + (11 : ℚ⟦X⟧) * E1 ^ 5 + E2 ^ 5)
  exact isRes5_add (isRes5_add hE0_5 h11E1_5) hE2_5

theorem section5_four_mul_right_of_isRes5_zero_rat
    (φ ψ : ℚ⟦X⟧) (hψ : IsRes5 0 ψ) :
    section5 ℚ 4 (φ * ψ) = section5 ℚ 4 φ * ψ := by
  ext n
  rw [coeff_section5, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  by_cases hn : n % 5 = 4
  · rw [if_pos hn]
    apply Finset.sum_congr rfl
    rintro ⟨i, j⟩ hij
    rw [Finset.mem_antidiagonal] at hij
    by_cases hj : j % 5 = 0
    · have hi : i % 5 = 4 := by omega
      rw [coeff_section5, if_pos hi]
    · rw [hψ j hj, mul_zero, mul_zero]
  · rw [if_neg hn]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ hij
    rw [Finset.mem_antidiagonal] at hij
    by_cases hj : j % 5 = 0
    · have hi : i % 5 ≠ 4 := by
        intro hi
        apply hn
        omega
      rw [coeff_section5, if_neg hi, zero_mul]
    · rw [hψ j hj, mul_zero]

theorem section5_four_E5RationalizerRat :
    section5 ℚ 4 E5RationalizerRat =
      (5 : ℚ⟦X⟧) * (E5 ℚ 1)^4 := by
  let E0 : ℚ⟦X⟧ := E5 ℚ 0
  let E1 : ℚ⟦X⟧ := E5 ℚ 1
  let E2 : ℚ⟦X⟧ := E5 ℚ 2
  let T0 : ℚ⟦X⟧ := E2^4
  let T1 : ℚ⟦X⟧ := -(E1 * E2^3)
  let T2 : ℚ⟦X⟧ := (2 : ℚ⟦X⟧) * E1^2 * E2^2
  let T3 : ℚ⟦X⟧ := -((3 : ℚ⟦X⟧) * E1^3 * E2)
  let T4 : ℚ⟦X⟧ := (5 : ℚ⟦X⟧) * E1^4
  let T5 : ℚ⟦X⟧ := -((3 : ℚ⟦X⟧) * E0 * E1^3)
  let T6 : ℚ⟦X⟧ := (2 : ℚ⟦X⟧) * E0^2 * E1^2
  let T7 : ℚ⟦X⟧ := -(E0^3 * E1)
  let T8 : ℚ⟦X⟧ := E0^4
  have hE0 : IsRes5 0 E0 := by simpa [E0] using isRes5_E5 ℚ 0
  have hE1 : IsRes5 1 E1 := by simpa [E1] using isRes5_E5 ℚ 1
  have hE2 : IsRes5 2 E2 := by simpa [E2] using isRes5_E5 ℚ 2
  have hE0_sq : IsRes5 0 (E0 ^ 2) := by
    simpa using isRes5_pow hE0 2
  have hE1_sq : IsRes5 2 (E1 ^ 2) := by
    simpa using isRes5_pow hE1 2
  have hE2_sq : IsRes5 4 (E2 ^ 2) := by
    simpa using isRes5_pow hE2 2
  have hE0_cu : IsRes5 0 (E0 ^ 3) := by
    simpa using isRes5_pow hE0 3
  have hE1_cu : IsRes5 3 (E1 ^ 3) := by
    simpa using isRes5_pow hE1 3
  have hE2_cu : IsRes5 1 (E2 ^ 3) := by
    simpa using isRes5_pow hE2 3
  have hT0 : IsRes5 3 T0 := by
    simpa [T0] using isRes5_pow hE2 4
  have hT1 : IsRes5 2 T1 := by
    have h := isRes5_mul hE1 hE2_cu
    exact isRes5_neg (by simpa [T1, Nat.add_mod, Nat.mod_mod] using h)
  have hT2 : IsRes5 1 T2 := by
    have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 2 2 hE1_sq) hE2_sq
    simpa [T2, Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have hT3 : IsRes5 0 T3 := by
    have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 3 3 hE1_cu) hE2
    exact isRes5_neg (by simpa [T3, Nat.add_mod, Nat.mod_mod, mul_assoc] using h)
  have hT4 : IsRes5 4 T4 := by
    have hE1_4 : IsRes5 4 (E1 ^ 4) := by
      simpa using isRes5_pow hE1 4
    exact isRes5_natCast_mul (R := ℚ) 5 4 hE1_4
  have hT5 : IsRes5 3 T5 := by
    have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 3 0 hE0) hE1_cu
    exact isRes5_neg (by simpa [T5, Nat.add_mod, Nat.mod_mod, mul_assoc] using h)
  have hT6 : IsRes5 2 T6 := by
    have h := isRes5_mul (isRes5_natCast_mul (R := ℚ) 2 0 hE0_sq) hE1_sq
    simpa [T6, Nat.add_mod, Nat.mod_mod, mul_assoc] using h
  have hT7 : IsRes5 1 T7 := by
    have h := isRes5_mul hE0_cu hE1
    exact isRes5_neg (by simpa [T7, Nat.add_mod, Nat.mod_mod] using h)
  have hT8 : IsRes5 0 T8 := by
    simpa [T8] using isRes5_pow hE0 4
  change section5 ℚ 4 E5RationalizerRat = T4
  rw [show E5RationalizerRat = T0 + T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8 by
    simp [E5RationalizerRat, E0, E1, E2, T0, T1, T2, T3, T4, T5, T6, T7, T8]
    ring]
  simp only [section5_add]
  rw [section5_eq_if_of_isRes5 4 3 hT0,
    section5_eq_if_of_isRes5 4 2 hT1,
    section5_eq_if_of_isRes5 4 1 hT2,
    section5_eq_if_of_isRes5 4 0 hT3,
    section5_eq_if_of_isRes5 4 4 hT4,
    section5_eq_if_of_isRes5 4 3 hT5,
    section5_eq_if_of_isRes5 4 2 hT6,
    section5_eq_if_of_isRes5 4 1 hT7,
    section5_eq_if_of_isRes5 4 0 hT8]
  norm_num

theorem section5_four_E5RationalizerRat_eq_neg_section5_four_qPochInfPS_pow_four :
    section5 ℚ 4 E5RationalizerRat =
      -section5 ℚ 4 ((qPochInfPS ℚ)^4) := by
  rw [section5_four_E5RationalizerRat, section5_four_qPochInfPS_pow_four_rat]
  ring

theorem qPochInfPS_mul_E5RationalizerRat_eq_E5DenominatorCoreRat :
    qPochInfPS ℚ * E5RationalizerRat = E5DenominatorCoreRat := by
  let E0 : ℚ⟦X⟧ := E5 ℚ 0
  let E1 : ℚ⟦X⟧ := E5 ℚ 1
  let E2 : ℚ⟦X⟧ := E5 ℚ 2
  have hQ : qPochInfPS ℚ = E0 + E1 + E2 := by
    simpa [E0, E1, E2] using qPochInfPS_five_dissection ℚ
  have h02 : E0 * E2 = -E1^2 := by
    simpa [E0, E1, E2] using E5_zero_mul_two_eq_neg_one_sq_rat
  rw [hQ]
  change
    (E0 + E1 + E2) *
      (E2^4 - E1 * E2^3 + (2 : ℚ⟦X⟧) * E1^2 * E2^2 -
        (3 : ℚ⟦X⟧) * E1^3 * E2 + (5 : ℚ⟦X⟧) * E1^4 -
        (3 : ℚ⟦X⟧) * E0 * E1^3 +
        (2 : ℚ⟦X⟧) * E0^2 * E1^2 - E0^3 * E1 + E0^4) =
    E0^5 + (11 : ℚ⟦X⟧) * E1^5 + E2^5
  have hrel : E0 * E2 + E1^2 = 0 := by
    rw [h02]
    ring
  have hfactor :
      (E0 + E1 + E2) *
          (E2^4 - E1 * E2^3 + (2 : ℚ⟦X⟧) * E1^2 * E2^2 -
            (3 : ℚ⟦X⟧) * E1^3 * E2 + (5 : ℚ⟦X⟧) * E1^4 -
            (3 : ℚ⟦X⟧) * E0 * E1^3 +
            (2 : ℚ⟦X⟧) * E0^2 * E1^2 - E0^3 * E1 + E0^4) -
          (E0^5 + (11 : ℚ⟦X⟧) * E1^5 + E2^5)
        =
      (E0 * E2 + E1^2) *
        (E2^3 - E1 * E2^2 + (2 : ℚ⟦X⟧) * E1^2 * E2 -
          (6 : ℚ⟦X⟧) * E1^3 + (2 : ℚ⟦X⟧) * E0 * E1^2 -
          E0^2 * E1 + E0^3) := by
    ring
  have hzero :
      (E0 + E1 + E2) *
          (E2^4 - E1 * E2^3 + (2 : ℚ⟦X⟧) * E1^2 * E2^2 -
            (3 : ℚ⟦X⟧) * E1^3 * E2 + (5 : ℚ⟦X⟧) * E1^4 -
            (3 : ℚ⟦X⟧) * E0 * E1^3 +
            (2 : ℚ⟦X⟧) * E0^2 * E1^2 - E0^3 * E1 + E0^4) -
          (E0^5 + (11 : ℚ⟦X⟧) * E1^5 + E2^5)
        = 0 := by
    rw [hfactor, hrel]
    ring
  exact sub_eq_zero.mp hzero

theorem section5_four_partitionGenFun_mul_E5DenominatorCoreRat :
    section5 ℚ 4 (partitionGenFun ℚ) * E5DenominatorCoreRat =
      section5 ℚ 4 E5RationalizerRat := by
  have hmul : partitionGenFun ℚ * qPochInfPS ℚ = 1 :=
    partitionGenFun_mul_qPochInfPS ℚ
  have hrat :
      E5RationalizerRat = partitionGenFun ℚ * E5DenominatorCoreRat := by
    calc
      E5RationalizerRat =
          (partitionGenFun ℚ * qPochInfPS ℚ) * E5RationalizerRat := by
            rw [hmul, one_mul]
      _ = partitionGenFun ℚ * (qPochInfPS ℚ * E5RationalizerRat) := by ring
      _ = partitionGenFun ℚ * E5DenominatorCoreRat := by
            rw [qPochInfPS_mul_E5RationalizerRat_eq_E5DenominatorCoreRat]
  calc
    section5 ℚ 4 (partitionGenFun ℚ) * E5DenominatorCoreRat =
        section5 ℚ 4 (partitionGenFun ℚ * E5DenominatorCoreRat) := by
          rw [section5_four_mul_right_of_isRes5_zero_rat
            (partitionGenFun ℚ) E5DenominatorCoreRat isRes5_E5DenominatorCoreRat]
    _ = section5 ℚ 4 E5RationalizerRat := by rw [← hrat]

theorem denominator_rationalization_of_E5_denominator_identity
    (hden :
      E5DenominatorCoreRat *
          PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) =
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6) :
    section5 ℚ 4 (partitionGenFun ℚ) *
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 =
      -PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
        section5 ℚ 4 ((qPochInfPS ℚ)^4) := by
  calc
    section5 ℚ 4 (partitionGenFun ℚ) *
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 =
      section5 ℚ 4 (partitionGenFun ℚ) *
        (E5DenominatorCoreRat *
          PowerSeries.expand 25 (by decide) (qPochInfPS ℚ)) := by rw [hden]
    _ =
      (section5 ℚ 4 (partitionGenFun ℚ) * E5DenominatorCoreRat) *
        PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) := by ring
    _ =
      section5 ℚ 4 E5RationalizerRat *
        PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) := by
          rw [section5_four_partitionGenFun_mul_E5DenominatorCoreRat]
    _ =
      (-section5 ℚ 4 ((qPochInfPS ℚ)^4)) *
        PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) := by
          rw [section5_four_E5RationalizerRat_eq_neg_section5_four_qPochInfPS_pow_four]
    _ =
      -PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
        section5 ℚ 4 ((qPochInfPS ℚ)^4) := by ring

/-- The compressed residue-4 partition-generating series
`∑ p(5n+4) X^n`, over `ℚ`. -/
noncomputable def mostBeautifulLHS : ℚ⟦X⟧ :=
  PowerSeries.mk (fun n : ℕ => (partitionGenFun ℚ).coeff (5 * n + 4))

@[simp] theorem coeff_mostBeautifulLHS (n : ℕ) :
    mostBeautifulLHS.coeff n = (partitionGenFun ℚ).coeff (5 * n + 4) := by
  rw [mostBeautifulLHS, PowerSeries.coeff_mk]

/-- The numerator core on the right side of MBI, `E(q^5)^5`. -/
noncomputable def mostBeautifulRHSCore : ℚ⟦X⟧ :=
  (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)) ^ 5

/-- Compressing the residue-4 section of `partitionGenFun` is exactly the
uncompressed section after multiplying by `X^4` and expanding by 5. -/
theorem section5_four_partitionGenFun_eq_X_pow_four_mul_expand_mostBeautifulLHS :
    section5 ℚ 4 (partitionGenFun ℚ) =
      PowerSeries.X ^ 4 * PowerSeries.expand 5 (by decide) mostBeautifulLHS := by
  ext n
  rw [coeff_section5, PowerSeries.coeff_X_pow_mul']
  by_cases hmod : n % 5 = 4
  · have hn4 : 4 ≤ n := by omega
    have hdvd : 5 ∣ n - 4 := by
      refine ⟨n / 5, ?_⟩
      omega
    rw [if_pos hmod, if_pos hn4, PowerSeries.coeff_expand, if_pos hdvd]
    have hidx : 5 * ((n - 4) / 5) + 4 = n := by omega
    rw [coeff_mostBeautifulLHS, hidx]
  · rw [if_neg hmod]
    by_cases hn4 : 4 ≤ n
    · rw [if_pos hn4, PowerSeries.coeff_expand]
      have hndvd : ¬ 5 ∣ n - 4 := by
        intro hdvd
        obtain ⟨k, hk⟩ := hdvd
        have : n % 5 = 4 := by omega
        exact hmod this
      rw [if_neg hndvd]
    · rw [if_neg hn4]

/-- If the denominator-cleared form of MBI is available, then the usual formal
power-series MBI follows by multiplying by the inverse relation
`partitionGenFun * qPochInfPS = 1`. -/
theorem most_beautiful_identity_of_cleared_denominator
    (hclear :
      mostBeautifulLHS * (qPochInfPS ℚ)^6 =
        5 • mostBeautifulRHSCore) :
    mostBeautifulLHS =
      5 • (mostBeautifulRHSCore * (partitionGenFun ℚ)^6) := by
  have hmul : partitionGenFun ℚ * qPochInfPS ℚ = 1 :=
    partitionGenFun_mul_qPochInfPS ℚ
  have hpow : (partitionGenFun ℚ)^6 * (qPochInfPS ℚ)^6 = 1 := by
    rw [← mul_pow, hmul, one_pow]
  have hpow' : (qPochInfPS ℚ)^6 * (partitionGenFun ℚ)^6 = 1 := by
    rw [mul_comm, hpow]
  calc
    mostBeautifulLHS = mostBeautifulLHS *
        ((qPochInfPS ℚ)^6 * (partitionGenFun ℚ)^6) := by rw [hpow', mul_one]
    _ = (mostBeautifulLHS * (qPochInfPS ℚ)^6) * (partitionGenFun ℚ)^6 := by ring
    _ = (5 • mostBeautifulRHSCore) * (partitionGenFun ℚ)^6 := by rw [hclear]
    _ = 5 • (mostBeautifulRHSCore * (partitionGenFun ℚ)^6) := by
      norm_num [nsmul_eq_mul]
      ring

/-- Conversely, the usual formal MBI implies the denominator-cleared form. -/
theorem cleared_denominator_of_most_beautiful_identity
    (hmbi :
      mostBeautifulLHS =
        5 • (mostBeautifulRHSCore * (partitionGenFun ℚ)^6)) :
    mostBeautifulLHS * (qPochInfPS ℚ)^6 =
      5 • mostBeautifulRHSCore := by
  have hmul : partitionGenFun ℚ * qPochInfPS ℚ = 1 :=
    partitionGenFun_mul_qPochInfPS ℚ
  have hpow : (partitionGenFun ℚ)^6 * (qPochInfPS ℚ)^6 = 1 := by
    rw [← mul_pow, hmul, one_pow]
  calc
    mostBeautifulLHS * (qPochInfPS ℚ)^6 =
        (5 • (mostBeautifulRHSCore * (partitionGenFun ℚ)^6)) *
          (qPochInfPS ℚ)^6 := by rw [hmbi]
    _ = 5 • (mostBeautifulRHSCore *
        ((partitionGenFun ℚ)^6 * (qPochInfPS ℚ)^6)) := by
      norm_num [nsmul_eq_mul]
      ring
    _ = 5 • mostBeautifulRHSCore := by rw [hpow, mul_one]

/-- The full formal MBI over `ℚ` is equivalent to the denominator-cleared
identity requested in the final lift. -/
theorem most_beautiful_identity_iff_cleared_denominator :
    (mostBeautifulLHS =
      5 • (mostBeautifulRHSCore * (partitionGenFun ℚ)^6)) ↔
    (mostBeautifulLHS * (qPochInfPS ℚ)^6 =
      5 • mostBeautifulRHSCore) := by
  constructor
  · exact cleared_denominator_of_most_beautiful_identity
  · exact most_beautiful_identity_of_cleared_denominator

theorem expand_five_mostBeautifulRHSCore :
    PowerSeries.expand 5 (by decide) mostBeautifulRHSCore =
      (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ))^5 := by
  rw [mostBeautifulRHSCore, map_pow]
  rw [← PowerSeries.expand_mul (p := 5) (hp := by decide) (q := 5)
    (hq := by decide) (qPochInfPS ℚ)]

theorem X_pow_four_mul_expand_five_injective {φ ψ : ℚ⟦X⟧}
    (h :
      PowerSeries.X ^ 4 * PowerSeries.expand 5 (by decide) φ =
        PowerSeries.X ^ 4 * PowerSeries.expand 5 (by decide) ψ) :
    φ = ψ := by
  ext n
  have hcoeff := congrArg (fun θ : ℚ⟦X⟧ => θ.coeff (5 * n + 4)) h
  simpa [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_expand] using hcoeff

/-- The uncompressed Hirschhorn 5.2.6 section formula implies the
denominator-cleared MBI.  This isolates the remaining mathematical gap:
prove the left-hand hypothesis, then `most_beautiful_identity_of_cleared_denominator`
finishes the stated identity. -/
theorem cleared_denominator_of_uncompressed_section_identity
    (hsec :
      section5 ℚ 4 (partitionGenFun ℚ) *
          (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 =
        5 •
          (PowerSeries.X ^ 4 *
            (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ))^5)) :
    mostBeautifulLHS * (qPochInfPS ℚ)^6 =
      5 • mostBeautifulRHSCore := by
  apply X_pow_four_mul_expand_five_injective
  rw [map_mul, map_pow]
  calc
    PowerSeries.X ^ 4 *
        (PowerSeries.expand 5 (by decide) mostBeautifulLHS *
          (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)) ^ 6)
        =
      (PowerSeries.X ^ 4 * PowerSeries.expand 5 (by decide) mostBeautifulLHS) *
          (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)) ^ 6 := by ring
    _ =
      section5 ℚ 4 (partitionGenFun ℚ) *
          (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)) ^ 6 := by
        rw [section5_four_partitionGenFun_eq_X_pow_four_mul_expand_mostBeautifulLHS]
    _ =
      5 •
        (PowerSeries.X ^ 4 *
          (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ)) ^ 5) := hsec
    _ =
      PowerSeries.X ^ 4 *
        PowerSeries.expand 5 (by decide) (5 • mostBeautifulRHSCore) := by
        rw [map_nsmul, expand_five_mostBeautifulRHSCore]
        norm_num [nsmul_eq_mul]
        ring

/-- Final assembly wrapper: the single remaining uncompressed section identity
implies the exact formal MBI statement over `ℚ`. -/
theorem most_beautiful_identity_of_uncompressed_section_identity
    (hsec :
      section5 ℚ 4 (partitionGenFun ℚ) *
          (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 =
        5 •
          (PowerSeries.X ^ 4 *
            (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ))^5)) :
    (PowerSeries.mk
        (fun n : ℕ => (partitionGenFun ℚ).coeff (5 * n + 4)) : ℚ⟦X⟧)
      =
    5 •
      ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^5 *
        (partitionGenFun ℚ)^6) := by
  change mostBeautifulLHS =
    5 • (mostBeautifulRHSCore * (partitionGenFun ℚ)^6)
  exact most_beautiful_identity_of_cleared_denominator
    (cleared_denominator_of_uncompressed_section_identity hsec)

/-- Hirschhorn's denominator rationalization is the only missing bridge from
the already-proved residue-4 identity for `(qPochInfPS)^4` to the uncompressed
section identity. -/
theorem uncompressed_section_identity_of_denominator_rationalization
    (hrat :
      section5 ℚ 4 (partitionGenFun ℚ) *
          (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 =
        -PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
          section5 ℚ 4 ((qPochInfPS ℚ)^4)) :
      section5 ℚ 4 (partitionGenFun ℚ) *
          (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 =
        5 •
          (PowerSeries.X ^ 4 *
            (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ))^5) := by
  rw [hrat,
    section5_four_qPochInfPS_pow_four_eq_neg_five_X_pow_four_expand_twentyfive_qPochInfPS_pow_four_rat]
  norm_num [nsmul_eq_mul]
  ring

/-- Final wrapper from the precise denominator-rationalization identity. -/
theorem most_beautiful_identity_of_denominator_rationalization
    (hrat :
      section5 ℚ 4 (partitionGenFun ℚ) *
          (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 =
        -PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
          section5 ℚ 4 ((qPochInfPS ℚ)^4)) :
    (PowerSeries.mk
        (fun n : ℕ => (partitionGenFun ℚ).coeff (5 * n + 4)) : ℚ⟦X⟧)
      =
    5 •
      ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^5 *
        (partitionGenFun ℚ)^6) := by
  exact most_beautiful_identity_of_uncompressed_section_identity
    (uncompressed_section_identity_of_denominator_rationalization hrat)

theorem most_beautiful_identity_of_E5_denominator_identity
    (hden :
      E5DenominatorCoreRat *
          PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) =
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6) :
    (PowerSeries.mk
        (fun n : ℕ => (partitionGenFun ℚ).coeff (5 * n + 4)) : ℚ⟦X⟧)
      =
    5 •
      ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^5 *
        (partitionGenFun ℚ)^6) := by
  exact most_beautiful_identity_of_denominator_rationalization
    (denominator_rationalization_of_E5_denominator_identity hden)

/-! ## JTP-product reduction of the remaining denominator identity -/

private theorem map_pentagonalTripleFactor014PS_rat_complex (n : ℕ) :
    PowerSeries.map (algebraMap ℚ ℂ) (pentagonalTripleFactor014PS ℚ n) =
      pentagonalTripleFactor014PS ℂ n := by
  simp [pentagonalTripleFactor014PS, apFactorPS, PowerSeries.map_X]

private theorem map_pentagonalTripleFactor023PS_rat_complex (n : ℕ) :
    PowerSeries.map (algebraMap ℚ ℂ) (pentagonalTripleFactor023PS ℚ n) =
      pentagonalTripleFactor023PS ℂ n := by
  simp [pentagonalTripleFactor023PS, apFactorPS, PowerSeries.map_X]

private theorem map_partial_pentagonalTripleFactor014PS_rat_complex (N : ℕ) :
    PowerSeries.map (algebraMap ℚ ℂ)
        (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS ℚ n) =
      ∏ n ∈ Finset.range N, pentagonalTripleFactor014PS ℂ n := by
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro n _hn
  exact map_pentagonalTripleFactor014PS_rat_complex n

private theorem map_partial_pentagonalTripleFactor023PS_rat_complex (N : ℕ) :
    PowerSeries.map (algebraMap ℚ ℂ)
        (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS ℚ n) =
      ∏ n ∈ Finset.range N, pentagonalTripleFactor023PS ℂ n := by
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro n _hn
  exact map_pentagonalTripleFactor023PS_rat_complex n

private theorem map_pentagonalProduct014PS_rat_complex :
    PowerSeries.map (algebraMap ℚ ℂ) (pentagonalProduct014PS ℚ) =
      pentagonalProduct014PS ℂ := by
  ext n
  rw [coeff_pentagonalProduct014PS_eq_coeff_partial ℂ n]
  calc
    (PowerSeries.map (algebraMap ℚ ℂ) (pentagonalProduct014PS ℚ)).coeff n
        = (algebraMap ℚ ℂ)
          ((∏ n ∈ Finset.range (n + 1), pentagonalTripleFactor014PS ℚ n).coeff n) := by
            rw [PowerSeries.coeff_map, coeff_pentagonalProduct014PS_eq_coeff_partial ℚ n]
    _ = (PowerSeries.map (algebraMap ℚ ℂ)
          (∏ n ∈ Finset.range (n + 1), pentagonalTripleFactor014PS ℚ n)).coeff n := by
            rw [PowerSeries.coeff_map]
    _ = (∏ n ∈ Finset.range (n + 1), pentagonalTripleFactor014PS ℂ n).coeff n := by
            rw [map_partial_pentagonalTripleFactor014PS_rat_complex]

private theorem map_pentagonalProduct023PS_rat_complex :
    PowerSeries.map (algebraMap ℚ ℂ) (pentagonalProduct023PS ℚ) =
      pentagonalProduct023PS ℂ := by
  ext n
  rw [coeff_pentagonalProduct023PS_eq_coeff_partial ℂ n]
  calc
    (PowerSeries.map (algebraMap ℚ ℂ) (pentagonalProduct023PS ℚ)).coeff n
        = (algebraMap ℚ ℂ)
          ((∏ n ∈ Finset.range (n + 1), pentagonalTripleFactor023PS ℚ n).coeff n) := by
            rw [PowerSeries.coeff_map, coeff_pentagonalProduct023PS_eq_coeff_partial ℚ n]
    _ = (PowerSeries.map (algebraMap ℚ ℂ)
          (∏ n ∈ Finset.range (n + 1), pentagonalTripleFactor023PS ℚ n)).coeff n := by
            rw [PowerSeries.coeff_map]
    _ = (∏ n ∈ Finset.range (n + 1), pentagonalTripleFactor023PS ℂ n).coeff n := by
            rw [map_partial_pentagonalTripleFactor023PS_rat_complex]

private theorem map_pentagonal014SeriesPS_rat_complex :
    PowerSeries.map (algebraMap ℚ ℂ) (pentagonal014SeriesPS ℚ) =
      pentagonal014SeriesPS ℂ := by
  ext n
  rw [PowerSeries.coeff_map, coeff_pentagonal014SeriesPS, coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hk : pentagonal014Exp k = n <;> simp [hk, negOnePowInt]

private theorem map_pentagonal023SeriesPS_rat_complex :
    PowerSeries.map (algebraMap ℚ ℂ) (pentagonal023SeriesPS ℚ) =
      pentagonal023SeriesPS ℂ := by
  ext n
  rw [PowerSeries.coeff_map, coeff_pentagonal023SeriesPS, coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hk : pentagonal023Exp k = n <;> simp [hk, negOnePowInt]

/-- Rational form of the new JTP keystone
`(q,q^4,q^5;q^5)_∞ = ∑ (-1)^k X^((5k^2-3k)/2)`. -/
theorem pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat :
    pentagonalProduct014PS ℚ = pentagonal014SeriesPS ℚ := by
  ext n
  apply (algebraMap ℚ ℂ).injective
  have h := congrArg (fun φ : ℂ⟦X⟧ => φ.coeff n) (by
    calc
      PowerSeries.map (algebraMap ℚ ℂ) (pentagonalProduct014PS ℚ)
          = pentagonalProduct014PS ℂ := map_pentagonalProduct014PS_rat_complex
      _ = pentagonal014SeriesPS ℂ :=
          pentagonalProduct014PS_eq_pentagonal014SeriesPS_complex
      _ = PowerSeries.map (algebraMap ℚ ℂ) (pentagonal014SeriesPS ℚ) :=
          map_pentagonal014SeriesPS_rat_complex.symm)
  simpa [PowerSeries.coeff_map] using h

/-- Rational form of the new JTP keystone
`(q^2,q^3,q^5;q^5)_∞ = ∑ (-1)^k X^((5k^2-k)/2)`. -/
theorem pentagonalProduct023PS_eq_pentagonal023SeriesPS_rat :
    pentagonalProduct023PS ℚ = pentagonal023SeriesPS ℚ := by
  ext n
  apply (algebraMap ℚ ℂ).injective
  have h := congrArg (fun φ : ℂ⟦X⟧ => φ.coeff n) (by
    calc
      PowerSeries.map (algebraMap ℚ ℂ) (pentagonalProduct023PS ℚ)
          = pentagonalProduct023PS ℂ := map_pentagonalProduct023PS_rat_complex
      _ = pentagonal023SeriesPS ℂ :=
          pentagonalProduct023PS_eq_pentagonal023SeriesPS_complex
      _ = PowerSeries.map (algebraMap ℚ ℂ) (pentagonal023SeriesPS ℚ) :=
          map_pentagonal023SeriesPS_rat_complex.symm)
  simpa [PowerSeries.coeff_map] using h

private def finFiveSigmaNatEquivNat : (Sigma fun _ : Fin 5 => ℕ) ≃ ℕ where
  toFun p := 5 * p.2 + p.1.val
  invFun k := Sigma.mk ⟨k % 5, Nat.mod_lt k (by decide)⟩ (k / 5)
  left_inv := by
    rintro ⟨i, n⟩
    simp
    constructor
    · ext
      exact Nat.mod_eq_of_lt i.2
    · have hi : i.val < 5 := i.2
      omega
  right_inv := by
    intro k
    exact Nat.div_add_mod k 5

private theorem continuous_expand (R : Type*) [CommRing R] [TopologicalSpace R]
    (s : ℕ) (hs : s ≠ 0) :
    Continuous (PowerSeries.expand s hs : R⟦X⟧ → R⟦X⟧) := by
  rw [continuous_iff_continuousAt]
  intro φ
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simp_rw [PowerSeries.coeff_expand s hs]
  by_cases hdiv : s ∣ n
  · simpa [hdiv] using
      (PowerSeries.WithPiTopology.continuous_coeff R (n / s)).tendsto φ
  · simpa [hdiv] using tendsto_const_nhds

private theorem qPochInfPS_eq_mod_five_ap_product_rat :
    qPochInfPS ℚ =
      qPochAPPS ℚ 1 5 * qPochAPPS ℚ 2 5 * qPochAPPS ℚ 3 5 *
        qPochAPPS ℚ 4 5 * qPochAPPS ℚ 5 5 := by
  let f : ℕ → ℚ⟦X⟧ := fun k => (1 : ℚ⟦X⟧) - PowerSeries.X ^ (k + 1)
  let e : (Sigma fun _ : Fin 5 => ℕ) ≃ ℕ := finFiveSigmaNatEquivNat
  have hf : HasProd f (qPochInfPS ℚ) := by
    rw [qPochInfPS_eq_tprod ℚ]
    exact (multipliable_one_sub_X_pow_succ ℚ).hasProd
  have hsig : HasProd (f ∘ e) (qPochInfPS ℚ) :=
    (Equiv.hasProd_iff e).mpr hf
  have hfiber : ∀ i : Fin 5,
      HasProd (fun n : ℕ => (f ∘ e) (Sigma.mk i n))
        (qPochAPPS ℚ (i.val + 1) 5) := by
    intro i
    convert hasProd_qPochAPPS ℚ (i.val + 1) 5 (by norm_num) using 1
    ext n
    simp [f, e, finFiveSigmaNatEquivNat, apFactorPS]
    congr 1
    ring
  have hfin : HasProd (fun i : Fin 5 => qPochAPPS ℚ (i.val + 1) 5)
      (qPochInfPS ℚ) := hsig.sigma hfiber
  have hfin' : HasProd (fun i : Fin 5 => qPochAPPS ℚ (i.val + 1) 5)
      (∏ i : Fin 5, qPochAPPS ℚ (i.val + 1) 5) := hasProd_fintype _
  have hprod : qPochInfPS ℚ = ∏ i : Fin 5, qPochAPPS ℚ (i.val + 1) 5 :=
    hfin.unique hfin'
  rw [hprod]
  norm_num [Fin.prod_univ_five]

private theorem expand_five_qPochInfPS_eq_qPochAPPS_five_rat :
    PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) = qPochAPPS ℚ 5 5 := by
  rw [qPochInfPS_eq_tprod ℚ]
  rw [(multipliable_one_sub_X_pow_succ ℚ).map_tprod
    (PowerSeries.expand 5 (by decide)) (continuous_expand ℚ 5 (by decide))]
  unfold qPochAPPS
  apply tprod_congr
  intro n
  calc
    PowerSeries.expand 5 (by decide) ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1))
        = (1 : ℚ⟦X⟧) - PowerSeries.X ^ (5 * (n + 1)) := by
          rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
    _ = apFactorPS ℚ 5 5 n := by
          rw [apFactorPS]
          congr 1
          ring

/-- The five residue classes modulo `5` split Euler's product into the two
mod-5 JTP product factors and one extra `(q^5;q^5)_∞`. -/
theorem pentagonalProduct014_mul_pentagonalProduct023_eq_qPochInfPS_mul_expand_five_qPochInfPS_rat :
    pentagonalProduct014PS ℚ * pentagonalProduct023PS ℚ =
      qPochInfPS ℚ * PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) := by
  rw [expand_five_qPochInfPS_eq_qPochAPPS_five_rat]
  rw [qPochInfPS_eq_mod_five_ap_product_rat]
  unfold pentagonalProduct014PS pentagonalProduct023PS
  ring

theorem pentagonal014Series_mul_pentagonal023Series_eq_qPochInfPS_mul_expand_five_qPochInfPS_rat :
    pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ =
      qPochInfPS ℚ * PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) := by
  rw [← pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat,
    ← pentagonalProduct023PS_eq_pentagonal023SeriesPS_rat,
    pentagonalProduct014_mul_pentagonalProduct023_eq_qPochInfPS_mul_expand_five_qPochInfPS_rat]

/-- The first JTP factor, lifted from the `q^5` variable to the ambient
`q`-series variable. -/
noncomputable def pentagonalProduct014AtFiveRat : ℚ⟦X⟧ :=
  PowerSeries.expand 5 (by decide) (pentagonalProduct014PS ℚ)

/-- The second JTP factor, lifted from the `q^5` variable to the ambient
`q`-series variable. -/
noncomputable def pentagonalProduct023AtFiveRat : ℚ⟦X⟧ :=
  PowerSeries.expand 5 (by decide) (pentagonalProduct023PS ℚ)

/-- Cross-multiplied Ramanujan product core for the remaining denominator
identity.  This is the formal version of the quintic expression in the
Rogers-Ramanujan continued fraction. -/
noncomputable def ramanujanMod5ProductCoreRat : ℚ⟦X⟧ :=
  (pentagonalProduct023AtFiveRat)^10 -
    (11 : ℚ⟦X⟧) * PowerSeries.X^5 *
      (pentagonalProduct014AtFiveRat)^5 * (pentagonalProduct023AtFiveRat)^5 -
    PowerSeries.X^10 * (pentagonalProduct014AtFiveRat)^10

/-- The same quintic product core before the ambient substitution `X ↦ X^5`.
Expanding this by `5` gives `ramanujanMod5ProductCoreRat`. -/
noncomputable def ramanujanMod5ProductCoreCompressedRat : ℚ⟦X⟧ :=
  (pentagonalProduct023PS ℚ)^10 -
    (11 : ℚ⟦X⟧) * PowerSeries.X *
      (pentagonalProduct014PS ℚ)^5 * (pentagonalProduct023PS ℚ)^5 -
    PowerSeries.X^2 * (pentagonalProduct014PS ℚ)^10

private theorem expand_natCast_eleven_rat :
    PowerSeries.expand 5 (by decide) (11 : ℚ⟦X⟧) = (11 : ℚ⟦X⟧) := by
  rw [show (11 : ℚ⟦X⟧) = PowerSeries.C (11 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 11).symm]
  rw [PowerSeries.expand_C]

theorem expand_five_ramanujanMod5ProductCoreCompressedRat :
    PowerSeries.expand 5 (by decide) ramanujanMod5ProductCoreCompressedRat =
      ramanujanMod5ProductCoreRat := by
  unfold ramanujanMod5ProductCoreCompressedRat ramanujanMod5ProductCoreRat
  rw [map_sub, map_sub, map_pow, map_mul, map_mul, map_mul, map_pow, map_pow,
    map_mul, map_pow, map_pow]
  rw [PowerSeries.expand_X, expand_natCast_eleven_rat]
  simp [pentagonalProduct014AtFiveRat, pentagonalProduct023AtFiveRat]
  ring_nf
  left
  trivial

theorem E5_zero_eq_expand_compressedSection5_zero_qPochInfPS_rat :
    E5 ℚ 0 =
      PowerSeries.expand 5 (by decide) (compressedSection5 ℚ 0 (qPochInfPS ℚ)) := by
  ext n
  rw [E5, coeff_section5, PowerSeries.coeff_expand, coeff_compressedSection5]
  by_cases h5 : 5 ∣ n
  · rw [if_pos h5]
    have hmod : n % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
    rw [if_pos hmod]
    rw [Nat.mul_div_cancel' h5]
    simp
  · rw [if_neg h5]
    have hmod : n % 5 ≠ 0 := by
      intro hm
      exact h5 (Nat.dvd_of_mod_eq_zero hm)
    rw [if_neg hmod]

/-- Compressed form of the remaining `E_0` bridge.  This is the exact
unexpanded 5-dissection identity whose `X ↦ X^5` expansion is `hE0`. -/
theorem E5_zero_product_bridge_of_compressed
    (h :
      compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonalProduct014PS ℚ =
        PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) *
          pentagonalProduct023PS ℚ) :
    E5 ℚ 0 * pentagonalProduct014AtFiveRat =
      PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
        pentagonalProduct023AtFiveRat := by
  calc
    E5 ℚ 0 * pentagonalProduct014AtFiveRat
        =
      PowerSeries.expand 5 (by decide) (compressedSection5 ℚ 0 (qPochInfPS ℚ)) *
        PowerSeries.expand 5 (by decide) (pentagonalProduct014PS ℚ) := by
          rw [E5_zero_eq_expand_compressedSection5_zero_qPochInfPS_rat,
            pentagonalProduct014AtFiveRat]
    _ =
      PowerSeries.expand 5 (by decide)
        (compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonalProduct014PS ℚ) := by
          rw [map_mul]
    _ =
      PowerSeries.expand 5 (by decide)
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) *
          pentagonalProduct023PS ℚ) := by
          rw [h]
    _ =
      PowerSeries.expand 5 (by decide) (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)) *
        PowerSeries.expand 5 (by decide) (pentagonalProduct023PS ℚ) := by
          rw [map_mul]
    _ =
      PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
        pentagonalProduct023AtFiveRat := by
          rw [pentagonalProduct023AtFiveRat]
          rw [← PowerSeries.expand_mul (p := 5) (hp := by decide) (q := 5)
            (hq := by decide) (qPochInfPS ℚ)]

/-- Compressed form of the quintic product core.  Expanding it by `5`
recovers the `hprod` needed by the final MBI wrapper. -/
theorem mod5_product_core_bridge_of_compressed
    (h :
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreCompressedRat =
        (qPochInfPS ℚ)^6 *
          (pentagonalProduct014PS ℚ)^5 *
          (pentagonalProduct023PS ℚ)^5) :
    (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreRat =
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          (pentagonalProduct014AtFiveRat)^5 *
          (pentagonalProduct023AtFiveRat)^5 := by
  have hmap := congrArg (PowerSeries.expand 5 (by decide)) h
  rw [map_mul, map_pow, map_mul, map_mul, map_pow, map_pow, map_pow,
    expand_five_ramanujanMod5ProductCoreCompressedRat] at hmap
  rw [← PowerSeries.expand_mul (p := 5) (hp := by decide) (q := 5)
    (hq := by decide) (qPochInfPS ℚ)] at hmap
  simpa [pentagonalProduct014AtFiveRat, pentagonalProduct023AtFiveRat, mul_assoc]
    using hmap

private theorem coeff_zero_pentagonalProduct014PS_rat :
    (pentagonalProduct014PS ℚ).coeff 0 = 1 := by
  rw [coeff_pentagonalProduct014PS_eq_coeff_partial ℚ 0]
  simp [pentagonalTripleFactor014PS, apFactorPS]

private theorem coeff_zero_pentagonalProduct023PS_rat :
    (pentagonalProduct023PS ℚ).coeff 0 = 1 := by
  rw [coeff_pentagonalProduct023PS_eq_coeff_partial ℚ 0]
  simp [pentagonalTripleFactor023PS, apFactorPS]

private theorem isUnit_pentagonalProduct014AtFiveRat :
    IsUnit pentagonalProduct014AtFiveRat := by
  rw [pentagonalProduct014AtFiveRat, PowerSeries.isUnit_iff_constantCoeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_expand]
  simp [coeff_zero_pentagonalProduct014PS_rat]

private theorem isUnit_pentagonalProduct023AtFiveRat :
    IsUnit pentagonalProduct023AtFiveRat := by
  rw [pentagonalProduct023AtFiveRat, PowerSeries.isUnit_iff_constantCoeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_expand]
  simp [coeff_zero_pentagonalProduct023PS_rat]

private theorem isUnit_expand_twentyfive_qPochInfPS_rat :
    IsUnit (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_expand]
  simp [coeff_zero_qPochInfPS]

private theorem isUnit_expand_five_qPochInfPS_rat :
    IsUnit (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_expand]
  simp [coeff_zero_qPochInfPS]

/-- The `E_2` product bridge follows from the `E_0` bridge together with
Hirschhorn (5.3.1) and (5.3.2).  Thus the product-side MBI reduction only
needs the `E_0` bridge and the remaining quintic product identity as
independent inputs. -/
theorem E5_two_product_bridge_of_E5_zero_product_bridge
    (hE0 :
      E5 ℚ 0 * pentagonalProduct014AtFiveRat =
        PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
          pentagonalProduct023AtFiveRat) :
    E5 ℚ 2 * pentagonalProduct023AtFiveRat =
      -PowerSeries.X^2 * PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
        pentagonalProduct014AtFiveRat := by
  let E0 : ℚ⟦X⟧ := E5 ℚ 0
  let E1 : ℚ⟦X⟧ := E5 ℚ 1
  let E2 : ℚ⟦X⟧ := E5 ℚ 2
  let H : ℚ⟦X⟧ := pentagonalProduct014AtFiveRat
  let G : ℚ⟦X⟧ := pentagonalProduct023AtFiveRat
  let W : ℚ⟦X⟧ := PowerSeries.expand 25 (by decide) (qPochInfPS ℚ)
  have hE0' : E0 * H = W * G := by
    simpa [E0, H, W, G] using hE0
  have hE1' : E1 = -PowerSeries.X * W := by
    simpa [E1, W] using E5_one_eq_neg_X_mul_expand_twentyfive_qPochInfPS ℚ
  have h02 : E0 * E2 = -PowerSeries.X^2 * W^2 := by
    calc
      E0 * E2 = -E1^2 := by
        simpa [E0, E1, E2] using E5_zero_mul_two_eq_neg_one_sq_rat
      _ = -PowerSeries.X^2 * W^2 := by
        rw [hE1']
        ring
  have hmul :
      (E2 * G) * W = (-PowerSeries.X^2 * W * H) * W := by
    calc
      (E2 * G) * W = (W * G) * E2 := by ring
      _ = (E0 * H) * E2 := by rw [← hE0']
      _ = (E0 * E2) * H := by ring
      _ = (-PowerSeries.X^2 * W^2) * H := by rw [h02]
      _ = (-PowerSeries.X^2 * W * H) * W := by ring
  have hW_unit : IsUnit W := by
    simpa [W] using isUnit_expand_twentyfive_qPochInfPS_rat
  have hmul_left :
      W * (E2 * G) = W * (-PowerSeries.X^2 * W * H) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  change E2 * G = -PowerSeries.X^2 * W * H
  exact hW_unit.mul_right_inj.mp hmul_left

/-
Closed algebraic reduction of the remaining denominator identity.

It isolates the exact product-side work left after the new JTP keystone:
prove the two cross-multiplied identifications of `E_0,E_2` with the mod-5
JTP products, and prove the single cross-multiplied Ramanujan quintic product
identity.  These three hypotheses imply the `hden` expected by the existing
`most_beautiful_identity_of_E5_denominator_identity` wrapper.
-/
set_option maxHeartbeats 1200000 in
theorem E5_denominator_identity_of_mod5_product_bridges
    (hE0 :
      E5 ℚ 0 * pentagonalProduct014AtFiveRat =
        PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
          pentagonalProduct023AtFiveRat)
    (hE2 :
      E5 ℚ 2 * pentagonalProduct023AtFiveRat =
        -PowerSeries.X^2 * PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
          pentagonalProduct014AtFiveRat)
    (hprod :
      (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreRat =
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          (pentagonalProduct014AtFiveRat)^5 *
          (pentagonalProduct023AtFiveRat)^5) :
    E5DenominatorCoreRat *
        PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) =
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 := by
  let E0 : ℚ⟦X⟧ := E5 ℚ 0
  let E1 : ℚ⟦X⟧ := E5 ℚ 1
  let E2 : ℚ⟦X⟧ := E5 ℚ 2
  let H : ℚ⟦X⟧ := pentagonalProduct014AtFiveRat
  let G : ℚ⟦X⟧ := pentagonalProduct023AtFiveRat
  let W : ℚ⟦X⟧ := PowerSeries.expand 25 (by decide) (qPochInfPS ℚ)
  let F : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)
  have hE0' : E0 * H = W * G := by
    simpa [E0, H, W, G] using hE0
  have hE1' : E1 = -PowerSeries.X * W := by
    simpa [E1, W] using E5_one_eq_neg_X_mul_expand_twentyfive_qPochInfPS ℚ
  have hE2' : E2 * G = -PowerSeries.X^2 * W * H := by
    simpa [E2, G, W, H] using hE2
  have hE0pow : E0^5 * H^5 = W^5 * G^5 := by
    rw [← mul_pow, hE0', mul_pow]
  have hE1pow : E1^5 = -PowerSeries.X^5 * W^5 := by
    rw [hE1']
    ring
  have hE2pow : E2^5 * G^5 = -PowerSeries.X^10 * W^5 * H^5 := by
    rw [← mul_pow, hE2']
    ring
  have hE0term :
      E0^5 * W * (H^5 * G^5) = W^6 * G^10 := by
    calc
      E0^5 * W * (H^5 * G^5) = (E0^5 * H^5) * W * G^5 := by ring
      _ = (W^5 * G^5) * W * G^5 := by rw [hE0pow]
      _ = W^6 * G^10 := by ring
  have hE1term :
      (11 : ℚ⟦X⟧) * E1^5 * W * (H^5 * G^5) =
        W^6 * (-(11 : ℚ⟦X⟧) * PowerSeries.X^5 * H^5 * G^5) := by
    rw [hE1pow]
    ring
  have hE2term :
      E2^5 * W * (H^5 * G^5) =
        W^6 * (-PowerSeries.X^10 * H^10) := by
    calc
      E2^5 * W * (H^5 * G^5) = (E2^5 * G^5) * W * H^5 := by ring
      _ = (-PowerSeries.X^10 * W^5 * H^5) * W * H^5 := by rw [hE2pow]
      _ = W^6 * (-PowerSeries.X^10 * H^10) := by ring
  have hmul :
      (E5DenominatorCoreRat * W) * (H^5 * G^5) =
        F^6 * (H^5 * G^5) := by
    calc
      (E5DenominatorCoreRat * W) * (H^5 * G^5)
          =
        E0^5 * W * (H^5 * G^5) +
          (11 : ℚ⟦X⟧) * E1^5 * W * (H^5 * G^5) +
          E2^5 * W * (H^5 * G^5) := by
            simp [E5DenominatorCoreRat, E0, E1, E2]
            ring
      _ =
        W^6 * G^10 +
          W^6 * (-(11 : ℚ⟦X⟧) * PowerSeries.X^5 * H^5 * G^5) +
          W^6 * (-PowerSeries.X^10 * H^10) := by
            rw [hE0term, hE1term, hE2term]
      _ =
        W^6 * (G^10 - (11 : ℚ⟦X⟧) * PowerSeries.X^5 * H^5 * G^5 -
          PowerSeries.X^10 * H^10) := by ring
      _ = F^6 * H^5 * G^5 := by
            simpa [W, F, H, G, ramanujanMod5ProductCoreRat] using hprod
      _ = F^6 * (H^5 * G^5) := by ring
  have hHG_unit : IsUnit (H^5 * G^5) :=
    (isUnit_pentagonalProduct014AtFiveRat.pow 5).mul
      (isUnit_pentagonalProduct023AtFiveRat.pow 5)
  have hmul_left :
      (H^5 * G^5) * (E5DenominatorCoreRat * W) =
        (H^5 * G^5) * F^6 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  exact hHG_unit.mul_right_inj.mp hmul_left

/-- Final wrapper for the product-side reduction: the two `E_0/E_2` bridge
identities plus the cross-multiplied Ramanujan quintic product identity imply
the formal Most Beautiful Identity. -/
theorem most_beautiful_identity_of_mod5_product_bridges
    (hE0 :
      E5 ℚ 0 * pentagonalProduct014AtFiveRat =
        PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
          pentagonalProduct023AtFiveRat)
    (hE2 :
      E5 ℚ 2 * pentagonalProduct023AtFiveRat =
        -PowerSeries.X^2 * PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
          pentagonalProduct014AtFiveRat)
    (hprod :
      (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreRat =
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          (pentagonalProduct014AtFiveRat)^5 *
          (pentagonalProduct023AtFiveRat)^5) :
    (PowerSeries.mk
        (fun n : ℕ => (partitionGenFun ℚ).coeff (5 * n + 4)) : ℚ⟦X⟧)
      =
    5 •
      ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^5 *
        (partitionGenFun ℚ)^6) := by
  exact most_beautiful_identity_of_E5_denominator_identity
    (E5_denominator_identity_of_mod5_product_bridges hE0 hE2 hprod)

/-- Final wrapper with `hE2` discharged from `hE0`: the remaining independent
product-side inputs are the `E_0` bridge and the cross-multiplied Ramanujan
quintic product identity. -/
theorem most_beautiful_identity_of_E5_zero_bridge_and_mod5_product_core
    (hE0 :
      E5 ℚ 0 * pentagonalProduct014AtFiveRat =
        PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
          pentagonalProduct023AtFiveRat)
    (hprod :
      (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreRat =
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          (pentagonalProduct014AtFiveRat)^5 *
          (pentagonalProduct023AtFiveRat)^5) :
    (PowerSeries.mk
        (fun n : ℕ => (partitionGenFun ℚ).coeff (5 * n + 4)) : ℚ⟦X⟧)
      =
    5 •
      ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^5 *
        (partitionGenFun ℚ)^6) := by
  exact most_beautiful_identity_of_mod5_product_bridges hE0
    (E5_two_product_bridge_of_E5_zero_product_bridge hE0) hprod

/-- Final wrapper in compressed variables.  The two remaining independent
inputs are now the unexpanded 5-dissection bridge for `E_0` and the unexpanded
quintic product core. -/
theorem most_beautiful_identity_of_compressed_E5_zero_bridge_and_product_core
    (hE0 :
      compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonalProduct014PS ℚ =
        PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) *
          pentagonalProduct023PS ℚ)
    (hprod :
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreCompressedRat =
        (qPochInfPS ℚ)^6 *
          (pentagonalProduct014PS ℚ)^5 *
          (pentagonalProduct023PS ℚ)^5) :
    (PowerSeries.mk
        (fun n : ℕ => (partitionGenFun ℚ).coeff (5 * n + 4)) : ℚ⟦X⟧)
      =
    5 •
      ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^5 *
        (partitionGenFun ℚ)^6) := by
  exact most_beautiful_identity_of_E5_zero_bridge_and_mod5_product_core
    (E5_zero_product_bridge_of_compressed hE0)
    (mod5_product_core_bridge_of_compressed hprod)

/-! ## Theta-series form of the final product gaps -/

/-- The compressed `E_0` bridge with both JTP products rewritten to their
theta-series forms. -/
theorem compressed_E5_zero_bridge_of_theta
    (h :
      compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonal014SeriesPS ℚ =
        PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) *
          pentagonal023SeriesPS ℚ) :
      compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonalProduct014PS ℚ =
        PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) *
          pentagonalProduct023PS ℚ := by
  rw [pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat,
    pentagonalProduct023PS_eq_pentagonal023SeriesPS_rat]
  exact h

/-- The compressed `E_0` bridge is exactly its theta-series rewrite. -/
theorem compressed_E5_zero_bridge_theta_iff :
    (compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonalProduct014PS ℚ =
        PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) *
          pentagonalProduct023PS ℚ) ↔
      (compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonal014SeriesPS ℚ =
        PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) *
          pentagonal023SeriesPS ℚ) := by
  rw [pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat,
    pentagonalProduct023PS_eq_pentagonal023SeriesPS_rat]

/-- Coefficient-matching form of the compressed `E_0` theta bridge. -/
theorem compressed_E5_zero_bridge_theta_of_coeff
    (hcoeff :
      ∀ n : ℕ,
        (∑ ij ∈ Finset.antidiagonal n,
          (qPochInfPS ℚ).coeff (5 * ij.1) *
            (pentagonal014SeriesPS ℚ).coeff ij.2) =
        (∑ ij ∈ Finset.antidiagonal n,
          (if 5 ∣ ij.1 then (qPochInfPS ℚ).coeff (ij.1 / 5) else 0) *
            (pentagonal023SeriesPS ℚ).coeff ij.2)) :
      compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonal014SeriesPS ℚ =
        PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) *
          pentagonal023SeriesPS ℚ := by
  ext n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  simpa [coeff_compressedSection5, PowerSeries.coeff_expand] using hcoeff n

/-- Theta-series rewrite of the compressed Ramanujan quintic core. -/
noncomputable def ramanujanMod5ProductCoreThetaRat : ℚ⟦X⟧ :=
  (pentagonal023SeriesPS ℚ)^10 -
    (11 : ℚ⟦X⟧) * PowerSeries.X *
      (pentagonal014SeriesPS ℚ)^5 * (pentagonal023SeriesPS ℚ)^5 -
    PowerSeries.X^2 * (pentagonal014SeriesPS ℚ)^10

/-- The compressed quintic core with both JTP products rewritten by the
rational keystone. -/
theorem ramanujanMod5ProductCoreCompressedRat_eq_theta :
    ramanujanMod5ProductCoreCompressedRat =
      ramanujanMod5ProductCoreThetaRat := by
  unfold ramanujanMod5ProductCoreCompressedRat ramanujanMod5ProductCoreThetaRat
  rw [pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat,
    pentagonalProduct023PS_eq_pentagonal023SeriesPS_rat]

/-- The compressed quintic product gap follows from its theta-series rewrite. -/
theorem mod5_product_core_compressed_of_theta
    (h :
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreThetaRat =
        (qPochInfPS ℚ)^6 *
          (pentagonal014SeriesPS ℚ)^5 *
          (pentagonal023SeriesPS ℚ)^5) :
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreCompressedRat =
        (qPochInfPS ℚ)^6 *
          (pentagonalProduct014PS ℚ)^5 *
          (pentagonalProduct023PS ℚ)^5 := by
  rw [ramanujanMod5ProductCoreCompressedRat_eq_theta,
    pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat,
    pentagonalProduct023PS_eq_pentagonal023SeriesPS_rat]
  exact h

/-- The compressed quintic product gap is exactly its theta-series rewrite. -/
theorem mod5_product_core_compressed_theta_iff :
    ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreCompressedRat =
        (qPochInfPS ℚ)^6 *
          (pentagonalProduct014PS ℚ)^5 *
          (pentagonalProduct023PS ℚ)^5) ↔
      ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreThetaRat =
        (qPochInfPS ℚ)^6 *
          (pentagonal014SeriesPS ℚ)^5 *
          (pentagonal023SeriesPS ℚ)^5) := by
  rw [ramanujanMod5ProductCoreCompressedRat_eq_theta,
    pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat,
    pentagonalProduct023PS_eq_pentagonal023SeriesPS_rat]

/-- Route-3 reduction of the compressed quintic gap to Hirschhorn's clean
product identity `(core) * E(q^5) = E(q)^11`. -/
theorem mod5_product_core_compressed_theta_of_clean_quintic
    (hclean :
      ramanujanMod5ProductCoreThetaRat *
          PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) =
        (qPochInfPS ℚ)^11) :
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreThetaRat =
        (qPochInfPS ℚ)^6 *
          (pentagonal014SeriesPS ℚ)^5 *
          (pentagonal023SeriesPS ℚ)^5 := by
  let E : ℚ⟦X⟧ := qPochInfPS ℚ
  let P5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)
  let H : ℚ⟦X⟧ := pentagonal014SeriesPS ℚ
  let G : ℚ⟦X⟧ := pentagonal023SeriesPS ℚ
  let C : ℚ⟦X⟧ := ramanujanMod5ProductCoreThetaRat
  have hHG : H * G = E * P5 := by
    simpa [H, G, E, P5] using
      pentagonal014Series_mul_pentagonal023Series_eq_qPochInfPS_mul_expand_five_qPochInfPS_rat
  have hHG5 : H^5 * G^5 = E^5 * P5^5 := by
    calc
      H^5 * G^5 = (H * G)^5 := by ring
      _ = (E * P5)^5 := by rw [hHG]
      _ = E^5 * P5^5 := by ring
  have hclean' : C * P5 = E^11 := by
    simpa [C, P5, E] using hclean
  change P5^6 * C = E^6 * H^5 * G^5
  calc
    P5^6 * C = P5^5 * (C * P5) := by ring
    _ = P5^5 * E^11 := by rw [hclean']
    _ = E^6 * (E^5 * P5^5) := by ring
    _ = E^6 * (H^5 * G^5) := by rw [hHG5]
    _ = E^6 * H^5 * G^5 := by ring

/-- The existing compressed theta `hprod` gap is equivalent to the cleaner
Hirschhorn 8.5.6 cross-multiplied identity `core * E(q^5) = E(q)^11`. -/
theorem mod5_product_core_compressed_theta_iff_clean_quintic :
    ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreThetaRat =
        (qPochInfPS ℚ)^6 *
          (pentagonal014SeriesPS ℚ)^5 *
          (pentagonal023SeriesPS ℚ)^5) ↔
      (ramanujanMod5ProductCoreThetaRat *
          PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) =
        (qPochInfPS ℚ)^11) := by
  constructor
  · intro hprod
    let E : ℚ⟦X⟧ := qPochInfPS ℚ
    let P5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)
    let H : ℚ⟦X⟧ := pentagonal014SeriesPS ℚ
    let G : ℚ⟦X⟧ := pentagonal023SeriesPS ℚ
    let C : ℚ⟦X⟧ := ramanujanMod5ProductCoreThetaRat
    have hHG : H * G = E * P5 := by
      simpa [H, G, E, P5] using
        pentagonal014Series_mul_pentagonal023Series_eq_qPochInfPS_mul_expand_five_qPochInfPS_rat
    have hHG5 : H^5 * G^5 = E^5 * P5^5 := by
      calc
        H^5 * G^5 = (H * G)^5 := by ring
        _ = (E * P5)^5 := by rw [hHG]
        _ = E^5 * P5^5 := by ring
    have hprod' : P5^6 * C = E^6 * H^5 * G^5 := by
      simpa [P5, C, E, H, G] using hprod
    have hmul : (C * P5) * P5^5 = E^11 * P5^5 := by
      calc
        (C * P5) * P5^5 = P5^6 * C := by ring
        _ = E^6 * H^5 * G^5 := hprod'
        _ = E^6 * (H^5 * G^5) := by ring
        _ = E^6 * (E^5 * P5^5) := by rw [hHG5]
        _ = E^11 * P5^5 := by ring
    have hP5_unit : IsUnit (P5^5) := by
      simpa [P5] using isUnit_expand_five_qPochInfPS_rat.pow 5
    have hmul_left : P5^5 * (C * P5) = P5^5 * E^11 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have hclean : C * P5 = E^11 := hP5_unit.mul_right_inj.mp hmul_left
    simpa [C, P5, E] using hclean
  · exact mod5_product_core_compressed_theta_of_clean_quintic

/-- Coefficient-matching form of the compressed quintic theta bridge. -/
theorem mod5_product_core_compressed_theta_of_coeff
    (hcoeff :
      ∀ n : ℕ,
        ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
            ramanujanMod5ProductCoreThetaRat).coeff n =
          ((qPochInfPS ℚ)^6 *
            (pentagonal014SeriesPS ℚ)^5 *
            (pentagonal023SeriesPS ℚ)^5).coeff n) :
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreThetaRat =
        (qPochInfPS ℚ)^6 *
          (pentagonal014SeriesPS ℚ)^5 *
          (pentagonal023SeriesPS ℚ)^5 := by
  ext n
  exact hcoeff n

/-- Final wrapper in theta-series variables.  This is the same two-gap
reduction as `most_beautiful_identity_of_compressed_E5_zero_bridge_and_product_core`,
but with the `pentagonalProduct0xxPS ℚ` factors already rewritten by the
`ℚ` JTP keystone. -/
theorem most_beautiful_identity_of_compressed_theta_bridges
    (hE0 :
      compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonal014SeriesPS ℚ =
        PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) *
          pentagonal023SeriesPS ℚ)
    (hprod :
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreThetaRat =
        (qPochInfPS ℚ)^6 *
          (pentagonal014SeriesPS ℚ)^5 *
          (pentagonal023SeriesPS ℚ)^5) :
    (PowerSeries.mk
        (fun n : ℕ => (partitionGenFun ℚ).coeff (5 * n + 4)) : ℚ⟦X⟧)
      =
    5 •
      ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^5 *
        (partitionGenFun ℚ)^6) := by
  exact most_beautiful_identity_of_compressed_E5_zero_bridge_and_product_core
    (compressed_E5_zero_bridge_of_theta hE0)
    (mod5_product_core_compressed_of_theta hprod)

/-- Final wrapper using the cleaner Route-3 quintic product identity
`ramanujanMod5ProductCoreThetaRat * E(q^5) = E(q)^11`. -/
theorem most_beautiful_identity_of_compressed_theta_clean_quintic
    (hE0 :
      compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonal014SeriesPS ℚ =
        PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) *
          pentagonal023SeriesPS ℚ)
    (hclean :
      ramanujanMod5ProductCoreThetaRat *
          PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) =
        (qPochInfPS ℚ)^11) :
    (PowerSeries.mk
        (fun n : ℕ => (partitionGenFun ℚ).coeff (5 * n + 4)) : ℚ⟦X⟧)
      =
    5 •
      ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^5 *
        (partitionGenFun ℚ)^6) := by
  exact most_beautiful_identity_of_compressed_theta_bridges hE0
    (mod5_product_core_compressed_theta_of_clean_quintic hclean)

/-- Final wrapper from the two explicit coefficient-matching obligations after
the `ℚ` JTP keystone has rewritten the product factors to theta series. -/
theorem most_beautiful_identity_of_compressed_theta_coeffs
    (hE0_coeff :
      ∀ n : ℕ,
        (∑ ij ∈ Finset.antidiagonal n,
          (qPochInfPS ℚ).coeff (5 * ij.1) *
            (pentagonal014SeriesPS ℚ).coeff ij.2) =
        (∑ ij ∈ Finset.antidiagonal n,
          (if 5 ∣ ij.1 then (qPochInfPS ℚ).coeff (ij.1 / 5) else 0) *
            (pentagonal023SeriesPS ℚ).coeff ij.2))
    (hprod_coeff :
      ∀ n : ℕ,
        ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
            ramanujanMod5ProductCoreThetaRat).coeff n =
          ((qPochInfPS ℚ)^6 *
            (pentagonal014SeriesPS ℚ)^5 *
            (pentagonal023SeriesPS ℚ)^5).coeff n) :
    (PowerSeries.mk
        (fun n : ℕ => (partitionGenFun ℚ).coeff (5 * n + 4)) : ℚ⟦X⟧)
      =
    5 •
      ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^5 *
        (partitionGenFun ℚ)^6) := by
  exact most_beautiful_identity_of_compressed_theta_bridges
    (compressed_E5_zero_bridge_theta_of_coeff hE0_coeff)
    (mod5_product_core_compressed_theta_of_coeff hprod_coeff)

/-- Injectivity of the substitution `X ↦ X^5` over rational power series. -/
theorem expand_five_injective_rat {φ ψ : ℚ⟦X⟧}
    (h : PowerSeries.expand 5 (by decide) φ = PowerSeries.expand 5 (by decide) ψ) :
    φ = ψ := by
  ext n
  have hcoeff := congrArg (fun θ : ℚ⟦X⟧ => θ.coeff (5 * n)) h
  change (PowerSeries.expand 5 (by decide) φ).coeff (5 * n) =
    (PowerSeries.expand 5 (by decide) ψ).coeff (5 * n) at hcoeff
  rw [PowerSeries.coeff_expand, PowerSeries.coeff_expand] at hcoeff
  have hdvd : 5 ∣ 5 * n := dvd_mul_right 5 n
  rw [if_pos hdvd, if_pos hdvd] at hcoeff
  simpa [Nat.mul_div_right n (by decide : 0 < 5)] using hcoeff

end Ch16MBIProof
end Pending
end QseriesFormalization
