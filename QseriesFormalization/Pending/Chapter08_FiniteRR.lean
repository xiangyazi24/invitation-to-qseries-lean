import QseriesFormalization.Chapter08
import QseriesFormalization.Chapter03

/-!
# Chapter 8 finite Rogers-Ramanujan sum side

Chan's Section 8.1 writes
`E_n(a) = sum_j q^(j^2 + a*j) [n-j-1 choose j]_q` and proves the
second-order recurrence
`E_{n+1}(a) = E_n(a) + q^(n+a-1) E_{n-1}(a)`.

The zero-based definition below is `EFinite q a N = E_{N+1}(a)`.
-/

namespace QseriesFormalization
namespace PartII
namespace Ch08

section Field

variable {R : Type*} [Field R]

/-- The finite Gaussian-polynomial sum side of Chan Theorem 8.1.
This is Chan's `E_{N+1}(a)`: `sum_j q^(j^2+a*j) [N-j choose j]_q`. -/
noncomputable def EFinite (q : R) (a N : Nat) : R :=
  ∑ j ∈ Finset.range (N + 1), q ^ (j ^ 2 + a * j) * gaussianBinom q (N - j) j

/-- Initial value `E_1(a) = 1`, in zero-based indexing. -/
@[simp] theorem EFinite_zero (q : R) (a : Nat) :
    EFinite q a 0 = 1 := by
  simp [EFinite]

/-- Initial value `E_2(a) = 1`, in zero-based indexing. -/
@[simp] theorem EFinite_one (q : R) (a : Nat) :
    EFinite q a 1 = 1 := by
  simp [EFinite, Finset.sum_range_succ, gaussianBinom]

private theorem EFinite_termB_eq (q : R) (a N j : Nat) :
    q ^ ((j + 1) ^ 2 + a * (j + 1) + ((N - j) - j)) *
        gaussianBinom q (N - j) j =
      q ^ (N + a + 1) *
        (q ^ (j ^ 2 + a * j) * gaussianBinom q (N - j) j) := by
  by_cases h2j : 2 * j ≤ N
  · have hsub : (N - j) - j = N - 2 * j := by omega
    have hexp :
        (j + 1) ^ 2 + a * (j + 1) + ((N - j) - j) =
          (N + a + 1) + (j ^ 2 + a * j) := by
      rw [hsub]
      ring_nf
      omega
    rw [hexp, pow_add]
    ring
  · have hlt : N - j < j := by omega
    rw [PartI.Ch03.gaussianBinom_eq_zero_of_lt q hlt]
    ring

private theorem EFinite_pascal_term (q : R) (a N j : Nat) (hj : j ≤ N) :
    q ^ ((j + 1) ^ 2 + a * (j + 1)) *
        gaussianBinom q (N + 1 - j) (j + 1) =
      q ^ ((j + 1) ^ 2 + a * (j + 1)) *
          gaussianBinom q (N - j) (j + 1) +
        q ^ (N + a + 1) *
          (q ^ (j ^ 2 + a * j) * gaussianBinom q (N - j) j) := by
  have hN :
      N + 1 - j = (N - j) + 1 := by omega
  rw [hN]
  show q ^ ((j + 1) ^ 2 + a * (j + 1)) *
        (gaussianBinom q (N - j) (j + 1) +
          q ^ ((N - j) - j) * gaussianBinom q (N - j) j) = _
  rw [mul_add]
  congr 1
  rw [← mul_assoc, ← pow_add]
  exact EFinite_termB_eq q a N j

/-- Chan Eq. (8.2) for the finite sum side, in zero-based indexing:
`EFinite q a N` is Chan's `E_{N+1}(a)`, so the displayed exponent is
`N + a + 1`. -/
theorem EFinite_recurrence (q : R) (a N : Nat) :
    EFinite q a (N + 2) =
      EFinite q a (N + 1) + q ^ (N + a + 1) * EFinite q a N := by
  rw [EFinite, Finset.sum_range_succ']
  simp only [Nat.sub_zero, gaussianBinom_zero_right]
  rw [Finset.sum_range_succ]
  have h_last_zero :
      q ^ ((N + 1 + 1) ^ 2 + a * (N + 1 + 1)) *
          gaussianBinom q (N + 2 - (N + 1 + 1)) (N + 1 + 1) = 0 := by
    have htop : N + 2 - (N + 1 + 1) = 0 := by omega
    rw [htop]
    rw [PartI.Ch03.gaussianBinom_eq_zero_of_lt q
      (by omega : (0 : Nat) < N + 1 + 1)]
    ring
  rw [h_last_zero, add_zero]
  have h_sum_eq :
      ∑ j ∈ Finset.range (N + 1),
          q ^ ((j + 1) ^ 2 + a * (j + 1)) *
            gaussianBinom q (N + 2 - (j + 1)) (j + 1) =
        (∑ j ∈ Finset.range (N + 1),
          q ^ ((j + 1) ^ 2 + a * (j + 1)) *
            gaussianBinom q (N - j) (j + 1)) +
          q ^ (N + a + 1) *
            (∑ j ∈ Finset.range (N + 1),
              q ^ (j ^ 2 + a * j) * gaussianBinom q (N - j) j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjN : j ≤ N := by
      simp only [Finset.mem_range] at hj
      omega
    have htop :
        N + 2 - (j + 1) = N + 1 - j := by omega
    rw [htop, EFinite_pascal_term q a N j hjN]
  rw [h_sum_eq]
  have h_E_succ :
      EFinite q a (N + 1) =
        1 + ∑ j ∈ Finset.range (N + 1),
          q ^ ((j + 1) ^ 2 + a * (j + 1)) *
            gaussianBinom q (N - j) (j + 1) := by
    rw [EFinite, Finset.sum_range_succ']
    have h0 :
        q ^ ((0 : Nat) ^ 2 + a * 0) * gaussianBinom q (N + 1 - 0) 0 = 1 := by
      simp
    rw [h0, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjN : j ≤ N := by
      simp only [Finset.mem_range] at hj
      omega
    congr 2
    omega
  have h_E_N :
      EFinite q a N =
        ∑ j ∈ Finset.range (N + 1),
          q ^ (j ^ 2 + a * j) * gaussianBinom q (N - j) j := rfl
  rw [h_E_succ, h_E_N]
  ring

/-- Chan Eq. (8.2) written in the book's one-based indexing:
since `EFinite q a N` is `E_{N+1}(a)`, this is
`E_{n+1}(a) = E_n(a) + q^(n+a-1) E_{n-1}(a)` for `n ≥ 2`. -/
theorem EFinite_chan_eq_8_2_of_two_le (q : R) (a n : Nat) (hn : 2 ≤ n) :
    EFinite q a n =
      EFinite q a (n - 1) + q ^ (n + a - 1) * EFinite q a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m : Nat, n = m + 2 := ⟨n - 2, by omega⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EFinite_recurrence q a m

/-! ### Chan's finite alternating Gaussian-polynomial side -/

/-- Integer exponent in Chan's alternating side:
`j(5j+1)/2 - 2aj`. -/
def DFiniteExponent (a : Nat) (j : Int) : Int :=
  (j * (5 * j + 1)) / 2 - 2 * (a : Int) * j

/-- Integer lower index in Chan's alternating side:
`⌊(N+3a-5j)/2⌋`.  Lean's integer division by positive `2` is floor division. -/
def DFiniteLower (a N : Nat) (j : Int) : Int :=
  ((N : Int) + 3 * (a : Int) - 5 * j) / 2

/-- A Gaussian binomial with an integer lower index, interpreted as zero
when the lower index is negative.  If the lower index is above the top, the
existing `gaussianBinom_eq_zero_of_lt` lemma supplies the zero value. -/
noncomputable def gaussianBinomIntLower (q : R) (top : Nat) (k : Int) : R :=
  if 0 ≤ k then gaussianBinom q top k.toNat else 0

/-- A symmetric finite bound large enough to contain all possible nonzero
terms of Chan's finite alternating sum. -/
def DFiniteBound (a N : Nat) : Nat :=
  N + 3 * a + 2

/-- One summand of Chan's finite alternating Gaussian-polynomial side. -/
noncomputable def DFiniteTerm (q : R) (a N : Nat) (j : Int) : R :=
  (-1 : R) ^ j * q ^ DFiniteExponent a j *
    gaussianBinomIntLower q (N + a) (DFiniteLower a N j)

/-- Chan's finite alternating Gaussian-polynomial side of Theorem 8.1:
`Σ_j (-1)^j q^(j(5j+1)/2-2aj) [N+a ; ⌊(N+3a-5j)/2⌋]_q`.

The finite bilateral sum uses `DFiniteBound`; outside this bound the integer
lower q-binomial index is out of range. -/
noncomputable def DFinite (q : R) (a N : Nat) : R :=
  bilateralSum (DFiniteTerm q a N) (DFiniteBound a N)

@[simp] theorem DFinite_zero_zero (q : R) :
    DFinite q 0 0 = 1 := by
  simp [DFinite, DFiniteTerm, DFiniteBound, DFiniteExponent, DFiniteLower,
    gaussianBinomIntLower, bilateralSum]

@[simp] theorem DFinite_zero_one (q : R) :
    DFinite q 0 1 = 1 := by
  simp [DFinite, DFiniteTerm, DFiniteBound, DFiniteExponent, DFiniteLower,
    gaussianBinomIntLower, bilateralSum]

@[simp] theorem DFinite_one_zero (q : R) :
    DFinite q 1 0 = 1 := by
  simp [DFinite, DFiniteTerm, DFiniteBound, DFiniteExponent, DFiniteLower,
    gaussianBinomIntLower, bilateralSum]

@[simp] theorem DFinite_one_one (q : R) :
    DFinite q 1 1 = 1 := by
  simp [DFinite, DFiniteTerm, DFiniteBound, DFiniteExponent, DFiniteLower,
    gaussianBinomIntLower, bilateralSum]

@[simp] theorem DFinite_zero_two (q : R) :
    DFinite q 0 2 = 1 + q := by
  simp [DFinite, DFiniteTerm, DFiniteBound, DFiniteExponent, DFiniteLower,
    gaussianBinomIntLower, bilateralSum, gaussianBinom]

@[simp] theorem DFinite_one_two (q : R) :
    DFinite q 1 2 = 1 + q ^ 2 := by
  simp [DFinite, DFiniteTerm, DFiniteBound, DFiniteExponent, DFiniteLower,
    gaussianBinomIntLower, bilateralSum, gaussianBinom]
  ring

theorem DFinite_a0_recurrence_zero (q : R) :
    DFinite q 0 2 = DFinite q 0 1 + q ^ 1 * DFinite q 0 0 := by
  simp

theorem DFinite_a1_recurrence_zero (q : R) :
    DFinite q 1 2 = DFinite q 1 1 + q ^ 2 * DFinite q 1 0 := by
  simp

/-! ### Alternating-side recurrence for the Rogers-Ramanujan cases -/

@[simp] private theorem gaussianBinomIntLower_neg (q : R) (top : Nat) (k : Int)
    (hk : k < 0) : gaussianBinomIntLower q top k = 0 := by
  simp [gaussianBinomIntLower, not_le.mpr hk]

@[simp] private theorem gaussianBinomIntLower_gt (q : R) (top : Nat) (k : Int)
    (hk : (top : Int) < k) : gaussianBinomIntLower q top k = 0 := by
  unfold gaussianBinomIntLower
  by_cases hk0 : 0 ≤ k
  · rw [if_pos hk0]
    rw [PartI.Ch03.gaussianBinom_eq_zero_of_lt q]
    omega
  · rw [if_neg hk0]

private theorem gaussianBinomIntLower_eq (q : R) (top : Nat) (k : Int)
    (hk0 : 0 ≤ k) :
    gaussianBinomIntLower q top k = gaussianBinom q top k.toNat := by
  simp [gaussianBinomIntLower, hk0]

private theorem gaussianBinomIntLower_natCast (q : R) (top k : Nat) :
    gaussianBinomIntLower q top (k : Int) = gaussianBinom q top k := by
  simp [gaussianBinomIntLower]

private lemma gaussianBinomIntLower_zero_right (q : R) (top : Nat) :
    gaussianBinomIntLower q top 0 = 1 := by
  simp [gaussianBinomIntLower]

private theorem gaussianBinomIntLower_lower1 (q : R) (top : Nat) (k : Int) :
    gaussianBinomIntLower q (top + 1) k =
      gaussianBinomIntLower q top k +
        q ^ ((top : Int) + 1 - k).toNat * gaussianBinomIntLower q top (k - 1) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [gaussianBinomIntLower_neg q (top + 1) k hk,
      gaussianBinomIntLower_neg q top k hk,
      gaussianBinomIntLower_neg q top (k - 1) (by omega)]
    ring
  · subst hk
    rw [gaussianBinomIntLower_zero_right, gaussianBinomIntLower_zero_right,
      gaussianBinomIntLower_neg q top ((0 : Int) - 1) (by norm_num)]
    ring
  · obtain ⟨m, rfl⟩ : ∃ m : Nat, k = (m : Int) :=
      ⟨k.toNat, (Int.toNat_of_nonneg hk.le).symm⟩
    have hm : 1 ≤ m := by exact_mod_cast hk
    obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
    rw [show ((l + 1 : Nat) : Int) - 1 = ((l : Nat) : Int) by push_cast; ring,
      gaussianBinomIntLower_natCast, gaussianBinomIntLower_natCast,
      gaussianBinomIntLower_natCast]
    by_cases hltop : l + 1 ≤ top
    · have hrec : gaussianBinom q (top + 1) (l + 1) =
          gaussianBinom q top (l + 1) + q ^ (top - l) * gaussianBinom q top l := rfl
      rw [hrec,
        show ((top : Int) + 1 - ((l + 1 : Nat) : Int)).toNat = top - l by
          push_cast; omega]
    · by_cases htopl : top = l
      · rw [← htopl, PartI.Ch03.gaussianBinom_self, PartI.Ch03.gaussianBinom_self,
          PartI.Ch03.gaussianBinom_eq_zero_of_lt q (Nat.lt_succ_self top),
          show ((top : Int) + 1 - ((top + 1 : Nat) : Int)).toNat = 0 by
            push_cast; omega]
        ring
      · rw [PartI.Ch03.gaussianBinom_eq_zero_of_lt q (show top + 1 < l + 1 by omega),
          PartI.Ch03.gaussianBinom_eq_zero_of_lt q (show top < l + 1 by omega),
          PartI.Ch03.gaussianBinom_eq_zero_of_lt q (show top < l by omega)]
        ring

private theorem gaussianBinomIntLower_upper1 (q : R) (top : Nat) (k : Int) :
    gaussianBinomIntLower q (top + 1) k =
      q ^ k.toNat * gaussianBinomIntLower q top k +
        gaussianBinomIntLower q top (k - 1) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [gaussianBinomIntLower_neg q (top + 1) k hk,
      gaussianBinomIntLower_neg q top k hk,
      gaussianBinomIntLower_neg q top (k - 1) (by omega)]
    ring
  · subst hk
    rw [gaussianBinomIntLower_zero_right, gaussianBinomIntLower_zero_right,
      gaussianBinomIntLower_neg q top ((0 : Int) - 1) (by norm_num)]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m : Nat, k = (m : Int) :=
      ⟨k.toNat, (Int.toNat_of_nonneg hk.le).symm⟩
    have hm : 1 ≤ m := by exact_mod_cast hk
    obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
    rw [Int.toNat_natCast,
      show ((l + 1 : Nat) : Int) - 1 = ((l : Nat) : Int) by push_cast; ring,
      gaussianBinomIntLower_natCast, gaussianBinomIntLower_natCast,
      gaussianBinomIntLower_natCast]
    by_cases hltop : l + 1 ≤ top
    · exact PartI.Ch03.gaussianBinom_pascal_alt q top l (by omega)
    · by_cases htopl : top = l
      · rw [← htopl, PartI.Ch03.gaussianBinom_self, PartI.Ch03.gaussianBinom_self,
          PartI.Ch03.gaussianBinom_eq_zero_of_lt q (Nat.lt_succ_self top)]
        ring
      · rw [PartI.Ch03.gaussianBinom_eq_zero_of_lt q (show top + 1 < l + 1 by omega),
          PartI.Ch03.gaussianBinom_eq_zero_of_lt q (show top < l + 1 by omega),
          PartI.Ch03.gaussianBinom_eq_zero_of_lt q (show top < l by omega)]
        ring

private theorem gaussianBinomIntLower_even_residual (q : R) (top : Nat) (b : Int) :
    gaussianBinomIntLower q (top + 2) (b + 1) -
        gaussianBinomIntLower q (top + 1) b -
        q ^ (top + 1) * gaussianBinomIntLower q top b =
      q ^ (b + 1).toNat * gaussianBinomIntLower q top (b + 1) := by
  have htop2 : top + 1 + 1 = top + 2 := by omega
  have hup := gaussianBinomIntLower_upper1 q (top + 1) (b + 1)
  rw [htop2, show (b + 1 : Int) - 1 = b from by ring] at hup
  have hlo := gaussianBinomIntLower_lower1 q top (b + 1)
  rw [show (b + 1 : Int) - 1 = b from by ring] at hlo
  have hkill :
      q ^ (b + 1).toNat *
          (q ^ ((top : Int) + 1 - (b + 1)).toNat * gaussianBinomIntLower q top b) =
        q ^ (top + 1) * gaussianBinomIntLower q top b := by
    by_cases hb : 0 ≤ b ∧ b ≤ (top : Int)
    · obtain ⟨hb0, hbtop⟩ := hb
      have he : (b + 1).toNat + ((top : Int) + 1 - (b + 1)).toNat = top + 1 := by
        omega
      rw [← mul_assoc, ← pow_add, he]
    · have hz : gaussianBinomIntLower q top b = 0 := by
        rcases not_and_or.mp hb with h | h
        · exact gaussianBinomIntLower_neg q top b (by omega)
        · exact gaussianBinomIntLower_gt q top b (by omega)
      rw [hz]
      ring
  rw [hup, hlo, mul_add, hkill]
  ring

private theorem gaussianBinomIntLower_odd_residual (q : R) (top : Nat) (b : Int) :
    gaussianBinomIntLower q (top + 2) (b + 1) -
        gaussianBinomIntLower q (top + 1) (b + 1) -
        q ^ (top + 1) * gaussianBinomIntLower q top b =
      q ^ ((top : Int) + 1 - b).toNat * gaussianBinomIntLower q top (b - 1) := by
  have htop2 : top + 1 + 1 = top + 2 := by omega
  have hexp : ((top + 1 : Nat) : Int) + 1 - (b + 1) = (top : Int) + 1 - b := by
    push_cast
    ring
  have hlo2 := gaussianBinomIntLower_lower1 q (top + 1) (b + 1)
  rw [htop2, show (b + 1 : Int) - 1 = b from by ring, hexp] at hlo2
  have hup2 := gaussianBinomIntLower_upper1 q top b
  have hkill :
      q ^ ((top : Int) + 1 - b).toNat *
          (q ^ b.toNat * gaussianBinomIntLower q top b) =
        q ^ (top + 1) * gaussianBinomIntLower q top b := by
    by_cases hb : 0 ≤ b ∧ b ≤ (top : Int)
    · obtain ⟨hb0, hbtop⟩ := hb
      have he : ((top : Int) + 1 - b).toNat + b.toNat = top + 1 := by
        omega
      rw [← mul_assoc, ← pow_add, he]
    · have hz : gaussianBinomIntLower q top b = 0 := by
        rcases not_and_or.mp hb with h | h
        · exact gaussianBinomIntLower_neg q top b (by omega)
        · exact gaussianBinomIntLower_gt q top b (by omega)
      rw [hz]
      ring
  rw [hlo2, hup2, mul_add, hkill]
  ring

private theorem DFiniteExponent_succ (a : Nat) (j : Int) :
    DFiniteExponent a (j + 1) =
      DFiniteExponent a j + (5 * j + 3 - 2 * (a : Int)) := by
  unfold DFiniteExponent
  have hring :
      (j + 1) * (5 * (j + 1) + 1) =
        j * (5 * j + 1) + 2 * (5 * j + 3) := by
    ring
  have hdiv :
      ((j + 1) * (5 * (j + 1) + 1)) / 2 =
        j * (5 * j + 1) / 2 + (5 * j + 3) := by
    rw [hring]
    omega
  rw [hdiv]
  ring

private theorem DFiniteExponent_nonneg_of_le_one (a : Nat) (ha : a ≤ 1) (j : Int) :
    0 ≤ DFiniteExponent a j := by
  have ha_cases : a = 0 ∨ a = 1 := by omega
  rcases ha_cases with rfl | rfl
  · unfold DFiniteExponent
    have hprod : 0 ≤ j * (5 * j + 1) := by
      nlinarith [sq_nonneg j, sq_nonneg (j + 1)]
    omega
  · unfold DFiniteExponent
    norm_num
    have hrewrite :
        j * (5 * j + 1) / 2 - 2 * j =
          j * (5 * j - 3) / 2 := by
      have hring : j * (5 * j + 1) = j * (5 * j - 3) + 2 * (2 * j) := by
        ring
      omega
    have hprod : 0 ≤ j * (5 * j - 3) := by
      by_cases hj0 : j ≤ 0
      · exact mul_nonneg_of_nonpos_of_nonpos hj0 (by omega)
      · have hj1 : 1 ≤ j := by omega
        exact mul_nonneg (by omega) (by omega)
    omega

private theorem DFiniteExponent_nonneg_a2_of_ne_one (j : Int) (hj : j ≠ 1) :
    0 ≤ DFiniteExponent 2 j := by
  unfold DFiniteExponent
  norm_num
  have hcases : j ≤ 0 ∨ 2 ≤ j := by omega
  have hprod : 0 ≤ j * (5 * j - 7) := by
    rcases hcases with hj0 | hj2
    · exact mul_nonneg_of_nonpos_of_nonpos hj0 (by omega)
    · exact mul_nonneg (by omega) (by omega)
  have hrew : j * (5 * j + 1) / 2 = j * (5 * j - 7) / 2 + 4 * j := by
    have hring : j * (5 * j + 1) = j * (5 * j - 7) + 2 * (4 * j) := by
      ring
    omega
  rw [hrew]
  omega

private lemma zpow_eq_pow_toNat_of_nonneg (q : R) {e : Int} (he : 0 ≤ e) :
    q ^ e = q ^ e.toNat := by
  rw [← Int.toNat_of_nonneg he]
  exact zpow_natCast q e.toNat

private lemma DFiniteExponent_shift_pow_of_le_two (q : R) (a N : Nat) (ha : a ≤ 2)
    (j : Int)
    (hpar : ((N : Int) + 3 * (a : Int) - 5 * j) % 2 ≠ 0)
    (hb1 : 1 ≤ DFiniteLower a N j)
    (hb2 : DFiniteLower a N j ≤ (N + a : Int) + 1) :
    q ^ DFiniteExponent a (j + 1) * q ^ (DFiniteLower a N j - 1).toNat =
      q ^ DFiniteExponent a j *
        q ^ (((N + a : Nat) : Int) + 1 - DFiniteLower a N j).toNat := by
  by_cases ha1 : a ≤ 1
  · have hexp :
        (DFiniteExponent a j).toNat +
            (((N + a : Nat) : Int) + 1 - DFiniteLower a N j).toNat =
          (DFiniteExponent a (j + 1)).toNat + (DFiniteLower a N j - 1).toNat := by
      have hnonneg_j := DFiniteExponent_nonneg_of_le_one a ha1 j
      have hnonneg_next := DFiniteExponent_nonneg_of_le_one a ha1 (j + 1)
      have hsucc := DFiniteExponent_succ a j
      simp only [DFiniteExponent, DFiniteLower] at hnonneg_j hnonneg_next hsucc hpar hb1 hb2 ⊢
      omega
    rw [zpow_eq_pow_toNat_of_nonneg q (DFiniteExponent_nonneg_of_le_one a ha1 (j + 1)),
      zpow_eq_pow_toNat_of_nonneg q (DFiniteExponent_nonneg_of_le_one a ha1 j)]
    rw [← pow_add, ← pow_add]
    rw [← hexp]
  · have ha2 : a = 2 := by omega
    subst a
    by_cases hq : q = 0
    · subst q
      by_cases hj0 : j = 0
      · subst j
        have hcpos : 0 < (((N + 2 : Nat) : Int) + 1 - DFiniteLower 2 N 0).toNat := by
          unfold DFiniteLower
          omega
        have hcne : (((N + 2 : Nat) : Int) + 1 - DFiniteLower 2 N 0).toNat ≠ 0 := by
          omega
        simp [DFiniteExponent]
        exact (pow_eq_zero_iff'.mpr ⟨rfl, hcne⟩).symm
      · by_cases hj1 : j = 1
        · subst j
          rw [show DFiniteExponent 2 ((1 : Int) + 1) = 3 by rfl,
            show DFiniteExponent 2 (1 : Int) = -1 by rfl]
          rw [zero_zpow (3 : Int) (by norm_num),
            zero_zpow (-1 : Int) (by norm_num)]
          ring
        · have hjnext : j + 1 ≠ 1 := by omega
          have hnonneg_j := DFiniteExponent_nonneg_a2_of_ne_one j hj1
          have hnonneg_next := DFiniteExponent_nonneg_a2_of_ne_one (j + 1) hjnext
          have hexp :
              (DFiniteExponent 2 j).toNat +
                  (((N + 2 : Nat) : Int) + 1 - DFiniteLower 2 N j).toNat =
                (DFiniteExponent 2 (j + 1)).toNat + (DFiniteLower 2 N j - 1).toNat := by
            have hsucc := DFiniteExponent_succ 2 j
            simp only [DFiniteExponent, DFiniteLower] at hnonneg_j hnonneg_next hsucc hpar hb1 hb2 ⊢
            omega
          rw [zpow_eq_pow_toNat_of_nonneg (0 : R) hnonneg_next,
            zpow_eq_pow_toNat_of_nonneg (0 : R) hnonneg_j]
          rw [← pow_add, ← pow_add]
          rw [← hexp]
    · have hexp :
          DFiniteExponent 2 (j + 1) + ((DFiniteLower 2 N j - 1).toNat : Int) =
            DFiniteExponent 2 j +
              ((((N + 2 : Nat) : Int) + 1 - DFiniteLower 2 N j).toNat : Int) := by
        have hsucc := DFiniteExponent_succ 2 j
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ DFiniteLower 2 N j - 1),
          Int.toNat_of_nonneg
            (by omega : 0 ≤ ((N + 2 : Nat) : Int) + 1 - DFiniteLower 2 N j)]
        simp only [DFiniteExponent, DFiniteLower] at hsucc hpar hb1 hb2 ⊢
        omega
      rw [← zpow_natCast q (DFiniteLower 2 N j - 1).toNat,
        ← zpow_natCast q (((N + 2 : Nat) : Int) + 1 - DFiniteLower 2 N j).toNat]
      rw [← zpow_add₀ hq, ← zpow_add₀ hq, hexp]

private lemma DFiniteTerm_right_zero (q : R) (a n : Nat) (j : Int)
    (hj : (n : Int) + 3 * (a : Int) + 2 < j) :
    DFiniteTerm q a n j = 0 := by
  unfold DFiniteTerm
  rw [gaussianBinomIntLower_neg q (n + a) (DFiniteLower a n j)]
  · ring
  · unfold DFiniteLower
    omega

private lemma DFiniteTerm_left_zero (q : R) (a n : Nat) (j : Int)
    (hj : j < -((n : Int) + 3 * (a : Int) + 2)) :
    DFiniteTerm q a n j = 0 := by
  unfold DFiniteTerm
  rw [gaussianBinomIntLower_gt q (n + a) (DFiniteLower a n j)]
  · ring
  · unfold DFiniteLower
    omega

private lemma DFinite_common_bound (q : R) (a n B : Nat)
    (hB : DFiniteBound a n ≤ B) :
    DFinite q a n = bilateralSum (DFiniteTerm q a n) B := by
  unfold DFinite
  symm
  refine Nat.le_induction (by rfl) ?_ B hB
  intro k hk ih
  rw [bilateralSum_succ, ih]
  have hpos : DFiniteTerm q a n (k + 1 : Int) = 0 := by
    exact DFiniteTerm_right_zero q a n (k + 1 : Int) (by
      unfold DFiniteBound at hk
      omega)
  have hneg : DFiniteTerm q a n (-(k + 1 : Int)) = 0 := by
    exact DFiniteTerm_left_zero q a n (-(k + 1 : Int)) (by
      unfold DFiniteBound at hk
      omega)
  rw [hpos, hneg]
  ring

private lemma bilateralSum_sub (f g : Int → R) :
    ∀ n : Nat, bilateralSum (fun j => f j - g j) n = bilateralSum f n - bilateralSum g n
  | 0 => by simp
  | Nat.succ n => by
      rw [bilateralSum_succ, bilateralSum_succ, bilateralSum_succ, bilateralSum_sub f g n]
      ring

private lemma bilateralSum_mul_left (c : R) (f : Int → R) :
    ∀ n : Nat, bilateralSum (fun j => c * f j) n = c * bilateralSum f n
  | 0 => by simp
  | Nat.succ n => by
      rw [bilateralSum_succ, bilateralSum_succ, bilateralSum_mul_left c f n]
      ring

private lemma bilateralSum_sub_telescope (F : Int → R) :
    ∀ n : Nat, bilateralSum (fun j => F j - F (j + 1)) n =
      F (-(n : Int)) - F ((n : Int) + 1)
  | 0 => by simp
  | Nat.succ n => by
      rw [bilateralSum_succ, bilateralSum_sub_telescope F n]
      push_cast
      ring

private noncomputable def DFiniteResidual (q : R) (a N : Nat) (j : Int) : R :=
  DFiniteTerm q a (N + 2) j - DFiniteTerm q a (N + 1) j -
    q ^ (N + a + 1) * DFiniteTerm q a N j

private noncomputable def DFiniteCarry (q : R) (a N : Nat) (j : Int) : R :=
  if ((N : Int) + 3 * (a : Int) - 5 * j) % 2 = 0 then
    (-1 : R) ^ j * q ^ DFiniteExponent a j *
      q ^ (DFiniteLower a N j + 1).toNat *
      gaussianBinomIntLower q (N + a) (DFiniteLower a N j + 1)
  else 0

private lemma DFiniteResidual_eq_carry_sub (q : R) (a N : Nat) (ha : a ≤ 2) (j : Int) :
    DFiniteResidual q a N j = DFiniteCarry q a N j - DFiniteCarry q a N (j + 1) := by
  have hB2 : DFiniteLower a (N + 2) j = DFiniteLower a N j + 1 := by
    unfold DFiniteLower
    omega
  by_cases hpar : ((N : Int) + 3 * (a : Int) - 5 * j) % 2 = 0
  · have hB1 : DFiniteLower a (N + 1) j = DFiniteLower a N j := by
      unfold DFiniteLower
      omega
    have hpar_next : ((N : Int) + 3 * (a : Int) - 5 * (j + 1)) % 2 ≠ 0 := by
      omega
    unfold DFiniteResidual DFiniteTerm DFiniteCarry
    rw [hB2, hB1, if_pos hpar, if_neg hpar_next]
    have hres := gaussianBinomIntLower_even_residual q (N + a) (DFiniteLower a N j)
    simp only [show N + 2 + a = N + a + 2 by omega,
      show N + 1 + a = N + a + 1 by omega] at hres ⊢
    linear_combination ((-1 : R) ^ j * q ^ DFiniteExponent a j) * hres
  · have hB1 : DFiniteLower a (N + 1) j = DFiniteLower a N j + 1 := by
      unfold DFiniteLower
      omega
    have hpar_next : ((N : Int) + 3 * (a : Int) - 5 * (j + 1)) % 2 = 0 := by
      omega
    have hBnext : DFiniteLower a N (j + 1) + 1 = DFiniteLower a N j - 1 := by
      unfold DFiniteLower
      omega
    have hsign : (-1 : R) ^ (j + 1) = -((-1 : R) ^ j) := by
      rw [zpow_add₀ (by norm_num : (-1 : R) ≠ 0)]
      norm_num
    have hres := gaussianBinomIntLower_odd_residual q (N + a) (DFiniteLower a N j)
    by_cases hz : gaussianBinomIntLower q (N + a) (DFiniteLower a N j - 1) = 0
    · unfold DFiniteResidual DFiniteTerm DFiniteCarry
      rw [hB2, hB1, hBnext, if_neg hpar, if_pos hpar_next]
      simp only [show N + 2 + a = N + a + 2 by omega,
        show N + 1 + a = N + a + 1 by omega] at hres ⊢
      simp only [hz, mul_zero, sub_zero] at hres ⊢
      linear_combination ((-1 : R) ^ j * q ^ DFiniteExponent a j) * hres
    · have hb_range :
          1 ≤ DFiniteLower a N j ∧ DFiniteLower a N j ≤ (N + a : Int) + 1 := by
        by_contra hcon
        apply hz
        rcases not_and_or.mp hcon with h | h
        · exact gaussianBinomIntLower_neg q (N + a) _ (by unfold DFiniteLower at *; omega)
        · exact gaussianBinomIntLower_gt q (N + a) _ (by unfold DFiniteLower at *; omega)
      obtain ⟨hb1, hb2⟩ := hb_range
      have hpow :
          q ^ DFiniteExponent a (j + 1) * q ^ (DFiniteLower a N j - 1).toNat =
            q ^ DFiniteExponent a j *
              q ^ (((N + a : Nat) : Int) + 1 - DFiniteLower a N j).toNat := by
        exact DFiniteExponent_shift_pow_of_le_two q a N ha j hpar hb1 hb2
      have hcarrypow :
          -((-1 : R) ^ j) * q ^ DFiniteExponent a (j + 1) *
              q ^ (DFiniteLower a N j - 1).toNat *
              gaussianBinomIntLower q (N + a) (DFiniteLower a N j - 1) =
            -((-1 : R) ^ j) * q ^ DFiniteExponent a j *
              q ^ (((N + a : Nat) : Int) + 1 - DFiniteLower a N j).toNat *
              gaussianBinomIntLower q (N + a) (DFiniteLower a N j - 1) := by
        calc
          -((-1 : R) ^ j) * q ^ DFiniteExponent a (j + 1) *
              q ^ (DFiniteLower a N j - 1).toNat *
              gaussianBinomIntLower q (N + a) (DFiniteLower a N j - 1)
              = -((-1 : R) ^ j) *
                  (q ^ DFiniteExponent a (j + 1) *
                    q ^ (DFiniteLower a N j - 1).toNat) *
                  gaussianBinomIntLower q (N + a) (DFiniteLower a N j - 1) := by
                ring
          _ = -((-1 : R) ^ j) *
                  (q ^ DFiniteExponent a j *
                    q ^ (((N + a : Nat) : Int) + 1 - DFiniteLower a N j).toNat) *
                  gaussianBinomIntLower q (N + a) (DFiniteLower a N j - 1) := by
                rw [hpow]
          _ = -((-1 : R) ^ j) * q ^ DFiniteExponent a j *
              q ^ (((N + a : Nat) : Int) + 1 - DFiniteLower a N j).toNat *
              gaussianBinomIntLower q (N + a) (DFiniteLower a N j - 1) := by
                ring
      unfold DFiniteResidual DFiniteTerm DFiniteCarry
      rw [hB2, hB1, hBnext, if_neg hpar, if_pos hpar_next, hsign]
      simp only [show N + 2 + a = N + a + 2 by omega,
        show N + 1 + a = N + a + 1 by omega] at hres ⊢
      rw [hcarrypow]
      linear_combination ((-1 : R) ^ j * q ^ DFiniteExponent a j) * hres

private lemma DFiniteCarry_left_zero (q : R) (a N : Nat) :
    DFiniteCarry q a N (-(DFiniteBound a (N + 2) : Int)) = 0 := by
  unfold DFiniteCarry
  by_cases h :
      ((N : Int) + 3 * (a : Int) - 5 * (-(DFiniteBound a (N + 2) : Int))) % 2 = 0
  · rw [if_pos h]
    rw [gaussianBinomIntLower_gt q (N + a)]
    · ring
    · unfold DFiniteLower DFiniteBound
      omega
  · rw [if_neg h]

private lemma DFiniteCarry_right_zero (q : R) (a N : Nat) :
    DFiniteCarry q a N ((DFiniteBound a (N + 2) : Int) + 1) = 0 := by
  unfold DFiniteCarry
  by_cases h :
      ((N : Int) + 3 * (a : Int) - 5 * ((DFiniteBound a (N + 2) : Int) + 1)) % 2 = 0
  · rw [if_pos h]
    rw [gaussianBinomIntLower_neg q (N + a)]
    · ring
    · unfold DFiniteLower DFiniteBound
      omega
  · rw [if_neg h]

private lemma DFiniteResidual_sum_zero (q : R) (a N : Nat) (ha : a ≤ 2) :
    bilateralSum (DFiniteResidual q a N) (DFiniteBound a (N + 2)) = 0 := by
  have hcongr :
      bilateralSum (DFiniteResidual q a N) (DFiniteBound a (N + 2)) =
        bilateralSum (fun j => DFiniteCarry q a N j - DFiniteCarry q a N (j + 1))
          (DFiniteBound a (N + 2)) := by
    refine bilateralSum_congr (DFiniteBound a (N + 2)) ?_
    intro j hj
    exact DFiniteResidual_eq_carry_sub q a N ha j
  rw [hcongr, bilateralSum_sub_telescope, DFiniteCarry_left_zero,
    DFiniteCarry_right_zero]
  ring

theorem DFinite_recurrence_of_a_le_two (q : R) (a N : Nat) (ha : a ≤ 2) :
    DFinite q a (N + 2) =
      DFinite q a (N + 1) + q ^ (N + a + 1) * DFinite q a N := by
  let B := DFiniteBound a (N + 2)
  have h := DFiniteResidual_sum_zero q a N ha
  have hsum :
      bilateralSum (DFiniteResidual q a N) B =
        bilateralSum (DFiniteTerm q a (N + 2)) B -
          bilateralSum (DFiniteTerm q a (N + 1)) B -
          q ^ (N + a + 1) * bilateralSum (DFiniteTerm q a N) B := by
    unfold DFiniteResidual
    rw [bilateralSum_sub, bilateralSum_sub, bilateralSum_mul_left]
  change bilateralSum (DFiniteResidual q a N) B = 0 at h
  rw [hsum] at h
  have hD2 : DFinite q a (N + 2) = bilateralSum (DFiniteTerm q a (N + 2)) B := by
    exact DFinite_common_bound q a (N + 2) B (by simp [B])
  have hD1 : DFinite q a (N + 1) = bilateralSum (DFiniteTerm q a (N + 1)) B := by
    exact DFinite_common_bound q a (N + 1) B (by simp [B, DFiniteBound])
  have hD0 : DFinite q a N = bilateralSum (DFiniteTerm q a N) B := by
    exact DFinite_common_bound q a N B (by simp [B, DFiniteBound])
  rw [hD2, hD1, hD0]
  linear_combination h

theorem DFinite_recurrence_of_a_le_one (q : R) (a N : Nat) (ha : a ≤ 1) :
    DFinite q a (N + 2) =
      DFinite q a (N + 1) + q ^ (N + a + 1) * DFinite q a N := by
  exact DFinite_recurrence_of_a_le_two q a N (by omega)

theorem DFinite_a0_recurrence (q : R) (N : Nat) :
    DFinite q 0 (N + 2) = DFinite q 0 (N + 1) + q ^ (N + 1) * DFinite q 0 N := by
  simpa using DFinite_recurrence_of_a_le_one q 0 N (by omega)

theorem DFinite_a1_recurrence (q : R) (N : Nat) :
    DFinite q 1 (N + 2) = DFinite q 1 (N + 1) + q ^ (N + 2) * DFinite q 1 N := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    DFinite_recurrence_of_a_le_one q 1 N (by omega)

theorem DFinite_a2_recurrence (q : R) (N : Nat) :
    DFinite q 2 (N + 2) = DFinite q 2 (N + 1) + q ^ (N + 3) * DFinite q 2 N := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    DFinite_recurrence_of_a_le_two q 2 N (by omega)

/-! ### Recurrence uniqueness bridge -/

/-- Uniqueness for a second-order recurrence with arbitrary coefficient
sequence. -/
theorem second_order_recurrence_unique (F G c : Nat → R)
    (h0 : F 0 = G 0) (h1 : F 1 = G 1)
    (hF : ∀ N, F (N + 2) = F (N + 1) + c N * F N)
    (hG : ∀ N, G (N + 2) = G (N + 1) + c N * G N) :
    ∀ N, F N = G N := by
  intro N
  refine Nat.strong_induction_on N ?_
  intro n ih
  cases n with
  | zero =>
      exact h0
  | succ n =>
      cases n with
      | zero =>
          exact h1
      | succ n =>
          have hprev1 : F (n + 1) = G (n + 1) := ih (n + 1) (by omega)
          have hprev0 : F n = G n := ih n (by omega)
          calc
            F (n + 2) = F (n + 1) + c n * F n := hF n
            _ = G (n + 1) + c n * G n := by rw [hprev1, hprev0]
            _ = G (n + 2) := (hG n).symm

/-- Any sequence satisfying Chan's order-two recurrence and matching
`EFinite` at `0,1` agrees with `EFinite` everywhere. -/
theorem EFinite_eq_of_recurrence (q : R) (a : Nat) (G : Nat → R)
    (hG0 : G 0 = 1) (hG1 : G 1 = 1)
    (hGrec : ∀ N, G (N + 2) = G (N + 1) + q ^ (N + a + 1) * G N) :
    ∀ N, EFinite q a N = G N := by
  exact second_order_recurrence_unique (EFinite q a) G
    (fun N => q ^ (N + a + 1))
    (by rw [EFinite_zero q a, hG0])
    (by rw [EFinite_one q a, hG1])
    (EFinite_recurrence q a) hGrec

/-- Conditional finite Rogers-Ramanujan identity: once the alternating
Gaussian-polynomial side is shown to satisfy Chan's same recurrence and
base cases, Theorem 8.1 follows by recurrence uniqueness. -/
theorem EFinite_eq_DFinite_of_recurrence (q : R) (a : Nat)
    (hD0 : DFinite q a 0 = 1) (hD1 : DFinite q a 1 = 1)
    (hDrec : ∀ N,
      DFinite q a (N + 2) =
        DFinite q a (N + 1) + q ^ (N + a + 1) * DFinite q a N) :
    ∀ N, EFinite q a N = DFinite q a N := by
  exact EFinite_eq_of_recurrence q a (DFinite q a) hD0 hD1 hDrec

/-- Conditional `a = 0` instance of Chan Theorem 8.1 from the alternating-side
recurrence. -/
theorem EFinite_eq_DFinite_a0_of_recurrence (q : R)
    (hDrec : ∀ N,
      DFinite q 0 (N + 2) =
        DFinite q 0 (N + 1) + q ^ (N + 1) * DFinite q 0 N) :
    ∀ N, EFinite q 0 N = DFinite q 0 N := by
  refine EFinite_eq_DFinite_of_recurrence q 0 ?_ ?_ ?_
  · simp
  · simp
  · intro N
    simpa using hDrec N

/-- Conditional `a = 1` instance of Chan Theorem 8.1 from the alternating-side
recurrence. -/
theorem EFinite_eq_DFinite_a1_of_recurrence (q : R)
    (hDrec : ∀ N,
      DFinite q 1 (N + 2) =
        DFinite q 1 (N + 1) + q ^ (N + 2) * DFinite q 1 N) :
    ∀ N, EFinite q 1 N = DFinite q 1 N := by
  refine EFinite_eq_DFinite_of_recurrence q 1 ?_ ?_ ?_
  · simp
  · simp
  · intro N
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hDrec N

/-- Chan Theorem 8.1 for the first Rogers-Ramanujan case `a = 0`. -/
theorem EFinite_eq_DFinite_a0 (q : R) :
    ∀ N, EFinite q 0 N = DFinite q 0 N :=
  EFinite_eq_DFinite_a0_of_recurrence q (DFinite_a0_recurrence q)

/-- Chan Theorem 8.1 for the second Rogers-Ramanujan case `a = 1`. -/
theorem EFinite_eq_DFinite_a1 (q : R) :
    ∀ N, EFinite q 1 N = DFinite q 1 N :=
  EFinite_eq_DFinite_a1_of_recurrence q (DFinite_a1_recurrence q)

/-- The current alternating-side formula is not an all-`a` finite identity:
already at `a = 2`, `N = 0`, and `q = 1`, it disagrees with `EFinite`. -/
theorem EFinite_ne_DFinite_a2_zero_at_one :
    EFinite (1 : Rat) 2 0 ≠ DFinite (1 : Rat) 2 0 := by
  norm_num [EFinite, DFinite, DFiniteTerm, DFiniteBound, DFiniteExponent, DFiniteLower,
    gaussianBinomIntLower, bilateralSum, gaussianBinom]

/-- The carry recurrence cannot hold for arbitrary `Nat a` over all fields:
at `a = 3`, `q = 0`, and `N = 0`, the recurrence statement is false. -/
theorem DFinite_recurrence_fails_a3_at_zero :
    DFinite (0 : Rat) 3 2 ≠
      DFinite (0 : Rat) 3 1 + (0 : Rat) ^ (0 + 3 + 1) * DFinite (0 : Rat) 3 0 := by
  norm_num [DFinite, DFiniteTerm, DFiniteBound, DFiniteExponent, DFiniteLower,
    gaussianBinomIntLower, bilateralSum]
  rw [show (5 : Int).toNat = 5 by rfl, PartI.Ch03.gaussianBinom_self]
  norm_num

end Field

end Ch08
end PartII
end QseriesFormalization
