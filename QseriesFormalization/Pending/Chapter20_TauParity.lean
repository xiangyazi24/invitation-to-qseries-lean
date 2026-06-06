import QseriesFormalization.Chapter19
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal
import QseriesFormalization.Pending.RamanujanTau_via_B2

/-!
# Ramanujan τ parity: `τ(m)` is odd ⇔ `m` is an odd perfect square

A classical theorem (Ramanujan), derived here from the B2 cube identity plus the
characteristic-2 Frobenius on power series.

Over `ZMod 2`:
* B2 gives `(qPoch)^24 = (jacobiThetaPS)^8`, and `τ(n+1) = ((jacobiThetaPS)^8).coeff n`.
* Frobenius `g^2 = expand 2 g` (`PowerSeries.expand_eq_pow_zmod`) iterated three times
  gives `(jacobiThetaPS)^8 = expand 2 (expand 2 (expand 2 jacobiThetaPS))`, whose
  `n`-th coefficient is `jacobiTripleSign (n/8)` when `8 ∣ n`, else `0`.
* `jacobiTripleSign m = (-1)^k (2k+1)` at triangular `m = k(k+1)/2` (odd, ≡ 1 mod 2),
  and `0` otherwise.  So mod 2 it is the indicator of triangular numbers.

Hence `τ(m)` is odd ⇔ `m − 1 = 8·T_k = 4k(k+1)` for some `k` ⇔ `m = (2k+1)²`.
-/

namespace QseriesFormalization
namespace Pending
namespace TauParity

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartIV.Ch20 (ramanujanTau)

/-- Over `ZMod 2`, `(jacobiThetaPS)^8 = expand 2 (expand 2 (expand 2 jacobiThetaPS))`
by three applications of the char-2 Frobenius `g^2 = expand 2 g`. -/
theorem jacobiThetaPS_pow_eight_eq_expand :
    (jacobiThetaPS (ZMod 2))^8 =
      PowerSeries.expand 2 (by norm_num)
        (PowerSeries.expand 2 (by norm_num)
          (PowerSeries.expand 2 (by norm_num) (jacobiThetaPS (ZMod 2)))) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  set φ := jacobiThetaPS (ZMod 2)
  have e : ∀ g : (ZMod 2)⟦X⟧, g ^ 2 = PowerSeries.expand 2 (by norm_num) g :=
    fun g => (PowerSeries.expand_eq_pow_zmod 2 (by norm_num) g).symm
  calc φ ^ 8 = ((φ ^ 2) ^ 2) ^ 2 := by ring
    _ = ((expand 2 (by norm_num) φ) ^ 2) ^ 2 := by rw [e φ]
    _ = (expand 2 (by norm_num) (expand 2 (by norm_num) φ)) ^ 2 := by
          rw [e (expand 2 (by norm_num) φ)]
    _ = expand 2 (by norm_num)
          (expand 2 (by norm_num) (expand 2 (by norm_num) φ)) := by
          rw [e (expand 2 (by norm_num) (expand 2 (by norm_num) φ))]

/-- Coefficient of `(jacobiThetaPS)^8` over `ZMod 2`:
`jacobiTripleSign (n/8)` cast to `ZMod 2` when `8 ∣ n`, else `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2 (n : ℕ) :
    ((jacobiThetaPS (ZMod 2))^8).coeff n =
      if 8 ∣ n then ((jacobiTripleSign (n / 8) : ℤ) : ZMod 2) else 0 := by
  rw [jacobiThetaPS_pow_eight_eq_expand]
  rw [PowerSeries.coeff_expand 2 (by norm_num)]
  by_cases h2 : 2 ∣ n
  · rw [if_pos h2, PowerSeries.coeff_expand 2 (by norm_num)]
    by_cases h4 : 2 ∣ (n / 2)
    · rw [if_pos h4, PowerSeries.coeff_expand 2 (by norm_num)]
      by_cases h8 : 2 ∣ (n / 2 / 2)
      · rw [if_pos h8, coeff_jacobiThetaPS]
        have hdvd8 : 8 ∣ n := by omega
        rw [if_pos hdvd8]
        congr 2
        omega
      · rw [if_neg h8]
        have hndvd8 : ¬ 8 ∣ n := by omega
        rw [if_neg hndvd8]
    · rw [if_neg h4]
      have hndvd8 : ¬ 8 ∣ n := by omega
      rw [if_neg hndvd8]
  · rw [if_neg h2]
    have hndvd8 : ¬ 8 ∣ n := by omega
    rw [if_neg hndvd8]

/-- `jacobiTripleSign m` mod 2 is the indicator of triangular numbers:
`(jacobiTripleSign m : ZMod 2) = 1` iff `m = k(k+1)/2` for some `k ≤ m`, else `0`. -/
theorem jacobiTripleSign_mod2 (m : ℕ) :
    ((jacobiTripleSign m : ℤ) : ZMod 2) =
      if (∃ k ≤ m, m = k * (k + 1) / 2) then 1 else 0 := by
  by_cases h : ∃ k ≤ m, m = k * (k + 1) / 2
  · rw [if_pos h]
    obtain ⟨k, _hk, hm⟩ := h
    rw [hm, jacobiTripleSign_triangular]
    push_cast
    -- (-1)^k * (2k+1) mod 2 = 1
    have hneg : ((-1 : ZMod 2)) = 1 := by decide
    rw [hneg, one_pow, one_mul]
    -- (2k+1 : ZMod 2) = 1
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2]; ring
  · rw [if_neg h]
    push_neg at h
    rw [jacobiTripleSign_of_not_triangular m h]
    simp

/-- Coefficient-one form of the mod-2 triangular indicator for
`jacobiTripleSign`. -/
theorem jacobiTripleSign_mod2_eq_one_iff (m : ℕ) :
    ((jacobiTripleSign m : ℤ) : ZMod 2) = 1 ↔
      ∃ k ≤ m, m = k * (k + 1) / 2 := by
  rw [jacobiTripleSign_mod2]
  by_cases htri : ∃ k ≤ m, m = k * (k + 1) / 2 <;> simp [htri]

/-- Coefficient-zero form of the mod-2 triangular indicator for
`jacobiTripleSign`. -/
theorem jacobiTripleSign_mod2_eq_zero_iff_not_triangular (m : ℕ) :
    ((jacobiTripleSign m : ℤ) : ZMod 2) = 0 ↔
      ¬ ∃ k ≤ m, m = k * (k + 1) / 2 := by
  rw [jacobiTripleSign_mod2]
  by_cases htri : ∃ k ≤ m, m = k * (k + 1) / 2 <;> simp [htri]

/-- Nonzero form of the mod-2 triangular indicator for `jacobiTripleSign`. -/
theorem jacobiTripleSign_mod2_ne_zero_iff (m : ℕ) :
    ((jacobiTripleSign m : ℤ) : ZMod 2) ≠ 0 ↔
      ∃ k ≤ m, m = k * (k + 1) / 2 := by
  rw [jacobiTripleSign_mod2]
  by_cases htri : ∃ k ≤ m, m = k * (k + 1) / 2 <;> simp [htri]

/-- Triangular arguments give value `1` modulo `2`. -/
theorem jacobiTripleSign_mod2_eq_one_of_triangular (k : ℕ) :
    ((jacobiTripleSign (k * (k + 1) / 2) : ℤ) : ZMod 2) = 1 :=
  (jacobiTripleSign_mod2_eq_one_iff (k * (k + 1) / 2)).mpr
    ⟨k, QseriesFormalization.PartIV.Ch19.k_le_triangular k, rfl⟩

/-- Non-triangular arguments give value `0` modulo `2`. -/
theorem jacobiTripleSign_mod2_eq_zero_of_not_triangular
    {m : ℕ} (hm : ¬ ∃ k ≤ m, m = k * (k + 1) / 2) :
    ((jacobiTripleSign m : ℤ) : ZMod 2) = 0 :=
  (jacobiTripleSign_mod2_eq_zero_iff_not_triangular m).mpr hm

/-- Concrete checkpoint: `jacobiTripleSign 0 = 1` modulo `2`. -/
theorem jacobiTripleSign_mod2_eq_one_at_zero :
    ((jacobiTripleSign 0 : ℤ) : ZMod 2) = 1 := by
  simpa using jacobiTripleSign_mod2_eq_one_of_triangular 0

/-- Concrete checkpoint: `jacobiTripleSign 1 = 1` modulo `2`. -/
theorem jacobiTripleSign_mod2_eq_one_at_one :
    ((jacobiTripleSign 1 : ℤ) : ZMod 2) = 1 := by
  simpa using jacobiTripleSign_mod2_eq_one_of_triangular 1

/-- Concrete checkpoint: `jacobiTripleSign 3 = 1` modulo `2`. -/
theorem jacobiTripleSign_mod2_eq_one_at_three :
    ((jacobiTripleSign 3 : ℤ) : ZMod 2) = 1 := by
  simpa using jacobiTripleSign_mod2_eq_one_of_triangular 2

/-- Concrete checkpoint: `jacobiTripleSign 6 = 1` modulo `2`. -/
theorem jacobiTripleSign_mod2_eq_one_at_six :
    ((jacobiTripleSign 6 : ℤ) : ZMod 2) = 1 := by
  simpa using jacobiTripleSign_mod2_eq_one_of_triangular 3

/-- Concrete checkpoint: `jacobiTripleSign 10 = 1` modulo `2`. -/
theorem jacobiTripleSign_mod2_eq_one_at_ten :
    ((jacobiTripleSign 10 : ℤ) : ZMod 2) = 1 := by
  simpa using jacobiTripleSign_mod2_eq_one_of_triangular 4

/-- Concrete checkpoint: `jacobiTripleSign 2 = 0` modulo `2`. -/
theorem jacobiTripleSign_mod2_eq_zero_at_two :
    ((jacobiTripleSign 2 : ℤ) : ZMod 2) = 0 :=
  jacobiTripleSign_mod2_eq_zero_of_not_triangular (by
    rintro ⟨k, hk, hEq⟩
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `jacobiTripleSign 4 = 0` modulo `2`. -/
theorem jacobiTripleSign_mod2_eq_zero_at_four :
    ((jacobiTripleSign 4 : ℤ) : ZMod 2) = 0 :=
  jacobiTripleSign_mod2_eq_zero_of_not_triangular (by
    rintro ⟨k, hk, hEq⟩
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `jacobiTripleSign 5 = 0` modulo `2`. -/
theorem jacobiTripleSign_mod2_eq_zero_at_five :
    ((jacobiTripleSign 5 : ℤ) : ZMod 2) = 0 :=
  jacobiTripleSign_mod2_eq_zero_of_not_triangular (by
    rintro ⟨k, hk, hEq⟩
    interval_cases k <;> norm_num at hEq)

/-- **τ mod 2, structural form**: `τ(n+1)` is odd (`= 1` in `ZMod 2`) iff
`n = 4k(k+1)` for some `k` (i.e. `n = 8·T_k`). -/
theorem ramanujanTau_mod2_eq_one_iff (n : ℕ) :
    ramanujanTau (ZMod 2) (n + 1) = 1 ↔ ∃ k, n = 4 * k * (k + 1) := by
  rw [QseriesFormalization.Pending.RTau.ramanujanTau_succ_eq_jacobiThetaPS_pow_eight_coeff,
    coeff_jacobiThetaPS_pow_eight_mod2]
  -- helper: n = 4·k·(k+1)  ⟺  8 ∣ n ∧ n/8 = k(k+1)/2  (linear once Q,t introduced)
  have hQ : ∀ k : ℕ, 4 * k * (k + 1) = 4 * (k * (k + 1)) := fun k => by ring
  by_cases h8 : 8 ∣ n
  · rw [if_pos h8, jacobiTripleSign_mod2]
    by_cases ht : ∃ j ≤ n / 8, n / 8 = j * (j + 1) / 2
    · rw [if_pos ht]
      constructor
      · intro _
        obtain ⟨j, _, hj⟩ := ht
        refine ⟨j, ?_⟩
        have h2t : 2 * (j * (j + 1) / 2) = j * (j + 1) :=
          QseriesFormalization.PartIV.Ch19.two_mul_triangular j
        have hn8 : n = 8 * (n / 8) := by omega
        rw [hQ j]; omega
      · intro _; rfl
    · rw [if_neg ht]
      constructor
      · intro hcontra; exact absurd hcontra (by decide)
      · rintro ⟨k, hk⟩
        exfalso; apply ht
        have h2t : 2 * (k * (k + 1) / 2) = k * (k + 1) :=
          QseriesFormalization.PartIV.Ch19.two_mul_triangular k
        rw [hQ k] at hk
        have hn8 : n / 8 = k * (k + 1) / 2 := by omega
        exact ⟨k, by rw [hn8]; exact QseriesFormalization.PartIV.Ch19.k_le_triangular k, hn8⟩
  · rw [if_neg h8]
    constructor
    · intro hcontra; exact absurd hcontra (by decide)
    · rintro ⟨k, hk⟩
      exfalso; apply h8
      have h2t : 2 * (k * (k + 1) / 2) = k * (k + 1) :=
        QseriesFormalization.PartIV.Ch19.two_mul_triangular k
      rw [hQ k] at hk
      omega

/-- **Ramanujan's τ parity theorem**: for `m ≥ 1`, `τ(m)` is odd iff `m` is an
odd perfect square. -/
theorem ramanujanTau_odd_iff_odd_square (m : ℕ) (hm : 1 ≤ m) :
    ramanujanTau (ZMod 2) m = 1 ↔ ∃ k, m = (2 * k + 1) ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [ramanujanTau_mod2_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by nlinarith [hk]⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by nlinarith [hk]⟩

/-- **`(q;q)_∞³` mod 2 is the triangular-number indicator series.**
Over `ZMod 2`, `((qPoch)^3).coeff n = 1` iff `n` is a triangular number, else `0`.
(Immediate from B2 `(qPoch)^3 = jacobiThetaPS` and `jacobiTripleSign_mod2`.) -/
theorem coeff_qPochInfPS_pow_three_mod2 (n : ℕ) :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff n =
      if (∃ k ≤ n, n = k * (k + 1) / 2) then 1 else 0 := by
  rw [QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS,
    coeff_jacobiThetaPS, jacobiTripleSign_mod2]

/-- In `ZMod 2`, every element different from `1` is `0`. -/
theorem zmod2_eq_zero_of_ne_one {x : ZMod 2} (hx : x ≠ 1) : x = 0 := by
  fin_cases x <;> simp_all

/-- In `ZMod 2`, being equal to `1` is the same as being nonzero. -/
theorem zmod2_eq_one_iff_ne_zero {x : ZMod 2} : x = 1 ↔ x ≠ 0 := by
  fin_cases x <;> simp

/-- Symmetric form: a nonzero `ZMod 2` element is exactly `1`. -/
theorem zmod2_ne_zero_iff_eq_one {x : ZMod 2} : x ≠ 0 ↔ x = 1 :=
  zmod2_eq_one_iff_ne_zero.symm

/-- Coefficient-one form of the mod-2 triangular indicator for `(q;q)_∞^3`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_one_iff (n : ℕ) :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff n = 1 ↔
      ∃ k ≤ n, n = k * (k + 1) / 2 := by
  rw [coeff_qPochInfPS_pow_three_mod2]
  by_cases htri : ∃ k ≤ n, n = k * (k + 1) / 2
  · simp [htri]
  · simp [htri]

/-- Coefficient-zero form of the mod-2 triangular indicator for `(q;q)_∞^3`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_zero_iff (n : ℕ) :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff n = 0 ↔
      ¬ ∃ k ≤ n, n = k * (k + 1) / 2 := by
  rw [coeff_qPochInfPS_pow_three_mod2]
  by_cases htri : ∃ k ≤ n, n = k * (k + 1) / 2
  · simp [htri]
  · simp [htri]

/-- Nonzero form of the mod-2 triangular indicator for `(q;q)_∞^3`. -/
theorem coeff_qPochInfPS_pow_three_mod2_ne_zero_iff (n : ℕ) :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff n ≠ 0 ↔
      ∃ k ≤ n, n = k * (k + 1) / 2 := by
  exact zmod2_ne_zero_iff_eq_one.trans
    (coeff_qPochInfPS_pow_three_mod2_eq_one_iff n)

/-- Every triangular exponent has coefficient `1` in `(q;q)_∞^3` over
`ZMod 2`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_one_of_triangular (k : ℕ) :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff (k * (k + 1) / 2) = 1 := by
  exact (coeff_qPochInfPS_pow_three_mod2_eq_one_iff
    (k * (k + 1) / 2)).mpr
      ⟨k, QseriesFormalization.PartIV.Ch19.k_le_triangular k, rfl⟩

/-- Non-triangular exponents have coefficient `0` in `(q;q)_∞^3` over
`ZMod 2`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_zero_of_not_triangular
    {n : ℕ} (hn : ¬ ∃ k ≤ n, n = k * (k + 1) / 2) :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff n = 0 :=
  (coeff_qPochInfPS_pow_three_mod2_eq_zero_iff n).mpr hn

/-- Concrete checkpoint: coefficient at triangular exponent `0` is `1`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_one_at_zero :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff 0 = 1 := by
  simpa using coeff_qPochInfPS_pow_three_mod2_eq_one_of_triangular 0

/-- Concrete checkpoint: coefficient at triangular exponent `1` is `1`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_one_at_one :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff 1 = 1 := by
  simpa using coeff_qPochInfPS_pow_three_mod2_eq_one_of_triangular 1

/-- Concrete checkpoint: coefficient at triangular exponent `3` is `1`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_one_at_three :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff 3 = 1 := by
  simpa using coeff_qPochInfPS_pow_three_mod2_eq_one_of_triangular 2

/-- Concrete checkpoint: coefficient at triangular exponent `6` is `1`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_one_at_six :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff 6 = 1 := by
  simpa using coeff_qPochInfPS_pow_three_mod2_eq_one_of_triangular 3

/-- Concrete checkpoint: coefficient at triangular exponent `10` is `1`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_one_at_ten :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff 10 = 1 := by
  simpa using coeff_qPochInfPS_pow_three_mod2_eq_one_of_triangular 4

/-- Concrete checkpoint: coefficient at triangular exponent `15` is `1`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_one_at_fifteen :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff 15 = 1 := by
  simpa using coeff_qPochInfPS_pow_three_mod2_eq_one_of_triangular 5

/-- Concrete checkpoint: coefficient at triangular exponent `21` is `1`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_one_at_twenty_one :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff 21 = 1 := by
  simpa using coeff_qPochInfPS_pow_three_mod2_eq_one_of_triangular 6

/-- Concrete checkpoint: coefficient at triangular exponent `28` is `1`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_one_at_twenty_eight :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff 28 = 1 := by
  simpa using coeff_qPochInfPS_pow_three_mod2_eq_one_of_triangular 7

/-- Concrete checkpoint: coefficient at non-triangular exponent `2` is `0`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_zero_at_two :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff 2 = 0 :=
  coeff_qPochInfPS_pow_three_mod2_eq_zero_of_not_triangular (by
    rintro ⟨k, hk, hEq⟩
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: coefficient at non-triangular exponent `4` is `0`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_zero_at_four :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff 4 = 0 :=
  coeff_qPochInfPS_pow_three_mod2_eq_zero_of_not_triangular (by
    rintro ⟨k, hk, hEq⟩
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: coefficient at non-triangular exponent `5` is `0`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_zero_at_five :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff 5 = 0 :=
  coeff_qPochInfPS_pow_three_mod2_eq_zero_of_not_triangular (by
    rintro ⟨k, hk, hEq⟩
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: coefficient at non-triangular exponent `7` is `0`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_zero_at_seven :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff 7 = 0 :=
  coeff_qPochInfPS_pow_three_mod2_eq_zero_of_not_triangular (by
    rintro ⟨k, hk, hEq⟩
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: coefficient at non-triangular exponent `11` is `0`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_zero_at_eleven :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff 11 = 0 :=
  coeff_qPochInfPS_pow_three_mod2_eq_zero_of_not_triangular (by
    rintro ⟨k, hk, hEq⟩
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: coefficient at non-triangular exponent `13` is `0`. -/
theorem coeff_qPochInfPS_pow_three_mod2_eq_zero_at_thirteen :
    ((qPochInfPS (ZMod 2)) ^ 3).coeff 13 = 0 :=
  coeff_qPochInfPS_pow_three_mod2_eq_zero_of_not_triangular (by
    rintro ⟨k, hk, hEq⟩
    interval_cases k <;> norm_num at hEq)

/-- Structural positive direction for the shifted tau parity theorem. -/
theorem ramanujanTau_succ_mod2_eq_one_of_four_mul (k : ℕ) :
    ramanujanTau (ZMod 2) (4 * k * (k + 1) + 1) = 1 := by
  exact (ramanujanTau_mod2_eq_one_iff (4 * k * (k + 1))).mpr ⟨k, rfl⟩

/-- Structural negative direction for the shifted tau parity theorem. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_not_four_mul
    {n : ℕ} (hn : ¬ ∃ k, n = 4 * k * (k + 1)) :
    ramanujanTau (ZMod 2) (n + 1) = 0 := by
  apply zmod2_eq_zero_of_ne_one
  intro h
  exact hn ((ramanujanTau_mod2_eq_one_iff n).mp h)

/-- Tau is odd at every odd square. -/
theorem ramanujanTau_mod2_eq_one_of_odd_square (k : ℕ) :
    ramanujanTau (ZMod 2) ((2 * k + 1) ^ 2) = 1 := by
  have hm : 1 ≤ (2 * k + 1) ^ 2 := by nlinarith [Nat.zero_le k]
  exact (ramanujanTau_odd_iff_odd_square ((2 * k + 1) ^ 2) hm).mpr ⟨k, rfl⟩

/-- Tau is even at positive indices that are not odd squares. -/
theorem ramanujanTau_mod2_eq_zero_of_not_odd_square
    {m : ℕ} (hm : 1 ≤ m) (hnsq : ¬ ∃ k, m = (2 * k + 1) ^ 2) :
    ramanujanTau (ZMod 2) m = 0 := by
  apply zmod2_eq_zero_of_ne_one
  intro h
  exact hnsq ((ramanujanTau_odd_iff_odd_square m hm).mp h)

/-- An odd square is `1 mod 2`. -/
theorem odd_square_mod_two (k : ℕ) :
    ((2 * k + 1) ^ 2) % 2 = 1 := by
  have hodd : (2 * k + 1) % 2 = 1 := by omega
  rw [pow_two, Nat.mul_mod, hodd]

/-- An even number cannot be an odd square. -/
theorem not_odd_square_of_mod_two_eq_zero {m : ℕ} (hm : m % 2 = 0) :
    ¬ ∃ k, m = (2 * k + 1) ^ 2 := by
  rintro ⟨k, hk⟩
  have hsq := odd_square_mod_two k
  rw [← hk, hm] at hsq
  norm_num at hsq

/-- Tau is even at every positive even index. -/
theorem ramanujanTau_mod2_eq_zero_of_even
    {m : ℕ} (hm : 1 ≤ m) (hEven : m % 2 = 0) :
    ramanujanTau (ZMod 2) m = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square hm
    (not_odd_square_of_mod_two_eq_zero hEven)

/-- Zero form of Ramanujan's tau parity theorem. -/
theorem ramanujanTau_mod2_eq_zero_iff_not_odd_square
    (m : ℕ) (hm : 1 ≤ m) :
    ramanujanTau (ZMod 2) m = 0 ↔ ¬ ∃ k, m = (2 * k + 1) ^ 2 := by
  constructor
  · intro hzero hsquare
    have hone := (ramanujanTau_odd_iff_odd_square m hm).mpr hsquare
    rw [hzero] at hone
    exact zero_ne_one hone
  · exact ramanujanTau_mod2_eq_zero_of_not_odd_square hm

/-- Nonzero form of Ramanujan's tau parity theorem. -/
theorem ramanujanTau_mod2_ne_zero_iff_odd_square
    (m : ℕ) (hm : 1 ≤ m) :
    ramanujanTau (ZMod 2) m ≠ 0 ↔ ∃ k, m = (2 * k + 1) ^ 2 := by
  constructor
  · intro hne
    have hone : ramanujanTau (ZMod 2) m = 1 := by
      by_contra hnot
      exact hne (zmod2_eq_zero_of_ne_one hnot)
    exact (ramanujanTau_odd_iff_odd_square m hm).mp hone
  · intro hsquare hzero
    have hone := (ramanujanTau_odd_iff_odd_square m hm).mpr hsquare
    rw [hzero] at hone
    exact zero_ne_one hone

/-- Zero form of the shifted structural tau parity theorem. -/
theorem ramanujanTau_succ_mod2_eq_zero_iff_not_four_mul (n : ℕ) :
    ramanujanTau (ZMod 2) (n + 1) = 0 ↔ ¬ ∃ k, n = 4 * k * (k + 1) := by
  constructor
  · intro hzero hfour
    have hone := (ramanujanTau_mod2_eq_one_iff n).mpr hfour
    rw [hzero] at hone
    exact zero_ne_one hone
  · exact ramanujanTau_succ_mod2_eq_zero_of_not_four_mul

/-- Nonzero form of the shifted structural tau parity theorem. -/
theorem ramanujanTau_succ_mod2_ne_zero_iff_four_mul (n : ℕ) :
    ramanujanTau (ZMod 2) (n + 1) ≠ 0 ↔ ∃ k, n = 4 * k * (k + 1) := by
  constructor
  · intro hne
    have hone : ramanujanTau (ZMod 2) (n + 1) = 1 := by
      by_contra hnot
      exact hne (zmod2_eq_zero_of_ne_one hnot)
    exact (ramanujanTau_mod2_eq_one_iff n).mp hone
  · intro hfour hzero
    have hone := (ramanujanTau_mod2_eq_one_iff n).mpr hfour
    rw [hzero] at hone
    exact zero_ne_one hone

/-- For any index, `τ(m) = 1` over `ZMod 2` iff it is nonzero. -/
theorem ramanujanTau_mod2_eq_one_iff_ne_zero (m : ℕ) :
    ramanujanTau (ZMod 2) m = 1 ↔ ramanujanTau (ZMod 2) m ≠ 0 :=
  zmod2_eq_one_iff_ne_zero

/-- Tau is nonzero modulo `2` at every odd square. -/
theorem ramanujanTau_mod2_ne_zero_of_odd_square (k : ℕ) :
    ramanujanTau (ZMod 2) ((2 * k + 1) ^ 2) ≠ 0 :=
  zmod2_eq_one_iff_ne_zero.1 (ramanujanTau_mod2_eq_one_of_odd_square k)

/-- Nonzero tau modulo `2` at a positive index forces that index to be an odd
square. -/
theorem odd_square_of_ramanujanTau_mod2_ne_zero
    {m : ℕ} (hm : 1 ≤ m) (hne : ramanujanTau (ZMod 2) m ≠ 0) :
    ∃ k, m = (2 * k + 1) ^ 2 :=
  (ramanujanTau_mod2_ne_zero_iff_odd_square m hm).mp hne

/-- Nonzero tau modulo `2` at a positive index forces the index to be odd. -/
theorem mod_two_eq_one_of_ramanujanTau_mod2_ne_zero
    {m : ℕ} (hm : 1 ≤ m) (hne : ramanujanTau (ZMod 2) m ≠ 0) :
    m % 2 = 1 := by
  obtain ⟨k, hk⟩ := odd_square_of_ramanujanTau_mod2_ne_zero hm hne
  rw [hk]
  exact odd_square_mod_two k

/-- Tau equal to `1` modulo `2` at a positive index forces the index to be
odd. -/
theorem mod_two_eq_one_of_ramanujanTau_mod2_eq_one
    {m : ℕ} (hm : 1 ≤ m) (hone : ramanujanTau (ZMod 2) m = 1) :
    m % 2 = 1 :=
  mod_two_eq_one_of_ramanujanTau_mod2_ne_zero hm
    ((ramanujanTau_mod2_eq_one_iff_ne_zero m).mp hone)

/-- Zero tau modulo `2` at a positive index rules out odd-square indices. -/
theorem not_odd_square_of_ramanujanTau_mod2_eq_zero
    {m : ℕ} (hm : 1 ≤ m) (hzero : ramanujanTau (ZMod 2) m = 0) :
    ¬ ∃ k, m = (2 * k + 1) ^ 2 :=
  (ramanujanTau_mod2_eq_zero_iff_not_odd_square m hm).mp hzero

/-- The shifted tau value is nonzero modulo `2` at every structural index
`4k(k+1)+1`. -/
theorem ramanujanTau_succ_mod2_ne_zero_of_four_mul (k : ℕ) :
    ramanujanTau (ZMod 2) (4 * k * (k + 1) + 1) ≠ 0 :=
  zmod2_eq_one_iff_ne_zero.1 (ramanujanTau_succ_mod2_eq_one_of_four_mul k)

/-- A nonzero shifted tau value modulo `2` forces the structural form
`n = 4k(k+1)`. -/
theorem four_mul_of_ramanujanTau_succ_mod2_ne_zero
    {n : ℕ} (hne : ramanujanTau (ZMod 2) (n + 1) ≠ 0) :
    ∃ k, n = 4 * k * (k + 1) :=
  (ramanujanTau_succ_mod2_ne_zero_iff_four_mul n).mp hne

/-- A zero shifted tau value modulo `2` rules out the structural form
`n = 4k(k+1)`. -/
theorem not_four_mul_of_ramanujanTau_succ_mod2_eq_zero
    {n : ℕ} (hzero : ramanujanTau (ZMod 2) (n + 1) = 0) :
    ¬ ∃ k, n = 4 * k * (k + 1) :=
  (ramanujanTau_succ_mod2_eq_zero_iff_not_four_mul n).mp hzero

/-- Concrete checkpoint: `τ(1)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_one :
    ramanujanTau (ZMod 2) 1 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 0

/-- Concrete checkpoint: `τ(9)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_nine :
    ramanujanTau (ZMod 2) 9 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 1

/-- Concrete checkpoint: `τ(25)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_twenty_five :
    ramanujanTau (ZMod 2) 25 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 2

/-- Concrete checkpoint: `τ(49)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_forty_nine :
    ramanujanTau (ZMod 2) 49 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 3

/-- Concrete checkpoint: `τ(81)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_eighty_one :
    ramanujanTau (ZMod 2) 81 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 4

/-- Concrete checkpoint: `τ(121)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_one_hundred_twenty_one :
    ramanujanTau (ZMod 2) 121 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 5

/-- Concrete checkpoint: `τ(169)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_one_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 169 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 6

/-- Concrete checkpoint: `τ(225)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_two_hundred_twenty_five :
    ramanujanTau (ZMod 2) 225 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 7

/-- Concrete checkpoint: `τ(289)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_two_hundred_eighty_nine :
    ramanujanTau (ZMod 2) 289 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 8

/-- Concrete checkpoint: `τ(361)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_three_hundred_sixty_one :
    ramanujanTau (ZMod 2) 361 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 9

/-- Concrete checkpoint: `τ(441)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_four_hundred_forty_one :
    ramanujanTau (ZMod 2) 441 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 10

/-- Concrete checkpoint: `τ(529)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_five_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 529 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 11

/-- Concrete checkpoint: `τ(625)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_six_hundred_twenty_five :
    ramanujanTau (ZMod 2) 625 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 12

/-- Concrete checkpoint: `τ(729)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_seven_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 729 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 13

/-- Concrete checkpoint: `τ(841)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_eight_hundred_forty_one :
    ramanujanTau (ZMod 2) 841 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 14

/-- Concrete checkpoint: `τ(961)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_nine_hundred_sixty_one :
    ramanujanTau (ZMod 2) 961 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 15

/-- Concrete checkpoint: `τ(1089)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_one_thousand_eighty_nine :
    ramanujanTau (ZMod 2) 1089 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 16

/-- Concrete checkpoint: `τ(1225)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_one_thousand_two_hundred_twenty_five :
    ramanujanTau (ZMod 2) 1225 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 17

/-- Concrete checkpoint: `τ(1369)` is odd. -/
theorem ramanujanTau_mod2_eq_one_at_one_thousand_three_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 1369 = 1 := by
  simpa using ramanujanTau_mod2_eq_one_of_odd_square 18

/-- Concrete checkpoint: `τ(2)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two :
    ramanujanTau (ZMod 2) 2 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(4)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_four :
    ramanujanTau (ZMod 2) 4 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(6)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_six :
    ramanujanTau (ZMod 2) 6 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(8)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eight :
    ramanujanTau (ZMod 2) 8 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(10)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_ten :
    ramanujanTau (ZMod 2) 10 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(12)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_twelve :
    ramanujanTau (ZMod 2) 12 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(14)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_fourteen :
    ramanujanTau (ZMod 2) 14 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(16)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_sixteen :
    ramanujanTau (ZMod 2) 16 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(18)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eighteen :
    ramanujanTau (ZMod 2) 18 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(20)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_twenty :
    ramanujanTau (ZMod 2) 20 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(22)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_twenty_two :
    ramanujanTau (ZMod 2) 22 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(24)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_twenty_four :
    ramanujanTau (ZMod 2) 24 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(26)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_twenty_six :
    ramanujanTau (ZMod 2) 26 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(28)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_twenty_eight :
    ramanujanTau (ZMod 2) 28 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(30)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_thirty :
    ramanujanTau (ZMod 2) 30 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(32)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_thirty_two :
    ramanujanTau (ZMod 2) 32 = 0 :=
  ramanujanTau_mod2_eq_zero_of_even (by norm_num) (by norm_num)

/-- Coefficient-one form for `(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_iff (n : ℕ) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n = 1 ↔
      ∃ k, n = 4 * k * (k + 1) := by
  rw [← QseriesFormalization.Pending.RTau.ramanujanTau_succ_eq_jacobiThetaPS_pow_eight_coeff]
  exact ramanujanTau_mod2_eq_one_iff n

/-- Coefficient-zero form for `(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_iff_not_four_mul (n : ℕ) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n = 0 ↔
      ¬ ∃ k, n = 4 * k * (k + 1) := by
  constructor
  · intro hzero hfour
    have hone := (coeff_jacobiThetaPS_pow_eight_mod2_eq_one_iff n).mpr hfour
    rw [hzero] at hone
    exact zero_ne_one hone
  · intro hnot
    apply zmod2_eq_zero_of_ne_one
    intro hone
    exact hnot ((coeff_jacobiThetaPS_pow_eight_mod2_eq_one_iff n).mp hone)

/-- Nonzero form for `(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_ne_zero_iff_four_mul (n : ℕ) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n ≠ 0 ↔
      ∃ k, n = 4 * k * (k + 1) := by
  exact zmod2_ne_zero_iff_eq_one.trans
    (coeff_jacobiThetaPS_pow_eight_mod2_eq_one_iff n)

/-- Structural positive direction for `(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul (k : ℕ) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff (4 * k * (k + 1)) = 1 :=
  (coeff_jacobiThetaPS_pow_eight_mod2_eq_one_iff (4 * k * (k + 1))).mpr ⟨k, rfl⟩

/-- Structural zero direction for `(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_not_four_mul
    {n : ℕ} (hn : ¬ ∃ k, n = 4 * k * (k + 1)) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n = 0 :=
  (coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_iff_not_four_mul n).mpr hn

/-- Concrete checkpoint: coefficient at exponent `0` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_zero :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 0 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 0

/-- Concrete checkpoint: coefficient at exponent `8` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_eight :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 8 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 1

/-- Concrete checkpoint: coefficient at exponent `24` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_twenty_four :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 24 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 2

/-- Concrete checkpoint: coefficient at exponent `48` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_forty_eight :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 48 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 3

/-- Concrete checkpoint: coefficient at exponent `80` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_eighty :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 80 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 4

/-- Concrete checkpoint: coefficient at exponent `120` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_one_hundred_twenty :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 120 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 5

/-- Concrete checkpoint: coefficient at exponent `168` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_one_hundred_sixty_eight :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 168 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 6

/-- Concrete checkpoint: coefficient at exponent `224` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_two_hundred_twenty_four :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 224 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 7

/-- Concrete checkpoint: coefficient at exponent `288` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_two_hundred_eighty_eight :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 288 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 8

/-- Concrete checkpoint: coefficient at exponent `360` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_three_hundred_sixty :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 360 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 9

/-- Concrete checkpoint: coefficient at exponent `440` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_four_hundred_forty :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 440 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 10

/-- Concrete checkpoint: coefficient at exponent `528` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_five_hundred_twenty_eight :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 528 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 11

/-- Concrete checkpoint: coefficient at exponent `624` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_six_hundred_twenty_four :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 624 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 12

/-- Concrete checkpoint: coefficient at exponent `728` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_seven_hundred_twenty_eight :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 728 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 13

/-- Concrete checkpoint: coefficient at exponent `840` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_eight_hundred_forty :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 840 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 14

/-- Concrete checkpoint: coefficient at exponent `960` is `1`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_at_nine_hundred_sixty :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 960 = 1 := by
  simpa using coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul 15

/-- Concrete checkpoint: coefficient at exponent `1` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_one :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 1 = 0 := by
  rw [← QseriesFormalization.Pending.RTau.ramanujanTau_succ_eq_jacobiThetaPS_pow_eight_coeff]
  exact ramanujanTau_mod2_eq_zero_at_two

/-- Concrete checkpoint: coefficient at exponent `3` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_three :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 3 = 0 := by
  rw [← QseriesFormalization.Pending.RTau.ramanujanTau_succ_eq_jacobiThetaPS_pow_eight_coeff]
  exact ramanujanTau_mod2_eq_zero_at_four

/-- Concrete checkpoint: coefficient at exponent `5` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_five :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 5 = 0 := by
  rw [← QseriesFormalization.Pending.RTau.ramanujanTau_succ_eq_jacobiThetaPS_pow_eight_coeff]
  exact ramanujanTau_mod2_eq_zero_at_six

/-- Concrete checkpoint: coefficient at exponent `7` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_seven :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 7 = 0 := by
  rw [← QseriesFormalization.Pending.RTau.ramanujanTau_succ_eq_jacobiThetaPS_pow_eight_coeff]
  exact ramanujanTau_mod2_eq_zero_at_eight

/-- Concrete checkpoint: coefficient at exponent `9` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_nine :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 9 = 0 := by
  rw [← QseriesFormalization.Pending.RTau.ramanujanTau_succ_eq_jacobiThetaPS_pow_eight_coeff]
  exact ramanujanTau_mod2_eq_zero_at_ten

/-- Concrete checkpoint: coefficient at exponent `11` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_eleven :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 11 = 0 := by
  rw [← QseriesFormalization.Pending.RTau.ramanujanTau_succ_eq_jacobiThetaPS_pow_eight_coeff]
  exact ramanujanTau_mod2_eq_zero_at_twelve

/-- Concrete checkpoint: coefficient at exponent `13` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_thirteen :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 13 = 0 := by
  rw [← QseriesFormalization.Pending.RTau.ramanujanTau_succ_eq_jacobiThetaPS_pow_eight_coeff]
  exact ramanujanTau_mod2_eq_zero_at_fourteen

/-- Concrete checkpoint: coefficient at exponent `15` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_fifteen :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 15 = 0 := by
  rw [← QseriesFormalization.Pending.RTau.ramanujanTau_succ_eq_jacobiThetaPS_pow_eight_coeff]
  exact ramanujanTau_mod2_eq_zero_at_sixteen

/-- Concrete checkpoint: coefficient at exponent `17` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_seventeen :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 17 = 0 := by
  rw [← QseriesFormalization.Pending.RTau.ramanujanTau_succ_eq_jacobiThetaPS_pow_eight_coeff]
  exact ramanujanTau_mod2_eq_zero_at_eighteen

/-- Concrete checkpoint: coefficient at exponent `19` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_nineteen :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 19 = 0 := by
  rw [← QseriesFormalization.Pending.RTau.ramanujanTau_succ_eq_jacobiThetaPS_pow_eight_coeff]
  exact ramanujanTau_mod2_eq_zero_at_twenty

/-- The structural exponents `4*k*(k+1)` are multiples of `8`. -/
theorem eight_dvd_four_mul_succ (k : ℕ) :
    8 ∣ 4 * k * (k + 1) := by
  refine ⟨k * (k + 1) / 2, ?_⟩
  have htri := QseriesFormalization.PartIV.Ch19.two_mul_triangular k
  calc
    4 * k * (k + 1)
        = 4 * (k * (k + 1)) := by ring
    _ = 4 * (2 * (k * (k + 1) / 2)) := by rw [htri]
    _ = 8 * (k * (k + 1) / 2) := by ring

/-- The structural tau indices `4*k*(k+1)+1` are exactly odd squares. -/
theorem four_mul_succ_add_one_eq_odd_square (k : ℕ) :
    4 * k * (k + 1) + 1 = (2 * k + 1) ^ 2 := by
  ring

/-- Odd squares in this parametrization expand to the structural tau indices. -/
theorem odd_square_eq_four_mul_succ_add_one (k : ℕ) :
    (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 :=
  (four_mul_succ_add_one_eq_odd_square k).symm

/-- The predecessor of an odd square is the shifted structural exponent. -/
theorem odd_square_pred_eq_four_mul_succ (k : ℕ) :
    (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := by
  rw [odd_square_eq_four_mul_succ_add_one]
  omega

/-- Odd-square predecessors are coefficient-one exponents for
`(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_odd_square_pred (k : ℕ) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff ((2 * k + 1) ^ 2 - 1) = 1 := by
  rw [odd_square_pred_eq_four_mul_succ]
  exact coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_four_mul k

/-- Odd-square predecessors are nonzero coefficient exponents for
`(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_ne_zero_of_odd_square_pred (k : ℕ) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff ((2 * k + 1) ^ 2 - 1) ≠ 0 :=
  zmod2_eq_one_iff_ne_zero.1
    (coeff_jacobiThetaPS_pow_eight_mod2_eq_one_of_odd_square_pred k)

/-- The structural exponents `4*k*(k+1)` are `0 mod 8`. -/
theorem four_mul_succ_mod_eight (k : ℕ) :
    (4 * k * (k + 1)) % 8 = 0 := by
  obtain ⟨m, hm⟩ := eight_dvd_four_mul_succ k
  rw [hm, Nat.mul_mod]
  norm_num

/-- The corresponding tau indices `4*k*(k+1)+1` are `1 mod 8`. -/
theorem four_mul_succ_add_one_mod_eight (k : ℕ) :
    (4 * k * (k + 1) + 1) % 8 = 1 := by
  rw [Nat.add_mod, four_mul_succ_mod_eight]

/-- An odd square is `1 mod 8`. -/
theorem odd_square_mod_eight (k : ℕ) :
    ((2 * k + 1) ^ 2) % 8 = 1 := by
  have hdiv : 8 ∣ 4 * k * (k + 1) := eight_dvd_four_mul_succ k
  rw [odd_square_eq_four_mul_succ_add_one]
  omega

/-- A nonzero shifted tau value modulo `2` forces the shifted exponent to be
`0 mod 8`. -/
theorem mod_eight_eq_zero_of_ramanujanTau_succ_mod2_ne_zero
    {n : ℕ} (hne : ramanujanTau (ZMod 2) (n + 1) ≠ 0) :
    n % 8 = 0 := by
  obtain ⟨k, hk⟩ := four_mul_of_ramanujanTau_succ_mod2_ne_zero hne
  obtain ⟨t, ht⟩ := eight_dvd_four_mul_succ k
  rw [hk, ht, Nat.mul_mod]
  norm_num

/-- A shifted tau value equal to `1` modulo `2` forces the shifted exponent to
be `0 mod 8`. -/
theorem mod_eight_eq_zero_of_ramanujanTau_succ_mod2_eq_one
    {n : ℕ} (hone : ramanujanTau (ZMod 2) (n + 1) = 1) :
    n % 8 = 0 :=
  mod_eight_eq_zero_of_ramanujanTau_succ_mod2_ne_zero
    ((ramanujanTau_mod2_eq_one_iff_ne_zero (n + 1)).mp hone)

/-- The shifted tau value is zero modulo `2` unless the shifted exponent is
`0 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_mod_eight_ne_zero
    {n : ℕ} (hn : n % 8 ≠ 0) :
    ramanujanTau (ZMod 2) (n + 1) = 0 := by
  by_contra hne
  exact hn (mod_eight_eq_zero_of_ramanujanTau_succ_mod2_ne_zero hne)

/-- The shifted tau value is zero modulo `2` at exponents congruent to
`1 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_mod_eight_eq_one
    {n : ℕ} (hn : n % 8 = 1) :
    ramanujanTau (ZMod 2) (n + 1) = 0 :=
  ramanujanTau_succ_mod2_eq_zero_of_mod_eight_ne_zero (by omega)

/-- The shifted tau value is zero modulo `2` at exponents congruent to
`2 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_mod_eight_eq_two
    {n : ℕ} (hn : n % 8 = 2) :
    ramanujanTau (ZMod 2) (n + 1) = 0 :=
  ramanujanTau_succ_mod2_eq_zero_of_mod_eight_ne_zero (by omega)

/-- The shifted tau value is zero modulo `2` at exponents congruent to
`3 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_mod_eight_eq_three
    {n : ℕ} (hn : n % 8 = 3) :
    ramanujanTau (ZMod 2) (n + 1) = 0 :=
  ramanujanTau_succ_mod2_eq_zero_of_mod_eight_ne_zero (by omega)

/-- The shifted tau value is zero modulo `2` at exponents congruent to
`4 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_mod_eight_eq_four
    {n : ℕ} (hn : n % 8 = 4) :
    ramanujanTau (ZMod 2) (n + 1) = 0 :=
  ramanujanTau_succ_mod2_eq_zero_of_mod_eight_ne_zero (by omega)

/-- The shifted tau value is zero modulo `2` at exponents congruent to
`5 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_mod_eight_eq_five
    {n : ℕ} (hn : n % 8 = 5) :
    ramanujanTau (ZMod 2) (n + 1) = 0 :=
  ramanujanTau_succ_mod2_eq_zero_of_mod_eight_ne_zero (by omega)

/-- The shifted tau value is zero modulo `2` at exponents congruent to
`6 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_mod_eight_eq_six
    {n : ℕ} (hn : n % 8 = 6) :
    ramanujanTau (ZMod 2) (n + 1) = 0 :=
  ramanujanTau_succ_mod2_eq_zero_of_mod_eight_ne_zero (by omega)

/-- The shifted tau value is zero modulo `2` at exponents congruent to
`7 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_mod_eight_eq_seven
    {n : ℕ} (hn : n % 8 = 7) :
    ramanujanTau (ZMod 2) (n + 1) = 0 :=
  ramanujanTau_succ_mod2_eq_zero_of_mod_eight_ne_zero (by omega)

/-- If `m` is not `1 mod 8`, it cannot be an odd square. -/
theorem not_odd_square_of_mod_eight_ne_one {m : ℕ} (hm : m % 8 ≠ 1) :
    ¬ ∃ k, m = (2 * k + 1) ^ 2 := by
  rintro ⟨k, hk⟩
  have hsq := odd_square_mod_eight k
  rw [← hk] at hsq
  exact hm hsq

/-- A number congruent to `0 mod 8` cannot be an odd square. -/
theorem not_odd_square_of_mod_eight_eq_zero {m : ℕ} (hm : m % 8 = 0) :
    ¬ ∃ k, m = (2 * k + 1) ^ 2 :=
  not_odd_square_of_mod_eight_ne_one (by omega)

/-- A number congruent to `2 mod 8` cannot be an odd square. -/
theorem not_odd_square_of_mod_eight_eq_two {m : ℕ} (hm : m % 8 = 2) :
    ¬ ∃ k, m = (2 * k + 1) ^ 2 :=
  not_odd_square_of_mod_eight_ne_one (by omega)

/-- A number congruent to `3 mod 8` cannot be an odd square. -/
theorem not_odd_square_of_mod_eight_eq_three {m : ℕ} (hm : m % 8 = 3) :
    ¬ ∃ k, m = (2 * k + 1) ^ 2 :=
  not_odd_square_of_mod_eight_ne_one (by omega)

/-- A number congruent to `4 mod 8` cannot be an odd square. -/
theorem not_odd_square_of_mod_eight_eq_four {m : ℕ} (hm : m % 8 = 4) :
    ¬ ∃ k, m = (2 * k + 1) ^ 2 :=
  not_odd_square_of_mod_eight_ne_one (by omega)

/-- A number congruent to `5 mod 8` cannot be an odd square. -/
theorem not_odd_square_of_mod_eight_eq_five {m : ℕ} (hm : m % 8 = 5) :
    ¬ ∃ k, m = (2 * k + 1) ^ 2 :=
  not_odd_square_of_mod_eight_ne_one (by omega)

/-- A number congruent to `6 mod 8` cannot be an odd square. -/
theorem not_odd_square_of_mod_eight_eq_six {m : ℕ} (hm : m % 8 = 6) :
    ¬ ∃ k, m = (2 * k + 1) ^ 2 :=
  not_odd_square_of_mod_eight_ne_one (by omega)

/-- A number congruent to `7 mod 8` cannot be an odd square. -/
theorem not_odd_square_of_mod_eight_eq_seven {m : ℕ} (hm : m % 8 = 7) :
    ¬ ∃ k, m = (2 * k + 1) ^ 2 :=
  not_odd_square_of_mod_eight_ne_one (by omega)

/-- Tau is even at every positive index not congruent to `1 mod 8`. -/
theorem ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one
    {m : ℕ} (hmpos : 1 ≤ m) (hm8 : m % 8 ≠ 1) :
    ramanujanTau (ZMod 2) m = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square hmpos
    (not_odd_square_of_mod_eight_ne_one hm8)

/-- Tau is even at every positive index congruent to `0 mod 8`. -/
theorem ramanujanTau_mod2_eq_zero_of_mod_eight_eq_zero
    {m : ℕ} (hmpos : 1 ≤ m) (hm8 : m % 8 = 0) :
    ramanujanTau (ZMod 2) m = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one hmpos (by omega)

/-- Tau is even at every positive index congruent to `2 mod 8`. -/
theorem ramanujanTau_mod2_eq_zero_of_mod_eight_eq_two
    {m : ℕ} (hmpos : 1 ≤ m) (hm8 : m % 8 = 2) :
    ramanujanTau (ZMod 2) m = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one hmpos (by omega)

/-- Tau is even at every positive index congruent to `3 mod 8`. -/
theorem ramanujanTau_mod2_eq_zero_of_mod_eight_eq_three
    {m : ℕ} (hmpos : 1 ≤ m) (hm8 : m % 8 = 3) :
    ramanujanTau (ZMod 2) m = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one hmpos (by omega)

/-- Tau is even at every positive index congruent to `4 mod 8`. -/
theorem ramanujanTau_mod2_eq_zero_of_mod_eight_eq_four
    {m : ℕ} (hmpos : 1 ≤ m) (hm8 : m % 8 = 4) :
    ramanujanTau (ZMod 2) m = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one hmpos (by omega)

/-- Tau is even at every positive index congruent to `5 mod 8`. -/
theorem ramanujanTau_mod2_eq_zero_of_mod_eight_eq_five
    {m : ℕ} (hmpos : 1 ≤ m) (hm8 : m % 8 = 5) :
    ramanujanTau (ZMod 2) m = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one hmpos (by omega)

/-- Tau is even at every positive index congruent to `6 mod 8`. -/
theorem ramanujanTau_mod2_eq_zero_of_mod_eight_eq_six
    {m : ℕ} (hmpos : 1 ≤ m) (hm8 : m % 8 = 6) :
    ramanujanTau (ZMod 2) m = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one hmpos (by omega)

/-- Tau is even at every positive index congruent to `7 mod 8`. -/
theorem ramanujanTau_mod2_eq_zero_of_mod_eight_eq_seven
    {m : ℕ} (hmpos : 1 ≤ m) (hm8 : m % 8 = 7) :
    ramanujanTau (ZMod 2) m = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one hmpos (by omega)

/-- Concrete checkpoint: `τ(3)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three :
    ramanujanTau (ZMod 2) 3 = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(5)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_five :
    ramanujanTau (ZMod 2) 5 = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(7)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_seven :
    ramanujanTau (ZMod 2) 7 = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(11)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eleven :
    ramanujanTau (ZMod 2) 11 = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(13)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_thirteen :
    ramanujanTau (ZMod 2) 13 = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(15)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_fifteen :
    ramanujanTau (ZMod 2) 15 = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(19)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_nineteen :
    ramanujanTau (ZMod 2) 19 = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(21)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_twenty_one :
    ramanujanTau (ZMod 2) 21 = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(23)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_twenty_three :
    ramanujanTau (ZMod 2) 23 = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(29)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_twenty_nine :
    ramanujanTau (ZMod 2) 29 = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(31)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_thirty_one :
    ramanujanTau (ZMod 2) 31 = 0 :=
  ramanujanTau_mod2_eq_zero_of_mod_eight_ne_one (by norm_num) (by norm_num)

/-- Concrete checkpoint: `τ(17)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_seventeen :
    ramanujanTau (ZMod 2) 17 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 2 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(33)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_thirty_three :
    ramanujanTau (ZMod 2) 33 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 2 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(41)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_forty_one :
    ramanujanTau (ZMod 2) 41 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 2 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(57)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_fifty_seven :
    ramanujanTau (ZMod 2) 57 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 3 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(65)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_sixty_five :
    ramanujanTau (ZMod 2) 65 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 3 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(73)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_seventy_three :
    ramanujanTau (ZMod 2) 73 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 3 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(89)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eighty_nine :
    ramanujanTau (ZMod 2) 89 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 4 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(97)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_ninety_seven :
    ramanujanTau (ZMod 2) 97 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 4 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(105)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_hundred_five :
    ramanujanTau (ZMod 2) 105 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 4 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(113)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_hundred_thirteen :
    ramanujanTau (ZMod 2) 113 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 4 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(129)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 129 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 5 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(137)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 137 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 5 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(145)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_hundred_forty_five :
    ramanujanTau (ZMod 2) 145 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 5 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(153)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_hundred_fifty_three :
    ramanujanTau (ZMod 2) 153 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 5 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(161)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_hundred_sixty_one :
    ramanujanTau (ZMod 2) 161 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 6 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(177)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 177 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 7 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(185)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_hundred_eighty_five :
    ramanujanTau (ZMod 2) 185 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 7 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(193)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_hundred_ninety_three :
    ramanujanTau (ZMod 2) 193 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 7 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(201)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_hundred_one :
    ramanujanTau (ZMod 2) 201 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 7 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(209)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_hundred_nine :
    ramanujanTau (ZMod 2) 209 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 7 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(217)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_hundred_seventeen :
    ramanujanTau (ZMod 2) 217 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 7 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(233)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_hundred_thirty_three :
    ramanujanTau (ZMod 2) 233 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 7 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(241)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_hundred_forty_one :
    ramanujanTau (ZMod 2) 241 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 8 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(249)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_hundred_forty_nine :
    ramanujanTau (ZMod 2) 249 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 8 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(257)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 257 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 8 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(265)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_hundred_sixty_five :
    ramanujanTau (ZMod 2) 265 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 8 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(273)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_hundred_seventy_three :
    ramanujanTau (ZMod 2) 273 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 8 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(281)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_hundred_eighty_one :
    ramanujanTau (ZMod 2) 281 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 8 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(297)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_hundred_ninety_seven :
    ramanujanTau (ZMod 2) 297 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 8 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(305)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_hundred_five :
    ramanujanTau (ZMod 2) 305 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 8 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(313)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_hundred_thirteen :
    ramanujanTau (ZMod 2) 313 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 10 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(321)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_hundred_twenty_one :
    ramanujanTau (ZMod 2) 321 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 10 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(329)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 329 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 10 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(337)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 337 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 10 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(345)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_hundred_forty_five :
    ramanujanTau (ZMod 2) 345 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 10 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(353)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_hundred_fifty_three :
    ramanujanTau (ZMod 2) 353 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 10 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(369)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 369 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 10 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(377)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 377 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 10 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(385)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_hundred_eighty_five :
    ramanujanTau (ZMod 2) 385 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(393)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_hundred_ninety_three :
    ramanujanTau (ZMod 2) 393 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(401)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_four_hundred_one :
    ramanujanTau (ZMod 2) 401 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(409)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_four_hundred_nine :
    ramanujanTau (ZMod 2) 409 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(417)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_four_hundred_seventeen :
    ramanujanTau (ZMod 2) 417 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(425)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_four_hundred_twenty_five :
    ramanujanTau (ZMod 2) 425 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(433)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_four_hundred_thirty_three :
    ramanujanTau (ZMod 2) 433 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(449)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_four_hundred_forty_nine :
    ramanujanTau (ZMod 2) 449 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(457)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_four_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 457 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(465)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_four_hundred_sixty_five :
    ramanujanTau (ZMod 2) 465 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(473)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_four_hundred_seventy_three :
    ramanujanTau (ZMod 2) 473 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(481)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_four_hundred_eighty_one :
    ramanujanTau (ZMod 2) 481 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(489)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_four_hundred_eighty_nine :
    ramanujanTau (ZMod 2) 489 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(497)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_four_hundred_ninety_seven :
    ramanujanTau (ZMod 2) 497 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(505)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_five_hundred_five :
    ramanujanTau (ZMod 2) 505 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(513)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_five_hundred_thirteen :
    ramanujanTau (ZMod 2) 513 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 11 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(537)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_five_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 537 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(545)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_five_hundred_forty_five :
    ramanujanTau (ZMod 2) 545 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(553)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_five_hundred_fifty_three :
    ramanujanTau (ZMod 2) 553 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(561)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_five_hundred_sixty_one :
    ramanujanTau (ZMod 2) 561 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(569)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_five_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 569 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(577)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_five_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 577 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(585)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_five_hundred_eighty_five :
    ramanujanTau (ZMod 2) 585 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(593)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_five_hundred_ninety_three :
    ramanujanTau (ZMod 2) 593 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(601)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_six_hundred_one :
    ramanujanTau (ZMod 2) 601 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(609)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_six_hundred_nine :
    ramanujanTau (ZMod 2) 609 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(617)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_six_hundred_seventeen :
    ramanujanTau (ZMod 2) 617 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(633)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_six_hundred_thirty_three :
    ramanujanTau (ZMod 2) 633 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(641)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_six_hundred_forty_one :
    ramanujanTau (ZMod 2) 641 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(649)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_six_hundred_forty_nine :
    ramanujanTau (ZMod 2) 649 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(657)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_six_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 657 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(665)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_six_hundred_sixty_five :
    ramanujanTau (ZMod 2) 665 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(673)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_six_hundred_seventy_three :
    ramanujanTau (ZMod 2) 673 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(681)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_six_hundred_eighty_one :
    ramanujanTau (ZMod 2) 681 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(689)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_six_hundred_eighty_nine :
    ramanujanTau (ZMod 2) 689 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(697)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_six_hundred_ninety_seven :
    ramanujanTau (ZMod 2) 697 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(705)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_seven_hundred_five :
    ramanujanTau (ZMod 2) 705 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(713)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_seven_hundred_thirteen :
    ramanujanTau (ZMod 2) 713 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(721)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_seven_hundred_twenty_one :
    ramanujanTau (ZMod 2) 721 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 12 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(737)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_seven_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 737 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 13 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(745)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_seven_hundred_forty_five :
    ramanujanTau (ZMod 2) 745 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 13 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(753)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_seven_hundred_fifty_three :
    ramanujanTau (ZMod 2) 753 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 13 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(761)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_seven_hundred_sixty_one :
    ramanujanTau (ZMod 2) 761 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 13 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(769)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_seven_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 769 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 13 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(777)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_seven_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 777 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 13 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(785)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_seven_hundred_eighty_five :
    ramanujanTau (ZMod 2) 785 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 13 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(793)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_seven_hundred_ninety_three :
    ramanujanTau (ZMod 2) 793 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 13 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(801)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eight_hundred_one :
    ramanujanTau (ZMod 2) 801 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 13 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(809)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eight_hundred_nine :
    ramanujanTau (ZMod 2) 809 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 14 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(817)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eight_hundred_seventeen :
    ramanujanTau (ZMod 2) 817 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 14 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(825)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eight_hundred_twenty_five :
    ramanujanTau (ZMod 2) 825 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 14 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(833)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eight_hundred_thirty_three :
    ramanujanTau (ZMod 2) 833 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 14 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(849)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eight_hundred_forty_nine :
    ramanujanTau (ZMod 2) 849 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 14 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(857)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eight_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 857 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 14 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(865)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eight_hundred_sixty_five :
    ramanujanTau (ZMod 2) 865 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 14 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(873)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eight_hundred_seventy_three :
    ramanujanTau (ZMod 2) 873 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 14 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(881)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eight_hundred_eighty_one :
    ramanujanTau (ZMod 2) 881 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 15 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(889)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eight_hundred_eighty_nine :
    ramanujanTau (ZMod 2) 889 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 15 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(897)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_eight_hundred_ninety_seven :
    ramanujanTau (ZMod 2) 897 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 15 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(905)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_nine_hundred_five :
    ramanujanTau (ZMod 2) 905 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 15 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(913)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_nine_hundred_thirteen :
    ramanujanTau (ZMod 2) 913 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 15 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(921)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_nine_hundred_twenty_one :
    ramanujanTau (ZMod 2) 921 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 15 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(929)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_nine_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 929 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 15 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(937)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_nine_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 937 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 15 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(945)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_nine_hundred_forty_five :
    ramanujanTau (ZMod 2) 945 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(953)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_nine_hundred_fifty_three :
    ramanujanTau (ZMod 2) 953 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(969)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_nine_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 969 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(977)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_nine_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 977 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(985)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_nine_hundred_eighty_five :
    ramanujanTau (ZMod 2) 985 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(993)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_nine_hundred_ninety_three :
    ramanujanTau (ZMod 2) 993 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1001)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_one :
    ramanujanTau (ZMod 2) 1001 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1009)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_nine :
    ramanujanTau (ZMod 2) 1009 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1017)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_seventeen :
    ramanujanTau (ZMod 2) 1017 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1025)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_twenty_five :
    ramanujanTau (ZMod 2) 1025 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1033)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_thirty_three :
    ramanujanTau (ZMod 2) 1033 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1041)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_forty_one :
    ramanujanTau (ZMod 2) 1041 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1049)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_forty_nine :
    ramanujanTau (ZMod 2) 1049 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1057)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_fifty_seven :
    ramanujanTau (ZMod 2) 1057 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1065)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_sixty_five :
    ramanujanTau (ZMod 2) 1065 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1073)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_seventy_three :
    ramanujanTau (ZMod 2) 1073 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 16 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1081)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_eighty_one :
    ramanujanTau (ZMod 2) 1081 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1097)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_ninety_seven :
    ramanujanTau (ZMod 2) 1097 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1105)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_one_hundred_five :
    ramanujanTau (ZMod 2) 1105 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1113)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_one_hundred_thirteen :
    ramanujanTau (ZMod 2) 1113 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1121)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_one_hundred_twenty_one :
    ramanujanTau (ZMod 2) 1121 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1129)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_one_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 1129 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1137)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_one_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 1137 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1145)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_one_hundred_forty_five :
    ramanujanTau (ZMod 2) 1145 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1153)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_one_hundred_fifty_three :
    ramanujanTau (ZMod 2) 1153 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1161)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_one_hundred_sixty_one :
    ramanujanTau (ZMod 2) 1161 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1169)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_one_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 1169 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1177)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_one_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 1177 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1185)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_one_hundred_eighty_five :
    ramanujanTau (ZMod 2) 1185 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1193)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_one_hundred_ninety_three :
    ramanujanTau (ZMod 2) 1193 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1201)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_two_hundred_one :
    ramanujanTau (ZMod 2) 1201 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1209)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_two_hundred_nine :
    ramanujanTau (ZMod 2) 1209 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1217)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_two_hundred_seventeen :
    ramanujanTau (ZMod 2) 1217 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 17 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1233)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_two_hundred_thirty_three :
    ramanujanTau (ZMod 2) 1233 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1241)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_two_hundred_forty_one :
    ramanujanTau (ZMod 2) 1241 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1249)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_two_hundred_forty_nine :
    ramanujanTau (ZMod 2) 1249 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1257)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_two_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 1257 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1265)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_two_hundred_sixty_five :
    ramanujanTau (ZMod 2) 1265 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1273)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_two_hundred_seventy_three :
    ramanujanTau (ZMod 2) 1273 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1281)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_two_hundred_eighty_one :
    ramanujanTau (ZMod 2) 1281 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1289)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_two_hundred_eighty_nine :
    ramanujanTau (ZMod 2) 1289 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1297)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_two_hundred_ninety_seven :
    ramanujanTau (ZMod 2) 1297 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1305)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_three_hundred_five :
    ramanujanTau (ZMod 2) 1305 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1313)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_three_hundred_thirteen :
    ramanujanTau (ZMod 2) 1313 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1321)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_three_hundred_twenty_one :
    ramanujanTau (ZMod 2) 1321 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1329)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_three_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 1329 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1337)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_three_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 1337 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1345)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_three_hundred_forty_five :
    ramanujanTau (ZMod 2) 1345 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1353)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_three_hundred_fifty_three :
    ramanujanTau (ZMod 2) 1353 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1361)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_three_hundred_sixty_one :
    ramanujanTau (ZMod 2) 1361 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1377)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_three_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 1377 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1385)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_three_hundred_eighty_five :
    ramanujanTau (ZMod 2) 1385 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1393)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_three_hundred_ninety_three :
    ramanujanTau (ZMod 2) 1393 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1401)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_four_hundred_one :
    ramanujanTau (ZMod 2) 1401 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1409)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_four_hundred_nine :
    ramanujanTau (ZMod 2) 1409 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1417)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_four_hundred_seventeen :
    ramanujanTau (ZMod 2) 1417 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 18 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1425)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_four_hundred_twenty_five :
    ramanujanTau (ZMod 2) 1425 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1433)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_four_hundred_thirty_three :
    ramanujanTau (ZMod 2) 1433 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1441)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_four_hundred_forty_one :
    ramanujanTau (ZMod 2) 1441 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1449)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_four_hundred_forty_nine :
    ramanujanTau (ZMod 2) 1449 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1457)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_four_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 1457 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1465)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_four_hundred_sixty_five :
    ramanujanTau (ZMod 2) 1465 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1473)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_four_hundred_seventy_three :
    ramanujanTau (ZMod 2) 1473 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1481)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_four_hundred_eighty_one :
    ramanujanTau (ZMod 2) 1481 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1489)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_four_hundred_eighty_nine :
    ramanujanTau (ZMod 2) 1489 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1497)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_four_hundred_ninety_seven :
    ramanujanTau (ZMod 2) 1497 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1505)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_five_hundred_five :
    ramanujanTau (ZMod 2) 1505 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1513)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_five_hundred_thirteen :
    ramanujanTau (ZMod 2) 1513 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1529)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_five_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 1529 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1537)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_five_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 1537 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1545)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_five_hundred_forty_five :
    ramanujanTau (ZMod 2) 1545 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1553)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_five_hundred_fifty_three :
    ramanujanTau (ZMod 2) 1553 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1561)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_five_hundred_sixty_one :
    ramanujanTau (ZMod 2) 1561 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1569)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_five_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 1569 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1577)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_five_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 1577 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1585)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_five_hundred_eighty_five :
    ramanujanTau (ZMod 2) 1585 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1593)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_five_hundred_ninety_three :
    ramanujanTau (ZMod 2) 1593 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1601)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_six_hundred_one :
    ramanujanTau (ZMod 2) 1601 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1609)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_six_hundred_nine :
    ramanujanTau (ZMod 2) 1609 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1617)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_six_hundred_seventeen :
    ramanujanTau (ZMod 2) 1617 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 19 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1625)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_six_hundred_twenty_five :
    ramanujanTau (ZMod 2) 1625 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 20 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1633)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_six_hundred_thirty_three :
    ramanujanTau (ZMod 2) 1633 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 20 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1641)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_six_hundred_forty_one :
    ramanujanTau (ZMod 2) 1641 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 20 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1649)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_six_hundred_forty_nine :
    ramanujanTau (ZMod 2) 1649 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 20 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1657)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_six_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 1657 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 20 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1665)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_six_hundred_sixty_five :
    ramanujanTau (ZMod 2) 1665 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 20 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1673)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_six_hundred_seventy_three :
    ramanujanTau (ZMod 2) 1673 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 20 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1689)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_six_hundred_eighty_nine :
    ramanujanTau (ZMod 2) 1689 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 20 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1697)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_six_hundred_ninety_seven :
    ramanujanTau (ZMod 2) 1697 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1705)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_seven_hundred_five :
    ramanujanTau (ZMod 2) 1705 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1713)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_seven_hundred_thirteen :
    ramanujanTau (ZMod 2) 1713 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1721)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_seven_hundred_twenty_one :
    ramanujanTau (ZMod 2) 1721 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1729)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_seven_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 1729 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1737)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_seven_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 1737 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1745)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_seven_hundred_forty_five :
    ramanujanTau (ZMod 2) 1745 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1753)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_seven_hundred_fifty_three :
    ramanujanTau (ZMod 2) 1753 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1761)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_seven_hundred_sixty_one :
    ramanujanTau (ZMod 2) 1761 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1769)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_seven_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 1769 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1777)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_seven_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 1777 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1785)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_seven_hundred_eighty_five :
    ramanujanTau (ZMod 2) 1785 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1793)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_seven_hundred_ninety_three :
    ramanujanTau (ZMod 2) 1793 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1801)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_eight_hundred_one :
    ramanujanTau (ZMod 2) 1801 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1809)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_eight_hundred_nine :
    ramanujanTau (ZMod 2) 1809 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1817)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_eight_hundred_seventeen :
    ramanujanTau (ZMod 2) 1817 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1825)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_eight_hundred_twenty_five :
    ramanujanTau (ZMod 2) 1825 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1833)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_eight_hundred_thirty_three :
    ramanujanTau (ZMod 2) 1833 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1841)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_eight_hundred_forty_one :
    ramanujanTau (ZMod 2) 1841 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1857)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_eight_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 1857 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1865)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_eight_hundred_sixty_five :
    ramanujanTau (ZMod 2) 1865 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1873)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_eight_hundred_seventy_three :
    ramanujanTau (ZMod 2) 1873 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1881)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_eight_hundred_eighty_one :
    ramanujanTau (ZMod 2) 1881 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1889)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_eight_hundred_eighty_nine :
    ramanujanTau (ZMod 2) 1889 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 21 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1897)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_eight_hundred_ninety_seven :
    ramanujanTau (ZMod 2) 1897 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1905)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_nine_hundred_five :
    ramanujanTau (ZMod 2) 1905 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1913)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_nine_hundred_thirteen :
    ramanujanTau (ZMod 2) 1913 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1921)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_nine_hundred_twenty_one :
    ramanujanTau (ZMod 2) 1921 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1929)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_nine_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 1929 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1937)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_nine_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 1937 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1945)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_nine_hundred_forty_five :
    ramanujanTau (ZMod 2) 1945 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1953)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_nine_hundred_fifty_three :
    ramanujanTau (ZMod 2) 1953 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1961)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_nine_hundred_sixty_one :
    ramanujanTau (ZMod 2) 1961 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1969)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_nine_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 1969 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1977)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_nine_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 1977 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1985)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_nine_hundred_eighty_five :
    ramanujanTau (ZMod 2) 1985 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(1993)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_one_thousand_nine_hundred_ninety_three :
    ramanujanTau (ZMod 2) 1993 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2001)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_one :
    ramanujanTau (ZMod 2) 2001 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2009)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_nine :
    ramanujanTau (ZMod 2) 2009 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2017)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_seventeen :
    ramanujanTau (ZMod 2) 2017 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 22 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2033)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_thirty_three :
    ramanujanTau (ZMod 2) 2033 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2041)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_forty_one :
    ramanujanTau (ZMod 2) 2041 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2049)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_forty_nine :
    ramanujanTau (ZMod 2) 2049 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2057)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_fifty_seven :
    ramanujanTau (ZMod 2) 2057 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2065)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_sixty_five :
    ramanujanTau (ZMod 2) 2065 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2073)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_seventy_three :
    ramanujanTau (ZMod 2) 2073 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2081)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_eighty_one :
    ramanujanTau (ZMod 2) 2081 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2089)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_eighty_nine :
    ramanujanTau (ZMod 2) 2089 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2097)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_ninety_seven :
    ramanujanTau (ZMod 2) 2097 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2105)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_one_hundred_five :
    ramanujanTau (ZMod 2) 2105 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2113)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_one_hundred_thirteen :
    ramanujanTau (ZMod 2) 2113 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2121)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_one_hundred_twenty_one :
    ramanujanTau (ZMod 2) 2121 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2129)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_one_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 2129 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2137)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_one_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 2137 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2145)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_one_hundred_forty_five :
    ramanujanTau (ZMod 2) 2145 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2153)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_one_hundred_fifty_three :
    ramanujanTau (ZMod 2) 2153 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2161)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_one_hundred_sixty_one :
    ramanujanTau (ZMod 2) 2161 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2169)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_one_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 2169 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2177)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_one_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 2177 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2185)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_one_hundred_eighty_five :
    ramanujanTau (ZMod 2) 2185 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2193)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_one_hundred_ninety_three :
    ramanujanTau (ZMod 2) 2193 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2201)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_two_hundred_one :
    ramanujanTau (ZMod 2) 2201 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2217)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_two_hundred_seventeen :
    ramanujanTau (ZMod 2) 2217 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2225)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_two_hundred_twenty_five :
    ramanujanTau (ZMod 2) 2225 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2233)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_two_hundred_thirty_three :
    ramanujanTau (ZMod 2) 2233 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2241)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_two_hundred_forty_one :
    ramanujanTau (ZMod 2) 2241 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2249)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_two_hundred_forty_nine :
    ramanujanTau (ZMod 2) 2249 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2257)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_two_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 2257 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2265)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_two_hundred_sixty_five :
    ramanujanTau (ZMod 2) 2265 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2273)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_two_hundred_seventy_three :
    ramanujanTau (ZMod 2) 2273 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2281)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_two_hundred_eighty_one :
    ramanujanTau (ZMod 2) 2281 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2289)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_two_hundred_eighty_nine :
    ramanujanTau (ZMod 2) 2289 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2297)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_two_hundred_ninety_seven :
    ramanujanTau (ZMod 2) 2297 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2305)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_three_hundred_five :
    ramanujanTau (ZMod 2) 2305 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2313)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_three_hundred_thirteen :
    ramanujanTau (ZMod 2) 2313 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2321)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_three_hundred_twenty_one :
    ramanujanTau (ZMod 2) 2321 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2329)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_three_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 2329 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2337)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_three_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 2337 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2345)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_three_hundred_forty_five :
    ramanujanTau (ZMod 2) 2345 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2353)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_three_hundred_fifty_three :
    ramanujanTau (ZMod 2) 2353 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 23 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2361)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_three_hundred_sixty_one :
    ramanujanTau (ZMod 2) 2361 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2369)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_three_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 2369 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2377)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_three_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 2377 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2385)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_three_hundred_eighty_five :
    ramanujanTau (ZMod 2) 2385 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2393)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_three_hundred_ninety_three :
    ramanujanTau (ZMod 2) 2393 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2409)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_four_hundred_nine :
    ramanujanTau (ZMod 2) 2409 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2417)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_four_hundred_seventeen :
    ramanujanTau (ZMod 2) 2417 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2425)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_four_hundred_twenty_five :
    ramanujanTau (ZMod 2) 2425 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2433)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_four_hundred_thirty_three :
    ramanujanTau (ZMod 2) 2433 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2441)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_four_hundred_forty_one :
    ramanujanTau (ZMod 2) 2441 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2449)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_four_hundred_forty_nine :
    ramanujanTau (ZMod 2) 2449 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2457)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_four_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 2457 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2465)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_four_hundred_sixty_five :
    ramanujanTau (ZMod 2) 2465 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2473)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_four_hundred_seventy_three :
    ramanujanTau (ZMod 2) 2473 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2481)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_four_hundred_eighty_one :
    ramanujanTau (ZMod 2) 2481 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2489)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_four_hundred_eighty_nine :
    ramanujanTau (ZMod 2) 2489 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 24 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2497)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_four_hundred_ninety_seven :
    ramanujanTau (ZMod 2) 2497 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 25 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2505)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_five_hundred_five :
    ramanujanTau (ZMod 2) 2505 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 25 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2513)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_five_hundred_thirteen :
    ramanujanTau (ZMod 2) 2513 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 25 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2521)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_five_hundred_twenty_one :
    ramanujanTau (ZMod 2) 2521 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 25 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2529)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_five_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 2529 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 25 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2537)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_five_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 2537 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 25 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2545)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_five_hundred_forty_five :
    ramanujanTau (ZMod 2) 2545 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 25 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2553)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_five_hundred_fifty_three :
    ramanujanTau (ZMod 2) 2553 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 25 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2561)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_five_hundred_sixty_one :
    ramanujanTau (ZMod 2) 2561 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 25 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2569)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_five_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 2569 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 25 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2577)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_five_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 2577 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 25 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2585)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_five_hundred_eighty_five :
    ramanujanTau (ZMod 2) 2585 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 25 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2593)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_five_hundred_ninety_three :
    ramanujanTau (ZMod 2) 2593 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 25 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2609)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_six_hundred_nine :
    ramanujanTau (ZMod 2) 2609 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2617)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_six_hundred_seventeen :
    ramanujanTau (ZMod 2) 2617 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2625)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_six_hundred_twenty_five :
    ramanujanTau (ZMod 2) 2625 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2633)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_six_hundred_thirty_three :
    ramanujanTau (ZMod 2) 2633 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2641)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_six_hundred_forty_one :
    ramanujanTau (ZMod 2) 2641 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2649)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_six_hundred_forty_nine :
    ramanujanTau (ZMod 2) 2649 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2657)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_six_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 2657 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2665)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_six_hundred_sixty_five :
    ramanujanTau (ZMod 2) 2665 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2673)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_six_hundred_seventy_three :
    ramanujanTau (ZMod 2) 2673 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2681)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_six_hundred_eighty_one :
    ramanujanTau (ZMod 2) 2681 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2689)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_six_hundred_eighty_nine :
    ramanujanTau (ZMod 2) 2689 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2697)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_six_hundred_ninety_seven :
    ramanujanTau (ZMod 2) 2697 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2705)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_seven_hundred_five :
    ramanujanTau (ZMod 2) 2705 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2713)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_seven_hundred_thirteen :
    ramanujanTau (ZMod 2) 2713 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2721)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_seven_hundred_twenty_one :
    ramanujanTau (ZMod 2) 2721 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2729)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_seven_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 2729 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2737)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_seven_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 2737 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2745)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_seven_hundred_forty_five :
    ramanujanTau (ZMod 2) 2745 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2753)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_seven_hundred_fifty_three :
    ramanujanTau (ZMod 2) 2753 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 26 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2761)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_seven_hundred_sixty_one :
    ramanujanTau (ZMod 2) 2761 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2769)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_seven_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 2769 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2777)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_seven_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 2777 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2785)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_seven_hundred_eighty_five :
    ramanujanTau (ZMod 2) 2785 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2793)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_seven_hundred_ninety_three :
    ramanujanTau (ZMod 2) 2793 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2801)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_eight_hundred_one :
    ramanujanTau (ZMod 2) 2801 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2817)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_eight_hundred_seventeen :
    ramanujanTau (ZMod 2) 2817 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2825)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_eight_hundred_twenty_five :
    ramanujanTau (ZMod 2) 2825 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2833)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_eight_hundred_thirty_three :
    ramanujanTau (ZMod 2) 2833 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2841)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_eight_hundred_forty_one :
    ramanujanTau (ZMod 2) 2841 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2849)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_eight_hundred_forty_nine :
    ramanujanTau (ZMod 2) 2849 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2857)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_eight_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 2857 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2865)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_eight_hundred_sixty_five :
    ramanujanTau (ZMod 2) 2865 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2873)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_eight_hundred_seventy_three :
    ramanujanTau (ZMod 2) 2873 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2881)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_eight_hundred_eighty_one :
    ramanujanTau (ZMod 2) 2881 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2889)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_eight_hundred_eighty_nine :
    ramanujanTau (ZMod 2) 2889 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2897)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_eight_hundred_ninety_seven :
    ramanujanTau (ZMod 2) 2897 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2905)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_nine_hundred_five :
    ramanujanTau (ZMod 2) 2905 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2913)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_nine_hundred_thirteen :
    ramanujanTau (ZMod 2) 2913 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2921)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_nine_hundred_twenty_one :
    ramanujanTau (ZMod 2) 2921 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2929)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_nine_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 2929 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2937)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_nine_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 2937 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2945)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_nine_hundred_forty_five :
    ramanujanTau (ZMod 2) 2945 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2953)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_nine_hundred_fifty_three :
    ramanujanTau (ZMod 2) 2953 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2961)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_nine_hundred_sixty_one :
    ramanujanTau (ZMod 2) 2961 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2969)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_nine_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 2969 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2977)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_nine_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 2977 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2985)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_nine_hundred_eighty_five :
    ramanujanTau (ZMod 2) 2985 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(2993)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_two_thousand_nine_hundred_ninety_three :
    ramanujanTau (ZMod 2) 2993 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3001)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_one :
    ramanujanTau (ZMod 2) 3001 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3009)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_nine :
    ramanujanTau (ZMod 2) 3009 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3017)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_seventeen :
    ramanujanTau (ZMod 2) 3017 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 27 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3033)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_thirty_three :
    ramanujanTau (ZMod 2) 3033 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3041)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_forty_one :
    ramanujanTau (ZMod 2) 3041 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3049)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_forty_nine :
    ramanujanTau (ZMod 2) 3049 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3057)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_fifty_seven :
    ramanujanTau (ZMod 2) 3057 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3065)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_sixty_five :
    ramanujanTau (ZMod 2) 3065 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3073)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_seventy_three :
    ramanujanTau (ZMod 2) 3073 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3081)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_eighty_one :
    ramanujanTau (ZMod 2) 3081 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3089)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_eighty_nine :
    ramanujanTau (ZMod 2) 3089 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3097)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_ninety_seven :
    ramanujanTau (ZMod 2) 3097 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3105)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_one_hundred_five :
    ramanujanTau (ZMod 2) 3105 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3113)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_one_hundred_thirteen :
    ramanujanTau (ZMod 2) 3113 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3121)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_one_hundred_twenty_one :
    ramanujanTau (ZMod 2) 3121 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3129)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_one_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 3129 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3137)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_one_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 3137 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3145)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_one_hundred_forty_five :
    ramanujanTau (ZMod 2) 3145 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3153)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_one_hundred_fifty_three :
    ramanujanTau (ZMod 2) 3153 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3161)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_one_hundred_sixty_one :
    ramanujanTau (ZMod 2) 3161 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3169)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_one_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 3169 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3177)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_one_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 3177 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3185)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_one_hundred_eighty_five :
    ramanujanTau (ZMod 2) 3185 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3193)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_one_hundred_ninety_three :
    ramanujanTau (ZMod 2) 3193 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3201)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_two_hundred_one :
    ramanujanTau (ZMod 2) 3201 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3209)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_two_hundred_nine :
    ramanujanTau (ZMod 2) 3209 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3217)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_two_hundred_seventeen :
    ramanujanTau (ZMod 2) 3217 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3225)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_two_hundred_twenty_five :
    ramanujanTau (ZMod 2) 3225 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3233)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_two_hundred_thirty_three :
    ramanujanTau (ZMod 2) 3233 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3241)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_two_hundred_forty_one :
    ramanujanTau (ZMod 2) 3241 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3257)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_two_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 3257 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3265)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_two_hundred_sixty_five :
    ramanujanTau (ZMod 2) 3265 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3273)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_two_hundred_seventy_three :
    ramanujanTau (ZMod 2) 3273 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3281)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_two_hundred_eighty_one :
    ramanujanTau (ZMod 2) 3281 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3289)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_two_hundred_eighty_nine :
    ramanujanTau (ZMod 2) 3289 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3297)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_two_hundred_ninety_seven :
    ramanujanTau (ZMod 2) 3297 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3305)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_three_hundred_five :
    ramanujanTau (ZMod 2) 3305 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3313)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_three_hundred_thirteen :
    ramanujanTau (ZMod 2) 3313 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3321)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_three_hundred_twenty_one :
    ramanujanTau (ZMod 2) 3321 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3329)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_three_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 3329 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3337)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_three_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 3337 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3345)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_three_hundred_forty_five :
    ramanujanTau (ZMod 2) 3345 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3353)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_three_hundred_fifty_three :
    ramanujanTau (ZMod 2) 3353 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3361)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_three_hundred_sixty_one :
    ramanujanTau (ZMod 2) 3361 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3369)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_three_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 3369 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3377)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_three_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 3377 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3385)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_three_hundred_eighty_five :
    ramanujanTau (ZMod 2) 3385 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3393)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_three_hundred_ninety_three :
    ramanujanTau (ZMod 2) 3393 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3401)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_four_hundred_one :
    ramanujanTau (ZMod 2) 3401 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3409)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_four_hundred_nine :
    ramanujanTau (ZMod 2) 3409 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3417)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_four_hundred_seventeen :
    ramanujanTau (ZMod 2) 3417 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 28 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3425)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_four_hundred_twenty_five :
    ramanujanTau (ZMod 2) 3425 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3433)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_four_hundred_thirty_three :
    ramanujanTau (ZMod 2) 3433 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3441)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_four_hundred_forty_one :
    ramanujanTau (ZMod 2) 3441 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3449)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_four_hundred_forty_nine :
    ramanujanTau (ZMod 2) 3449 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3457)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_four_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 3457 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3465)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_four_hundred_sixty_five :
    ramanujanTau (ZMod 2) 3465 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3473)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_four_hundred_seventy_three :
    ramanujanTau (ZMod 2) 3473 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3489)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_four_hundred_eighty_nine :
    ramanujanTau (ZMod 2) 3489 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3497)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_four_hundred_ninety_seven :
    ramanujanTau (ZMod 2) 3497 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3505)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_five_hundred_five :
    ramanujanTau (ZMod 2) 3505 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3513)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_five_hundred_thirteen :
    ramanujanTau (ZMod 2) 3513 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3521)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_five_hundred_twenty_one :
    ramanujanTau (ZMod 2) 3521 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3529)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_five_hundred_twenty_nine :
    ramanujanTau (ZMod 2) 3529 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3537)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_five_hundred_thirty_seven :
    ramanujanTau (ZMod 2) 3537 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3545)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_five_hundred_forty_five :
    ramanujanTau (ZMod 2) 3545 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3553)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_five_hundred_fifty_three :
    ramanujanTau (ZMod 2) 3553 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3561)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_five_hundred_sixty_one :
    ramanujanTau (ZMod 2) 3561 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3569)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_five_hundred_sixty_nine :
    ramanujanTau (ZMod 2) 3569 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3577)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_five_hundred_seventy_seven :
    ramanujanTau (ZMod 2) 3577 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3585)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_five_hundred_eighty_five :
    ramanujanTau (ZMod 2) 3585 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3593)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_five_hundred_ninety_three :
    ramanujanTau (ZMod 2) 3593 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3601)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_six_hundred_one :
    ramanujanTau (ZMod 2) 3601 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3609)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_six_hundred_nine :
    ramanujanTau (ZMod 2) 3609 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3617)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_six_hundred_seventeen :
    ramanujanTau (ZMod 2) 3617 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 29 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3625)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_six_hundred_twenty_five :
    ramanujanTau (ZMod 2) 3625 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 30 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3633)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_six_hundred_thirty_three :
    ramanujanTau (ZMod 2) 3633 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 30 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3641)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_six_hundred_forty_one :
    ramanujanTau (ZMod 2) 3641 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 30 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3649)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_six_hundred_forty_nine :
    ramanujanTau (ZMod 2) 3649 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 30 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3657)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_six_hundred_fifty_seven :
    ramanujanTau (ZMod 2) 3657 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 30 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3665)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_six_hundred_sixty_five :
    ramanujanTau (ZMod 2) 3665 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 30 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3673)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_six_hundred_seventy_three :
    ramanujanTau (ZMod 2) 3673 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 30 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: `τ(3681)` is even. -/
theorem ramanujanTau_mod2_eq_zero_at_three_thousand_six_hundred_eighty_one :
    ramanujanTau (ZMod 2) 3681 = 0 :=
  ramanujanTau_mod2_eq_zero_of_not_odd_square (by norm_num) (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 30 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Nonzero tau modulo `2` at a positive index forces the index to be
`1 mod 8`. -/
theorem mod_eight_eq_one_of_ramanujanTau_mod2_ne_zero
    {m : ℕ} (hmpos : 1 ≤ m) (hne : ramanujanTau (ZMod 2) m ≠ 0) :
    m % 8 = 1 := by
  obtain ⟨k, hk⟩ := odd_square_of_ramanujanTau_mod2_ne_zero hmpos hne
  rw [hk]
  exact odd_square_mod_eight k

/-- Tau equal to `1` modulo `2` at a positive index forces the index to be
`1 mod 8`. -/
theorem mod_eight_eq_one_of_ramanujanTau_mod2_eq_one
    {m : ℕ} (hmpos : 1 ≤ m) (hone : ramanujanTau (ZMod 2) m = 1) :
    m % 8 = 1 :=
  mod_eight_eq_one_of_ramanujanTau_mod2_ne_zero hmpos
    ((ramanujanTau_mod2_eq_one_iff_ne_zero m).mp hone)

/-- A nonzero shifted tau value modulo `2` forces the full index to be
`1 mod 8`. -/
theorem mod_eight_eq_one_of_ramanujanTau_succ_mod2_ne_zero
    {n : ℕ} (hne : ramanujanTau (ZMod 2) (n + 1) ≠ 0) :
    (n + 1) % 8 = 1 :=
  mod_eight_eq_one_of_ramanujanTau_mod2_ne_zero (Nat.succ_pos n) hne

/-- A shifted tau value equal to `1` modulo `2` forces the full index to be
`1 mod 8`. -/
theorem mod_eight_eq_one_of_ramanujanTau_succ_mod2_eq_one
    {n : ℕ} (hone : ramanujanTau (ZMod 2) (n + 1) = 1) :
    (n + 1) % 8 = 1 :=
  mod_eight_eq_one_of_ramanujanTau_succ_mod2_ne_zero
    ((ramanujanTau_mod2_eq_one_iff_ne_zero (n + 1)).mp hone)

/-- The shifted tau value is zero modulo `2` whenever the full index is not
`1 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_ne_one
    {n : ℕ} (hn : (n + 1) % 8 ≠ 1) :
    ramanujanTau (ZMod 2) (n + 1) = 0 := by
  by_contra hne
  exact hn (mod_eight_eq_one_of_ramanujanTau_succ_mod2_ne_zero hne)

/-- The shifted tau value is zero modulo `2` when the full index is
`0 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_eq_zero
    {n : ℕ} (hn : (n + 1) % 8 = 0) :
    ramanujanTau (ZMod 2) (n + 1) = 0 :=
  ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_ne_one (by omega)

/-- The shifted tau value is zero modulo `2` when the full index is
`2 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_eq_two
    {n : ℕ} (hn : (n + 1) % 8 = 2) :
    ramanujanTau (ZMod 2) (n + 1) = 0 :=
  ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_ne_one (by omega)

/-- The shifted tau value is zero modulo `2` when the full index is
`3 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_eq_three
    {n : ℕ} (hn : (n + 1) % 8 = 3) :
    ramanujanTau (ZMod 2) (n + 1) = 0 :=
  ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_ne_one (by omega)

/-- The shifted tau value is zero modulo `2` when the full index is
`4 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_eq_four
    {n : ℕ} (hn : (n + 1) % 8 = 4) :
    ramanujanTau (ZMod 2) (n + 1) = 0 :=
  ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_ne_one (by omega)

/-- The shifted tau value is zero modulo `2` when the full index is
`5 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_eq_five
    {n : ℕ} (hn : (n + 1) % 8 = 5) :
    ramanujanTau (ZMod 2) (n + 1) = 0 :=
  ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_ne_one (by omega)

/-- The shifted tau value is zero modulo `2` when the full index is
`6 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_eq_six
    {n : ℕ} (hn : (n + 1) % 8 = 6) :
    ramanujanTau (ZMod 2) (n + 1) = 0 :=
  ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_ne_one (by omega)

/-- The shifted tau value is zero modulo `2` when the full index is
`7 mod 8`. -/
theorem ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_eq_seven
    {n : ℕ} (hn : (n + 1) % 8 = 7) :
    ramanujanTau (ZMod 2) (n + 1) = 0 :=
  ramanujanTau_succ_mod2_eq_zero_of_succ_mod_eight_ne_one (by omega)

/-- A nonzero coefficient of `(jacobiThetaPS)^8` over `ZMod 2` can occur only
at an exponent divisible by `8`. -/
theorem eight_dvd_of_coeff_jacobiThetaPS_pow_eight_mod2_ne_zero
    {n : ℕ} (hne : ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n ≠ 0) :
    8 ∣ n := by
  obtain ⟨k, hk⟩ :=
    (coeff_jacobiThetaPS_pow_eight_mod2_ne_zero_iff_four_mul n).mp hne
  rw [hk]
  exact eight_dvd_four_mul_succ k

/-- A nonzero coefficient of `(jacobiThetaPS)^8` over `ZMod 2` has exponent
`0 mod 8`. -/
theorem mod_eight_eq_zero_of_coeff_jacobiThetaPS_pow_eight_mod2_ne_zero
    {n : ℕ} (hne : ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n ≠ 0) :
    n % 8 = 0 := by
  obtain ⟨m, rfl⟩ := eight_dvd_of_coeff_jacobiThetaPS_pow_eight_mod2_ne_zero hne
  rw [Nat.mul_mod]
  norm_num

/-- Exponents not divisible by `8` have zero coefficient in `(jacobiThetaPS)^8`
over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_not_eight_dvd
    {n : ℕ} (hn : ¬ 8 ∣ n) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_not_four_mul (by
    rintro ⟨k, rfl⟩
    exact hn (eight_dvd_four_mul_succ k))

/-- Odd exponents have zero coefficient in `(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_odd
    {n : ℕ} (hn : n % 2 = 1) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_not_eight_dvd (by
    rintro ⟨m, rfl⟩
    have hmod : (8 * m) % 2 = 0 := by
      rw [Nat.mul_mod]
      norm_num
    rw [hmod] at hn
    norm_num at hn)

/-- A nonzero residue modulo `8` rules out divisibility by `8`. -/
theorem not_eight_dvd_of_mod_eight_ne_zero {n : ℕ} (hn : n % 8 ≠ 0) :
    ¬ 8 ∣ n := by
  rintro ⟨m, rfl⟩
  have hmod : (8 * m) % 8 = 0 := by
    rw [Nat.mul_mod]
    norm_num
  exact hn hmod

/-- Exponents with nonzero residue modulo `8` have zero coefficient in
`(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_ne_zero
    {n : ℕ} (hn : n % 8 ≠ 0) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_not_eight_dvd
    (not_eight_dvd_of_mod_eight_ne_zero hn)

/-- Exponents congruent to `1` modulo `8` have zero coefficient in
`(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_eq_one
    {n : ℕ} (hn : n % 8 = 1) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_ne_zero (by omega)

/-- Exponents congruent to `2` modulo `8` have zero coefficient in
`(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_eq_two
    {n : ℕ} (hn : n % 8 = 2) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_ne_zero (by omega)

/-- Exponents congruent to `3` modulo `8` have zero coefficient in
`(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_eq_three
    {n : ℕ} (hn : n % 8 = 3) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_ne_zero (by omega)

/-- Exponents congruent to `4` modulo `8` have zero coefficient in
`(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_eq_four
    {n : ℕ} (hn : n % 8 = 4) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_ne_zero (by omega)

/-- Exponents congruent to `5` modulo `8` have zero coefficient in
`(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_eq_five
    {n : ℕ} (hn : n % 8 = 5) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_ne_zero (by omega)

/-- Exponents congruent to `6` modulo `8` have zero coefficient in
`(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_eq_six
    {n : ℕ} (hn : n % 8 = 6) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_ne_zero (by omega)

/-- Exponents congruent to `7` modulo `8` have zero coefficient in
`(jacobiThetaPS)^8` over `ZMod 2`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_eq_seven
    {n : ℕ} (hn : n % 8 = 7) :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff n = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_ne_zero (by omega)

/-- Concrete checkpoint: coefficient at exponent `2` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_two :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 2 = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_ne_zero (by norm_num)

/-- Concrete checkpoint: coefficient at exponent `4` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_four :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 4 = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_ne_zero (by norm_num)

/-- Concrete checkpoint: coefficient at exponent `6` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_six :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 6 = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_ne_zero (by norm_num)

/-- Concrete checkpoint: coefficient at exponent `10` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_ten :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 10 = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_ne_zero (by norm_num)

/-- Concrete checkpoint: coefficient at exponent `12` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_twelve :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 12 = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_ne_zero (by norm_num)

/-- Concrete checkpoint: coefficient at exponent `14` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_fourteen :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 14 = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_mod_eight_ne_zero (by norm_num)

/-- Concrete checkpoint: coefficient at exponent `16` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_sixteen :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 16 = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_not_four_mul (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 2 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: coefficient at exponent `32` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_thirty_two :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 32 = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_not_four_mul (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 3 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: coefficient at exponent `40` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_forty :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 40 = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_not_four_mul (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 3 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: coefficient at exponent `56` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_fifty_six :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 56 = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_not_four_mul (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 4 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: coefficient at exponent `64` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_sixty_four :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 64 = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_not_four_mul (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 4 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

/-- Concrete checkpoint: coefficient at exponent `72` is `0`. -/
theorem coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_at_seventy_two :
    ((jacobiThetaPS (ZMod 2)) ^ 8).coeff 72 = 0 :=
  coeff_jacobiThetaPS_pow_eight_mod2_eq_zero_of_not_four_mul (by
    rintro ⟨k, hEq⟩
    have hk_le : k ≤ 5 := by nlinarith [hEq, Nat.zero_le k]
    interval_cases k <;> norm_num at hEq)

end TauParity
end Pending
end QseriesFormalization
