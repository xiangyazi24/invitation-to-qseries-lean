import QseriesFormalization.Chapter17
import QseriesFormalization.Chapter01_PartitionCount54

/-!
# Chapter 17 — Ramanujan congruences at higher `n`

Companion file to `Chapter17.lean`.  With `partitionCount 12..22` now
proved unconditionally (`Chapter01_PartitionCount{12..22}.lean`), we can
extend Chan §17's verified `5∣p(5n+4)`, `7∣p(7n+5)`, `11∣p(11n+6)`
congruences from the n=0 and n=1 cases (in `Chapter17.lean`) to several
larger `n`:

| Family | New `n` | Witness |
|--------|---------|---------|
| 5 ∣ p(5n+4) | n=2 | p(14) = 135 = 27·5 |
| 5 ∣ p(5n+4) | n=3 | p(19) = 490 = 98·5 |
| 7 ∣ p(7n+5) | n=1 | p(12) = 77 = 11·7 |
| 7 ∣ p(7n+5) | n=2 | p(19) = 490 = 70·7 |
| 11 ∣ p(11n+6) | n=1 | p(17) = 297 = 27·11 |

Each is proved unconditionally by `simp` on the relevant
`partitionCount_N` value plus `decide` on the divisibility. -/

namespace QseriesFormalization
namespace PartIV
namespace Ch17

open QseriesFormalization.Ch01 (partitionCount)

/-! ## Mod-5 family: `5 ∣ p(5n+4)` -/

/-- `p(5·2 + 4) = p(14) = 135 = 27·5`. -/
theorem partition_5n_plus_4_mod_5_n_two :
    partitionCount (5 * 2 + 4) % 5 = 0 := by
  rw [show (5 * 2 + 4 : ℕ) = 14 from rfl,
      QseriesFormalization.Ch01.partitionCount_fourteen]

/-- `p(5·3 + 4) = p(19) = 490 = 98·5`. -/
theorem partition_5n_plus_4_mod_5_n_three :
    partitionCount (5 * 3 + 4) % 5 = 0 := by
  rw [show (5 * 3 + 4 : ℕ) = 19 from rfl,
      QseriesFormalization.Ch01.partitionCount_nineteen]

/-- `p(5·4 + 4) = p(24) = 1575 = 315·5`. -/
theorem partition_5n_plus_4_mod_5_n_four :
    partitionCount (5 * 4 + 4) % 5 = 0 := by
  rw [show (5 * 4 + 4 : ℕ) = 24 from rfl,
      QseriesFormalization.Ch01.partitionCount_twentyfour]

/-- `p(5·5 + 4) = p(29) = 4565 = 913·5`. -/
theorem partition_5n_plus_4_mod_5_n_five :
    partitionCount (5 * 5 + 4) % 5 = 0 := by
  rw [show (5 * 5 + 4 : ℕ) = 29 from rfl,
      QseriesFormalization.Ch01.partitionCount_twentynine]

/-- `p(5·6 + 4) = p(34) = 12310 = 2462·5`. -/
theorem partition_5n_plus_4_mod_5_n_six :
    partitionCount (5 * 6 + 4) % 5 = 0 := by
  rw [show (5 * 6 + 4 : ℕ) = 34 from rfl,
      QseriesFormalization.Ch01.partitionCount_thirtyfour]

/-- `p(5·7 + 4) = p(39) = 31185 = 6237·5`. -/
theorem partition_5n_plus_4_mod_5_n_seven :
    partitionCount (5 * 7 + 4) % 5 = 0 := by
  rw [show (5 * 7 + 4 : ℕ) = 39 from rfl,
      QseriesFormalization.Ch01.partitionCount_thirtynine]

/-- `p(5·8 + 4) = p(44) = 75175 = 15035·5`. -/
theorem partition_5n_plus_4_mod_5_n_eight :
    partitionCount (5 * 8 + 4) % 5 = 0 := by
  rw [show (5 * 8 + 4 : ℕ) = 44 from rfl,
      QseriesFormalization.Ch01.partitionCount_fortyfour]

/-- `p(5·9 + 4) = p(49) = 173525 = 34705·5`. -/
theorem partition_5n_plus_4_mod_5_n_nine :
    partitionCount (5 * 9 + 4) % 5 = 0 := by
  rw [show (5 * 9 + 4 : ℕ) = 49 from rfl,
      QseriesFormalization.Ch01.partitionCount_fortynine]

/-- `p(5·10 + 4) = p(54) = 386155 = 77231·5`. -/
theorem partition_5n_plus_4_mod_5_n_ten :
    partitionCount (5 * 10 + 4) % 5 = 0 := by
  rw [show (5 * 10 + 4 : ℕ) = 54 from rfl,
      QseriesFormalization.Ch01.partitionCount_fiftyfour]

/-! ## Mod-7 family: `7 ∣ p(7n+5)` -/

/-- `p(7·1 + 5) = p(12) = 77 = 11·7`. -/
theorem partition_7n_plus_5_mod_7_n_one :
    partitionCount (7 * 1 + 5) % 7 = 0 := by
  rw [show (7 * 1 + 5 : ℕ) = 12 from rfl,
      QseriesFormalization.Ch01.partitionCount_twelve]

/-- `p(7·2 + 5) = p(19) = 490 = 70·7`. -/
theorem partition_7n_plus_5_mod_7_n_two :
    partitionCount (7 * 2 + 5) % 7 = 0 := by
  rw [show (7 * 2 + 5 : ℕ) = 19 from rfl,
      QseriesFormalization.Ch01.partitionCount_nineteen]

/-- `p(7·3 + 5) = p(26) = 2436 = 348·7`. -/
theorem partition_7n_plus_5_mod_7_n_three :
    partitionCount (7 * 3 + 5) % 7 = 0 := by
  rw [show (7 * 3 + 5 : ℕ) = 26 from rfl,
      QseriesFormalization.Ch01.partitionCount_twentysix]

/-- `p(7·4 + 5) = p(33) = 10143 = 1449·7`. -/
theorem partition_7n_plus_5_mod_7_n_four :
    partitionCount (7 * 4 + 5) % 7 = 0 := by
  rw [show (7 * 4 + 5 : ℕ) = 33 from rfl,
      QseriesFormalization.Ch01.partitionCount_thirtythree]

/-- `p(7·5 + 5) = p(40) = 37338 = 5334·7`. -/
theorem partition_7n_plus_5_mod_7_n_five :
    partitionCount (7 * 5 + 5) % 7 = 0 := by
  rw [show (7 * 5 + 5 : ℕ) = 40 from rfl,
      QseriesFormalization.Ch01.partitionCount_forty]

/-- `p(7·6 + 5) = p(47) = 124754 = 17822·7`. -/
theorem partition_7n_plus_5_mod_7_n_six :
    partitionCount (7 * 6 + 5) % 7 = 0 := by
  rw [show (7 * 6 + 5 : ℕ) = 47 from rfl,
      QseriesFormalization.Ch01.partitionCount_fortyseven]

/-- `p(7·7 + 5) = p(54) = 386155 = 55165·7`. -/
theorem partition_7n_plus_5_mod_7_n_seven :
    partitionCount (7 * 7 + 5) % 7 = 0 := by
  rw [show (7 * 7 + 5 : ℕ) = 54 from rfl,
      QseriesFormalization.Ch01.partitionCount_fiftyfour]

/-! ## Mod-11 family: `11 ∣ p(11n+6)` -/

/-- `p(11·1 + 6) = p(17) = 297 = 27·11`. -/
theorem partition_11n_plus_6_mod_11_n_one :
    partitionCount (11 * 1 + 6) % 11 = 0 := by
  rw [show (11 * 1 + 6 : ℕ) = 17 from rfl,
      QseriesFormalization.Ch01.partitionCount_seventeen]

/-- `p(11·2 + 6) = p(28) = 3718 = 338·11`. -/
theorem partition_11n_plus_6_mod_11_n_two :
    partitionCount (11 * 2 + 6) % 11 = 0 := by
  rw [show (11 * 2 + 6 : ℕ) = 28 from rfl,
      QseriesFormalization.Ch01.partitionCount_twentyeight]

/-- `p(11·3 + 6) = p(39) = 31185 = 2835·11`. -/
theorem partition_11n_plus_6_mod_11_n_three :
    partitionCount (11 * 3 + 6) % 11 = 0 := by
  rw [show (11 * 3 + 6 : ℕ) = 39 from rfl,
      QseriesFormalization.Ch01.partitionCount_thirtynine]

/-- `p(11·4 + 6) = p(50) = 204226 = 18566·11`. -/
theorem partition_11n_plus_6_mod_11_n_four :
    partitionCount (11 * 4 + 6) % 11 = 0 := by
  rw [show (11 * 4 + 6 : ℕ) = 50 from rfl,
      QseriesFormalization.Ch01.partitionCount_fifty]

end Ch17
end PartIV
end QseriesFormalization
