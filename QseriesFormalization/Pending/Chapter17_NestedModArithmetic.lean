import QseriesFormalization.Basic

/-!
# Chapter 17 nested progression modular arithmetic

Small arithmetic lemmas for the nested residue classes used in the
Ramanujan partition congruence corollaries.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch17NestedModArithmetic

/-- Decompose a natural number in residue class `4 mod 5`. -/
theorem eq_five_mul_div_plus_four_of_mod_eq_four {m : ℕ} (hm : m % 5 = 4) :
    m = 5 * (m / 5) + 4 := by
  have h := (Nat.mod_add_div m 5).symm
  omega

/-- Decompose a natural number in residue class `5 mod 7`. -/
theorem eq_seven_mul_div_plus_five_of_mod_eq_five {m : ℕ} (hm : m % 7 = 5) :
    m = 7 * (m / 7) + 5 := by
  have h := (Nat.mod_add_div m 7).symm
  omega

/-- Decompose a natural number in residue class `6 mod 11`. -/
theorem eq_eleven_mul_div_plus_six_of_mod_eq_six {m : ℕ} (hm : m % 11 = 6) :
    m = 11 * (m / 11) + 6 := by
  have h := (Nat.mod_add_div m 11).symm
  omega

/-- Decompose a `4 mod 5` index into the one-level nested mod-5 shape. -/
theorem eq_25_mul_div_plus_5_mul_mod_plus_four_of_mod_eq_four
    {m : ℕ} (hm : m % 5 = 4) :
    m = 25 * ((m / 5) / 5) + 5 * ((m / 5) % 5) + 4 := by
  have h0 := eq_five_mul_div_plus_four_of_mod_eq_four hm
  have h1 := (Nat.mod_add_div (m / 5) 5).symm
  omega

/-- Decompose a `5 mod 7` index into the one-level nested mod-7 shape. -/
theorem eq_49_mul_div_plus_7_mul_mod_plus_five_of_mod_eq_five
    {m : ℕ} (hm : m % 7 = 5) :
    m = 49 * ((m / 7) / 7) + 7 * ((m / 7) % 7) + 5 := by
  have h0 := eq_seven_mul_div_plus_five_of_mod_eq_five hm
  have h1 := (Nat.mod_add_div (m / 7) 7).symm
  omega

/-- Decompose a `6 mod 11` index into the one-level nested mod-11 shape. -/
theorem eq_121_mul_div_plus_11_mul_mod_plus_six_of_mod_eq_six
    {m : ℕ} (hm : m % 11 = 6) :
    m = 121 * ((m / 11) / 11) + 11 * ((m / 11) % 11) + 6 := by
  have h0 := eq_eleven_mul_div_plus_six_of_mod_eq_six hm
  have h1 := (Nat.mod_add_div (m / 11) 11).symm
  omega

/-- Decompose a `4 mod 5` index into the two-level nested mod-5 shape. -/
theorem eq_125_mul_div_plus_25_mul_mod_plus_5_mul_mod_plus_four_of_mod_eq_four
    {m : ℕ} (hm : m % 5 = 4) :
    m = 125 * (((m / 5) / 5) / 5) +
      25 * (((m / 5) / 5) % 5) + 5 * ((m / 5) % 5) + 4 := by
  have h0 := eq_five_mul_div_plus_four_of_mod_eq_four hm
  have h1 := (Nat.mod_add_div (m / 5) 5).symm
  have h2 := (Nat.mod_add_div ((m / 5) / 5) 5).symm
  omega

/-- Decompose a `5 mod 7` index into the two-level nested mod-7 shape. -/
theorem eq_343_mul_div_plus_49_mul_mod_plus_7_mul_mod_plus_five_of_mod_eq_five
    {m : ℕ} (hm : m % 7 = 5) :
    m = 343 * (((m / 7) / 7) / 7) +
      49 * (((m / 7) / 7) % 7) + 7 * ((m / 7) % 7) + 5 := by
  have h0 := eq_seven_mul_div_plus_five_of_mod_eq_five hm
  have h1 := (Nat.mod_add_div (m / 7) 7).symm
  have h2 := (Nat.mod_add_div ((m / 7) / 7) 7).symm
  omega

/-- Decompose a `6 mod 11` index into the two-level nested mod-11 shape. -/
theorem eq_1331_mul_div_plus_121_mul_mod_plus_11_mul_mod_plus_six_of_mod_eq_six
    {m : ℕ} (hm : m % 11 = 6) :
    m = 1331 * (((m / 11) / 11) / 11) +
      121 * (((m / 11) / 11) % 11) + 11 * ((m / 11) % 11) + 6 := by
  have h0 := eq_eleven_mul_div_plus_six_of_mod_eq_six hm
  have h1 := (Nat.mod_add_div (m / 11) 11).symm
  have h2 := (Nat.mod_add_div ((m / 11) / 11) 11).symm
  omega

/-- Decompose a `4 mod 5` index into the three-level nested mod-5 shape. -/
theorem eq_625_mul_div_plus_125_mul_mod_plus_25_mul_mod_plus_5_mul_mod_plus_four_of_mod_eq_four
    {m : ℕ} (hm : m % 5 = 4) :
    m = 625 * ((((m / 5) / 5) / 5) / 5) +
      125 * ((((m / 5) / 5) / 5) % 5) +
      25 * (((m / 5) / 5) % 5) + 5 * ((m / 5) % 5) + 4 := by
  have h0 := eq_five_mul_div_plus_four_of_mod_eq_four hm
  have h1 := (Nat.mod_add_div (m / 5) 5).symm
  have h2 := (Nat.mod_add_div ((m / 5) / 5) 5).symm
  have h3 := (Nat.mod_add_div (((m / 5) / 5) / 5) 5).symm
  omega

/-- Decompose a `5 mod 7` index into the three-level nested mod-7 shape. -/
theorem eq_2401_mul_div_plus_343_mul_mod_plus_49_mul_mod_plus_7_mul_mod_plus_five_of_mod_eq_five
    {m : ℕ} (hm : m % 7 = 5) :
    m = 2401 * ((((m / 7) / 7) / 7) / 7) +
      343 * ((((m / 7) / 7) / 7) % 7) +
      49 * (((m / 7) / 7) % 7) + 7 * ((m / 7) % 7) + 5 := by
  have h0 := eq_seven_mul_div_plus_five_of_mod_eq_five hm
  have h1 := (Nat.mod_add_div (m / 7) 7).symm
  have h2 := (Nat.mod_add_div ((m / 7) / 7) 7).symm
  have h3 := (Nat.mod_add_div (((m / 7) / 7) / 7) 7).symm
  omega

/-- Decompose a `6 mod 11` index into the three-level nested mod-11 shape. -/
theorem eq_14641_mul_div_plus_1331_mul_mod_plus_121_mul_mod_plus_11_mul_mod_plus_six_of_mod_eq_six
    {m : ℕ} (hm : m % 11 = 6) :
    m = 14641 * ((((m / 11) / 11) / 11) / 11) +
      1331 * ((((m / 11) / 11) / 11) % 11) +
      121 * (((m / 11) / 11) % 11) + 11 * ((m / 11) % 11) + 6 := by
  have h0 := eq_eleven_mul_div_plus_six_of_mod_eq_six hm
  have h1 := (Nat.mod_add_div (m / 11) 11).symm
  have h2 := (Nat.mod_add_div ((m / 11) / 11) 11).symm
  have h3 := (Nat.mod_add_div (((m / 11) / 11) / 11) 11).symm
  omega

/-- Decompose a `4 mod 5` index into the four-level nested mod-5 shape. -/
theorem eq_3125_mul_div_plus_625_mul_mod_plus_125_mul_mod_plus_25_mul_mod_plus_5_mul_mod_plus_four_of_mod_eq_four
    {m : ℕ} (hm : m % 5 = 4) :
    m = 3125 * (((((m / 5) / 5) / 5) / 5) / 5) +
      625 * (((((m / 5) / 5) / 5) / 5) % 5) +
      125 * ((((m / 5) / 5) / 5) % 5) +
      25 * (((m / 5) / 5) % 5) + 5 * ((m / 5) % 5) + 4 := by
  have h0 := eq_five_mul_div_plus_four_of_mod_eq_four hm
  have h1 := (Nat.mod_add_div (m / 5) 5).symm
  have h2 := (Nat.mod_add_div ((m / 5) / 5) 5).symm
  have h3 := (Nat.mod_add_div (((m / 5) / 5) / 5) 5).symm
  have h4 := (Nat.mod_add_div ((((m / 5) / 5) / 5) / 5) 5).symm
  omega

/-- Decompose a `5 mod 7` index into the four-level nested mod-7 shape. -/
theorem eq_16807_mul_div_plus_2401_mul_mod_plus_343_mul_mod_plus_49_mul_mod_plus_7_mul_mod_plus_five_of_mod_eq_five
    {m : ℕ} (hm : m % 7 = 5) :
    m = 16807 * (((((m / 7) / 7) / 7) / 7) / 7) +
      2401 * (((((m / 7) / 7) / 7) / 7) % 7) +
      343 * ((((m / 7) / 7) / 7) % 7) +
      49 * (((m / 7) / 7) % 7) + 7 * ((m / 7) % 7) + 5 := by
  have h0 := eq_seven_mul_div_plus_five_of_mod_eq_five hm
  have h1 := (Nat.mod_add_div (m / 7) 7).symm
  have h2 := (Nat.mod_add_div ((m / 7) / 7) 7).symm
  have h3 := (Nat.mod_add_div (((m / 7) / 7) / 7) 7).symm
  have h4 := (Nat.mod_add_div ((((m / 7) / 7) / 7) / 7) 7).symm
  omega

/-- Decompose a `6 mod 11` index into the four-level nested mod-11 shape. -/
theorem eq_161051_mul_div_plus_14641_mul_mod_plus_1331_mul_mod_plus_121_mul_mod_plus_11_mul_mod_plus_six_of_mod_eq_six
    {m : ℕ} (hm : m % 11 = 6) :
    m = 161051 * (((((m / 11) / 11) / 11) / 11) / 11) +
      14641 * (((((m / 11) / 11) / 11) / 11) % 11) +
      1331 * ((((m / 11) / 11) / 11) % 11) +
      121 * (((m / 11) / 11) % 11) + 11 * ((m / 11) % 11) + 6 := by
  have h0 := eq_eleven_mul_div_plus_six_of_mod_eq_six hm
  have h1 := (Nat.mod_add_div (m / 11) 11).symm
  have h2 := (Nat.mod_add_div ((m / 11) / 11) 11).symm
  have h3 := (Nat.mod_add_div (((m / 11) / 11) / 11) 11).symm
  have h4 := (Nat.mod_add_div ((((m / 11) / 11) / 11) / 11) 11).symm
  omega

/-- Bounded one-level nested representation of a `4 mod 5` index. -/
theorem exists_one_level_mod5_of_mod_eq_four {m : ℕ} (hm : m % 5 = 4) :
    ∃ n a, a < 5 ∧ m = 25 * n + 5 * a + 4 := by
  refine ⟨(m / 5) / 5, (m / 5) % 5, Nat.mod_lt _ (by decide), ?_⟩
  exact eq_25_mul_div_plus_5_mul_mod_plus_four_of_mod_eq_four hm

/-- Bounded one-level nested representation of a `5 mod 7` index. -/
theorem exists_one_level_mod7_of_mod_eq_five {m : ℕ} (hm : m % 7 = 5) :
    ∃ n a, a < 7 ∧ m = 49 * n + 7 * a + 5 := by
  refine ⟨(m / 7) / 7, (m / 7) % 7, Nat.mod_lt _ (by decide), ?_⟩
  exact eq_49_mul_div_plus_7_mul_mod_plus_five_of_mod_eq_five hm

/-- Bounded one-level nested representation of a `6 mod 11` index. -/
theorem exists_one_level_mod11_of_mod_eq_six {m : ℕ} (hm : m % 11 = 6) :
    ∃ n a, a < 11 ∧ m = 121 * n + 11 * a + 6 := by
  refine ⟨(m / 11) / 11, (m / 11) % 11, Nat.mod_lt _ (by decide), ?_⟩
  exact eq_121_mul_div_plus_11_mul_mod_plus_six_of_mod_eq_six hm

/-- Bounded two-level nested representation of a `4 mod 5` index. -/
theorem exists_two_level_mod5_of_mod_eq_four {m : ℕ} (hm : m % 5 = 4) :
    ∃ n a b, a < 5 ∧ b < 5 ∧ m = 125 * n + 25 * a + 5 * b + 4 := by
  refine ⟨((m / 5) / 5) / 5, ((m / 5) / 5) % 5, (m / 5) % 5,
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), ?_⟩
  exact eq_125_mul_div_plus_25_mul_mod_plus_5_mul_mod_plus_four_of_mod_eq_four hm

/-- Bounded two-level nested representation of a `5 mod 7` index. -/
theorem exists_two_level_mod7_of_mod_eq_five {m : ℕ} (hm : m % 7 = 5) :
    ∃ n a b, a < 7 ∧ b < 7 ∧ m = 343 * n + 49 * a + 7 * b + 5 := by
  refine ⟨((m / 7) / 7) / 7, ((m / 7) / 7) % 7, (m / 7) % 7,
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), ?_⟩
  exact eq_343_mul_div_plus_49_mul_mod_plus_7_mul_mod_plus_five_of_mod_eq_five hm

/-- Bounded two-level nested representation of a `6 mod 11` index. -/
theorem exists_two_level_mod11_of_mod_eq_six {m : ℕ} (hm : m % 11 = 6) :
    ∃ n a b, a < 11 ∧ b < 11 ∧ m = 1331 * n + 121 * a + 11 * b + 6 := by
  refine ⟨((m / 11) / 11) / 11, ((m / 11) / 11) % 11, (m / 11) % 11,
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), ?_⟩
  exact eq_1331_mul_div_plus_121_mul_mod_plus_11_mul_mod_plus_six_of_mod_eq_six hm

/-- Bounded three-level nested representation of a `4 mod 5` index. -/
theorem exists_three_level_mod5_of_mod_eq_four {m : ℕ} (hm : m % 5 = 4) :
    ∃ n a b c, a < 5 ∧ b < 5 ∧ c < 5 ∧
      m = 625 * n + 125 * a + 25 * b + 5 * c + 4 := by
  refine ⟨(((m / 5) / 5) / 5) / 5, (((m / 5) / 5) / 5) % 5,
    ((m / 5) / 5) % 5, (m / 5) % 5,
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), ?_⟩
  exact eq_625_mul_div_plus_125_mul_mod_plus_25_mul_mod_plus_5_mul_mod_plus_four_of_mod_eq_four hm

/-- Bounded three-level nested representation of a `5 mod 7` index. -/
theorem exists_three_level_mod7_of_mod_eq_five {m : ℕ} (hm : m % 7 = 5) :
    ∃ n a b c, a < 7 ∧ b < 7 ∧ c < 7 ∧
      m = 2401 * n + 343 * a + 49 * b + 7 * c + 5 := by
  refine ⟨(((m / 7) / 7) / 7) / 7, (((m / 7) / 7) / 7) % 7,
    ((m / 7) / 7) % 7, (m / 7) % 7,
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), ?_⟩
  exact eq_2401_mul_div_plus_343_mul_mod_plus_49_mul_mod_plus_7_mul_mod_plus_five_of_mod_eq_five hm

/-- Bounded three-level nested representation of a `6 mod 11` index. -/
theorem exists_three_level_mod11_of_mod_eq_six {m : ℕ} (hm : m % 11 = 6) :
    ∃ n a b c, a < 11 ∧ b < 11 ∧ c < 11 ∧
      m = 14641 * n + 1331 * a + 121 * b + 11 * c + 6 := by
  refine ⟨(((m / 11) / 11) / 11) / 11, (((m / 11) / 11) / 11) % 11,
    ((m / 11) / 11) % 11, (m / 11) % 11,
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), ?_⟩
  exact eq_14641_mul_div_plus_1331_mul_mod_plus_121_mul_mod_plus_11_mul_mod_plus_six_of_mod_eq_six hm

/-- Bounded four-level nested representation of a `4 mod 5` index. -/
theorem exists_four_level_mod5_of_mod_eq_four {m : ℕ} (hm : m % 5 = 4) :
    ∃ n a b c d, a < 5 ∧ b < 5 ∧ c < 5 ∧ d < 5 ∧
      m = 3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4 := by
  refine ⟨((((m / 5) / 5) / 5) / 5) / 5, ((((m / 5) / 5) / 5) / 5) % 5,
    (((m / 5) / 5) / 5) % 5, ((m / 5) / 5) % 5, (m / 5) % 5,
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide), ?_⟩
  exact eq_3125_mul_div_plus_625_mul_mod_plus_125_mul_mod_plus_25_mul_mod_plus_5_mul_mod_plus_four_of_mod_eq_four hm

/-- Bounded four-level nested representation of a `5 mod 7` index. -/
theorem exists_four_level_mod7_of_mod_eq_five {m : ℕ} (hm : m % 7 = 5) :
    ∃ n a b c d, a < 7 ∧ b < 7 ∧ c < 7 ∧ d < 7 ∧
      m = 16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5 := by
  refine ⟨((((m / 7) / 7) / 7) / 7) / 7, ((((m / 7) / 7) / 7) / 7) % 7,
    (((m / 7) / 7) / 7) % 7, ((m / 7) / 7) % 7, (m / 7) % 7,
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide), ?_⟩
  exact eq_16807_mul_div_plus_2401_mul_mod_plus_343_mul_mod_plus_49_mul_mod_plus_7_mul_mod_plus_five_of_mod_eq_five hm

/-- Bounded four-level nested representation of a `6 mod 11` index. -/
theorem exists_four_level_mod11_of_mod_eq_six {m : ℕ} (hm : m % 11 = 6) :
    ∃ n a b c d, a < 11 ∧ b < 11 ∧ c < 11 ∧ d < 11 ∧
      m = 161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6 := by
  refine ⟨((((m / 11) / 11) / 11) / 11) / 11,
    ((((m / 11) / 11) / 11) / 11) % 11, (((m / 11) / 11) / 11) % 11,
    ((m / 11) / 11) % 11, (m / 11) % 11,
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide), ?_⟩
  exact eq_161051_mul_div_plus_14641_mul_mod_plus_1331_mul_mod_plus_121_mul_mod_plus_11_mul_mod_plus_six_of_mod_eq_six hm

/-- The base mod-5 Ramanujan progression is in residue class `4`. -/
theorem mod_5n_plus_4_eq_four (n : ℕ) :
    (5 * n + 4) % 5 = 4 := by
  omega

/-- The base mod-7 Ramanujan progression is in residue class `5`. -/
theorem mod_7n_plus_5_eq_five (n : ℕ) :
    (7 * n + 5) % 7 = 5 := by
  omega

/-- The base mod-11 Ramanujan progression is in residue class `6`. -/
theorem mod_11n_plus_6_eq_six (n : ℕ) :
    (11 * n + 6) % 11 = 6 := by
  omega

/-- The one-level mod-5 nested progression remains in residue class `4`. -/
theorem mod_25n_plus_5a_plus_4_eq_four (n a : ℕ) :
    (25 * n + 5 * a + 4) % 5 = 4 := by
  omega

/-- The two-level mod-5 nested progression remains in residue class `4`. -/
theorem mod_125n_plus_25a_plus_5b_plus_4_eq_four (n a b : ℕ) :
    (125 * n + 25 * a + 5 * b + 4) % 5 = 4 := by
  omega

/-- The concrete one-level mod-5 representative remains in residue class `4`. -/
theorem mod_25n_plus_24_eq_four (n : ℕ) :
    (25 * n + 24) % 5 = 4 := by
  omega

/-- The concrete two-level mod-5 representative remains in residue class `4`. -/
theorem mod_125n_plus_124_eq_four (n : ℕ) :
    (125 * n + 124) % 5 = 4 := by
  omega

/-- The one-level mod-7 nested progression remains in residue class `5`. -/
theorem mod_49n_plus_7a_plus_5_eq_five (n a : ℕ) :
    (49 * n + 7 * a + 5) % 7 = 5 := by
  omega

/-- The two-level mod-7 nested progression remains in residue class `5`. -/
theorem mod_343n_plus_49a_plus_7b_plus_5_eq_five (n a b : ℕ) :
    (343 * n + 49 * a + 7 * b + 5) % 7 = 5 := by
  omega

/-- The concrete one-level mod-7 representative remains in residue class `5`. -/
theorem mod_49n_plus_47_eq_five (n : ℕ) :
    (49 * n + 47) % 7 = 5 := by
  omega

/-- The concrete two-level mod-7 representative remains in residue class `5`. -/
theorem mod_343n_plus_341_eq_five (n : ℕ) :
    (343 * n + 341) % 7 = 5 := by
  omega

/-- The one-level mod-11 nested progression remains in residue class `6`. -/
theorem mod_121n_plus_11a_plus_6_eq_six (n a : ℕ) :
    (121 * n + 11 * a + 6) % 11 = 6 := by
  omega

/-- The two-level mod-11 nested progression remains in residue class `6`. -/
theorem mod_1331n_plus_121a_plus_11b_plus_6_eq_six (n a b : ℕ) :
    (1331 * n + 121 * a + 11 * b + 6) % 11 = 6 := by
  omega

/-- The three-level mod-5 nested progression remains in residue class `4`. -/
theorem mod_625n_plus_125a_plus_25b_plus_5c_plus_4_eq_four
    (n a b c : ℕ) :
    (625 * n + 125 * a + 25 * b + 5 * c + 4) % 5 = 4 := by
  omega

/-- The four-level mod-5 nested progression remains in residue class `4`. -/
theorem mod_3125n_plus_625a_plus_125b_plus_25c_plus_5d_plus_4_eq_four
    (n a b c d : ℕ) :
    (3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4) % 5 = 4 := by
  omega

/-- The three-level mod-7 nested progression remains in residue class `5`. -/
theorem mod_2401n_plus_343a_plus_49b_plus_7c_plus_5_eq_five
    (n a b c : ℕ) :
    (2401 * n + 343 * a + 49 * b + 7 * c + 5) % 7 = 5 := by
  omega

/-- The four-level mod-7 nested progression remains in residue class `5`. -/
theorem mod_16807n_plus_2401a_plus_343b_plus_49c_plus_7d_plus_5_eq_five
    (n a b c d : ℕ) :
    (16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5) % 7 = 5 := by
  omega

/-- The three-level mod-11 nested progression remains in residue class `6`. -/
theorem mod_14641n_plus_1331a_plus_121b_plus_11c_plus_6_eq_six
    (n a b c : ℕ) :
    (14641 * n + 1331 * a + 121 * b + 11 * c + 6) % 11 = 6 := by
  omega

/-- The four-level mod-11 nested progression remains in residue class `6`. -/
theorem mod_161051n_plus_14641a_plus_1331b_plus_121c_plus_11d_plus_6_eq_six
    (n a b c d : ℕ) :
    (161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6) % 11 = 6 := by
  omega

/-- A natural number is `4 mod 5` iff it has a bounded one-level mod-5
nested representation. -/
theorem mod_eq_four_iff_exists_one_level_mod5 (m : ℕ) :
    m % 5 = 4 ↔ ∃ n a, a < 5 ∧ m = 25 * n + 5 * a + 4 := by
  constructor
  · exact exists_one_level_mod5_of_mod_eq_four
  · rintro ⟨n, a, ha, rfl⟩
    exact mod_25n_plus_5a_plus_4_eq_four n a

/-- A natural number is `5 mod 7` iff it has a bounded one-level mod-7
nested representation. -/
theorem mod_eq_five_iff_exists_one_level_mod7 (m : ℕ) :
    m % 7 = 5 ↔ ∃ n a, a < 7 ∧ m = 49 * n + 7 * a + 5 := by
  constructor
  · exact exists_one_level_mod7_of_mod_eq_five
  · rintro ⟨n, a, ha, rfl⟩
    exact mod_49n_plus_7a_plus_5_eq_five n a

/-- A natural number is `6 mod 11` iff it has a bounded one-level mod-11
nested representation. -/
theorem mod_eq_six_iff_exists_one_level_mod11 (m : ℕ) :
    m % 11 = 6 ↔ ∃ n a, a < 11 ∧ m = 121 * n + 11 * a + 6 := by
  constructor
  · exact exists_one_level_mod11_of_mod_eq_six
  · rintro ⟨n, a, ha, rfl⟩
    exact mod_121n_plus_11a_plus_6_eq_six n a

/-- A natural number is `4 mod 5` iff it has a bounded two-level mod-5
nested representation. -/
theorem mod_eq_four_iff_exists_two_level_mod5 (m : ℕ) :
    m % 5 = 4 ↔
      ∃ n a b, a < 5 ∧ b < 5 ∧ m = 125 * n + 25 * a + 5 * b + 4 := by
  constructor
  · exact exists_two_level_mod5_of_mod_eq_four
  · rintro ⟨n, a, b, ha, hb, rfl⟩
    exact mod_125n_plus_25a_plus_5b_plus_4_eq_four n a b

/-- A natural number is `5 mod 7` iff it has a bounded two-level mod-7
nested representation. -/
theorem mod_eq_five_iff_exists_two_level_mod7 (m : ℕ) :
    m % 7 = 5 ↔
      ∃ n a b, a < 7 ∧ b < 7 ∧ m = 343 * n + 49 * a + 7 * b + 5 := by
  constructor
  · exact exists_two_level_mod7_of_mod_eq_five
  · rintro ⟨n, a, b, ha, hb, rfl⟩
    exact mod_343n_plus_49a_plus_7b_plus_5_eq_five n a b

/-- A natural number is `6 mod 11` iff it has a bounded two-level mod-11
nested representation. -/
theorem mod_eq_six_iff_exists_two_level_mod11 (m : ℕ) :
    m % 11 = 6 ↔
      ∃ n a b, a < 11 ∧ b < 11 ∧ m = 1331 * n + 121 * a + 11 * b + 6 := by
  constructor
  · exact exists_two_level_mod11_of_mod_eq_six
  · rintro ⟨n, a, b, ha, hb, rfl⟩
    exact mod_1331n_plus_121a_plus_11b_plus_6_eq_six n a b

/-- A natural number is `4 mod 5` iff it has a bounded three-level mod-5
nested representation. -/
theorem mod_eq_four_iff_exists_three_level_mod5 (m : ℕ) :
    m % 5 = 4 ↔
      ∃ n a b c, a < 5 ∧ b < 5 ∧ c < 5 ∧
        m = 625 * n + 125 * a + 25 * b + 5 * c + 4 := by
  constructor
  · exact exists_three_level_mod5_of_mod_eq_four
  · rintro ⟨n, a, b, c, ha, hb, hc, rfl⟩
    exact mod_625n_plus_125a_plus_25b_plus_5c_plus_4_eq_four n a b c

/-- A natural number is `5 mod 7` iff it has a bounded three-level mod-7
nested representation. -/
theorem mod_eq_five_iff_exists_three_level_mod7 (m : ℕ) :
    m % 7 = 5 ↔
      ∃ n a b c, a < 7 ∧ b < 7 ∧ c < 7 ∧
        m = 2401 * n + 343 * a + 49 * b + 7 * c + 5 := by
  constructor
  · exact exists_three_level_mod7_of_mod_eq_five
  · rintro ⟨n, a, b, c, ha, hb, hc, rfl⟩
    exact mod_2401n_plus_343a_plus_49b_plus_7c_plus_5_eq_five n a b c

/-- A natural number is `6 mod 11` iff it has a bounded three-level mod-11
nested representation. -/
theorem mod_eq_six_iff_exists_three_level_mod11 (m : ℕ) :
    m % 11 = 6 ↔
      ∃ n a b c, a < 11 ∧ b < 11 ∧ c < 11 ∧
        m = 14641 * n + 1331 * a + 121 * b + 11 * c + 6 := by
  constructor
  · exact exists_three_level_mod11_of_mod_eq_six
  · rintro ⟨n, a, b, c, ha, hb, hc, rfl⟩
    exact mod_14641n_plus_1331a_plus_121b_plus_11c_plus_6_eq_six n a b c

/-- A natural number is `4 mod 5` iff it has a bounded four-level mod-5
nested representation. -/
theorem mod_eq_four_iff_exists_four_level_mod5 (m : ℕ) :
    m % 5 = 4 ↔
      ∃ n a b c d, a < 5 ∧ b < 5 ∧ c < 5 ∧ d < 5 ∧
        m = 3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4 := by
  constructor
  · exact exists_four_level_mod5_of_mod_eq_four
  · rintro ⟨n, a, b, c, d, ha, hb, hc, hd, rfl⟩
    exact mod_3125n_plus_625a_plus_125b_plus_25c_plus_5d_plus_4_eq_four n a b c d

/-- A natural number is `5 mod 7` iff it has a bounded four-level mod-7
nested representation. -/
theorem mod_eq_five_iff_exists_four_level_mod7 (m : ℕ) :
    m % 7 = 5 ↔
      ∃ n a b c d, a < 7 ∧ b < 7 ∧ c < 7 ∧ d < 7 ∧
        m = 16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5 := by
  constructor
  · exact exists_four_level_mod7_of_mod_eq_five
  · rintro ⟨n, a, b, c, d, ha, hb, hc, hd, rfl⟩
    exact mod_16807n_plus_2401a_plus_343b_plus_49c_plus_7d_plus_5_eq_five n a b c d

/-- A natural number is `6 mod 11` iff it has a bounded four-level mod-11
nested representation. -/
theorem mod_eq_six_iff_exists_four_level_mod11 (m : ℕ) :
    m % 11 = 6 ↔
      ∃ n a b c d, a < 11 ∧ b < 11 ∧ c < 11 ∧ d < 11 ∧
        m = 161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6 := by
  constructor
  · exact exists_four_level_mod11_of_mod_eq_six
  · rintro ⟨n, a, b, c, d, ha, hb, hc, hd, rfl⟩
    exact mod_161051n_plus_14641a_plus_1331b_plus_121c_plus_11d_plus_6_eq_six n a b c d

/-- One-level bounded nested representation characterizations for the three
classical Ramanujan residue classes. -/
theorem one_level_nested_representation_iff_facts :
    (∀ m, m % 5 = 4 ↔ ∃ n a, a < 5 ∧ m = 25 * n + 5 * a + 4) ∧
      (∀ m, m % 7 = 5 ↔ ∃ n a, a < 7 ∧ m = 49 * n + 7 * a + 5) ∧
      (∀ m, m % 11 = 6 ↔ ∃ n a, a < 11 ∧ m = 121 * n + 11 * a + 6) := by
  exact ⟨mod_eq_four_iff_exists_one_level_mod5,
    mod_eq_five_iff_exists_one_level_mod7,
    mod_eq_six_iff_exists_one_level_mod11⟩

/-- Two-level bounded nested representation characterizations for the three
classical Ramanujan residue classes. -/
theorem two_level_nested_representation_iff_facts :
    (∀ m, m % 5 = 4 ↔
      ∃ n a b, a < 5 ∧ b < 5 ∧ m = 125 * n + 25 * a + 5 * b + 4) ∧
      (∀ m, m % 7 = 5 ↔
        ∃ n a b, a < 7 ∧ b < 7 ∧ m = 343 * n + 49 * a + 7 * b + 5) ∧
      (∀ m, m % 11 = 6 ↔
        ∃ n a b, a < 11 ∧ b < 11 ∧ m = 1331 * n + 121 * a + 11 * b + 6) := by
  exact ⟨mod_eq_four_iff_exists_two_level_mod5,
    mod_eq_five_iff_exists_two_level_mod7,
    mod_eq_six_iff_exists_two_level_mod11⟩

/-- Three-level bounded nested representation characterizations for the three
classical Ramanujan residue classes. -/
theorem three_level_nested_representation_iff_facts :
    (∀ m, m % 5 = 4 ↔
      ∃ n a b c, a < 5 ∧ b < 5 ∧ c < 5 ∧
        m = 625 * n + 125 * a + 25 * b + 5 * c + 4) ∧
      (∀ m, m % 7 = 5 ↔
        ∃ n a b c, a < 7 ∧ b < 7 ∧ c < 7 ∧
          m = 2401 * n + 343 * a + 49 * b + 7 * c + 5) ∧
      (∀ m, m % 11 = 6 ↔
        ∃ n a b c, a < 11 ∧ b < 11 ∧ c < 11 ∧
          m = 14641 * n + 1331 * a + 121 * b + 11 * c + 6) := by
  exact ⟨mod_eq_four_iff_exists_three_level_mod5,
    mod_eq_five_iff_exists_three_level_mod7,
    mod_eq_six_iff_exists_three_level_mod11⟩

/-- Four-level bounded nested representation characterizations for the three
classical Ramanujan residue classes. -/
theorem four_level_nested_representation_iff_facts :
    (∀ m, m % 5 = 4 ↔
      ∃ n a b c d, a < 5 ∧ b < 5 ∧ c < 5 ∧ d < 5 ∧
        m = 3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4) ∧
      (∀ m, m % 7 = 5 ↔
        ∃ n a b c d, a < 7 ∧ b < 7 ∧ c < 7 ∧ d < 7 ∧
          m = 16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5) ∧
      (∀ m, m % 11 = 6 ↔
        ∃ n a b c d, a < 11 ∧ b < 11 ∧ c < 11 ∧ d < 11 ∧
          m = 161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6) := by
  exact ⟨mod_eq_four_iff_exists_four_level_mod5,
    mod_eq_five_iff_exists_four_level_mod7,
    mod_eq_six_iff_exists_four_level_mod11⟩

/-- The concrete one-level mod-11 representative remains in residue class `6`. -/
theorem mod_121n_plus_116_eq_six (n : ℕ) :
    (121 * n + 116) % 11 = 6 := by
  omega

/-- The concrete two-level mod-11 representative remains in residue class `6`. -/
theorem mod_1331n_plus_1326_eq_six (n : ℕ) :
    (1331 * n + 1326) % 11 = 6 := by
  omega

/-- The concrete three-level mod-5 representative remains in residue class `4`. -/
theorem mod_625n_plus_624_eq_four (n : ℕ) :
    (625 * n + 624) % 5 = 4 := by
  omega

/-- The concrete four-level mod-5 representative remains in residue class `4`. -/
theorem mod_3125n_plus_3124_eq_four (n : ℕ) :
    (3125 * n + 3124) % 5 = 4 := by
  omega

/-- The concrete three-level mod-7 representative remains in residue class `5`. -/
theorem mod_2401n_plus_2399_eq_five (n : ℕ) :
    (2401 * n + 2399) % 7 = 5 := by
  omega

/-- The concrete four-level mod-7 representative remains in residue class `5`. -/
theorem mod_16807n_plus_16805_eq_five (n : ℕ) :
    (16807 * n + 16805) % 7 = 5 := by
  omega

/-- The concrete three-level mod-11 representative remains in residue class `6`. -/
theorem mod_14641n_plus_14636_eq_six (n : ℕ) :
    (14641 * n + 14636) % 11 = 6 := by
  omega

/-- The concrete four-level mod-11 representative remains in residue class `6`. -/
theorem mod_161051n_plus_161046_eq_six (n : ℕ) :
    (161051 * n + 161046) % 11 = 6 := by
  omega

/-- The concrete one-level mod-5 representative is the `a = 4` nested case. -/
theorem eq_25n_plus_24_as_one_level_nested (n : ℕ) :
    25 * n + 24 = 25 * n + 5 * 4 + 4 := by
  omega

/-- The concrete two-level mod-5 representative is the `a = b = 4` nested
case. -/
theorem eq_125n_plus_124_as_two_level_nested (n : ℕ) :
    125 * n + 124 = 125 * n + 25 * 4 + 5 * 4 + 4 := by
  omega

/-- The concrete one-level mod-7 representative is the `a = 6` nested case. -/
theorem eq_49n_plus_47_as_one_level_nested (n : ℕ) :
    49 * n + 47 = 49 * n + 7 * 6 + 5 := by
  omega

/-- The concrete two-level mod-7 representative is the `a = b = 6` nested
case. -/
theorem eq_343n_plus_341_as_two_level_nested (n : ℕ) :
    343 * n + 341 = 343 * n + 49 * 6 + 7 * 6 + 5 := by
  omega

/-- The concrete one-level mod-11 representative is the `a = 10` nested case. -/
theorem eq_121n_plus_116_as_one_level_nested (n : ℕ) :
    121 * n + 116 = 121 * n + 11 * 10 + 6 := by
  omega

/-- The concrete two-level mod-11 representative is the `a = b = 10` nested
case. -/
theorem eq_1331n_plus_1326_as_two_level_nested (n : ℕ) :
    1331 * n + 1326 = 1331 * n + 121 * 10 + 11 * 10 + 6 := by
  omega

/-- The concrete three-level mod-5 representative is the all-`4` nested case. -/
theorem eq_625n_plus_624_as_three_level_nested (n : ℕ) :
    625 * n + 624 = 625 * n + 125 * 4 + 25 * 4 + 5 * 4 + 4 := by
  omega

/-- The concrete four-level mod-5 representative is the all-`4` nested case. -/
theorem eq_3125n_plus_3124_as_four_level_nested (n : ℕ) :
    3125 * n + 3124 =
      3125 * n + 625 * 4 + 125 * 4 + 25 * 4 + 5 * 4 + 4 := by
  omega

/-- The concrete three-level mod-7 representative is the all-`6` nested case. -/
theorem eq_2401n_plus_2399_as_three_level_nested (n : ℕ) :
    2401 * n + 2399 = 2401 * n + 343 * 6 + 49 * 6 + 7 * 6 + 5 := by
  omega

/-- The concrete four-level mod-7 representative is the all-`6` nested case. -/
theorem eq_16807n_plus_16805_as_four_level_nested (n : ℕ) :
    16807 * n + 16805 =
      16807 * n + 2401 * 6 + 343 * 6 + 49 * 6 + 7 * 6 + 5 := by
  omega

/-- The concrete three-level mod-11 representative is the all-`10` nested
case. -/
theorem eq_14641n_plus_14636_as_three_level_nested (n : ℕ) :
    14641 * n + 14636 =
      14641 * n + 1331 * 10 + 121 * 10 + 11 * 10 + 6 := by
  omega

/-- The concrete four-level mod-11 representative is the all-`10` nested
case. -/
theorem eq_161051n_plus_161046_as_four_level_nested (n : ℕ) :
    161051 * n + 161046 =
      161051 * n + 14641 * 10 + 1331 * 10 + 121 * 10 + 11 * 10 + 6 := by
  omega

/-- A one-level mod-5 nested progression is a base mod-5 progression. -/
theorem eq_25n_plus_5a_plus_4_as_base_progression (n a : ℕ) :
    25 * n + 5 * a + 4 = 5 * (5 * n + a) + 4 := by
  omega

/-- A one-level mod-7 nested progression is a base mod-7 progression. -/
theorem eq_49n_plus_7a_plus_5_as_base_progression (n a : ℕ) :
    49 * n + 7 * a + 5 = 7 * (7 * n + a) + 5 := by
  omega

/-- A one-level mod-11 nested progression is a base mod-11 progression. -/
theorem eq_121n_plus_11a_plus_6_as_base_progression (n a : ℕ) :
    121 * n + 11 * a + 6 = 11 * (11 * n + a) + 6 := by
  omega

/-- A two-level mod-5 nested progression is a one-level mod-5 nested
progression. -/
theorem eq_125n_plus_25a_plus_5b_plus_4_as_one_level_nested
    (n a b : ℕ) :
    125 * n + 25 * a + 5 * b + 4 = 25 * (5 * n + a) + 5 * b + 4 := by
  omega

/-- A two-level mod-7 nested progression is a one-level mod-7 nested
progression. -/
theorem eq_343n_plus_49a_plus_7b_plus_5_as_one_level_nested
    (n a b : ℕ) :
    343 * n + 49 * a + 7 * b + 5 = 49 * (7 * n + a) + 7 * b + 5 := by
  omega

/-- A two-level mod-11 nested progression is a one-level mod-11 nested
progression. -/
theorem eq_1331n_plus_121a_plus_11b_plus_6_as_one_level_nested
    (n a b : ℕ) :
    1331 * n + 121 * a + 11 * b + 6 =
      121 * (11 * n + a) + 11 * b + 6 := by
  omega

/-- The one-level concrete mod-5 representative is a base mod-5 progression. -/
theorem eq_25n_plus_24_as_base_progression (n : ℕ) :
    25 * n + 24 = 5 * (5 * n + 4) + 4 := by
  omega

/-- The two-level concrete mod-5 representative is a base mod-5 progression
over the one-level representative. -/
theorem eq_125n_plus_124_as_base_progression (n : ℕ) :
    125 * n + 124 = 5 * (25 * n + 24) + 4 := by
  omega

/-- The one-level concrete mod-7 representative is a base mod-7 progression. -/
theorem eq_49n_plus_47_as_base_progression (n : ℕ) :
    49 * n + 47 = 7 * (7 * n + 6) + 5 := by
  omega

/-- The two-level concrete mod-7 representative is a base mod-7 progression
over the one-level representative. -/
theorem eq_343n_plus_341_as_base_progression (n : ℕ) :
    343 * n + 341 = 7 * (49 * n + 48) + 5 := by
  omega

/-- The one-level concrete mod-11 representative is a base mod-11 progression. -/
theorem eq_121n_plus_116_as_base_progression (n : ℕ) :
    121 * n + 116 = 11 * (11 * n + 10) + 6 := by
  omega

/-- The two-level concrete mod-11 representative is a base mod-11 progression
over the one-level representative. -/
theorem eq_1331n_plus_1326_as_base_progression (n : ℕ) :
    1331 * n + 1326 = 11 * (121 * n + 120) + 6 := by
  omega

/-- The three-level concrete mod-5 representative is a base mod-5 progression
over the two-level representative. -/
theorem eq_625n_plus_624_as_base_progression (n : ℕ) :
    625 * n + 624 = 5 * (125 * n + 124) + 4 := by
  omega

/-- The four-level concrete mod-5 representative is a base mod-5 progression
over the three-level representative. -/
theorem eq_3125n_plus_3124_as_base_progression (n : ℕ) :
    3125 * n + 3124 = 5 * (625 * n + 624) + 4 := by
  omega

/-- The three-level concrete mod-7 representative is a base mod-7 progression. -/
theorem eq_2401n_plus_2399_as_base_progression (n : ℕ) :
    2401 * n + 2399 = 7 * (343 * n + 342) + 5 := by
  omega

/-- The four-level concrete mod-7 representative is a base mod-7 progression. -/
theorem eq_16807n_plus_16805_as_base_progression (n : ℕ) :
    16807 * n + 16805 = 7 * (2401 * n + 2400) + 5 := by
  omega

/-- The three-level concrete mod-11 representative is a base mod-11
progression. -/
theorem eq_14641n_plus_14636_as_base_progression (n : ℕ) :
    14641 * n + 14636 = 11 * (1331 * n + 1330) + 6 := by
  omega

/-- The four-level concrete mod-11 representative is a base mod-11
progression. -/
theorem eq_161051n_plus_161046_as_base_progression (n : ℕ) :
    161051 * n + 161046 = 11 * (14641 * n + 14640) + 6 := by
  omega

/-- The concrete two-level mod-5 representative is a one-level nested
progression over `5n+4`. -/
theorem eq_125n_plus_124_as_one_level_nested_over_base (n : ℕ) :
    125 * n + 124 = 25 * (5 * n + 4) + 5 * 4 + 4 := by
  omega

/-- The concrete two-level mod-7 representative is a one-level nested
progression over `7n+6`. -/
theorem eq_343n_plus_341_as_one_level_nested_over_base (n : ℕ) :
    343 * n + 341 = 49 * (7 * n + 6) + 7 * 6 + 5 := by
  omega

/-- The concrete two-level mod-11 representative is a one-level nested
progression over `11n+10`. -/
theorem eq_1331n_plus_1326_as_one_level_nested_over_base (n : ℕ) :
    1331 * n + 1326 = 121 * (11 * n + 10) + 11 * 10 + 6 := by
  omega

/-- The concrete three-level mod-5 representative is a two-level nested
progression over `5n+4`. -/
theorem eq_625n_plus_624_as_two_level_nested_over_base (n : ℕ) :
    625 * n + 624 = 125 * (5 * n + 4) + 25 * 4 + 5 * 4 + 4 := by
  omega

/-- The concrete four-level mod-5 representative is a three-level nested
progression over `5n+4`. -/
theorem eq_3125n_plus_3124_as_three_level_nested_over_base (n : ℕ) :
    3125 * n + 3124 =
      625 * (5 * n + 4) + 125 * 4 + 25 * 4 + 5 * 4 + 4 := by
  omega

/-- The concrete three-level mod-7 representative is a two-level nested
progression over `7n+6`. -/
theorem eq_2401n_plus_2399_as_two_level_nested_over_base (n : ℕ) :
    2401 * n + 2399 = 343 * (7 * n + 6) + 49 * 6 + 7 * 6 + 5 := by
  omega

/-- The concrete four-level mod-7 representative is a three-level nested
progression over `7n+6`. -/
theorem eq_16807n_plus_16805_as_three_level_nested_over_base (n : ℕ) :
    16807 * n + 16805 =
      2401 * (7 * n + 6) + 343 * 6 + 49 * 6 + 7 * 6 + 5 := by
  omega

/-- The concrete three-level mod-11 representative is a two-level nested
progression over `11n+10`. -/
theorem eq_14641n_plus_14636_as_two_level_nested_over_base (n : ℕ) :
    14641 * n + 14636 =
      1331 * (11 * n + 10) + 121 * 10 + 11 * 10 + 6 := by
  omega

/-- The concrete four-level mod-11 representative is a three-level nested
progression over `11n+10`. -/
theorem eq_161051n_plus_161046_as_three_level_nested_over_base (n : ℕ) :
    161051 * n + 161046 =
      14641 * (11 * n + 10) + 1331 * 10 + 121 * 10 + 11 * 10 + 6 := by
  omega

/-- A three-level mod-5 nested progression is a two-level mod-5 nested
progression. -/
theorem eq_625n_plus_125a_plus_25b_plus_5c_plus_4_as_two_level_nested
    (n a b c : ℕ) :
    625 * n + 125 * a + 25 * b + 5 * c + 4 =
      125 * (5 * n + a) + 25 * b + 5 * c + 4 := by
  omega

/-- A four-level mod-5 nested progression is a three-level mod-5 nested
progression. -/
theorem eq_3125n_plus_625a_plus_125b_plus_25c_plus_5d_plus_4_as_three_level_nested
    (n a b c d : ℕ) :
    3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4 =
      625 * (5 * n + a) + 125 * b + 25 * c + 5 * d + 4 := by
  omega

/-- A three-level mod-7 nested progression is a two-level mod-7 nested
progression. -/
theorem eq_2401n_plus_343a_plus_49b_plus_7c_plus_5_as_two_level_nested
    (n a b c : ℕ) :
    2401 * n + 343 * a + 49 * b + 7 * c + 5 =
      343 * (7 * n + a) + 49 * b + 7 * c + 5 := by
  omega

/-- A four-level mod-7 nested progression is a three-level mod-7 nested
progression. -/
theorem eq_16807n_plus_2401a_plus_343b_plus_49c_plus_7d_plus_5_as_three_level_nested
    (n a b c d : ℕ) :
    16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5 =
      2401 * (7 * n + a) + 343 * b + 49 * c + 7 * d + 5 := by
  omega

/-- A three-level mod-11 nested progression is a two-level mod-11 nested
progression. -/
theorem eq_14641n_plus_1331a_plus_121b_plus_11c_plus_6_as_two_level_nested
    (n a b c : ℕ) :
    14641 * n + 1331 * a + 121 * b + 11 * c + 6 =
      1331 * (11 * n + a) + 121 * b + 11 * c + 6 := by
  omega

/-- A four-level mod-11 nested progression is a three-level mod-11 nested
progression. -/
theorem eq_161051n_plus_14641a_plus_1331b_plus_121c_plus_11d_plus_6_as_three_level_nested
    (n a b c d : ℕ) :
    161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6 =
      14641 * (11 * n + a) + 1331 * b + 121 * c + 11 * d + 6 := by
  omega

/-- Base residue facts for the three classical Ramanujan moduli. -/
theorem base_residue_facts :
    (∀ n, (5 * n + 4) % 5 = 4) ∧
      (∀ n, (7 * n + 5) % 7 = 5) ∧
      (∀ n, (11 * n + 6) % 11 = 6) := by
  exact ⟨mod_5n_plus_4_eq_four,
    mod_7n_plus_5_eq_five,
    mod_11n_plus_6_eq_six⟩

/-- One-level nested residue facts for the three classical Ramanujan moduli. -/
theorem nested_one_level_residue_facts :
    (∀ n a, (25 * n + 5 * a + 4) % 5 = 4) ∧
      (∀ n a, (49 * n + 7 * a + 5) % 7 = 5) ∧
      (∀ n a, (121 * n + 11 * a + 6) % 11 = 6) := by
  exact ⟨mod_25n_plus_5a_plus_4_eq_four,
    mod_49n_plus_7a_plus_5_eq_five,
    mod_121n_plus_11a_plus_6_eq_six⟩

/-- Two-level nested residue facts for the three classical Ramanujan moduli. -/
theorem nested_two_level_residue_facts :
    (∀ n a b, (125 * n + 25 * a + 5 * b + 4) % 5 = 4) ∧
      (∀ n a b, (343 * n + 49 * a + 7 * b + 5) % 7 = 5) ∧
      (∀ n a b, (1331 * n + 121 * a + 11 * b + 6) % 11 = 6) := by
  exact ⟨mod_125n_plus_25a_plus_5b_plus_4_eq_four,
    mod_343n_plus_49a_plus_7b_plus_5_eq_five,
    mod_1331n_plus_121a_plus_11b_plus_6_eq_six⟩

/-- Three-level nested residue facts for the three classical Ramanujan moduli. -/
theorem nested_three_level_residue_facts :
    (∀ n a b c, (625 * n + 125 * a + 25 * b + 5 * c + 4) % 5 = 4) ∧
      (∀ n a b c, (2401 * n + 343 * a + 49 * b + 7 * c + 5) % 7 = 5) ∧
      (∀ n a b c,
        (14641 * n + 1331 * a + 121 * b + 11 * c + 6) % 11 = 6) := by
  exact ⟨mod_625n_plus_125a_plus_25b_plus_5c_plus_4_eq_four,
    mod_2401n_plus_343a_plus_49b_plus_7c_plus_5_eq_five,
    mod_14641n_plus_1331a_plus_121b_plus_11c_plus_6_eq_six⟩

/-- Four-level nested residue facts for the three classical Ramanujan moduli. -/
theorem nested_four_level_residue_facts :
    (∀ n a b c d,
      (3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4) % 5 = 4) ∧
      (∀ n a b c d,
        (16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5) % 7 = 5) ∧
      (∀ n a b c d,
        (161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6) % 11 = 6) := by
  exact ⟨mod_3125n_plus_625a_plus_125b_plus_25c_plus_5d_plus_4_eq_four,
    mod_16807n_plus_2401a_plus_343b_plus_49c_plus_7d_plus_5_eq_five,
    mod_161051n_plus_14641a_plus_1331b_plus_121c_plus_11d_plus_6_eq_six⟩

/-- Concrete one-level representative residue facts for the three classical
Ramanujan moduli. -/
theorem nested_concrete_one_level_residue_facts :
    (∀ n, (25 * n + 24) % 5 = 4) ∧
      (∀ n, (49 * n + 47) % 7 = 5) ∧
      (∀ n, (121 * n + 116) % 11 = 6) := by
  exact ⟨mod_25n_plus_24_eq_four,
    mod_49n_plus_47_eq_five,
    mod_121n_plus_116_eq_six⟩

/-- Concrete deepest representative residue facts for the three classical
Ramanujan moduli. -/
theorem nested_concrete_residue_facts :
    (∀ n, (125 * n + 124) % 5 = 4) ∧
      (∀ n, (343 * n + 341) % 7 = 5) ∧
      (∀ n, (1331 * n + 1326) % 11 = 6) := by
  exact ⟨mod_125n_plus_124_eq_four,
    mod_343n_plus_341_eq_five,
    mod_1331n_plus_1326_eq_six⟩

/-- Concrete two-level representative residue facts for the three classical
Ramanujan moduli. -/
theorem nested_concrete_two_level_residue_facts :
    (∀ n, (125 * n + 124) % 5 = 4) ∧
      (∀ n, (343 * n + 341) % 7 = 5) ∧
      (∀ n, (1331 * n + 1326) % 11 = 6) :=
  nested_concrete_residue_facts

/-- Concrete three-level representative residue facts for the three classical
Ramanujan moduli. -/
theorem nested_concrete_three_level_residue_facts :
    (∀ n, (625 * n + 624) % 5 = 4) ∧
      (∀ n, (2401 * n + 2399) % 7 = 5) ∧
      (∀ n, (14641 * n + 14636) % 11 = 6) := by
  exact ⟨mod_625n_plus_624_eq_four,
    mod_2401n_plus_2399_eq_five,
    mod_14641n_plus_14636_eq_six⟩

/-- Concrete four-level representative residue facts for the three classical
Ramanujan moduli. -/
theorem nested_concrete_four_level_residue_facts :
    (∀ n, (3125 * n + 3124) % 5 = 4) ∧
      (∀ n, (16807 * n + 16805) % 7 = 5) ∧
      (∀ n, (161051 * n + 161046) % 11 = 6) := by
  exact ⟨mod_3125n_plus_3124_eq_four,
    mod_16807n_plus_16805_eq_five,
    mod_161051n_plus_161046_eq_six⟩

/-- Base mod-5 progression membership is exactly residue class `4`. -/
theorem exists_base_mod5_iff_mod_eq_four (m : ℕ) :
    (∃ n, m = 5 * n + 4) ↔ m % 5 = 4 := by
  constructor
  · rintro ⟨n, rfl⟩
    exact mod_5n_plus_4_eq_four n
  · intro hm
    exact ⟨m / 5, eq_five_mul_div_plus_four_of_mod_eq_four hm⟩

/-- Base mod-7 progression membership is exactly residue class `5`. -/
theorem exists_base_mod7_iff_mod_eq_five (m : ℕ) :
    (∃ n, m = 7 * n + 5) ↔ m % 7 = 5 := by
  constructor
  · rintro ⟨n, rfl⟩
    exact mod_7n_plus_5_eq_five n
  · intro hm
    exact ⟨m / 7, eq_seven_mul_div_plus_five_of_mod_eq_five hm⟩

/-- Base mod-11 progression membership is exactly residue class `6`. -/
theorem exists_base_mod11_iff_mod_eq_six (m : ℕ) :
    (∃ n, m = 11 * n + 6) ↔ m % 11 = 6 := by
  constructor
  · rintro ⟨n, rfl⟩
    exact mod_11n_plus_6_eq_six n
  · intro hm
    exact ⟨m / 11, eq_eleven_mul_div_plus_six_of_mod_eq_six hm⟩

/-- Bounded one-level mod-5 membership is exactly residue class `4`. -/
theorem exists_one_level_mod5_iff_mod_eq_four (m : ℕ) :
    (∃ n a, a < 5 ∧ m = 25 * n + 5 * a + 4) ↔ m % 5 = 4 := by
  constructor
  · rintro ⟨n, a, _ha, rfl⟩
    exact mod_25n_plus_5a_plus_4_eq_four n a
  · exact exists_one_level_mod5_of_mod_eq_four

/-- Bounded one-level mod-7 membership is exactly residue class `5`. -/
theorem exists_one_level_mod7_iff_mod_eq_five (m : ℕ) :
    (∃ n a, a < 7 ∧ m = 49 * n + 7 * a + 5) ↔ m % 7 = 5 := by
  constructor
  · rintro ⟨n, a, _ha, rfl⟩
    exact mod_49n_plus_7a_plus_5_eq_five n a
  · exact exists_one_level_mod7_of_mod_eq_five

/-- Bounded one-level mod-11 membership is exactly residue class `6`. -/
theorem exists_one_level_mod11_iff_mod_eq_six (m : ℕ) :
    (∃ n a, a < 11 ∧ m = 121 * n + 11 * a + 6) ↔ m % 11 = 6 := by
  constructor
  · rintro ⟨n, a, _ha, rfl⟩
    exact mod_121n_plus_11a_plus_6_eq_six n a
  · exact exists_one_level_mod11_of_mod_eq_six

/-- Bounded two-level mod-5 membership is exactly residue class `4`. -/
theorem exists_two_level_mod5_iff_mod_eq_four (m : ℕ) :
    (∃ n a b, a < 5 ∧ b < 5 ∧
      m = 125 * n + 25 * a + 5 * b + 4) ↔ m % 5 = 4 := by
  constructor
  · rintro ⟨n, a, b, _ha, _hb, rfl⟩
    exact mod_125n_plus_25a_plus_5b_plus_4_eq_four n a b
  · exact exists_two_level_mod5_of_mod_eq_four

/-- Bounded two-level mod-7 membership is exactly residue class `5`. -/
theorem exists_two_level_mod7_iff_mod_eq_five (m : ℕ) :
    (∃ n a b, a < 7 ∧ b < 7 ∧
      m = 343 * n + 49 * a + 7 * b + 5) ↔ m % 7 = 5 := by
  constructor
  · rintro ⟨n, a, b, _ha, _hb, rfl⟩
    exact mod_343n_plus_49a_plus_7b_plus_5_eq_five n a b
  · exact exists_two_level_mod7_of_mod_eq_five

/-- Bounded two-level mod-11 membership is exactly residue class `6`. -/
theorem exists_two_level_mod11_iff_mod_eq_six (m : ℕ) :
    (∃ n a b, a < 11 ∧ b < 11 ∧
      m = 1331 * n + 121 * a + 11 * b + 6) ↔ m % 11 = 6 := by
  constructor
  · rintro ⟨n, a, b, _ha, _hb, rfl⟩
    exact mod_1331n_plus_121a_plus_11b_plus_6_eq_six n a b
  · exact exists_two_level_mod11_of_mod_eq_six

/-- Bounded three-level mod-5 membership is exactly residue class `4`. -/
theorem exists_three_level_mod5_iff_mod_eq_four (m : ℕ) :
    (∃ n a b c, a < 5 ∧ b < 5 ∧ c < 5 ∧
      m = 625 * n + 125 * a + 25 * b + 5 * c + 4) ↔ m % 5 = 4 := by
  constructor
  · rintro ⟨n, a, b, c, _ha, _hb, _hc, rfl⟩
    exact mod_625n_plus_125a_plus_25b_plus_5c_plus_4_eq_four n a b c
  · exact exists_three_level_mod5_of_mod_eq_four

/-- Bounded three-level mod-7 membership is exactly residue class `5`. -/
theorem exists_three_level_mod7_iff_mod_eq_five (m : ℕ) :
    (∃ n a b c, a < 7 ∧ b < 7 ∧ c < 7 ∧
      m = 2401 * n + 343 * a + 49 * b + 7 * c + 5) ↔ m % 7 = 5 := by
  constructor
  · rintro ⟨n, a, b, c, _ha, _hb, _hc, rfl⟩
    exact mod_2401n_plus_343a_plus_49b_plus_7c_plus_5_eq_five n a b c
  · exact exists_three_level_mod7_of_mod_eq_five

/-- Bounded three-level mod-11 membership is exactly residue class `6`. -/
theorem exists_three_level_mod11_iff_mod_eq_six (m : ℕ) :
    (∃ n a b c, a < 11 ∧ b < 11 ∧ c < 11 ∧
      m = 14641 * n + 1331 * a + 121 * b + 11 * c + 6) ↔ m % 11 = 6 := by
  constructor
  · rintro ⟨n, a, b, c, _ha, _hb, _hc, rfl⟩
    exact mod_14641n_plus_1331a_plus_121b_plus_11c_plus_6_eq_six n a b c
  · exact exists_three_level_mod11_of_mod_eq_six

/-- Bounded four-level mod-5 membership is exactly residue class `4`. -/
theorem exists_four_level_mod5_iff_mod_eq_four (m : ℕ) :
    (∃ n a b c d, a < 5 ∧ b < 5 ∧ c < 5 ∧ d < 5 ∧
      m = 3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4) ↔
      m % 5 = 4 := by
  constructor
  · rintro ⟨n, a, b, c, d, _ha, _hb, _hc, _hd, rfl⟩
    exact mod_3125n_plus_625a_plus_125b_plus_25c_plus_5d_plus_4_eq_four n a b c d
  · exact exists_four_level_mod5_of_mod_eq_four

/-- Bounded four-level mod-7 membership is exactly residue class `5`. -/
theorem exists_four_level_mod7_iff_mod_eq_five (m : ℕ) :
    (∃ n a b c d, a < 7 ∧ b < 7 ∧ c < 7 ∧ d < 7 ∧
      m = 16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5) ↔
      m % 7 = 5 := by
  constructor
  · rintro ⟨n, a, b, c, d, _ha, _hb, _hc, _hd, rfl⟩
    exact mod_16807n_plus_2401a_plus_343b_plus_49c_plus_7d_plus_5_eq_five n a b c d
  · exact exists_four_level_mod7_of_mod_eq_five

/-- Bounded four-level mod-11 membership is exactly residue class `6`. -/
theorem exists_four_level_mod11_iff_mod_eq_six (m : ℕ) :
    (∃ n a b c d, a < 11 ∧ b < 11 ∧ c < 11 ∧ d < 11 ∧
      m = 161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6) ↔
      m % 11 = 6 := by
  constructor
  · rintro ⟨n, a, b, c, d, _ha, _hb, _hc, _hd, rfl⟩
    exact mod_161051n_plus_14641a_plus_1331b_plus_121c_plus_11d_plus_6_eq_six
      n a b c d
  · exact exists_four_level_mod11_of_mod_eq_six

/-- Base progression membership iff facts for the three classical Ramanujan
moduli. -/
theorem base_membership_iff_residue_facts :
    (∀ m, (∃ n, m = 5 * n + 4) ↔ m % 5 = 4) ∧
      (∀ m, (∃ n, m = 7 * n + 5) ↔ m % 7 = 5) ∧
      (∀ m, (∃ n, m = 11 * n + 6) ↔ m % 11 = 6) := by
  exact ⟨exists_base_mod5_iff_mod_eq_four,
    exists_base_mod7_iff_mod_eq_five,
    exists_base_mod11_iff_mod_eq_six⟩

/-- One-level bounded nested membership iff facts for the three classical
Ramanujan moduli. -/
theorem one_level_membership_iff_residue_facts :
    (∀ m, (∃ n a, a < 5 ∧ m = 25 * n + 5 * a + 4) ↔ m % 5 = 4) ∧
      (∀ m, (∃ n a, a < 7 ∧ m = 49 * n + 7 * a + 5) ↔ m % 7 = 5) ∧
      (∀ m, (∃ n a, a < 11 ∧ m = 121 * n + 11 * a + 6) ↔
        m % 11 = 6) := by
  exact ⟨exists_one_level_mod5_iff_mod_eq_four,
    exists_one_level_mod7_iff_mod_eq_five,
    exists_one_level_mod11_iff_mod_eq_six⟩

/-- Two-level bounded nested membership iff facts for the three classical
Ramanujan moduli. -/
theorem two_level_membership_iff_residue_facts :
    (∀ m, (∃ n a b, a < 5 ∧ b < 5 ∧
      m = 125 * n + 25 * a + 5 * b + 4) ↔ m % 5 = 4) ∧
      (∀ m, (∃ n a b, a < 7 ∧ b < 7 ∧
        m = 343 * n + 49 * a + 7 * b + 5) ↔ m % 7 = 5) ∧
      (∀ m, (∃ n a b, a < 11 ∧ b < 11 ∧
        m = 1331 * n + 121 * a + 11 * b + 6) ↔ m % 11 = 6) := by
  exact ⟨exists_two_level_mod5_iff_mod_eq_four,
    exists_two_level_mod7_iff_mod_eq_five,
    exists_two_level_mod11_iff_mod_eq_six⟩

/-- Three-level bounded nested membership iff facts for the three classical
Ramanujan moduli. -/
theorem three_level_membership_iff_residue_facts :
    (∀ m, (∃ n a b c, a < 5 ∧ b < 5 ∧ c < 5 ∧
      m = 625 * n + 125 * a + 25 * b + 5 * c + 4) ↔ m % 5 = 4) ∧
      (∀ m, (∃ n a b c, a < 7 ∧ b < 7 ∧ c < 7 ∧
        m = 2401 * n + 343 * a + 49 * b + 7 * c + 5) ↔ m % 7 = 5) ∧
      (∀ m, (∃ n a b c, a < 11 ∧ b < 11 ∧ c < 11 ∧
        m = 14641 * n + 1331 * a + 121 * b + 11 * c + 6) ↔
        m % 11 = 6) := by
  exact ⟨exists_three_level_mod5_iff_mod_eq_four,
    exists_three_level_mod7_iff_mod_eq_five,
    exists_three_level_mod11_iff_mod_eq_six⟩

/-- Four-level bounded nested membership iff facts for the three classical
Ramanujan moduli. -/
theorem four_level_membership_iff_residue_facts :
    (∀ m, (∃ n a b c d, a < 5 ∧ b < 5 ∧ c < 5 ∧ d < 5 ∧
      m = 3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4) ↔
      m % 5 = 4) ∧
      (∀ m, (∃ n a b c d, a < 7 ∧ b < 7 ∧ c < 7 ∧ d < 7 ∧
        m = 16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5) ↔
        m % 7 = 5) ∧
      (∀ m, (∃ n a b c d, a < 11 ∧ b < 11 ∧ c < 11 ∧ d < 11 ∧
        m = 161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6) ↔
        m % 11 = 6) := by
  exact ⟨exists_four_level_mod5_iff_mod_eq_four,
    exists_four_level_mod7_iff_mod_eq_five,
    exists_four_level_mod11_iff_mod_eq_six⟩

/-- Unbounded one-level mod-5 membership is exactly residue class `4`. -/
theorem exists_one_level_mod5_unbounded_iff_mod_eq_four (m : ℕ) :
    (∃ n a, m = 25 * n + 5 * a + 4) ↔ m % 5 = 4 := by
  constructor
  · rintro ⟨n, a, rfl⟩
    exact mod_25n_plus_5a_plus_4_eq_four n a
  · intro hm
    obtain ⟨n, a, _ha, h⟩ := exists_one_level_mod5_of_mod_eq_four hm
    exact ⟨n, a, h⟩

/-- Unbounded one-level mod-7 membership is exactly residue class `5`. -/
theorem exists_one_level_mod7_unbounded_iff_mod_eq_five (m : ℕ) :
    (∃ n a, m = 49 * n + 7 * a + 5) ↔ m % 7 = 5 := by
  constructor
  · rintro ⟨n, a, rfl⟩
    exact mod_49n_plus_7a_plus_5_eq_five n a
  · intro hm
    obtain ⟨n, a, _ha, h⟩ := exists_one_level_mod7_of_mod_eq_five hm
    exact ⟨n, a, h⟩

/-- Unbounded one-level mod-11 membership is exactly residue class `6`. -/
theorem exists_one_level_mod11_unbounded_iff_mod_eq_six (m : ℕ) :
    (∃ n a, m = 121 * n + 11 * a + 6) ↔ m % 11 = 6 := by
  constructor
  · rintro ⟨n, a, rfl⟩
    exact mod_121n_plus_11a_plus_6_eq_six n a
  · intro hm
    obtain ⟨n, a, _ha, h⟩ := exists_one_level_mod11_of_mod_eq_six hm
    exact ⟨n, a, h⟩

/-- Unbounded two-level mod-5 membership is exactly residue class `4`. -/
theorem exists_two_level_mod5_unbounded_iff_mod_eq_four (m : ℕ) :
    (∃ n a b, m = 125 * n + 25 * a + 5 * b + 4) ↔ m % 5 = 4 := by
  constructor
  · rintro ⟨n, a, b, rfl⟩
    exact mod_125n_plus_25a_plus_5b_plus_4_eq_four n a b
  · intro hm
    obtain ⟨n, a, b, _ha, _hb, h⟩ := exists_two_level_mod5_of_mod_eq_four hm
    exact ⟨n, a, b, h⟩

/-- Unbounded two-level mod-7 membership is exactly residue class `5`. -/
theorem exists_two_level_mod7_unbounded_iff_mod_eq_five (m : ℕ) :
    (∃ n a b, m = 343 * n + 49 * a + 7 * b + 5) ↔ m % 7 = 5 := by
  constructor
  · rintro ⟨n, a, b, rfl⟩
    exact mod_343n_plus_49a_plus_7b_plus_5_eq_five n a b
  · intro hm
    obtain ⟨n, a, b, _ha, _hb, h⟩ := exists_two_level_mod7_of_mod_eq_five hm
    exact ⟨n, a, b, h⟩

/-- Unbounded two-level mod-11 membership is exactly residue class `6`. -/
theorem exists_two_level_mod11_unbounded_iff_mod_eq_six (m : ℕ) :
    (∃ n a b, m = 1331 * n + 121 * a + 11 * b + 6) ↔ m % 11 = 6 := by
  constructor
  · rintro ⟨n, a, b, rfl⟩
    exact mod_1331n_plus_121a_plus_11b_plus_6_eq_six n a b
  · intro hm
    obtain ⟨n, a, b, _ha, _hb, h⟩ := exists_two_level_mod11_of_mod_eq_six hm
    exact ⟨n, a, b, h⟩

/-- Unbounded three-level mod-5 membership is exactly residue class `4`. -/
theorem exists_three_level_mod5_unbounded_iff_mod_eq_four (m : ℕ) :
    (∃ n a b c, m = 625 * n + 125 * a + 25 * b + 5 * c + 4) ↔
      m % 5 = 4 := by
  constructor
  · rintro ⟨n, a, b, c, rfl⟩
    exact mod_625n_plus_125a_plus_25b_plus_5c_plus_4_eq_four n a b c
  · intro hm
    obtain ⟨n, a, b, c, _ha, _hb, _hc, h⟩ := exists_three_level_mod5_of_mod_eq_four hm
    exact ⟨n, a, b, c, h⟩

/-- Unbounded three-level mod-7 membership is exactly residue class `5`. -/
theorem exists_three_level_mod7_unbounded_iff_mod_eq_five (m : ℕ) :
    (∃ n a b c, m = 2401 * n + 343 * a + 49 * b + 7 * c + 5) ↔
      m % 7 = 5 := by
  constructor
  · rintro ⟨n, a, b, c, rfl⟩
    exact mod_2401n_plus_343a_plus_49b_plus_7c_plus_5_eq_five n a b c
  · intro hm
    obtain ⟨n, a, b, c, _ha, _hb, _hc, h⟩ := exists_three_level_mod7_of_mod_eq_five hm
    exact ⟨n, a, b, c, h⟩

/-- Unbounded three-level mod-11 membership is exactly residue class `6`. -/
theorem exists_three_level_mod11_unbounded_iff_mod_eq_six (m : ℕ) :
    (∃ n a b c, m = 14641 * n + 1331 * a + 121 * b + 11 * c + 6) ↔
      m % 11 = 6 := by
  constructor
  · rintro ⟨n, a, b, c, rfl⟩
    exact mod_14641n_plus_1331a_plus_121b_plus_11c_plus_6_eq_six n a b c
  · intro hm
    obtain ⟨n, a, b, c, _ha, _hb, _hc, h⟩ := exists_three_level_mod11_of_mod_eq_six hm
    exact ⟨n, a, b, c, h⟩

/-- Unbounded four-level mod-5 membership is exactly residue class `4`. -/
theorem exists_four_level_mod5_unbounded_iff_mod_eq_four (m : ℕ) :
    (∃ n a b c d, m = 3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4) ↔
      m % 5 = 4 := by
  constructor
  · rintro ⟨n, a, b, c, d, rfl⟩
    exact mod_3125n_plus_625a_plus_125b_plus_25c_plus_5d_plus_4_eq_four n a b c d
  · intro hm
    obtain ⟨n, a, b, c, d, _ha, _hb, _hc, _hd, h⟩ :=
      exists_four_level_mod5_of_mod_eq_four hm
    exact ⟨n, a, b, c, d, h⟩

/-- Unbounded four-level mod-7 membership is exactly residue class `5`. -/
theorem exists_four_level_mod7_unbounded_iff_mod_eq_five (m : ℕ) :
    (∃ n a b c d, m = 16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5) ↔
      m % 7 = 5 := by
  constructor
  · rintro ⟨n, a, b, c, d, rfl⟩
    exact mod_16807n_plus_2401a_plus_343b_plus_49c_plus_7d_plus_5_eq_five n a b c d
  · intro hm
    obtain ⟨n, a, b, c, d, _ha, _hb, _hc, _hd, h⟩ :=
      exists_four_level_mod7_of_mod_eq_five hm
    exact ⟨n, a, b, c, d, h⟩

/-- Unbounded four-level mod-11 membership is exactly residue class `6`. -/
theorem exists_four_level_mod11_unbounded_iff_mod_eq_six (m : ℕ) :
    (∃ n a b c d,
      m = 161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6) ↔
      m % 11 = 6 := by
  constructor
  · rintro ⟨n, a, b, c, d, rfl⟩
    exact mod_161051n_plus_14641a_plus_1331b_plus_121c_plus_11d_plus_6_eq_six
      n a b c d
  · intro hm
    obtain ⟨n, a, b, c, d, _ha, _hb, _hc, _hd, h⟩ :=
      exists_four_level_mod11_of_mod_eq_six hm
    exact ⟨n, a, b, c, d, h⟩

/-- Unbounded one-level membership iff facts for the three classical Ramanujan
moduli. -/
theorem one_level_unbounded_membership_iff_residue_facts :
    (∀ m, (∃ n a, m = 25 * n + 5 * a + 4) ↔ m % 5 = 4) ∧
      (∀ m, (∃ n a, m = 49 * n + 7 * a + 5) ↔ m % 7 = 5) ∧
      (∀ m, (∃ n a, m = 121 * n + 11 * a + 6) ↔ m % 11 = 6) := by
  exact ⟨exists_one_level_mod5_unbounded_iff_mod_eq_four,
    exists_one_level_mod7_unbounded_iff_mod_eq_five,
    exists_one_level_mod11_unbounded_iff_mod_eq_six⟩

/-- Unbounded two-level membership iff facts for the three classical Ramanujan
moduli. -/
theorem two_level_unbounded_membership_iff_residue_facts :
    (∀ m, (∃ n a b, m = 125 * n + 25 * a + 5 * b + 4) ↔ m % 5 = 4) ∧
      (∀ m, (∃ n a b, m = 343 * n + 49 * a + 7 * b + 5) ↔ m % 7 = 5) ∧
      (∀ m, (∃ n a b, m = 1331 * n + 121 * a + 11 * b + 6) ↔
        m % 11 = 6) := by
  exact ⟨exists_two_level_mod5_unbounded_iff_mod_eq_four,
    exists_two_level_mod7_unbounded_iff_mod_eq_five,
    exists_two_level_mod11_unbounded_iff_mod_eq_six⟩

/-- Unbounded three-level membership iff facts for the three classical
Ramanujan moduli. -/
theorem three_level_unbounded_membership_iff_residue_facts :
    (∀ m, (∃ n a b c, m = 625 * n + 125 * a + 25 * b + 5 * c + 4) ↔
      m % 5 = 4) ∧
      (∀ m, (∃ n a b c, m = 2401 * n + 343 * a + 49 * b + 7 * c + 5) ↔
        m % 7 = 5) ∧
      (∀ m, (∃ n a b c, m = 14641 * n + 1331 * a + 121 * b + 11 * c + 6) ↔
        m % 11 = 6) := by
  exact ⟨exists_three_level_mod5_unbounded_iff_mod_eq_four,
    exists_three_level_mod7_unbounded_iff_mod_eq_five,
    exists_three_level_mod11_unbounded_iff_mod_eq_six⟩

/-- Unbounded four-level membership iff facts for the three classical Ramanujan
moduli. -/
theorem four_level_unbounded_membership_iff_residue_facts :
    (∀ m, (∃ n a b c d,
      m = 3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4) ↔
      m % 5 = 4) ∧
      (∀ m, (∃ n a b c d,
        m = 16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5) ↔
        m % 7 = 5) ∧
      (∀ m, (∃ n a b c d,
        m = 161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6) ↔
        m % 11 = 6) := by
  exact ⟨exists_four_level_mod5_unbounded_iff_mod_eq_four,
    exists_four_level_mod7_unbounded_iff_mod_eq_five,
    exists_four_level_mod11_unbounded_iff_mod_eq_six⟩

/-- General quotient decomposition after a fixed residue computation. -/
theorem eq_mul_div_plus_of_mod_eq {q r m : ℕ} (hm : m % q = r) :
    m = q * (m / q) + r := by
  have h := (Nat.mod_add_div m q).symm
  omega

/-- General membership criterion for a single arithmetic progression. -/
theorem exists_mul_add_iff_mod_eq {q r m : ℕ} (hr : r < q) :
    (∃ n, m = q * n + r) ↔ m % q = r := by
  constructor
  · rintro ⟨n, rfl⟩
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  · intro hm
    exact ⟨m / q, eq_mul_div_plus_of_mod_eq hm⟩

/-- The concrete `25n+24` progression is residue `24 mod 25`. -/
theorem mod_25n_plus_24_eq_24 (n : ℕ) :
    (25 * n + 24) % 25 = 24 := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- The concrete `125n+124` progression is residue `124 mod 125`. -/
theorem mod_125n_plus_124_eq_124 (n : ℕ) :
    (125 * n + 124) % 125 = 124 := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- The concrete `625n+624` progression is residue `624 mod 625`. -/
theorem mod_625n_plus_624_eq_624 (n : ℕ) :
    (625 * n + 624) % 625 = 624 := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- The concrete `3125n+3124` progression is residue `3124 mod 3125`. -/
theorem mod_3125n_plus_3124_eq_3124 (n : ℕ) :
    (3125 * n + 3124) % 3125 = 3124 := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- The concrete `49n+47` progression is residue `47 mod 49`. -/
theorem mod_49n_plus_47_eq_47 (n : ℕ) :
    (49 * n + 47) % 49 = 47 := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- The concrete `343n+341` progression is residue `341 mod 343`. -/
theorem mod_343n_plus_341_eq_341 (n : ℕ) :
    (343 * n + 341) % 343 = 341 := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- The concrete `2401n+2399` progression is residue `2399 mod 2401`. -/
theorem mod_2401n_plus_2399_eq_2399 (n : ℕ) :
    (2401 * n + 2399) % 2401 = 2399 := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- The concrete `16807n+16805` progression is residue `16805 mod 16807`. -/
theorem mod_16807n_plus_16805_eq_16805 (n : ℕ) :
    (16807 * n + 16805) % 16807 = 16805 := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- The concrete `121n+116` progression is residue `116 mod 121`. -/
theorem mod_121n_plus_116_eq_116 (n : ℕ) :
    (121 * n + 116) % 121 = 116 := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- The concrete `1331n+1326` progression is residue `1326 mod 1331`. -/
theorem mod_1331n_plus_1326_eq_1326 (n : ℕ) :
    (1331 * n + 1326) % 1331 = 1326 := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- The concrete `14641n+14636` progression is residue `14636 mod 14641`. -/
theorem mod_14641n_plus_14636_eq_14636 (n : ℕ) :
    (14641 * n + 14636) % 14641 = 14636 := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- The concrete `161051n+161046` progression is residue `161046 mod 161051`. -/
theorem mod_161051n_plus_161046_eq_161046 (n : ℕ) :
    (161051 * n + 161046) % 161051 = 161046 := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Decompose a residue `24 mod 25`. -/
theorem eq_25_mul_div_plus_24_of_mod_eq_24 {m : ℕ} (hm : m % 25 = 24) :
    m = 25 * (m / 25) + 24 := by
  exact eq_mul_div_plus_of_mod_eq hm

/-- Decompose a residue `124 mod 125`. -/
theorem eq_125_mul_div_plus_124_of_mod_eq_124 {m : ℕ} (hm : m % 125 = 124) :
    m = 125 * (m / 125) + 124 := by
  exact eq_mul_div_plus_of_mod_eq hm

/-- Decompose a residue `624 mod 625`. -/
theorem eq_625_mul_div_plus_624_of_mod_eq_624 {m : ℕ} (hm : m % 625 = 624) :
    m = 625 * (m / 625) + 624 := by
  exact eq_mul_div_plus_of_mod_eq hm

/-- Decompose a residue `3124 mod 3125`. -/
theorem eq_3125_mul_div_plus_3124_of_mod_eq_3124 {m : ℕ}
    (hm : m % 3125 = 3124) :
    m = 3125 * (m / 3125) + 3124 := by
  exact eq_mul_div_plus_of_mod_eq hm

/-- Decompose a residue `47 mod 49`. -/
theorem eq_49_mul_div_plus_47_of_mod_eq_47 {m : ℕ} (hm : m % 49 = 47) :
    m = 49 * (m / 49) + 47 := by
  exact eq_mul_div_plus_of_mod_eq hm

/-- Decompose a residue `341 mod 343`. -/
theorem eq_343_mul_div_plus_341_of_mod_eq_341 {m : ℕ} (hm : m % 343 = 341) :
    m = 343 * (m / 343) + 341 := by
  exact eq_mul_div_plus_of_mod_eq hm

/-- Decompose a residue `2399 mod 2401`. -/
theorem eq_2401_mul_div_plus_2399_of_mod_eq_2399 {m : ℕ}
    (hm : m % 2401 = 2399) :
    m = 2401 * (m / 2401) + 2399 := by
  exact eq_mul_div_plus_of_mod_eq hm

/-- Decompose a residue `16805 mod 16807`. -/
theorem eq_16807_mul_div_plus_16805_of_mod_eq_16805 {m : ℕ}
    (hm : m % 16807 = 16805) :
    m = 16807 * (m / 16807) + 16805 := by
  exact eq_mul_div_plus_of_mod_eq hm

/-- Decompose a residue `116 mod 121`. -/
theorem eq_121_mul_div_plus_116_of_mod_eq_116 {m : ℕ} (hm : m % 121 = 116) :
    m = 121 * (m / 121) + 116 := by
  exact eq_mul_div_plus_of_mod_eq hm

/-- Decompose a residue `1326 mod 1331`. -/
theorem eq_1331_mul_div_plus_1326_of_mod_eq_1326 {m : ℕ}
    (hm : m % 1331 = 1326) :
    m = 1331 * (m / 1331) + 1326 := by
  exact eq_mul_div_plus_of_mod_eq hm

/-- Decompose a residue `14636 mod 14641`. -/
theorem eq_14641_mul_div_plus_14636_of_mod_eq_14636 {m : ℕ}
    (hm : m % 14641 = 14636) :
    m = 14641 * (m / 14641) + 14636 := by
  exact eq_mul_div_plus_of_mod_eq hm

/-- Decompose a residue `161046 mod 161051`. -/
theorem eq_161051_mul_div_plus_161046_of_mod_eq_161046 {m : ℕ}
    (hm : m % 161051 = 161046) :
    m = 161051 * (m / 161051) + 161046 := by
  exact eq_mul_div_plus_of_mod_eq hm

/-- Membership in `25n+24` is exactly residue `24 mod 25`. -/
theorem exists_mod25_progression_iff_mod_eq_24 (m : ℕ) :
    (∃ n, m = 25 * n + 24) ↔ m % 25 = 24 := by
  exact exists_mul_add_iff_mod_eq (by decide)

/-- Membership in `125n+124` is exactly residue `124 mod 125`. -/
theorem exists_mod125_progression_iff_mod_eq_124 (m : ℕ) :
    (∃ n, m = 125 * n + 124) ↔ m % 125 = 124 := by
  exact exists_mul_add_iff_mod_eq (by decide)

/-- Membership in `625n+624` is exactly residue `624 mod 625`. -/
theorem exists_mod625_progression_iff_mod_eq_624 (m : ℕ) :
    (∃ n, m = 625 * n + 624) ↔ m % 625 = 624 := by
  exact exists_mul_add_iff_mod_eq (by decide)

/-- Membership in `3125n+3124` is exactly residue `3124 mod 3125`. -/
theorem exists_mod3125_progression_iff_mod_eq_3124 (m : ℕ) :
    (∃ n, m = 3125 * n + 3124) ↔ m % 3125 = 3124 := by
  exact exists_mul_add_iff_mod_eq (by decide)

/-- Membership in `49n+47` is exactly residue `47 mod 49`. -/
theorem exists_mod49_progression_iff_mod_eq_47 (m : ℕ) :
    (∃ n, m = 49 * n + 47) ↔ m % 49 = 47 := by
  exact exists_mul_add_iff_mod_eq (by decide)

/-- Membership in `343n+341` is exactly residue `341 mod 343`. -/
theorem exists_mod343_progression_iff_mod_eq_341 (m : ℕ) :
    (∃ n, m = 343 * n + 341) ↔ m % 343 = 341 := by
  exact exists_mul_add_iff_mod_eq (by decide)

/-- Membership in `2401n+2399` is exactly residue `2399 mod 2401`. -/
theorem exists_mod2401_progression_iff_mod_eq_2399 (m : ℕ) :
    (∃ n, m = 2401 * n + 2399) ↔ m % 2401 = 2399 := by
  exact exists_mul_add_iff_mod_eq (by decide)

/-- Membership in `16807n+16805` is exactly residue `16805 mod 16807`. -/
theorem exists_mod16807_progression_iff_mod_eq_16805 (m : ℕ) :
    (∃ n, m = 16807 * n + 16805) ↔ m % 16807 = 16805 := by
  exact exists_mul_add_iff_mod_eq (by decide)

/-- Membership in `121n+116` is exactly residue `116 mod 121`. -/
theorem exists_mod121_progression_iff_mod_eq_116 (m : ℕ) :
    (∃ n, m = 121 * n + 116) ↔ m % 121 = 116 := by
  exact exists_mul_add_iff_mod_eq (by decide)

/-- Membership in `1331n+1326` is exactly residue `1326 mod 1331`. -/
theorem exists_mod1331_progression_iff_mod_eq_1326 (m : ℕ) :
    (∃ n, m = 1331 * n + 1326) ↔ m % 1331 = 1326 := by
  exact exists_mul_add_iff_mod_eq (by decide)

/-- Membership in `14641n+14636` is exactly residue `14636 mod 14641`. -/
theorem exists_mod14641_progression_iff_mod_eq_14636 (m : ℕ) :
    (∃ n, m = 14641 * n + 14636) ↔ m % 14641 = 14636 := by
  exact exists_mul_add_iff_mod_eq (by decide)

/-- Membership in `161051n+161046` is exactly residue `161046 mod 161051`. -/
theorem exists_mod161051_progression_iff_mod_eq_161046 (m : ℕ) :
    (∃ n, m = 161051 * n + 161046) ↔ m % 161051 = 161046 := by
  exact exists_mul_add_iff_mod_eq (by decide)

/-- Concrete higher-power mod-5 progression membership facts. -/
theorem concrete_mod5_power_membership_iff_residue_facts :
    (∀ m, (∃ n, m = 25 * n + 24) ↔ m % 25 = 24) ∧
      (∀ m, (∃ n, m = 125 * n + 124) ↔ m % 125 = 124) ∧
      (∀ m, (∃ n, m = 625 * n + 624) ↔ m % 625 = 624) ∧
      (∀ m, (∃ n, m = 3125 * n + 3124) ↔ m % 3125 = 3124) := by
  exact ⟨exists_mod25_progression_iff_mod_eq_24,
    exists_mod125_progression_iff_mod_eq_124,
    exists_mod625_progression_iff_mod_eq_624,
    exists_mod3125_progression_iff_mod_eq_3124⟩

/-- Concrete higher-power mod-7 progression membership facts. -/
theorem concrete_mod7_power_membership_iff_residue_facts :
    (∀ m, (∃ n, m = 49 * n + 47) ↔ m % 49 = 47) ∧
      (∀ m, (∃ n, m = 343 * n + 341) ↔ m % 343 = 341) ∧
      (∀ m, (∃ n, m = 2401 * n + 2399) ↔ m % 2401 = 2399) ∧
      (∀ m, (∃ n, m = 16807 * n + 16805) ↔ m % 16807 = 16805) := by
  exact ⟨exists_mod49_progression_iff_mod_eq_47,
    exists_mod343_progression_iff_mod_eq_341,
    exists_mod2401_progression_iff_mod_eq_2399,
    exists_mod16807_progression_iff_mod_eq_16805⟩

/-- Concrete higher-power mod-11 progression membership facts. -/
theorem concrete_mod11_power_membership_iff_residue_facts :
    (∀ m, (∃ n, m = 121 * n + 116) ↔ m % 121 = 116) ∧
      (∀ m, (∃ n, m = 1331 * n + 1326) ↔ m % 1331 = 1326) ∧
      (∀ m, (∃ n, m = 14641 * n + 14636) ↔ m % 14641 = 14636) ∧
      (∀ m, (∃ n, m = 161051 * n + 161046) ↔
        m % 161051 = 161046) := by
  exact ⟨exists_mod121_progression_iff_mod_eq_116,
    exists_mod1331_progression_iff_mod_eq_1326,
    exists_mod14641_progression_iff_mod_eq_14636,
    exists_mod161051_progression_iff_mod_eq_161046⟩

/-- Divide an expression known to be `5*y+4` by `5`. -/
theorem div_by_5_eq_of_eq_five_mul_add_four {x y : ℕ} (h : x = 5 * y + 4) :
    x / 5 = y := by
  have h0 := (Nat.mod_add_div x 5).symm
  have hm : x % 5 = 4 := by
    rw [h]
    omega
  omega

/-- Divide an expression known to be `7*y+5` by `7`. -/
theorem div_by_7_eq_of_eq_seven_mul_add_five {x y : ℕ} (h : x = 7 * y + 5) :
    x / 7 = y := by
  have h0 := (Nat.mod_add_div x 7).symm
  have hm : x % 7 = 5 := by
    rw [h]
    omega
  omega

/-- Divide an expression known to be `11*y+6` by `11`. -/
theorem div_by_11_eq_of_eq_eleven_mul_add_six {x y : ℕ}
    (h : x = 11 * y + 6) :
    x / 11 = y := by
  have h0 := (Nat.mod_add_div x 11).symm
  have hm : x % 11 = 6 := by
    rw [h]
    omega
  omega

/-- Dropping the terminal `4 mod 5` digit from `25n+24`. -/
theorem div_25n_plus_24_by_5_eq_5n_plus_4 (n : ℕ) :
    (25 * n + 24) / 5 = 5 * n + 4 := by
  exact div_by_5_eq_of_eq_five_mul_add_four (by omega)

/-- Dropping the terminal `4 mod 5` digit from `125n+124`. -/
theorem div_125n_plus_124_by_5_eq_25n_plus_24 (n : ℕ) :
    (125 * n + 124) / 5 = 25 * n + 24 := by
  exact div_by_5_eq_of_eq_five_mul_add_four (by omega)

/-- Dropping the terminal `4 mod 5` digit from `625n+624`. -/
theorem div_625n_plus_624_by_5_eq_125n_plus_124 (n : ℕ) :
    (625 * n + 624) / 5 = 125 * n + 124 := by
  exact div_by_5_eq_of_eq_five_mul_add_four (by omega)

/-- Dropping the terminal `4 mod 5` digit from `3125n+3124`. -/
theorem div_3125n_plus_3124_by_5_eq_625n_plus_624 (n : ℕ) :
    (3125 * n + 3124) / 5 = 625 * n + 624 := by
  exact div_by_5_eq_of_eq_five_mul_add_four (by omega)

/-- Dropping the terminal `5 mod 7` digit from `49n+47`. -/
theorem div_49n_plus_47_by_7_eq_7n_plus_6 (n : ℕ) :
    (49 * n + 47) / 7 = 7 * n + 6 := by
  exact div_by_7_eq_of_eq_seven_mul_add_five (by omega)

/-- Dropping the terminal `5 mod 7` digit from `343n+341`. -/
theorem div_343n_plus_341_by_7_eq_49n_plus_48 (n : ℕ) :
    (343 * n + 341) / 7 = 49 * n + 48 := by
  exact div_by_7_eq_of_eq_seven_mul_add_five (by omega)

/-- Dropping the terminal `5 mod 7` digit from `2401n+2399`. -/
theorem div_2401n_plus_2399_by_7_eq_343n_plus_342 (n : ℕ) :
    (2401 * n + 2399) / 7 = 343 * n + 342 := by
  exact div_by_7_eq_of_eq_seven_mul_add_five (by omega)

/-- Dropping the terminal `5 mod 7` digit from `16807n+16805`. -/
theorem div_16807n_plus_16805_by_7_eq_2401n_plus_2400 (n : ℕ) :
    (16807 * n + 16805) / 7 = 2401 * n + 2400 := by
  exact div_by_7_eq_of_eq_seven_mul_add_five (by omega)

/-- Dropping the terminal `6 mod 11` digit from `121n+116`. -/
theorem div_121n_plus_116_by_11_eq_11n_plus_10 (n : ℕ) :
    (121 * n + 116) / 11 = 11 * n + 10 := by
  exact div_by_11_eq_of_eq_eleven_mul_add_six (by omega)

/-- Dropping the terminal `6 mod 11` digit from `1331n+1326`. -/
theorem div_1331n_plus_1326_by_11_eq_121n_plus_120 (n : ℕ) :
    (1331 * n + 1326) / 11 = 121 * n + 120 := by
  exact div_by_11_eq_of_eq_eleven_mul_add_six (by omega)

/-- Dropping the terminal `6 mod 11` digit from `14641n+14636`. -/
theorem div_14641n_plus_14636_by_11_eq_1331n_plus_1330 (n : ℕ) :
    (14641 * n + 14636) / 11 = 1331 * n + 1330 := by
  exact div_by_11_eq_of_eq_eleven_mul_add_six (by omega)

/-- Dropping the terminal `6 mod 11` digit from `161051n+161046`. -/
theorem div_161051n_plus_161046_by_11_eq_14641n_plus_14640 (n : ℕ) :
    (161051 * n + 161046) / 11 = 14641 * n + 14640 := by
  exact div_by_11_eq_of_eq_eleven_mul_add_six (by omega)

/-- Dividing a full concrete mod-5 period recovers the parameter. -/
theorem div_25n_plus_24_by_25_eq_n (n : ℕ) :
    (25 * n + 24) / 25 = n := by
  have h := (Nat.mod_add_div (25 * n + 24) 25).symm
  have hm := mod_25n_plus_24_eq_24 n
  omega

/-- Dividing a full concrete mod-5 period recovers the parameter. -/
theorem div_125n_plus_124_by_125_eq_n (n : ℕ) :
    (125 * n + 124) / 125 = n := by
  have h := (Nat.mod_add_div (125 * n + 124) 125).symm
  have hm := mod_125n_plus_124_eq_124 n
  omega

/-- Dividing a full concrete mod-5 period recovers the parameter. -/
theorem div_625n_plus_624_by_625_eq_n (n : ℕ) :
    (625 * n + 624) / 625 = n := by
  have h := (Nat.mod_add_div (625 * n + 624) 625).symm
  have hm := mod_625n_plus_624_eq_624 n
  omega

/-- Dividing a full concrete mod-5 period recovers the parameter. -/
theorem div_3125n_plus_3124_by_3125_eq_n (n : ℕ) :
    (3125 * n + 3124) / 3125 = n := by
  have h := (Nat.mod_add_div (3125 * n + 3124) 3125).symm
  have hm := mod_3125n_plus_3124_eq_3124 n
  omega

/-- Dividing a full concrete mod-7 period recovers the parameter. -/
theorem div_49n_plus_47_by_49_eq_n (n : ℕ) :
    (49 * n + 47) / 49 = n := by
  have h := (Nat.mod_add_div (49 * n + 47) 49).symm
  have hm := mod_49n_plus_47_eq_47 n
  omega

/-- Dividing a full concrete mod-7 period recovers the parameter. -/
theorem div_343n_plus_341_by_343_eq_n (n : ℕ) :
    (343 * n + 341) / 343 = n := by
  have h := (Nat.mod_add_div (343 * n + 341) 343).symm
  have hm := mod_343n_plus_341_eq_341 n
  omega

/-- Dividing a full concrete mod-7 period recovers the parameter. -/
theorem div_2401n_plus_2399_by_2401_eq_n (n : ℕ) :
    (2401 * n + 2399) / 2401 = n := by
  have h := (Nat.mod_add_div (2401 * n + 2399) 2401).symm
  have hm := mod_2401n_plus_2399_eq_2399 n
  omega

/-- Dividing a full concrete mod-7 period recovers the parameter. -/
theorem div_16807n_plus_16805_by_16807_eq_n (n : ℕ) :
    (16807 * n + 16805) / 16807 = n := by
  have h := (Nat.mod_add_div (16807 * n + 16805) 16807).symm
  have hm := mod_16807n_plus_16805_eq_16805 n
  omega

/-- Dividing a full concrete mod-11 period recovers the parameter. -/
theorem div_121n_plus_116_by_121_eq_n (n : ℕ) :
    (121 * n + 116) / 121 = n := by
  have h := (Nat.mod_add_div (121 * n + 116) 121).symm
  have hm := mod_121n_plus_116_eq_116 n
  omega

/-- Dividing a full concrete mod-11 period recovers the parameter. -/
theorem div_1331n_plus_1326_by_1331_eq_n (n : ℕ) :
    (1331 * n + 1326) / 1331 = n := by
  have h := (Nat.mod_add_div (1331 * n + 1326) 1331).symm
  have hm := mod_1331n_plus_1326_eq_1326 n
  omega

/-- Dividing a full concrete mod-11 period recovers the parameter. -/
theorem div_14641n_plus_14636_by_14641_eq_n (n : ℕ) :
    (14641 * n + 14636) / 14641 = n := by
  have h := (Nat.mod_add_div (14641 * n + 14636) 14641).symm
  have hm := mod_14641n_plus_14636_eq_14636 n
  omega

/-- Dividing a full concrete mod-11 period recovers the parameter. -/
theorem div_161051n_plus_161046_by_161051_eq_n (n : ℕ) :
    (161051 * n + 161046) / 161051 = n := by
  have h := (Nat.mod_add_div (161051 * n + 161046) 161051).symm
  have hm := mod_161051n_plus_161046_eq_161046 n
  omega

/-- Terminal-digit quotient facts for the concrete higher-power progressions. -/
theorem concrete_power_div_by_base_facts :
    (∀ n, (25 * n + 24) / 5 = 5 * n + 4) ∧
      (∀ n, (125 * n + 124) / 5 = 25 * n + 24) ∧
      (∀ n, (625 * n + 624) / 5 = 125 * n + 124) ∧
      (∀ n, (3125 * n + 3124) / 5 = 625 * n + 624) ∧
      (∀ n, (49 * n + 47) / 7 = 7 * n + 6) ∧
      (∀ n, (343 * n + 341) / 7 = 49 * n + 48) ∧
      (∀ n, (2401 * n + 2399) / 7 = 343 * n + 342) ∧
      (∀ n, (16807 * n + 16805) / 7 = 2401 * n + 2400) ∧
      (∀ n, (121 * n + 116) / 11 = 11 * n + 10) ∧
      (∀ n, (1331 * n + 1326) / 11 = 121 * n + 120) ∧
      (∀ n, (14641 * n + 14636) / 11 = 1331 * n + 1330) ∧
      (∀ n, (161051 * n + 161046) / 11 = 14641 * n + 14640) := by
  exact ⟨div_25n_plus_24_by_5_eq_5n_plus_4,
    div_125n_plus_124_by_5_eq_25n_plus_24,
    div_625n_plus_624_by_5_eq_125n_plus_124,
    div_3125n_plus_3124_by_5_eq_625n_plus_624,
    div_49n_plus_47_by_7_eq_7n_plus_6,
    div_343n_plus_341_by_7_eq_49n_plus_48,
    div_2401n_plus_2399_by_7_eq_343n_plus_342,
    div_16807n_plus_16805_by_7_eq_2401n_plus_2400,
    div_121n_plus_116_by_11_eq_11n_plus_10,
    div_1331n_plus_1326_by_11_eq_121n_plus_120,
    div_14641n_plus_14636_by_11_eq_1331n_plus_1330,
    div_161051n_plus_161046_by_11_eq_14641n_plus_14640⟩

/-- Full-period quotient facts for the concrete higher-power progressions. -/
theorem concrete_power_full_period_division_facts :
    (∀ n, (25 * n + 24) / 25 = n) ∧
      (∀ n, (125 * n + 124) / 125 = n) ∧
      (∀ n, (625 * n + 624) / 625 = n) ∧
      (∀ n, (3125 * n + 3124) / 3125 = n) ∧
      (∀ n, (49 * n + 47) / 49 = n) ∧
      (∀ n, (343 * n + 341) / 343 = n) ∧
      (∀ n, (2401 * n + 2399) / 2401 = n) ∧
      (∀ n, (16807 * n + 16805) / 16807 = n) ∧
      (∀ n, (121 * n + 116) / 121 = n) ∧
      (∀ n, (1331 * n + 1326) / 1331 = n) ∧
      (∀ n, (14641 * n + 14636) / 14641 = n) ∧
      (∀ n, (161051 * n + 161046) / 161051 = n) := by
  exact ⟨div_25n_plus_24_by_25_eq_n,
    div_125n_plus_124_by_125_eq_n,
    div_625n_plus_624_by_625_eq_n,
    div_3125n_plus_3124_by_3125_eq_n,
    div_49n_plus_47_by_49_eq_n,
    div_343n_plus_341_by_343_eq_n,
    div_2401n_plus_2399_by_2401_eq_n,
    div_16807n_plus_16805_by_16807_eq_n,
    div_121n_plus_116_by_121_eq_n,
    div_1331n_plus_1326_by_1331_eq_n,
    div_14641n_plus_14636_by_14641_eq_n,
    div_161051n_plus_161046_by_161051_eq_n⟩

/-- Divide by `q` after rewriting into quotient-plus-remainder form. -/
theorem div_eq_of_eq_mul_add_of_lt {x q y r : ℕ}
    (h : x = q * y + r) (hr : r < q) :
    x / q = y := by
  apply Nat.div_eq_of_lt_le
  · rw [h]
    nlinarith
  · rw [h]
    nlinarith

/-- Intermediate quotient from `125n+124` down to the base mod-5 progression. -/
theorem div_125n_plus_124_by_25_eq_5n_plus_4 (n : ℕ) :
    (125 * n + 124) / 25 = 5 * n + 4 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 125 * n + 124) (q := 25) (y := 5 * n + 4) (r := 24)
    (by omega) (by decide)

/-- Intermediate quotient from `625n+624` to the one-level concrete mod-5
progression. -/
theorem div_625n_plus_624_by_25_eq_25n_plus_24 (n : ℕ) :
    (625 * n + 624) / 25 = 25 * n + 24 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 625 * n + 624) (q := 25) (y := 25 * n + 24) (r := 24)
    (by omega) (by decide)

/-- Intermediate quotient from `625n+624` down to the base mod-5 progression. -/
theorem div_625n_plus_624_by_125_eq_5n_plus_4 (n : ℕ) :
    (625 * n + 624) / 125 = 5 * n + 4 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 625 * n + 624) (q := 125) (y := 5 * n + 4) (r := 124)
    (by omega) (by decide)

/-- Intermediate quotient from `3125n+3124` to the two-level concrete mod-5
progression. -/
theorem div_3125n_plus_3124_by_25_eq_125n_plus_124 (n : ℕ) :
    (3125 * n + 3124) / 25 = 125 * n + 124 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 3125 * n + 3124) (q := 25) (y := 125 * n + 124) (r := 24)
    (by omega) (by decide)

/-- Intermediate quotient from `3125n+3124` to the one-level concrete mod-5
progression. -/
theorem div_3125n_plus_3124_by_125_eq_25n_plus_24 (n : ℕ) :
    (3125 * n + 3124) / 125 = 25 * n + 24 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 3125 * n + 3124) (q := 125) (y := 25 * n + 24) (r := 124)
    (by omega) (by decide)

/-- Intermediate quotient from `3125n+3124` down to the base mod-5
progression. -/
theorem div_3125n_plus_3124_by_625_eq_5n_plus_4 (n : ℕ) :
    (3125 * n + 3124) / 625 = 5 * n + 4 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 3125 * n + 3124) (q := 625) (y := 5 * n + 4) (r := 624)
    (by omega) (by decide)

/-- Intermediate quotient from `343n+341` down to the base mod-7 progression. -/
theorem div_343n_plus_341_by_49_eq_7n_plus_6 (n : ℕ) :
    (343 * n + 341) / 49 = 7 * n + 6 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 343 * n + 341) (q := 49) (y := 7 * n + 6) (r := 47)
    (by omega) (by decide)

/-- Intermediate quotient from `2401n+2399` to the one-level concrete mod-7
progression. -/
theorem div_2401n_plus_2399_by_49_eq_49n_plus_48 (n : ℕ) :
    (2401 * n + 2399) / 49 = 49 * n + 48 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 2401 * n + 2399) (q := 49) (y := 49 * n + 48) (r := 47)
    (by omega) (by decide)

/-- Intermediate quotient from `2401n+2399` down to the base mod-7 progression. -/
theorem div_2401n_plus_2399_by_343_eq_7n_plus_6 (n : ℕ) :
    (2401 * n + 2399) / 343 = 7 * n + 6 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 2401 * n + 2399) (q := 343) (y := 7 * n + 6) (r := 341)
    (by omega) (by decide)

/-- Intermediate quotient from `16807n+16805` to the two-level concrete mod-7
progression. -/
theorem div_16807n_plus_16805_by_49_eq_343n_plus_342 (n : ℕ) :
    (16807 * n + 16805) / 49 = 343 * n + 342 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 16807 * n + 16805) (q := 49) (y := 343 * n + 342) (r := 47)
    (by omega) (by decide)

/-- Intermediate quotient from `16807n+16805` to the one-level concrete mod-7
progression. -/
theorem div_16807n_plus_16805_by_343_eq_49n_plus_48 (n : ℕ) :
    (16807 * n + 16805) / 343 = 49 * n + 48 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 16807 * n + 16805) (q := 343) (y := 49 * n + 48) (r := 341)
    (by omega) (by decide)

/-- Intermediate quotient from `16807n+16805` down to the base mod-7
progression. -/
theorem div_16807n_plus_16805_by_2401_eq_7n_plus_6 (n : ℕ) :
    (16807 * n + 16805) / 2401 = 7 * n + 6 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 16807 * n + 16805) (q := 2401) (y := 7 * n + 6) (r := 2399)
    (by omega) (by decide)

/-- Intermediate quotient from `1331n+1326` down to the base mod-11
progression. -/
theorem div_1331n_plus_1326_by_121_eq_11n_plus_10 (n : ℕ) :
    (1331 * n + 1326) / 121 = 11 * n + 10 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 1331 * n + 1326) (q := 121) (y := 11 * n + 10) (r := 116)
    (by omega) (by decide)

/-- Intermediate quotient from `14641n+14636` to the one-level concrete mod-11
progression. -/
theorem div_14641n_plus_14636_by_121_eq_121n_plus_120 (n : ℕ) :
    (14641 * n + 14636) / 121 = 121 * n + 120 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 14641 * n + 14636) (q := 121) (y := 121 * n + 120) (r := 116)
    (by omega) (by decide)

/-- Intermediate quotient from `14641n+14636` down to the base mod-11
progression. -/
theorem div_14641n_plus_14636_by_1331_eq_11n_plus_10 (n : ℕ) :
    (14641 * n + 14636) / 1331 = 11 * n + 10 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 14641 * n + 14636) (q := 1331) (y := 11 * n + 10) (r := 1326)
    (by omega) (by decide)

/-- Intermediate quotient from `161051n+161046` to the two-level concrete
mod-11 progression. -/
theorem div_161051n_plus_161046_by_121_eq_1331n_plus_1330 (n : ℕ) :
    (161051 * n + 161046) / 121 = 1331 * n + 1330 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 161051 * n + 161046) (q := 121) (y := 1331 * n + 1330) (r := 116)
    (by omega) (by decide)

/-- Intermediate quotient from `161051n+161046` to the one-level concrete
mod-11 progression. -/
theorem div_161051n_plus_161046_by_1331_eq_121n_plus_120 (n : ℕ) :
    (161051 * n + 161046) / 1331 = 121 * n + 120 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 161051 * n + 161046) (q := 1331) (y := 121 * n + 120) (r := 1326)
    (by omega) (by decide)

/-- Intermediate quotient from `161051n+161046` down to the base mod-11
progression. -/
theorem div_161051n_plus_161046_by_14641_eq_11n_plus_10 (n : ℕ) :
    (161051 * n + 161046) / 14641 = 11 * n + 10 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := 161051 * n + 161046) (q := 14641) (y := 11 * n + 10) (r := 14636)
    (by omega) (by decide)

/-- Intermediate quotient facts for concrete higher-power mod-5 progressions. -/
theorem concrete_mod5_power_intermediate_division_facts :
    (∀ n, (125 * n + 124) / 25 = 5 * n + 4) ∧
      (∀ n, (625 * n + 624) / 25 = 25 * n + 24) ∧
      (∀ n, (625 * n + 624) / 125 = 5 * n + 4) ∧
      (∀ n, (3125 * n + 3124) / 25 = 125 * n + 124) ∧
      (∀ n, (3125 * n + 3124) / 125 = 25 * n + 24) ∧
      (∀ n, (3125 * n + 3124) / 625 = 5 * n + 4) := by
  exact ⟨div_125n_plus_124_by_25_eq_5n_plus_4,
    div_625n_plus_624_by_25_eq_25n_plus_24,
    div_625n_plus_624_by_125_eq_5n_plus_4,
    div_3125n_plus_3124_by_25_eq_125n_plus_124,
    div_3125n_plus_3124_by_125_eq_25n_plus_24,
    div_3125n_plus_3124_by_625_eq_5n_plus_4⟩

/-- Intermediate quotient facts for concrete higher-power mod-7 progressions. -/
theorem concrete_mod7_power_intermediate_division_facts :
    (∀ n, (343 * n + 341) / 49 = 7 * n + 6) ∧
      (∀ n, (2401 * n + 2399) / 49 = 49 * n + 48) ∧
      (∀ n, (2401 * n + 2399) / 343 = 7 * n + 6) ∧
      (∀ n, (16807 * n + 16805) / 49 = 343 * n + 342) ∧
      (∀ n, (16807 * n + 16805) / 343 = 49 * n + 48) ∧
      (∀ n, (16807 * n + 16805) / 2401 = 7 * n + 6) := by
  exact ⟨div_343n_plus_341_by_49_eq_7n_plus_6,
    div_2401n_plus_2399_by_49_eq_49n_plus_48,
    div_2401n_plus_2399_by_343_eq_7n_plus_6,
    div_16807n_plus_16805_by_49_eq_343n_plus_342,
    div_16807n_plus_16805_by_343_eq_49n_plus_48,
    div_16807n_plus_16805_by_2401_eq_7n_plus_6⟩

/-- Intermediate quotient facts for concrete higher-power mod-11 progressions. -/
theorem concrete_mod11_power_intermediate_division_facts :
    (∀ n, (1331 * n + 1326) / 121 = 11 * n + 10) ∧
      (∀ n, (14641 * n + 14636) / 121 = 121 * n + 120) ∧
      (∀ n, (14641 * n + 14636) / 1331 = 11 * n + 10) ∧
      (∀ n, (161051 * n + 161046) / 121 = 1331 * n + 1330) ∧
      (∀ n, (161051 * n + 161046) / 1331 = 121 * n + 120) ∧
      (∀ n, (161051 * n + 161046) / 14641 = 11 * n + 10) := by
  exact ⟨div_1331n_plus_1326_by_121_eq_11n_plus_10,
    div_14641n_plus_14636_by_121_eq_121n_plus_120,
    div_14641n_plus_14636_by_1331_eq_11n_plus_10,
    div_161051n_plus_161046_by_121_eq_1331n_plus_1330,
    div_161051n_plus_161046_by_1331_eq_121n_plus_120,
    div_161051n_plus_161046_by_14641_eq_11n_plus_10⟩

/-- Project a known residue modulo a product to the right factor. -/
theorem mod_eq_mod_of_mod_mul_eq {m a b r : ℕ} (h : m % (a * b) = r) :
    m % b = r % b := by
  have h0 := Nat.mod_mul_left_mod m a b
  rw [h] at h0
  exact h0.symm

/-- A `24 mod 25` residue projects to `4 mod 5`. -/
theorem mod_25_eq_24_implies_mod_5_eq_4 {m : ℕ} (hm : m % 25 = 24) :
    m % 5 = 4 := by
  have h : m % (5 * 5) = 24 := by
    simpa using hm
  have hproj := mod_eq_mod_of_mod_mul_eq (m := m) (a := 5) (b := 5) (r := 24) h
  norm_num at hproj
  exact hproj

/-- A `124 mod 125` residue projects to `24 mod 25`. -/
theorem mod_125_eq_124_implies_mod_25_eq_24 {m : ℕ} (hm : m % 125 = 124) :
    m % 25 = 24 := by
  have h : m % (5 * 25) = 124 := by
    simpa using hm
  have hproj := mod_eq_mod_of_mod_mul_eq (m := m) (a := 5) (b := 25) (r := 124) h
  norm_num at hproj
  exact hproj

/-- A `124 mod 125` residue projects to `4 mod 5`. -/
theorem mod_125_eq_124_implies_mod_5_eq_4 {m : ℕ} (hm : m % 125 = 124) :
    m % 5 = 4 := by
  exact mod_25_eq_24_implies_mod_5_eq_4
    (mod_125_eq_124_implies_mod_25_eq_24 hm)

/-- A `624 mod 625` residue projects to `124 mod 125`. -/
theorem mod_625_eq_624_implies_mod_125_eq_124 {m : ℕ} (hm : m % 625 = 624) :
    m % 125 = 124 := by
  have h : m % (5 * 125) = 624 := by
    simpa using hm
  have hproj := mod_eq_mod_of_mod_mul_eq (m := m) (a := 5) (b := 125) (r := 624) h
  norm_num at hproj
  exact hproj

/-- A `624 mod 625` residue projects to `24 mod 25`. -/
theorem mod_625_eq_624_implies_mod_25_eq_24 {m : ℕ} (hm : m % 625 = 624) :
    m % 25 = 24 := by
  exact mod_125_eq_124_implies_mod_25_eq_24
    (mod_625_eq_624_implies_mod_125_eq_124 hm)

/-- A `624 mod 625` residue projects to `4 mod 5`. -/
theorem mod_625_eq_624_implies_mod_5_eq_4 {m : ℕ} (hm : m % 625 = 624) :
    m % 5 = 4 := by
  exact mod_125_eq_124_implies_mod_5_eq_4
    (mod_625_eq_624_implies_mod_125_eq_124 hm)

/-- A `3124 mod 3125` residue projects to `624 mod 625`. -/
theorem mod_3125_eq_3124_implies_mod_625_eq_624 {m : ℕ}
    (hm : m % 3125 = 3124) :
    m % 625 = 624 := by
  have h : m % (5 * 625) = 3124 := by
    simpa using hm
  have hproj := mod_eq_mod_of_mod_mul_eq (m := m) (a := 5) (b := 625)
    (r := 3124) h
  norm_num at hproj
  exact hproj

/-- A `3124 mod 3125` residue projects to `124 mod 125`. -/
theorem mod_3125_eq_3124_implies_mod_125_eq_124 {m : ℕ}
    (hm : m % 3125 = 3124) :
    m % 125 = 124 := by
  exact mod_625_eq_624_implies_mod_125_eq_124
    (mod_3125_eq_3124_implies_mod_625_eq_624 hm)

/-- A `3124 mod 3125` residue projects to `24 mod 25`. -/
theorem mod_3125_eq_3124_implies_mod_25_eq_24 {m : ℕ}
    (hm : m % 3125 = 3124) :
    m % 25 = 24 := by
  exact mod_625_eq_624_implies_mod_25_eq_24
    (mod_3125_eq_3124_implies_mod_625_eq_624 hm)

/-- A `3124 mod 3125` residue projects to `4 mod 5`. -/
theorem mod_3125_eq_3124_implies_mod_5_eq_4 {m : ℕ}
    (hm : m % 3125 = 3124) :
    m % 5 = 4 := by
  exact mod_625_eq_624_implies_mod_5_eq_4
    (mod_3125_eq_3124_implies_mod_625_eq_624 hm)

/-- A `47 mod 49` residue projects to `5 mod 7`. -/
theorem mod_49_eq_47_implies_mod_7_eq_5 {m : ℕ} (hm : m % 49 = 47) :
    m % 7 = 5 := by
  have h : m % (7 * 7) = 47 := by
    simpa using hm
  have hproj := mod_eq_mod_of_mod_mul_eq (m := m) (a := 7) (b := 7) (r := 47) h
  norm_num at hproj
  exact hproj

/-- A `341 mod 343` residue projects to `47 mod 49`. -/
theorem mod_343_eq_341_implies_mod_49_eq_47 {m : ℕ} (hm : m % 343 = 341) :
    m % 49 = 47 := by
  have h : m % (7 * 49) = 341 := by
    simpa using hm
  have hproj := mod_eq_mod_of_mod_mul_eq (m := m) (a := 7) (b := 49) (r := 341) h
  norm_num at hproj
  exact hproj

/-- A `341 mod 343` residue projects to `5 mod 7`. -/
theorem mod_343_eq_341_implies_mod_7_eq_5 {m : ℕ} (hm : m % 343 = 341) :
    m % 7 = 5 := by
  exact mod_49_eq_47_implies_mod_7_eq_5
    (mod_343_eq_341_implies_mod_49_eq_47 hm)

/-- A `2399 mod 2401` residue projects to `341 mod 343`. -/
theorem mod_2401_eq_2399_implies_mod_343_eq_341 {m : ℕ}
    (hm : m % 2401 = 2399) :
    m % 343 = 341 := by
  have h : m % (7 * 343) = 2399 := by
    simpa using hm
  have hproj := mod_eq_mod_of_mod_mul_eq (m := m) (a := 7) (b := 343)
    (r := 2399) h
  norm_num at hproj
  exact hproj

/-- A `2399 mod 2401` residue projects to `47 mod 49`. -/
theorem mod_2401_eq_2399_implies_mod_49_eq_47 {m : ℕ}
    (hm : m % 2401 = 2399) :
    m % 49 = 47 := by
  exact mod_343_eq_341_implies_mod_49_eq_47
    (mod_2401_eq_2399_implies_mod_343_eq_341 hm)

/-- A `2399 mod 2401` residue projects to `5 mod 7`. -/
theorem mod_2401_eq_2399_implies_mod_7_eq_5 {m : ℕ}
    (hm : m % 2401 = 2399) :
    m % 7 = 5 := by
  exact mod_343_eq_341_implies_mod_7_eq_5
    (mod_2401_eq_2399_implies_mod_343_eq_341 hm)

/-- A `16805 mod 16807` residue projects to `2399 mod 2401`. -/
theorem mod_16807_eq_16805_implies_mod_2401_eq_2399 {m : ℕ}
    (hm : m % 16807 = 16805) :
    m % 2401 = 2399 := by
  have h : m % (7 * 2401) = 16805 := by
    simpa using hm
  have hproj := mod_eq_mod_of_mod_mul_eq (m := m) (a := 7) (b := 2401)
    (r := 16805) h
  norm_num at hproj
  exact hproj

/-- A `16805 mod 16807` residue projects to `341 mod 343`. -/
theorem mod_16807_eq_16805_implies_mod_343_eq_341 {m : ℕ}
    (hm : m % 16807 = 16805) :
    m % 343 = 341 := by
  exact mod_2401_eq_2399_implies_mod_343_eq_341
    (mod_16807_eq_16805_implies_mod_2401_eq_2399 hm)

/-- A `16805 mod 16807` residue projects to `47 mod 49`. -/
theorem mod_16807_eq_16805_implies_mod_49_eq_47 {m : ℕ}
    (hm : m % 16807 = 16805) :
    m % 49 = 47 := by
  exact mod_2401_eq_2399_implies_mod_49_eq_47
    (mod_16807_eq_16805_implies_mod_2401_eq_2399 hm)

/-- A `16805 mod 16807` residue projects to `5 mod 7`. -/
theorem mod_16807_eq_16805_implies_mod_7_eq_5 {m : ℕ}
    (hm : m % 16807 = 16805) :
    m % 7 = 5 := by
  exact mod_2401_eq_2399_implies_mod_7_eq_5
    (mod_16807_eq_16805_implies_mod_2401_eq_2399 hm)

/-- A `116 mod 121` residue projects to `6 mod 11`. -/
theorem mod_121_eq_116_implies_mod_11_eq_6 {m : ℕ} (hm : m % 121 = 116) :
    m % 11 = 6 := by
  have h : m % (11 * 11) = 116 := by
    simpa using hm
  have hproj := mod_eq_mod_of_mod_mul_eq (m := m) (a := 11) (b := 11)
    (r := 116) h
  norm_num at hproj
  exact hproj

/-- A `1326 mod 1331` residue projects to `116 mod 121`. -/
theorem mod_1331_eq_1326_implies_mod_121_eq_116 {m : ℕ}
    (hm : m % 1331 = 1326) :
    m % 121 = 116 := by
  have h : m % (11 * 121) = 1326 := by
    simpa using hm
  have hproj := mod_eq_mod_of_mod_mul_eq (m := m) (a := 11) (b := 121)
    (r := 1326) h
  norm_num at hproj
  exact hproj

/-- A `1326 mod 1331` residue projects to `6 mod 11`. -/
theorem mod_1331_eq_1326_implies_mod_11_eq_6 {m : ℕ}
    (hm : m % 1331 = 1326) :
    m % 11 = 6 := by
  exact mod_121_eq_116_implies_mod_11_eq_6
    (mod_1331_eq_1326_implies_mod_121_eq_116 hm)

/-- A `14636 mod 14641` residue projects to `1326 mod 1331`. -/
theorem mod_14641_eq_14636_implies_mod_1331_eq_1326 {m : ℕ}
    (hm : m % 14641 = 14636) :
    m % 1331 = 1326 := by
  have h : m % (11 * 1331) = 14636 := by
    simpa using hm
  have hproj := mod_eq_mod_of_mod_mul_eq (m := m) (a := 11) (b := 1331)
    (r := 14636) h
  norm_num at hproj
  exact hproj

/-- A `14636 mod 14641` residue projects to `116 mod 121`. -/
theorem mod_14641_eq_14636_implies_mod_121_eq_116 {m : ℕ}
    (hm : m % 14641 = 14636) :
    m % 121 = 116 := by
  exact mod_1331_eq_1326_implies_mod_121_eq_116
    (mod_14641_eq_14636_implies_mod_1331_eq_1326 hm)

/-- A `14636 mod 14641` residue projects to `6 mod 11`. -/
theorem mod_14641_eq_14636_implies_mod_11_eq_6 {m : ℕ}
    (hm : m % 14641 = 14636) :
    m % 11 = 6 := by
  exact mod_1331_eq_1326_implies_mod_11_eq_6
    (mod_14641_eq_14636_implies_mod_1331_eq_1326 hm)

/-- A `161046 mod 161051` residue projects to `14636 mod 14641`. -/
theorem mod_161051_eq_161046_implies_mod_14641_eq_14636 {m : ℕ}
    (hm : m % 161051 = 161046) :
    m % 14641 = 14636 := by
  have h : m % (11 * 14641) = 161046 := by
    simpa using hm
  have hproj := mod_eq_mod_of_mod_mul_eq (m := m) (a := 11) (b := 14641)
    (r := 161046) h
  norm_num at hproj
  exact hproj

/-- A `161046 mod 161051` residue projects to `1326 mod 1331`. -/
theorem mod_161051_eq_161046_implies_mod_1331_eq_1326 {m : ℕ}
    (hm : m % 161051 = 161046) :
    m % 1331 = 1326 := by
  exact mod_14641_eq_14636_implies_mod_1331_eq_1326
    (mod_161051_eq_161046_implies_mod_14641_eq_14636 hm)

/-- A `161046 mod 161051` residue projects to `116 mod 121`. -/
theorem mod_161051_eq_161046_implies_mod_121_eq_116 {m : ℕ}
    (hm : m % 161051 = 161046) :
    m % 121 = 116 := by
  exact mod_14641_eq_14636_implies_mod_121_eq_116
    (mod_161051_eq_161046_implies_mod_14641_eq_14636 hm)

/-- A `161046 mod 161051` residue projects to `6 mod 11`. -/
theorem mod_161051_eq_161046_implies_mod_11_eq_6 {m : ℕ}
    (hm : m % 161051 = 161046) :
    m % 11 = 6 := by
  exact mod_14641_eq_14636_implies_mod_11_eq_6
    (mod_161051_eq_161046_implies_mod_14641_eq_14636 hm)

/-- Projection facts for concrete higher-power mod-5 residues. -/
theorem concrete_mod5_power_residue_projection_facts :
    (∀ m, m % 25 = 24 → m % 5 = 4) ∧
      (∀ m, m % 125 = 124 → m % 25 = 24) ∧
      (∀ m, m % 125 = 124 → m % 5 = 4) ∧
      (∀ m, m % 625 = 624 → m % 125 = 124) ∧
      (∀ m, m % 625 = 624 → m % 25 = 24) ∧
      (∀ m, m % 625 = 624 → m % 5 = 4) ∧
      (∀ m, m % 3125 = 3124 → m % 625 = 624) ∧
      (∀ m, m % 3125 = 3124 → m % 125 = 124) ∧
      (∀ m, m % 3125 = 3124 → m % 25 = 24) ∧
      (∀ m, m % 3125 = 3124 → m % 5 = 4) := by
  exact ⟨fun _ => mod_25_eq_24_implies_mod_5_eq_4,
    fun _ => mod_125_eq_124_implies_mod_25_eq_24,
    fun _ => mod_125_eq_124_implies_mod_5_eq_4,
    fun _ => mod_625_eq_624_implies_mod_125_eq_124,
    fun _ => mod_625_eq_624_implies_mod_25_eq_24,
    fun _ => mod_625_eq_624_implies_mod_5_eq_4,
    fun _ => mod_3125_eq_3124_implies_mod_625_eq_624,
    fun _ => mod_3125_eq_3124_implies_mod_125_eq_124,
    fun _ => mod_3125_eq_3124_implies_mod_25_eq_24,
    fun _ => mod_3125_eq_3124_implies_mod_5_eq_4⟩

/-- Projection facts for concrete higher-power mod-7 residues. -/
theorem concrete_mod7_power_residue_projection_facts :
    (∀ m, m % 49 = 47 → m % 7 = 5) ∧
      (∀ m, m % 343 = 341 → m % 49 = 47) ∧
      (∀ m, m % 343 = 341 → m % 7 = 5) ∧
      (∀ m, m % 2401 = 2399 → m % 343 = 341) ∧
      (∀ m, m % 2401 = 2399 → m % 49 = 47) ∧
      (∀ m, m % 2401 = 2399 → m % 7 = 5) ∧
      (∀ m, m % 16807 = 16805 → m % 2401 = 2399) ∧
      (∀ m, m % 16807 = 16805 → m % 343 = 341) ∧
      (∀ m, m % 16807 = 16805 → m % 49 = 47) ∧
      (∀ m, m % 16807 = 16805 → m % 7 = 5) := by
  exact ⟨fun _ => mod_49_eq_47_implies_mod_7_eq_5,
    fun _ => mod_343_eq_341_implies_mod_49_eq_47,
    fun _ => mod_343_eq_341_implies_mod_7_eq_5,
    fun _ => mod_2401_eq_2399_implies_mod_343_eq_341,
    fun _ => mod_2401_eq_2399_implies_mod_49_eq_47,
    fun _ => mod_2401_eq_2399_implies_mod_7_eq_5,
    fun _ => mod_16807_eq_16805_implies_mod_2401_eq_2399,
    fun _ => mod_16807_eq_16805_implies_mod_343_eq_341,
    fun _ => mod_16807_eq_16805_implies_mod_49_eq_47,
    fun _ => mod_16807_eq_16805_implies_mod_7_eq_5⟩

/-- Projection facts for concrete higher-power mod-11 residues. -/
theorem concrete_mod11_power_residue_projection_facts :
    (∀ m, m % 121 = 116 → m % 11 = 6) ∧
      (∀ m, m % 1331 = 1326 → m % 121 = 116) ∧
      (∀ m, m % 1331 = 1326 → m % 11 = 6) ∧
      (∀ m, m % 14641 = 14636 → m % 1331 = 1326) ∧
      (∀ m, m % 14641 = 14636 → m % 121 = 116) ∧
      (∀ m, m % 14641 = 14636 → m % 11 = 6) ∧
      (∀ m, m % 161051 = 161046 → m % 14641 = 14636) ∧
      (∀ m, m % 161051 = 161046 → m % 1331 = 1326) ∧
      (∀ m, m % 161051 = 161046 → m % 121 = 116) ∧
      (∀ m, m % 161051 = 161046 → m % 11 = 6) := by
  exact ⟨fun _ => mod_121_eq_116_implies_mod_11_eq_6,
    fun _ => mod_1331_eq_1326_implies_mod_121_eq_116,
    fun _ => mod_1331_eq_1326_implies_mod_11_eq_6,
    fun _ => mod_14641_eq_14636_implies_mod_1331_eq_1326,
    fun _ => mod_14641_eq_14636_implies_mod_121_eq_116,
    fun _ => mod_14641_eq_14636_implies_mod_11_eq_6,
    fun _ => mod_161051_eq_161046_implies_mod_14641_eq_14636,
    fun _ => mod_161051_eq_161046_implies_mod_1331_eq_1326,
    fun _ => mod_161051_eq_161046_implies_mod_121_eq_116,
    fun _ => mod_161051_eq_161046_implies_mod_11_eq_6⟩

/-- Membership in `25n+24` implies membership in the base mod-5 progression. -/
theorem exists_mod25_progression_implies_base_mod5_progression (m : ℕ) :
    (∃ n, m = 25 * n + 24) → ∃ n, m = 5 * n + 4 := by
  rintro ⟨n, rfl⟩
  exact ⟨5 * n + 4, by omega⟩

/-- Membership in `125n+124` implies membership in `25n+24`. -/
theorem exists_mod125_progression_implies_mod25_progression (m : ℕ) :
    (∃ n, m = 125 * n + 124) → ∃ n, m = 25 * n + 24 := by
  rintro ⟨n, rfl⟩
  exact ⟨5 * n + 4, by omega⟩

/-- Membership in `125n+124` implies membership in the base mod-5 progression. -/
theorem exists_mod125_progression_implies_base_mod5_progression (m : ℕ) :
    (∃ n, m = 125 * n + 124) → ∃ n, m = 5 * n + 4 := by
  intro h
  exact exists_mod25_progression_implies_base_mod5_progression m
    (exists_mod125_progression_implies_mod25_progression m h)

/-- Membership in `625n+624` implies membership in `125n+124`. -/
theorem exists_mod625_progression_implies_mod125_progression (m : ℕ) :
    (∃ n, m = 625 * n + 624) → ∃ n, m = 125 * n + 124 := by
  rintro ⟨n, rfl⟩
  exact ⟨5 * n + 4, by omega⟩

/-- Membership in `625n+624` implies membership in `25n+24`. -/
theorem exists_mod625_progression_implies_mod25_progression (m : ℕ) :
    (∃ n, m = 625 * n + 624) → ∃ n, m = 25 * n + 24 := by
  intro h
  exact exists_mod125_progression_implies_mod25_progression m
    (exists_mod625_progression_implies_mod125_progression m h)

/-- Membership in `625n+624` implies membership in the base mod-5 progression. -/
theorem exists_mod625_progression_implies_base_mod5_progression (m : ℕ) :
    (∃ n, m = 625 * n + 624) → ∃ n, m = 5 * n + 4 := by
  intro h
  exact exists_mod125_progression_implies_base_mod5_progression m
    (exists_mod625_progression_implies_mod125_progression m h)

/-- Membership in `3125n+3124` implies membership in `625n+624`. -/
theorem exists_mod3125_progression_implies_mod625_progression (m : ℕ) :
    (∃ n, m = 3125 * n + 3124) → ∃ n, m = 625 * n + 624 := by
  rintro ⟨n, rfl⟩
  exact ⟨5 * n + 4, by omega⟩

/-- Membership in `3125n+3124` implies membership in `125n+124`. -/
theorem exists_mod3125_progression_implies_mod125_progression (m : ℕ) :
    (∃ n, m = 3125 * n + 3124) → ∃ n, m = 125 * n + 124 := by
  intro h
  exact exists_mod625_progression_implies_mod125_progression m
    (exists_mod3125_progression_implies_mod625_progression m h)

/-- Membership in `3125n+3124` implies membership in `25n+24`. -/
theorem exists_mod3125_progression_implies_mod25_progression (m : ℕ) :
    (∃ n, m = 3125 * n + 3124) → ∃ n, m = 25 * n + 24 := by
  intro h
  exact exists_mod625_progression_implies_mod25_progression m
    (exists_mod3125_progression_implies_mod625_progression m h)

/-- Membership in `3125n+3124` implies membership in the base mod-5 progression. -/
theorem exists_mod3125_progression_implies_base_mod5_progression (m : ℕ) :
    (∃ n, m = 3125 * n + 3124) → ∃ n, m = 5 * n + 4 := by
  intro h
  exact exists_mod625_progression_implies_base_mod5_progression m
    (exists_mod3125_progression_implies_mod625_progression m h)

/-- Membership in `49n+47` implies membership in the base mod-7 progression. -/
theorem exists_mod49_progression_implies_base_mod7_progression (m : ℕ) :
    (∃ n, m = 49 * n + 47) → ∃ n, m = 7 * n + 5 := by
  rintro ⟨n, rfl⟩
  exact ⟨7 * n + 6, by omega⟩

/-- Membership in `343n+341` implies membership in `49n+47`. -/
theorem exists_mod343_progression_implies_mod49_progression (m : ℕ) :
    (∃ n, m = 343 * n + 341) → ∃ n, m = 49 * n + 47 := by
  rintro ⟨n, rfl⟩
  exact ⟨7 * n + 6, by omega⟩

/-- Membership in `343n+341` implies membership in the base mod-7 progression. -/
theorem exists_mod343_progression_implies_base_mod7_progression (m : ℕ) :
    (∃ n, m = 343 * n + 341) → ∃ n, m = 7 * n + 5 := by
  intro h
  exact exists_mod49_progression_implies_base_mod7_progression m
    (exists_mod343_progression_implies_mod49_progression m h)

/-- Membership in `2401n+2399` implies membership in `343n+341`. -/
theorem exists_mod2401_progression_implies_mod343_progression (m : ℕ) :
    (∃ n, m = 2401 * n + 2399) → ∃ n, m = 343 * n + 341 := by
  rintro ⟨n, rfl⟩
  exact ⟨7 * n + 6, by omega⟩

/-- Membership in `2401n+2399` implies membership in `49n+47`. -/
theorem exists_mod2401_progression_implies_mod49_progression (m : ℕ) :
    (∃ n, m = 2401 * n + 2399) → ∃ n, m = 49 * n + 47 := by
  intro h
  exact exists_mod343_progression_implies_mod49_progression m
    (exists_mod2401_progression_implies_mod343_progression m h)

/-- Membership in `2401n+2399` implies membership in the base mod-7 progression. -/
theorem exists_mod2401_progression_implies_base_mod7_progression (m : ℕ) :
    (∃ n, m = 2401 * n + 2399) → ∃ n, m = 7 * n + 5 := by
  intro h
  exact exists_mod343_progression_implies_base_mod7_progression m
    (exists_mod2401_progression_implies_mod343_progression m h)

/-- Membership in `16807n+16805` implies membership in `2401n+2399`. -/
theorem exists_mod16807_progression_implies_mod2401_progression (m : ℕ) :
    (∃ n, m = 16807 * n + 16805) → ∃ n, m = 2401 * n + 2399 := by
  rintro ⟨n, rfl⟩
  exact ⟨7 * n + 6, by omega⟩

/-- Membership in `16807n+16805` implies membership in `343n+341`. -/
theorem exists_mod16807_progression_implies_mod343_progression (m : ℕ) :
    (∃ n, m = 16807 * n + 16805) → ∃ n, m = 343 * n + 341 := by
  intro h
  exact exists_mod2401_progression_implies_mod343_progression m
    (exists_mod16807_progression_implies_mod2401_progression m h)

/-- Membership in `16807n+16805` implies membership in `49n+47`. -/
theorem exists_mod16807_progression_implies_mod49_progression (m : ℕ) :
    (∃ n, m = 16807 * n + 16805) → ∃ n, m = 49 * n + 47 := by
  intro h
  exact exists_mod2401_progression_implies_mod49_progression m
    (exists_mod16807_progression_implies_mod2401_progression m h)

/-- Membership in `16807n+16805` implies membership in the base mod-7
progression. -/
theorem exists_mod16807_progression_implies_base_mod7_progression (m : ℕ) :
    (∃ n, m = 16807 * n + 16805) → ∃ n, m = 7 * n + 5 := by
  intro h
  exact exists_mod2401_progression_implies_base_mod7_progression m
    (exists_mod16807_progression_implies_mod2401_progression m h)

/-- Membership in `121n+116` implies membership in the base mod-11 progression. -/
theorem exists_mod121_progression_implies_base_mod11_progression (m : ℕ) :
    (∃ n, m = 121 * n + 116) → ∃ n, m = 11 * n + 6 := by
  rintro ⟨n, rfl⟩
  exact ⟨11 * n + 10, by omega⟩

/-- Membership in `1331n+1326` implies membership in `121n+116`. -/
theorem exists_mod1331_progression_implies_mod121_progression (m : ℕ) :
    (∃ n, m = 1331 * n + 1326) → ∃ n, m = 121 * n + 116 := by
  rintro ⟨n, rfl⟩
  exact ⟨11 * n + 10, by omega⟩

/-- Membership in `1331n+1326` implies membership in the base mod-11
progression. -/
theorem exists_mod1331_progression_implies_base_mod11_progression (m : ℕ) :
    (∃ n, m = 1331 * n + 1326) → ∃ n, m = 11 * n + 6 := by
  intro h
  exact exists_mod121_progression_implies_base_mod11_progression m
    (exists_mod1331_progression_implies_mod121_progression m h)

/-- Membership in `14641n+14636` implies membership in `1331n+1326`. -/
theorem exists_mod14641_progression_implies_mod1331_progression (m : ℕ) :
    (∃ n, m = 14641 * n + 14636) → ∃ n, m = 1331 * n + 1326 := by
  rintro ⟨n, rfl⟩
  exact ⟨11 * n + 10, by omega⟩

/-- Membership in `14641n+14636` implies membership in `121n+116`. -/
theorem exists_mod14641_progression_implies_mod121_progression (m : ℕ) :
    (∃ n, m = 14641 * n + 14636) → ∃ n, m = 121 * n + 116 := by
  intro h
  exact exists_mod1331_progression_implies_mod121_progression m
    (exists_mod14641_progression_implies_mod1331_progression m h)

/-- Membership in `14641n+14636` implies membership in the base mod-11
progression. -/
theorem exists_mod14641_progression_implies_base_mod11_progression (m : ℕ) :
    (∃ n, m = 14641 * n + 14636) → ∃ n, m = 11 * n + 6 := by
  intro h
  exact exists_mod1331_progression_implies_base_mod11_progression m
    (exists_mod14641_progression_implies_mod1331_progression m h)

/-- Membership in `161051n+161046` implies membership in `14641n+14636`. -/
theorem exists_mod161051_progression_implies_mod14641_progression (m : ℕ) :
    (∃ n, m = 161051 * n + 161046) → ∃ n, m = 14641 * n + 14636 := by
  rintro ⟨n, rfl⟩
  exact ⟨11 * n + 10, by omega⟩

/-- Membership in `161051n+161046` implies membership in `1331n+1326`. -/
theorem exists_mod161051_progression_implies_mod1331_progression (m : ℕ) :
    (∃ n, m = 161051 * n + 161046) → ∃ n, m = 1331 * n + 1326 := by
  intro h
  exact exists_mod14641_progression_implies_mod1331_progression m
    (exists_mod161051_progression_implies_mod14641_progression m h)

/-- Membership in `161051n+161046` implies membership in `121n+116`. -/
theorem exists_mod161051_progression_implies_mod121_progression (m : ℕ) :
    (∃ n, m = 161051 * n + 161046) → ∃ n, m = 121 * n + 116 := by
  intro h
  exact exists_mod14641_progression_implies_mod121_progression m
    (exists_mod161051_progression_implies_mod14641_progression m h)

/-- Membership in `161051n+161046` implies membership in the base mod-11
progression. -/
theorem exists_mod161051_progression_implies_base_mod11_progression (m : ℕ) :
    (∃ n, m = 161051 * n + 161046) → ∃ n, m = 11 * n + 6 := by
  intro h
  exact exists_mod14641_progression_implies_base_mod11_progression m
    (exists_mod161051_progression_implies_mod14641_progression m h)

/-- Membership projection facts for concrete higher-power mod-5 progressions. -/
theorem concrete_mod5_power_membership_projection_facts :
    (∀ m, (∃ n, m = 25 * n + 24) → ∃ n, m = 5 * n + 4) ∧
      (∀ m, (∃ n, m = 125 * n + 124) → ∃ n, m = 25 * n + 24) ∧
      (∀ m, (∃ n, m = 125 * n + 124) → ∃ n, m = 5 * n + 4) ∧
      (∀ m, (∃ n, m = 625 * n + 624) → ∃ n, m = 125 * n + 124) ∧
      (∀ m, (∃ n, m = 625 * n + 624) → ∃ n, m = 25 * n + 24) ∧
      (∀ m, (∃ n, m = 625 * n + 624) → ∃ n, m = 5 * n + 4) ∧
      (∀ m, (∃ n, m = 3125 * n + 3124) → ∃ n, m = 625 * n + 624) ∧
      (∀ m, (∃ n, m = 3125 * n + 3124) → ∃ n, m = 125 * n + 124) ∧
      (∀ m, (∃ n, m = 3125 * n + 3124) → ∃ n, m = 25 * n + 24) ∧
      (∀ m, (∃ n, m = 3125 * n + 3124) → ∃ n, m = 5 * n + 4) := by
  exact ⟨exists_mod25_progression_implies_base_mod5_progression,
    exists_mod125_progression_implies_mod25_progression,
    exists_mod125_progression_implies_base_mod5_progression,
    exists_mod625_progression_implies_mod125_progression,
    exists_mod625_progression_implies_mod25_progression,
    exists_mod625_progression_implies_base_mod5_progression,
    exists_mod3125_progression_implies_mod625_progression,
    exists_mod3125_progression_implies_mod125_progression,
    exists_mod3125_progression_implies_mod25_progression,
    exists_mod3125_progression_implies_base_mod5_progression⟩

/-- Membership projection facts for concrete higher-power mod-7 progressions. -/
theorem concrete_mod7_power_membership_projection_facts :
    (∀ m, (∃ n, m = 49 * n + 47) → ∃ n, m = 7 * n + 5) ∧
      (∀ m, (∃ n, m = 343 * n + 341) → ∃ n, m = 49 * n + 47) ∧
      (∀ m, (∃ n, m = 343 * n + 341) → ∃ n, m = 7 * n + 5) ∧
      (∀ m, (∃ n, m = 2401 * n + 2399) → ∃ n, m = 343 * n + 341) ∧
      (∀ m, (∃ n, m = 2401 * n + 2399) → ∃ n, m = 49 * n + 47) ∧
      (∀ m, (∃ n, m = 2401 * n + 2399) → ∃ n, m = 7 * n + 5) ∧
      (∀ m, (∃ n, m = 16807 * n + 16805) → ∃ n, m = 2401 * n + 2399) ∧
      (∀ m, (∃ n, m = 16807 * n + 16805) → ∃ n, m = 343 * n + 341) ∧
      (∀ m, (∃ n, m = 16807 * n + 16805) → ∃ n, m = 49 * n + 47) ∧
      (∀ m, (∃ n, m = 16807 * n + 16805) → ∃ n, m = 7 * n + 5) := by
  exact ⟨exists_mod49_progression_implies_base_mod7_progression,
    exists_mod343_progression_implies_mod49_progression,
    exists_mod343_progression_implies_base_mod7_progression,
    exists_mod2401_progression_implies_mod343_progression,
    exists_mod2401_progression_implies_mod49_progression,
    exists_mod2401_progression_implies_base_mod7_progression,
    exists_mod16807_progression_implies_mod2401_progression,
    exists_mod16807_progression_implies_mod343_progression,
    exists_mod16807_progression_implies_mod49_progression,
    exists_mod16807_progression_implies_base_mod7_progression⟩

/-- Membership projection facts for concrete higher-power mod-11 progressions. -/
theorem concrete_mod11_power_membership_projection_facts :
    (∀ m, (∃ n, m = 121 * n + 116) → ∃ n, m = 11 * n + 6) ∧
      (∀ m, (∃ n, m = 1331 * n + 1326) → ∃ n, m = 121 * n + 116) ∧
      (∀ m, (∃ n, m = 1331 * n + 1326) → ∃ n, m = 11 * n + 6) ∧
      (∀ m, (∃ n, m = 14641 * n + 14636) → ∃ n, m = 1331 * n + 1326) ∧
      (∀ m, (∃ n, m = 14641 * n + 14636) → ∃ n, m = 121 * n + 116) ∧
      (∀ m, (∃ n, m = 14641 * n + 14636) → ∃ n, m = 11 * n + 6) ∧
      (∀ m, (∃ n, m = 161051 * n + 161046) →
        ∃ n, m = 14641 * n + 14636) ∧
      (∀ m, (∃ n, m = 161051 * n + 161046) →
        ∃ n, m = 1331 * n + 1326) ∧
      (∀ m, (∃ n, m = 161051 * n + 161046) →
        ∃ n, m = 121 * n + 116) ∧
      (∀ m, (∃ n, m = 161051 * n + 161046) → ∃ n, m = 11 * n + 6) := by
  exact ⟨exists_mod121_progression_implies_base_mod11_progression,
    exists_mod1331_progression_implies_mod121_progression,
    exists_mod1331_progression_implies_base_mod11_progression,
    exists_mod14641_progression_implies_mod1331_progression,
    exists_mod14641_progression_implies_mod121_progression,
    exists_mod14641_progression_implies_base_mod11_progression,
    exists_mod161051_progression_implies_mod14641_progression,
    exists_mod161051_progression_implies_mod1331_progression,
    exists_mod161051_progression_implies_mod121_progression,
    exists_mod161051_progression_implies_base_mod11_progression⟩

/-- Dividing a `24 mod 25` residue by `5` leaves quotient residue `4 mod 5`. -/
theorem div_of_mod25_eq24_by_5_mod5_eq4 (m : ℕ) (hm : m % 25 = 24) :
    (m / 5) % 5 = 4 := by
  have hdec := eq_25_mul_div_plus_24_of_mod_eq_24 hm
  have hdiv : m / 5 = 5 * (m / 25) + 4 := by
    exact div_by_5_eq_of_eq_five_mul_add_four (by omega)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `124 mod 125` residue by `5` leaves quotient residue `24 mod 25`. -/
theorem div_of_mod125_eq124_by_5_mod25_eq24 (m : ℕ) (hm : m % 125 = 124) :
    (m / 5) % 25 = 24 := by
  have hdec := eq_125_mul_div_plus_124_of_mod_eq_124 hm
  have hdiv : m / 5 = 25 * (m / 125) + 24 := by
    exact div_by_5_eq_of_eq_five_mul_add_four (by omega)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `624 mod 625` residue by `5` leaves quotient residue
`124 mod 125`. -/
theorem div_of_mod625_eq624_by_5_mod125_eq124 (m : ℕ) (hm : m % 625 = 624) :
    (m / 5) % 125 = 124 := by
  have hdec := eq_625_mul_div_plus_624_of_mod_eq_624 hm
  have hdiv : m / 5 = 125 * (m / 625) + 124 := by
    exact div_by_5_eq_of_eq_five_mul_add_four (by omega)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `3124 mod 3125` residue by `5` leaves quotient residue
`624 mod 625`. -/
theorem div_of_mod3125_eq3124_by_5_mod625_eq624 (m : ℕ)
    (hm : m % 3125 = 3124) :
    (m / 5) % 625 = 624 := by
  have hdec := eq_3125_mul_div_plus_3124_of_mod_eq_3124 hm
  have hdiv : m / 5 = 625 * (m / 3125) + 624 := by
    exact div_by_5_eq_of_eq_five_mul_add_four (by omega)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `47 mod 49` residue by `7` leaves quotient residue `6 mod 7`. -/
theorem div_of_mod49_eq47_by_7_mod7_eq6 (m : ℕ) (hm : m % 49 = 47) :
    (m / 7) % 7 = 6 := by
  have hdec := eq_49_mul_div_plus_47_of_mod_eq_47 hm
  have hdiv : m / 7 = 7 * (m / 49) + 6 := by
    exact div_by_7_eq_of_eq_seven_mul_add_five (by omega)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `341 mod 343` residue by `7` leaves quotient residue
`48 mod 49`. -/
theorem div_of_mod343_eq341_by_7_mod49_eq48 (m : ℕ) (hm : m % 343 = 341) :
    (m / 7) % 49 = 48 := by
  have hdec := eq_343_mul_div_plus_341_of_mod_eq_341 hm
  have hdiv : m / 7 = 49 * (m / 343) + 48 := by
    exact div_by_7_eq_of_eq_seven_mul_add_five (by omega)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `2399 mod 2401` residue by `7` leaves quotient residue
`342 mod 343`. -/
theorem div_of_mod2401_eq2399_by_7_mod343_eq342 (m : ℕ)
    (hm : m % 2401 = 2399) :
    (m / 7) % 343 = 342 := by
  have hdec := eq_2401_mul_div_plus_2399_of_mod_eq_2399 hm
  have hdiv : m / 7 = 343 * (m / 2401) + 342 := by
    exact div_by_7_eq_of_eq_seven_mul_add_five (by omega)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `16805 mod 16807` residue by `7` leaves quotient residue
`2400 mod 2401`. -/
theorem div_of_mod16807_eq16805_by_7_mod2401_eq2400 (m : ℕ)
    (hm : m % 16807 = 16805) :
    (m / 7) % 2401 = 2400 := by
  have hdec := eq_16807_mul_div_plus_16805_of_mod_eq_16805 hm
  have hdiv : m / 7 = 2401 * (m / 16807) + 2400 := by
    exact div_by_7_eq_of_eq_seven_mul_add_five (by omega)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `116 mod 121` residue by `11` leaves quotient residue
`10 mod 11`. -/
theorem div_of_mod121_eq116_by_11_mod11_eq10 (m : ℕ) (hm : m % 121 = 116) :
    (m / 11) % 11 = 10 := by
  have hdec := eq_121_mul_div_plus_116_of_mod_eq_116 hm
  have hdiv : m / 11 = 11 * (m / 121) + 10 := by
    exact div_by_11_eq_of_eq_eleven_mul_add_six (by omega)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `1326 mod 1331` residue by `11` leaves quotient residue
`120 mod 121`. -/
theorem div_of_mod1331_eq1326_by_11_mod121_eq120 (m : ℕ)
    (hm : m % 1331 = 1326) :
    (m / 11) % 121 = 120 := by
  have hdec := eq_1331_mul_div_plus_1326_of_mod_eq_1326 hm
  have hdiv : m / 11 = 121 * (m / 1331) + 120 := by
    exact div_by_11_eq_of_eq_eleven_mul_add_six (by omega)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `14636 mod 14641` residue by `11` leaves quotient residue
`1330 mod 1331`. -/
theorem div_of_mod14641_eq14636_by_11_mod1331_eq1330 (m : ℕ)
    (hm : m % 14641 = 14636) :
    (m / 11) % 1331 = 1330 := by
  have hdec := eq_14641_mul_div_plus_14636_of_mod_eq_14636 hm
  have hdiv : m / 11 = 1331 * (m / 14641) + 1330 := by
    exact div_by_11_eq_of_eq_eleven_mul_add_six (by omega)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `161046 mod 161051` residue by `11` leaves quotient residue
`14640 mod 14641`. -/
theorem div_of_mod161051_eq161046_by_11_mod14641_eq14640 (m : ℕ)
    (hm : m % 161051 = 161046) :
    (m / 11) % 14641 = 14640 := by
  have hdec := eq_161051_mul_div_plus_161046_of_mod_eq_161046 hm
  have hdiv : m / 11 = 14641 * (m / 161051) + 14640 := by
    exact div_by_11_eq_of_eq_eleven_mul_add_six (by omega)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Exact quotient residue facts after dividing concrete higher-power residues
by the base modulus. -/
theorem concrete_power_div_by_base_residue_facts :
    (∀ m, m % 25 = 24 → (m / 5) % 5 = 4) ∧
      (∀ m, m % 125 = 124 → (m / 5) % 25 = 24) ∧
      (∀ m, m % 625 = 624 → (m / 5) % 125 = 124) ∧
      (∀ m, m % 3125 = 3124 → (m / 5) % 625 = 624) ∧
      (∀ m, m % 49 = 47 → (m / 7) % 7 = 6) ∧
      (∀ m, m % 343 = 341 → (m / 7) % 49 = 48) ∧
      (∀ m, m % 2401 = 2399 → (m / 7) % 343 = 342) ∧
      (∀ m, m % 16807 = 16805 → (m / 7) % 2401 = 2400) ∧
      (∀ m, m % 121 = 116 → (m / 11) % 11 = 10) ∧
      (∀ m, m % 1331 = 1326 → (m / 11) % 121 = 120) ∧
      (∀ m, m % 14641 = 14636 → (m / 11) % 1331 = 1330) ∧
      (∀ m, m % 161051 = 161046 → (m / 11) % 14641 = 14640) := by
  exact ⟨div_of_mod25_eq24_by_5_mod5_eq4,
    div_of_mod125_eq124_by_5_mod25_eq24,
    div_of_mod625_eq624_by_5_mod125_eq124,
    div_of_mod3125_eq3124_by_5_mod625_eq624,
    div_of_mod49_eq47_by_7_mod7_eq6,
    div_of_mod343_eq341_by_7_mod49_eq48,
    div_of_mod2401_eq2399_by_7_mod343_eq342,
    div_of_mod16807_eq16805_by_7_mod2401_eq2400,
    div_of_mod121_eq116_by_11_mod11_eq10,
    div_of_mod1331_eq1326_by_11_mod121_eq120,
    div_of_mod14641_eq14636_by_11_mod1331_eq1330,
    div_of_mod161051_eq161046_by_11_mod14641_eq14640⟩

/-- Dividing a `124 mod 125` residue by `25` leaves quotient residue
`4 mod 5`. -/
theorem div_of_mod125_eq124_by_25_mod5_eq4 (m : ℕ) (hm : m % 125 = 124) :
    (m / 25) % 5 = 4 := by
  have hdec := eq_125_mul_div_plus_124_of_mod_eq_124 hm
  have hdiv : m / 25 = 5 * (m / 125) + 4 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 25) (y := 5 * (m / 125) + 4) (r := 24)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `624 mod 625` residue by `25` leaves quotient residue
`24 mod 25`. -/
theorem div_of_mod625_eq624_by_25_mod25_eq24 (m : ℕ) (hm : m % 625 = 624) :
    (m / 25) % 25 = 24 := by
  have hdec := eq_625_mul_div_plus_624_of_mod_eq_624 hm
  have hdiv : m / 25 = 25 * (m / 625) + 24 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 25) (y := 25 * (m / 625) + 24) (r := 24)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `624 mod 625` residue by `125` leaves quotient residue
`4 mod 5`. -/
theorem div_of_mod625_eq624_by_125_mod5_eq4 (m : ℕ) (hm : m % 625 = 624) :
    (m / 125) % 5 = 4 := by
  have hdec := eq_625_mul_div_plus_624_of_mod_eq_624 hm
  have hdiv : m / 125 = 5 * (m / 625) + 4 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 125) (y := 5 * (m / 625) + 4) (r := 124)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `3124 mod 3125` residue by `25` leaves quotient residue
`124 mod 125`. -/
theorem div_of_mod3125_eq3124_by_25_mod125_eq124 (m : ℕ)
    (hm : m % 3125 = 3124) :
    (m / 25) % 125 = 124 := by
  have hdec := eq_3125_mul_div_plus_3124_of_mod_eq_3124 hm
  have hdiv : m / 25 = 125 * (m / 3125) + 124 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 25) (y := 125 * (m / 3125) + 124) (r := 24)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `3124 mod 3125` residue by `125` leaves quotient residue
`24 mod 25`. -/
theorem div_of_mod3125_eq3124_by_125_mod25_eq24 (m : ℕ)
    (hm : m % 3125 = 3124) :
    (m / 125) % 25 = 24 := by
  have hdec := eq_3125_mul_div_plus_3124_of_mod_eq_3124 hm
  have hdiv : m / 125 = 25 * (m / 3125) + 24 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 125) (y := 25 * (m / 3125) + 24) (r := 124)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `3124 mod 3125` residue by `625` leaves quotient residue
`4 mod 5`. -/
theorem div_of_mod3125_eq3124_by_625_mod5_eq4 (m : ℕ)
    (hm : m % 3125 = 3124) :
    (m / 625) % 5 = 4 := by
  have hdec := eq_3125_mul_div_plus_3124_of_mod_eq_3124 hm
  have hdiv : m / 625 = 5 * (m / 3125) + 4 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 625) (y := 5 * (m / 3125) + 4) (r := 624)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `341 mod 343` residue by `49` leaves quotient residue
`6 mod 7`. -/
theorem div_of_mod343_eq341_by_49_mod7_eq6 (m : ℕ) (hm : m % 343 = 341) :
    (m / 49) % 7 = 6 := by
  have hdec := eq_343_mul_div_plus_341_of_mod_eq_341 hm
  have hdiv : m / 49 = 7 * (m / 343) + 6 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 49) (y := 7 * (m / 343) + 6) (r := 47)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `2399 mod 2401` residue by `49` leaves quotient residue
`48 mod 49`. -/
theorem div_of_mod2401_eq2399_by_49_mod49_eq48 (m : ℕ)
    (hm : m % 2401 = 2399) :
    (m / 49) % 49 = 48 := by
  have hdec := eq_2401_mul_div_plus_2399_of_mod_eq_2399 hm
  have hdiv : m / 49 = 49 * (m / 2401) + 48 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 49) (y := 49 * (m / 2401) + 48) (r := 47)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `2399 mod 2401` residue by `343` leaves quotient residue
`6 mod 7`. -/
theorem div_of_mod2401_eq2399_by_343_mod7_eq6 (m : ℕ)
    (hm : m % 2401 = 2399) :
    (m / 343) % 7 = 6 := by
  have hdec := eq_2401_mul_div_plus_2399_of_mod_eq_2399 hm
  have hdiv : m / 343 = 7 * (m / 2401) + 6 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 343) (y := 7 * (m / 2401) + 6) (r := 341)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `16805 mod 16807` residue by `49` leaves quotient residue
`342 mod 343`. -/
theorem div_of_mod16807_eq16805_by_49_mod343_eq342 (m : ℕ)
    (hm : m % 16807 = 16805) :
    (m / 49) % 343 = 342 := by
  have hdec := eq_16807_mul_div_plus_16805_of_mod_eq_16805 hm
  have hdiv : m / 49 = 343 * (m / 16807) + 342 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 49) (y := 343 * (m / 16807) + 342) (r := 47)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `16805 mod 16807` residue by `343` leaves quotient residue
`48 mod 49`. -/
theorem div_of_mod16807_eq16805_by_343_mod49_eq48 (m : ℕ)
    (hm : m % 16807 = 16805) :
    (m / 343) % 49 = 48 := by
  have hdec := eq_16807_mul_div_plus_16805_of_mod_eq_16805 hm
  have hdiv : m / 343 = 49 * (m / 16807) + 48 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 343) (y := 49 * (m / 16807) + 48) (r := 341)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `16805 mod 16807` residue by `2401` leaves quotient residue
`6 mod 7`. -/
theorem div_of_mod16807_eq16805_by_2401_mod7_eq6 (m : ℕ)
    (hm : m % 16807 = 16805) :
    (m / 2401) % 7 = 6 := by
  have hdec := eq_16807_mul_div_plus_16805_of_mod_eq_16805 hm
  have hdiv : m / 2401 = 7 * (m / 16807) + 6 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 2401) (y := 7 * (m / 16807) + 6) (r := 2399)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `1326 mod 1331` residue by `121` leaves quotient residue
`10 mod 11`. -/
theorem div_of_mod1331_eq1326_by_121_mod11_eq10 (m : ℕ)
    (hm : m % 1331 = 1326) :
    (m / 121) % 11 = 10 := by
  have hdec := eq_1331_mul_div_plus_1326_of_mod_eq_1326 hm
  have hdiv : m / 121 = 11 * (m / 1331) + 10 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 121) (y := 11 * (m / 1331) + 10) (r := 116)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `14636 mod 14641` residue by `121` leaves quotient residue
`120 mod 121`. -/
theorem div_of_mod14641_eq14636_by_121_mod121_eq120 (m : ℕ)
    (hm : m % 14641 = 14636) :
    (m / 121) % 121 = 120 := by
  have hdec := eq_14641_mul_div_plus_14636_of_mod_eq_14636 hm
  have hdiv : m / 121 = 121 * (m / 14641) + 120 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 121) (y := 121 * (m / 14641) + 120) (r := 116)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `14636 mod 14641` residue by `1331` leaves quotient residue
`10 mod 11`. -/
theorem div_of_mod14641_eq14636_by_1331_mod11_eq10 (m : ℕ)
    (hm : m % 14641 = 14636) :
    (m / 1331) % 11 = 10 := by
  have hdec := eq_14641_mul_div_plus_14636_of_mod_eq_14636 hm
  have hdiv : m / 1331 = 11 * (m / 14641) + 10 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 1331) (y := 11 * (m / 14641) + 10) (r := 1326)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `161046 mod 161051` residue by `121` leaves quotient residue
`1330 mod 1331`. -/
theorem div_of_mod161051_eq161046_by_121_mod1331_eq1330 (m : ℕ)
    (hm : m % 161051 = 161046) :
    (m / 121) % 1331 = 1330 := by
  have hdec := eq_161051_mul_div_plus_161046_of_mod_eq_161046 hm
  have hdiv : m / 121 = 1331 * (m / 161051) + 1330 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 121) (y := 1331 * (m / 161051) + 1330) (r := 116)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `161046 mod 161051` residue by `1331` leaves quotient residue
`120 mod 121`. -/
theorem div_of_mod161051_eq161046_by_1331_mod121_eq120 (m : ℕ)
    (hm : m % 161051 = 161046) :
    (m / 1331) % 121 = 120 := by
  have hdec := eq_161051_mul_div_plus_161046_of_mod_eq_161046 hm
  have hdiv : m / 1331 = 121 * (m / 161051) + 120 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 1331) (y := 121 * (m / 161051) + 120) (r := 1326)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Dividing a `161046 mod 161051` residue by `14641` leaves quotient residue
`10 mod 11`. -/
theorem div_of_mod161051_eq161046_by_14641_mod11_eq10 (m : ℕ)
    (hm : m % 161051 = 161046) :
    (m / 14641) % 11 = 10 := by
  have hdec := eq_161051_mul_div_plus_161046_of_mod_eq_161046 hm
  have hdiv : m / 14641 = 11 * (m / 161051) + 10 := by
    exact div_eq_of_eq_mul_add_of_lt
      (x := m) (q := 14641) (y := 11 * (m / 161051) + 10) (r := 14636)
      (by omega) (by decide)
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide)]

/-- Intermediate quotient residue facts for concrete higher-power mod-5
residues. -/
theorem concrete_mod5_power_intermediate_div_residue_facts :
    (∀ m, m % 125 = 124 → (m / 25) % 5 = 4) ∧
      (∀ m, m % 625 = 624 → (m / 25) % 25 = 24) ∧
      (∀ m, m % 625 = 624 → (m / 125) % 5 = 4) ∧
      (∀ m, m % 3125 = 3124 → (m / 25) % 125 = 124) ∧
      (∀ m, m % 3125 = 3124 → (m / 125) % 25 = 24) ∧
      (∀ m, m % 3125 = 3124 → (m / 625) % 5 = 4) := by
  exact ⟨div_of_mod125_eq124_by_25_mod5_eq4,
    div_of_mod625_eq624_by_25_mod25_eq24,
    div_of_mod625_eq624_by_125_mod5_eq4,
    div_of_mod3125_eq3124_by_25_mod125_eq124,
    div_of_mod3125_eq3124_by_125_mod25_eq24,
    div_of_mod3125_eq3124_by_625_mod5_eq4⟩

/-- Intermediate quotient residue facts for concrete higher-power mod-7
residues. -/
theorem concrete_mod7_power_intermediate_div_residue_facts :
    (∀ m, m % 343 = 341 → (m / 49) % 7 = 6) ∧
      (∀ m, m % 2401 = 2399 → (m / 49) % 49 = 48) ∧
      (∀ m, m % 2401 = 2399 → (m / 343) % 7 = 6) ∧
      (∀ m, m % 16807 = 16805 → (m / 49) % 343 = 342) ∧
      (∀ m, m % 16807 = 16805 → (m / 343) % 49 = 48) ∧
      (∀ m, m % 16807 = 16805 → (m / 2401) % 7 = 6) := by
  exact ⟨div_of_mod343_eq341_by_49_mod7_eq6,
    div_of_mod2401_eq2399_by_49_mod49_eq48,
    div_of_mod2401_eq2399_by_343_mod7_eq6,
    div_of_mod16807_eq16805_by_49_mod343_eq342,
    div_of_mod16807_eq16805_by_343_mod49_eq48,
    div_of_mod16807_eq16805_by_2401_mod7_eq6⟩

/-- Intermediate quotient residue facts for concrete higher-power mod-11
residues. -/
theorem concrete_mod11_power_intermediate_div_residue_facts :
    (∀ m, m % 1331 = 1326 → (m / 121) % 11 = 10) ∧
      (∀ m, m % 14641 = 14636 → (m / 121) % 121 = 120) ∧
      (∀ m, m % 14641 = 14636 → (m / 1331) % 11 = 10) ∧
      (∀ m, m % 161051 = 161046 → (m / 121) % 1331 = 1330) ∧
      (∀ m, m % 161051 = 161046 → (m / 1331) % 121 = 120) ∧
      (∀ m, m % 161051 = 161046 → (m / 14641) % 11 = 10) := by
  exact ⟨div_of_mod1331_eq1326_by_121_mod11_eq10,
    div_of_mod14641_eq14636_by_121_mod121_eq120,
    div_of_mod14641_eq14636_by_1331_mod11_eq10,
    div_of_mod161051_eq161046_by_121_mod1331_eq1330,
    div_of_mod161051_eq161046_by_1331_mod121_eq120,
    div_of_mod161051_eq161046_by_14641_mod11_eq10⟩

/-- If `m` has residue `r` modulo `q` and `r+c=q`, then `q` divides
`m+c`. -/
theorem dvd_add_of_mod_eq {q r c m : ℕ} (hmod : r + c = q) (hm : m % q = r) :
    q ∣ m + c := by
  refine ⟨m / q + 1, ?_⟩
  have h := (Nat.mod_add_div m q).symm
  nlinarith

/-- A `4 mod 5` residue has `m+1` divisible by `5`. -/
theorem dvd_add_one_of_mod5_eq4 (m : ℕ) (hm : m % 5 = 4) :
    5 ∣ m + 1 := by
  exact dvd_add_of_mod_eq (q := 5) (r := 4) (c := 1) (by decide) hm

/-- A `24 mod 25` residue has `m+1` divisible by `25`. -/
theorem dvd_add_one_of_mod25_eq24 (m : ℕ) (hm : m % 25 = 24) :
    25 ∣ m + 1 := by
  exact dvd_add_of_mod_eq (q := 25) (r := 24) (c := 1) (by decide) hm

/-- A `124 mod 125` residue has `m+1` divisible by `125`. -/
theorem dvd_add_one_of_mod125_eq124 (m : ℕ) (hm : m % 125 = 124) :
    125 ∣ m + 1 := by
  exact dvd_add_of_mod_eq (q := 125) (r := 124) (c := 1) (by decide) hm

/-- A `624 mod 625` residue has `m+1` divisible by `625`. -/
theorem dvd_add_one_of_mod625_eq624 (m : ℕ) (hm : m % 625 = 624) :
    625 ∣ m + 1 := by
  exact dvd_add_of_mod_eq (q := 625) (r := 624) (c := 1) (by decide) hm

/-- A `3124 mod 3125` residue has `m+1` divisible by `3125`. -/
theorem dvd_add_one_of_mod3125_eq3124 (m : ℕ) (hm : m % 3125 = 3124) :
    3125 ∣ m + 1 := by
  exact dvd_add_of_mod_eq (q := 3125) (r := 3124) (c := 1) (by decide) hm

/-- A `5 mod 7` residue has `m+2` divisible by `7`. -/
theorem dvd_add_two_of_mod7_eq5 (m : ℕ) (hm : m % 7 = 5) :
    7 ∣ m + 2 := by
  exact dvd_add_of_mod_eq (q := 7) (r := 5) (c := 2) (by decide) hm

/-- A `47 mod 49` residue has `m+2` divisible by `49`. -/
theorem dvd_add_two_of_mod49_eq47 (m : ℕ) (hm : m % 49 = 47) :
    49 ∣ m + 2 := by
  exact dvd_add_of_mod_eq (q := 49) (r := 47) (c := 2) (by decide) hm

/-- A `341 mod 343` residue has `m+2` divisible by `343`. -/
theorem dvd_add_two_of_mod343_eq341 (m : ℕ) (hm : m % 343 = 341) :
    343 ∣ m + 2 := by
  exact dvd_add_of_mod_eq (q := 343) (r := 341) (c := 2) (by decide) hm

/-- A `2399 mod 2401` residue has `m+2` divisible by `2401`. -/
theorem dvd_add_two_of_mod2401_eq2399 (m : ℕ) (hm : m % 2401 = 2399) :
    2401 ∣ m + 2 := by
  exact dvd_add_of_mod_eq (q := 2401) (r := 2399) (c := 2) (by decide) hm

/-- A `16805 mod 16807` residue has `m+2` divisible by `16807`. -/
theorem dvd_add_two_of_mod16807_eq16805 (m : ℕ)
    (hm : m % 16807 = 16805) :
    16807 ∣ m + 2 := by
  exact dvd_add_of_mod_eq (q := 16807) (r := 16805) (c := 2) (by decide) hm

/-- A `6 mod 11` residue has `m+5` divisible by `11`. -/
theorem dvd_add_five_of_mod11_eq6 (m : ℕ) (hm : m % 11 = 6) :
    11 ∣ m + 5 := by
  exact dvd_add_of_mod_eq (q := 11) (r := 6) (c := 5) (by decide) hm

/-- A `116 mod 121` residue has `m+5` divisible by `121`. -/
theorem dvd_add_five_of_mod121_eq116 (m : ℕ) (hm : m % 121 = 116) :
    121 ∣ m + 5 := by
  exact dvd_add_of_mod_eq (q := 121) (r := 116) (c := 5) (by decide) hm

/-- A `1326 mod 1331` residue has `m+5` divisible by `1331`. -/
theorem dvd_add_five_of_mod1331_eq1326 (m : ℕ) (hm : m % 1331 = 1326) :
    1331 ∣ m + 5 := by
  exact dvd_add_of_mod_eq (q := 1331) (r := 1326) (c := 5) (by decide) hm

/-- A `14636 mod 14641` residue has `m+5` divisible by `14641`. -/
theorem dvd_add_five_of_mod14641_eq14636 (m : ℕ)
    (hm : m % 14641 = 14636) :
    14641 ∣ m + 5 := by
  exact dvd_add_of_mod_eq (q := 14641) (r := 14636) (c := 5) (by decide) hm

/-- A `161046 mod 161051` residue has `m+5` divisible by `161051`. -/
theorem dvd_add_five_of_mod161051_eq161046 (m : ℕ)
    (hm : m % 161051 = 161046) :
    161051 ∣ m + 5 := by
  exact dvd_add_of_mod_eq (q := 161051) (r := 161046) (c := 5) (by decide) hm

/-- Divisibility form of the concrete mod-5 power residues. -/
theorem concrete_mod5_power_residue_dvd_add_one_facts :
    (∀ m, m % 5 = 4 → 5 ∣ m + 1) ∧
      (∀ m, m % 25 = 24 → 25 ∣ m + 1) ∧
      (∀ m, m % 125 = 124 → 125 ∣ m + 1) ∧
      (∀ m, m % 625 = 624 → 625 ∣ m + 1) ∧
      (∀ m, m % 3125 = 3124 → 3125 ∣ m + 1) := by
  exact ⟨dvd_add_one_of_mod5_eq4,
    dvd_add_one_of_mod25_eq24,
    dvd_add_one_of_mod125_eq124,
    dvd_add_one_of_mod625_eq624,
    dvd_add_one_of_mod3125_eq3124⟩

/-- Divisibility form of the concrete mod-7 power residues. -/
theorem concrete_mod7_power_residue_dvd_add_two_facts :
    (∀ m, m % 7 = 5 → 7 ∣ m + 2) ∧
      (∀ m, m % 49 = 47 → 49 ∣ m + 2) ∧
      (∀ m, m % 343 = 341 → 343 ∣ m + 2) ∧
      (∀ m, m % 2401 = 2399 → 2401 ∣ m + 2) ∧
      (∀ m, m % 16807 = 16805 → 16807 ∣ m + 2) := by
  exact ⟨dvd_add_two_of_mod7_eq5,
    dvd_add_two_of_mod49_eq47,
    dvd_add_two_of_mod343_eq341,
    dvd_add_two_of_mod2401_eq2399,
    dvd_add_two_of_mod16807_eq16805⟩

/-- Divisibility form of the concrete mod-11 power residues. -/
theorem concrete_mod11_power_residue_dvd_add_five_facts :
    (∀ m, m % 11 = 6 → 11 ∣ m + 5) ∧
      (∀ m, m % 121 = 116 → 121 ∣ m + 5) ∧
      (∀ m, m % 1331 = 1326 → 1331 ∣ m + 5) ∧
      (∀ m, m % 14641 = 14636 → 14641 ∣ m + 5) ∧
      (∀ m, m % 161051 = 161046 → 161051 ∣ m + 5) := by
  exact ⟨dvd_add_five_of_mod11_eq6,
    dvd_add_five_of_mod121_eq116,
    dvd_add_five_of_mod1331_eq1326,
    dvd_add_five_of_mod14641_eq14636,
    dvd_add_five_of_mod161051_eq161046⟩

/-- Divisibility of `m+1` by `5` gives residue `4 mod 5`. -/
theorem mod5_eq4_of_dvd_add_one (m : ℕ) (h : 5 ∣ m + 1) :
    m % 5 = 4 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 5).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 5)
  omega

/-- Divisibility of `m+1` by `25` gives residue `24 mod 25`. -/
theorem mod25_eq24_of_dvd_add_one (m : ℕ) (h : 25 ∣ m + 1) :
    m % 25 = 24 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 25).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 25)
  omega

/-- Divisibility of `m+1` by `125` gives residue `124 mod 125`. -/
theorem mod125_eq124_of_dvd_add_one (m : ℕ) (h : 125 ∣ m + 1) :
    m % 125 = 124 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 125).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 125)
  omega

/-- Divisibility of `m+1` by `625` gives residue `624 mod 625`. -/
theorem mod625_eq624_of_dvd_add_one (m : ℕ) (h : 625 ∣ m + 1) :
    m % 625 = 624 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 625).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 625)
  omega

/-- Divisibility of `m+1` by `3125` gives residue `3124 mod 3125`. -/
theorem mod3125_eq3124_of_dvd_add_one (m : ℕ) (h : 3125 ∣ m + 1) :
    m % 3125 = 3124 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 3125).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 3125)
  omega

/-- Divisibility of `m+2` by `7` gives residue `5 mod 7`. -/
theorem mod7_eq5_of_dvd_add_two (m : ℕ) (h : 7 ∣ m + 2) :
    m % 7 = 5 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 7).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 7)
  omega

/-- Divisibility of `m+2` by `49` gives residue `47 mod 49`. -/
theorem mod49_eq47_of_dvd_add_two (m : ℕ) (h : 49 ∣ m + 2) :
    m % 49 = 47 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 49).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 49)
  omega

/-- Divisibility of `m+2` by `343` gives residue `341 mod 343`. -/
theorem mod343_eq341_of_dvd_add_two (m : ℕ) (h : 343 ∣ m + 2) :
    m % 343 = 341 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 343).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 343)
  omega

/-- Divisibility of `m+2` by `2401` gives residue `2399 mod 2401`. -/
theorem mod2401_eq2399_of_dvd_add_two (m : ℕ) (h : 2401 ∣ m + 2) :
    m % 2401 = 2399 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 2401).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 2401)
  omega

/-- Divisibility of `m+2` by `16807` gives residue `16805 mod 16807`. -/
theorem mod16807_eq16805_of_dvd_add_two (m : ℕ) (h : 16807 ∣ m + 2) :
    m % 16807 = 16805 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 16807).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 16807)
  omega

/-- Divisibility of `m+5` by `11` gives residue `6 mod 11`. -/
theorem mod11_eq6_of_dvd_add_five (m : ℕ) (h : 11 ∣ m + 5) :
    m % 11 = 6 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 11).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 11)
  omega

/-- Divisibility of `m+5` by `121` gives residue `116 mod 121`. -/
theorem mod121_eq116_of_dvd_add_five (m : ℕ) (h : 121 ∣ m + 5) :
    m % 121 = 116 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 121).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 121)
  omega

/-- Divisibility of `m+5` by `1331` gives residue `1326 mod 1331`. -/
theorem mod1331_eq1326_of_dvd_add_five (m : ℕ) (h : 1331 ∣ m + 5) :
    m % 1331 = 1326 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 1331).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 1331)
  omega

/-- Divisibility of `m+5` by `14641` gives residue `14636 mod 14641`. -/
theorem mod14641_eq14636_of_dvd_add_five (m : ℕ) (h : 14641 ∣ m + 5) :
    m % 14641 = 14636 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 14641).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 14641)
  omega

/-- Divisibility of `m+5` by `161051` gives residue `161046 mod 161051`. -/
theorem mod161051_eq161046_of_dvd_add_five (m : ℕ)
    (h : 161051 ∣ m + 5) :
    m % 161051 = 161046 := by
  obtain ⟨k, hk⟩ := h
  have h0 := (Nat.mod_add_div m 161051).symm
  have hlt := Nat.mod_lt m (by decide : 0 < 161051)
  omega

/-- Divisibility iff form of the concrete mod-5 power residues. -/
theorem concrete_mod5_power_residue_iff_dvd_add_one_facts :
    (∀ m, m % 5 = 4 ↔ 5 ∣ m + 1) ∧
      (∀ m, m % 25 = 24 ↔ 25 ∣ m + 1) ∧
      (∀ m, m % 125 = 124 ↔ 125 ∣ m + 1) ∧
      (∀ m, m % 625 = 624 ↔ 625 ∣ m + 1) ∧
      (∀ m, m % 3125 = 3124 ↔ 3125 ∣ m + 1) := by
  exact ⟨fun m => ⟨dvd_add_one_of_mod5_eq4 m, mod5_eq4_of_dvd_add_one m⟩,
    fun m => ⟨dvd_add_one_of_mod25_eq24 m, mod25_eq24_of_dvd_add_one m⟩,
    fun m => ⟨dvd_add_one_of_mod125_eq124 m, mod125_eq124_of_dvd_add_one m⟩,
    fun m => ⟨dvd_add_one_of_mod625_eq624 m, mod625_eq624_of_dvd_add_one m⟩,
    fun m => ⟨dvd_add_one_of_mod3125_eq3124 m,
      mod3125_eq3124_of_dvd_add_one m⟩⟩

/-- Divisibility iff form of the concrete mod-7 power residues. -/
theorem concrete_mod7_power_residue_iff_dvd_add_two_facts :
    (∀ m, m % 7 = 5 ↔ 7 ∣ m + 2) ∧
      (∀ m, m % 49 = 47 ↔ 49 ∣ m + 2) ∧
      (∀ m, m % 343 = 341 ↔ 343 ∣ m + 2) ∧
      (∀ m, m % 2401 = 2399 ↔ 2401 ∣ m + 2) ∧
      (∀ m, m % 16807 = 16805 ↔ 16807 ∣ m + 2) := by
  exact ⟨fun m => ⟨dvd_add_two_of_mod7_eq5 m, mod7_eq5_of_dvd_add_two m⟩,
    fun m => ⟨dvd_add_two_of_mod49_eq47 m, mod49_eq47_of_dvd_add_two m⟩,
    fun m => ⟨dvd_add_two_of_mod343_eq341 m, mod343_eq341_of_dvd_add_two m⟩,
    fun m => ⟨dvd_add_two_of_mod2401_eq2399 m,
      mod2401_eq2399_of_dvd_add_two m⟩,
    fun m => ⟨dvd_add_two_of_mod16807_eq16805 m,
      mod16807_eq16805_of_dvd_add_two m⟩⟩

/-- Divisibility iff form of the concrete mod-11 power residues. -/
theorem concrete_mod11_power_residue_iff_dvd_add_five_facts :
    (∀ m, m % 11 = 6 ↔ 11 ∣ m + 5) ∧
      (∀ m, m % 121 = 116 ↔ 121 ∣ m + 5) ∧
      (∀ m, m % 1331 = 1326 ↔ 1331 ∣ m + 5) ∧
      (∀ m, m % 14641 = 14636 ↔ 14641 ∣ m + 5) ∧
      (∀ m, m % 161051 = 161046 ↔ 161051 ∣ m + 5) := by
  exact ⟨fun m => ⟨dvd_add_five_of_mod11_eq6 m, mod11_eq6_of_dvd_add_five m⟩,
    fun m => ⟨dvd_add_five_of_mod121_eq116 m, mod121_eq116_of_dvd_add_five m⟩,
    fun m => ⟨dvd_add_five_of_mod1331_eq1326 m,
      mod1331_eq1326_of_dvd_add_five m⟩,
    fun m => ⟨dvd_add_five_of_mod14641_eq14636 m,
      mod14641_eq14636_of_dvd_add_five m⟩,
    fun m => ⟨dvd_add_five_of_mod161051_eq161046 m,
      mod161051_eq161046_of_dvd_add_five m⟩⟩

/-- If `m` has residue `r` modulo `q` and `r+c=q`, then adding `c` advances
the quotient by one. -/
theorem div_add_eq_div_add_one_of_mod_eq {q r c m : ℕ}
    (hq : 0 < q) (hmod : r + c = q) (hm : m % q = r) :
    (m + c) / q = m / q + 1 := by
  have h := (Nat.mod_add_div m q).symm
  apply Nat.div_eq_of_lt_le
  · nlinarith
  · nlinarith

/-- Quotient formula for `4 mod 5` after adding `1`. -/
theorem div_add_one_by_5_eq_succ_div_of_mod5_eq4 (m : ℕ) (hm : m % 5 = 4) :
    (m + 1) / 5 = m / 5 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 5) (r := 4) (c := 1)
    (by decide) (by decide) hm

/-- Quotient formula for `24 mod 25` after adding `1`. -/
theorem div_add_one_by_25_eq_succ_div_of_mod25_eq24 (m : ℕ)
    (hm : m % 25 = 24) :
    (m + 1) / 25 = m / 25 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 25) (r := 24) (c := 1)
    (by decide) (by decide) hm

/-- Quotient formula for `124 mod 125` after adding `1`. -/
theorem div_add_one_by_125_eq_succ_div_of_mod125_eq124 (m : ℕ)
    (hm : m % 125 = 124) :
    (m + 1) / 125 = m / 125 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 125) (r := 124) (c := 1)
    (by decide) (by decide) hm

/-- Quotient formula for `624 mod 625` after adding `1`. -/
theorem div_add_one_by_625_eq_succ_div_of_mod625_eq624 (m : ℕ)
    (hm : m % 625 = 624) :
    (m + 1) / 625 = m / 625 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 625) (r := 624) (c := 1)
    (by decide) (by decide) hm

/-- Quotient formula for `3124 mod 3125` after adding `1`. -/
theorem div_add_one_by_3125_eq_succ_div_of_mod3125_eq3124 (m : ℕ)
    (hm : m % 3125 = 3124) :
    (m + 1) / 3125 = m / 3125 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 3125) (r := 3124) (c := 1)
    (by decide) (by decide) hm

/-- Quotient formula for `5 mod 7` after adding `2`. -/
theorem div_add_two_by_7_eq_succ_div_of_mod7_eq5 (m : ℕ) (hm : m % 7 = 5) :
    (m + 2) / 7 = m / 7 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 7) (r := 5) (c := 2)
    (by decide) (by decide) hm

/-- Quotient formula for `47 mod 49` after adding `2`. -/
theorem div_add_two_by_49_eq_succ_div_of_mod49_eq47 (m : ℕ)
    (hm : m % 49 = 47) :
    (m + 2) / 49 = m / 49 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 49) (r := 47) (c := 2)
    (by decide) (by decide) hm

/-- Quotient formula for `341 mod 343` after adding `2`. -/
theorem div_add_two_by_343_eq_succ_div_of_mod343_eq341 (m : ℕ)
    (hm : m % 343 = 341) :
    (m + 2) / 343 = m / 343 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 343) (r := 341) (c := 2)
    (by decide) (by decide) hm

/-- Quotient formula for `2399 mod 2401` after adding `2`. -/
theorem div_add_two_by_2401_eq_succ_div_of_mod2401_eq2399 (m : ℕ)
    (hm : m % 2401 = 2399) :
    (m + 2) / 2401 = m / 2401 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 2401) (r := 2399) (c := 2)
    (by decide) (by decide) hm

/-- Quotient formula for `16805 mod 16807` after adding `2`. -/
theorem div_add_two_by_16807_eq_succ_div_of_mod16807_eq16805 (m : ℕ)
    (hm : m % 16807 = 16805) :
    (m + 2) / 16807 = m / 16807 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 16807) (r := 16805) (c := 2)
    (by decide) (by decide) hm

/-- Quotient formula for `6 mod 11` after adding `5`. -/
theorem div_add_five_by_11_eq_succ_div_of_mod11_eq6 (m : ℕ)
    (hm : m % 11 = 6) :
    (m + 5) / 11 = m / 11 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 11) (r := 6) (c := 5)
    (by decide) (by decide) hm

/-- Quotient formula for `116 mod 121` after adding `5`. -/
theorem div_add_five_by_121_eq_succ_div_of_mod121_eq116 (m : ℕ)
    (hm : m % 121 = 116) :
    (m + 5) / 121 = m / 121 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 121) (r := 116) (c := 5)
    (by decide) (by decide) hm

/-- Quotient formula for `1326 mod 1331` after adding `5`. -/
theorem div_add_five_by_1331_eq_succ_div_of_mod1331_eq1326 (m : ℕ)
    (hm : m % 1331 = 1326) :
    (m + 5) / 1331 = m / 1331 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 1331) (r := 1326) (c := 5)
    (by decide) (by decide) hm

/-- Quotient formula for `14636 mod 14641` after adding `5`. -/
theorem div_add_five_by_14641_eq_succ_div_of_mod14641_eq14636 (m : ℕ)
    (hm : m % 14641 = 14636) :
    (m + 5) / 14641 = m / 14641 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 14641) (r := 14636) (c := 5)
    (by decide) (by decide) hm

/-- Quotient formula for `161046 mod 161051` after adding `5`. -/
theorem div_add_five_by_161051_eq_succ_div_of_mod161051_eq161046 (m : ℕ)
    (hm : m % 161051 = 161046) :
    (m + 5) / 161051 = m / 161051 + 1 := by
  exact div_add_eq_div_add_one_of_mod_eq (q := 161051) (r := 161046) (c := 5)
    (by decide) (by decide) hm

/-- Quotient-after-shift facts for concrete mod-5 power residues. -/
theorem concrete_mod5_power_shifted_quotient_facts :
    (∀ m, m % 5 = 4 → (m + 1) / 5 = m / 5 + 1) ∧
      (∀ m, m % 25 = 24 → (m + 1) / 25 = m / 25 + 1) ∧
      (∀ m, m % 125 = 124 → (m + 1) / 125 = m / 125 + 1) ∧
      (∀ m, m % 625 = 624 → (m + 1) / 625 = m / 625 + 1) ∧
      (∀ m, m % 3125 = 3124 → (m + 1) / 3125 = m / 3125 + 1) := by
  exact ⟨div_add_one_by_5_eq_succ_div_of_mod5_eq4,
    div_add_one_by_25_eq_succ_div_of_mod25_eq24,
    div_add_one_by_125_eq_succ_div_of_mod125_eq124,
    div_add_one_by_625_eq_succ_div_of_mod625_eq624,
    div_add_one_by_3125_eq_succ_div_of_mod3125_eq3124⟩

/-- Quotient-after-shift facts for concrete mod-7 power residues. -/
theorem concrete_mod7_power_shifted_quotient_facts :
    (∀ m, m % 7 = 5 → (m + 2) / 7 = m / 7 + 1) ∧
      (∀ m, m % 49 = 47 → (m + 2) / 49 = m / 49 + 1) ∧
      (∀ m, m % 343 = 341 → (m + 2) / 343 = m / 343 + 1) ∧
      (∀ m, m % 2401 = 2399 → (m + 2) / 2401 = m / 2401 + 1) ∧
      (∀ m, m % 16807 = 16805 → (m + 2) / 16807 = m / 16807 + 1) := by
  exact ⟨div_add_two_by_7_eq_succ_div_of_mod7_eq5,
    div_add_two_by_49_eq_succ_div_of_mod49_eq47,
    div_add_two_by_343_eq_succ_div_of_mod343_eq341,
    div_add_two_by_2401_eq_succ_div_of_mod2401_eq2399,
    div_add_two_by_16807_eq_succ_div_of_mod16807_eq16805⟩

/-- Quotient-after-shift facts for concrete mod-11 power residues. -/
theorem concrete_mod11_power_shifted_quotient_facts :
    (∀ m, m % 11 = 6 → (m + 5) / 11 = m / 11 + 1) ∧
      (∀ m, m % 121 = 116 → (m + 5) / 121 = m / 121 + 1) ∧
      (∀ m, m % 1331 = 1326 → (m + 5) / 1331 = m / 1331 + 1) ∧
      (∀ m, m % 14641 = 14636 → (m + 5) / 14641 = m / 14641 + 1) ∧
      (∀ m, m % 161051 = 161046 → (m + 5) / 161051 = m / 161051 + 1) := by
  exact ⟨div_add_five_by_11_eq_succ_div_of_mod11_eq6,
    div_add_five_by_121_eq_succ_div_of_mod121_eq116,
    div_add_five_by_1331_eq_succ_div_of_mod1331_eq1326,
    div_add_five_by_14641_eq_succ_div_of_mod14641_eq14636,
    div_add_five_by_161051_eq_succ_div_of_mod161051_eq161046⟩

/-- If `m` has residue `r` modulo `q` and `r+c=q`, then `m+c` has zero
residue modulo `q`. -/
theorem mod_add_eq_zero_of_mod_eq {q r c m : ℕ}
    (hc : c < q) (hmod : r + c = q) (hm : m % q = r) :
    (m + c) % q = 0 := by
  rw [Nat.add_mod, hm, Nat.mod_eq_of_lt hc, hmod, Nat.mod_self]

/-- Adding `1` to a `4 mod 5` residue gives zero residue modulo `5`. -/
theorem mod_add_one_eq_zero_of_mod5_eq4 (m : ℕ) (hm : m % 5 = 4) :
    (m + 1) % 5 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 5) (r := 4) (c := 1)
    (by decide) (by decide) hm

/-- Adding `1` to a `24 mod 25` residue gives zero residue modulo `25`. -/
theorem mod_add_one_eq_zero_of_mod25_eq24 (m : ℕ) (hm : m % 25 = 24) :
    (m + 1) % 25 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 25) (r := 24) (c := 1)
    (by decide) (by decide) hm

/-- Adding `1` to a `124 mod 125` residue gives zero residue modulo `125`. -/
theorem mod_add_one_eq_zero_of_mod125_eq124 (m : ℕ) (hm : m % 125 = 124) :
    (m + 1) % 125 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 125) (r := 124) (c := 1)
    (by decide) (by decide) hm

/-- Adding `1` to a `624 mod 625` residue gives zero residue modulo `625`. -/
theorem mod_add_one_eq_zero_of_mod625_eq624 (m : ℕ) (hm : m % 625 = 624) :
    (m + 1) % 625 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 625) (r := 624) (c := 1)
    (by decide) (by decide) hm

/-- Adding `1` to a `3124 mod 3125` residue gives zero residue modulo `3125`. -/
theorem mod_add_one_eq_zero_of_mod3125_eq3124 (m : ℕ)
    (hm : m % 3125 = 3124) :
    (m + 1) % 3125 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 3125) (r := 3124) (c := 1)
    (by decide) (by decide) hm

/-- Adding `2` to a `5 mod 7` residue gives zero residue modulo `7`. -/
theorem mod_add_two_eq_zero_of_mod7_eq5 (m : ℕ) (hm : m % 7 = 5) :
    (m + 2) % 7 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 7) (r := 5) (c := 2)
    (by decide) (by decide) hm

/-- Adding `2` to a `47 mod 49` residue gives zero residue modulo `49`. -/
theorem mod_add_two_eq_zero_of_mod49_eq47 (m : ℕ) (hm : m % 49 = 47) :
    (m + 2) % 49 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 49) (r := 47) (c := 2)
    (by decide) (by decide) hm

/-- Adding `2` to a `341 mod 343` residue gives zero residue modulo `343`. -/
theorem mod_add_two_eq_zero_of_mod343_eq341 (m : ℕ) (hm : m % 343 = 341) :
    (m + 2) % 343 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 343) (r := 341) (c := 2)
    (by decide) (by decide) hm

/-- Adding `2` to a `2399 mod 2401` residue gives zero residue modulo `2401`. -/
theorem mod_add_two_eq_zero_of_mod2401_eq2399 (m : ℕ)
    (hm : m % 2401 = 2399) :
    (m + 2) % 2401 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 2401) (r := 2399) (c := 2)
    (by decide) (by decide) hm

/-- Adding `2` to a `16805 mod 16807` residue gives zero residue modulo
`16807`. -/
theorem mod_add_two_eq_zero_of_mod16807_eq16805 (m : ℕ)
    (hm : m % 16807 = 16805) :
    (m + 2) % 16807 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 16807) (r := 16805) (c := 2)
    (by decide) (by decide) hm

/-- Adding `5` to a `6 mod 11` residue gives zero residue modulo `11`. -/
theorem mod_add_five_eq_zero_of_mod11_eq6 (m : ℕ) (hm : m % 11 = 6) :
    (m + 5) % 11 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 11) (r := 6) (c := 5)
    (by decide) (by decide) hm

/-- Adding `5` to a `116 mod 121` residue gives zero residue modulo `121`. -/
theorem mod_add_five_eq_zero_of_mod121_eq116 (m : ℕ) (hm : m % 121 = 116) :
    (m + 5) % 121 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 121) (r := 116) (c := 5)
    (by decide) (by decide) hm

/-- Adding `5` to a `1326 mod 1331` residue gives zero residue modulo `1331`. -/
theorem mod_add_five_eq_zero_of_mod1331_eq1326 (m : ℕ)
    (hm : m % 1331 = 1326) :
    (m + 5) % 1331 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 1331) (r := 1326) (c := 5)
    (by decide) (by decide) hm

/-- Adding `5` to a `14636 mod 14641` residue gives zero residue modulo
`14641`. -/
theorem mod_add_five_eq_zero_of_mod14641_eq14636 (m : ℕ)
    (hm : m % 14641 = 14636) :
    (m + 5) % 14641 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 14641) (r := 14636) (c := 5)
    (by decide) (by decide) hm

/-- Adding `5` to a `161046 mod 161051` residue gives zero residue modulo
`161051`. -/
theorem mod_add_five_eq_zero_of_mod161051_eq161046 (m : ℕ)
    (hm : m % 161051 = 161046) :
    (m + 5) % 161051 = 0 := by
  exact mod_add_eq_zero_of_mod_eq (q := 161051) (r := 161046) (c := 5)
    (by decide) (by decide) hm

/-- Shift-to-zero residue facts for concrete mod-5 power residues. -/
theorem concrete_mod5_power_shifted_zero_mod_facts :
    (∀ m, m % 5 = 4 → (m + 1) % 5 = 0) ∧
      (∀ m, m % 25 = 24 → (m + 1) % 25 = 0) ∧
      (∀ m, m % 125 = 124 → (m + 1) % 125 = 0) ∧
      (∀ m, m % 625 = 624 → (m + 1) % 625 = 0) ∧
      (∀ m, m % 3125 = 3124 → (m + 1) % 3125 = 0) := by
  exact ⟨mod_add_one_eq_zero_of_mod5_eq4,
    mod_add_one_eq_zero_of_mod25_eq24,
    mod_add_one_eq_zero_of_mod125_eq124,
    mod_add_one_eq_zero_of_mod625_eq624,
    mod_add_one_eq_zero_of_mod3125_eq3124⟩

/-- Shift-to-zero residue facts for concrete mod-7 power residues. -/
theorem concrete_mod7_power_shifted_zero_mod_facts :
    (∀ m, m % 7 = 5 → (m + 2) % 7 = 0) ∧
      (∀ m, m % 49 = 47 → (m + 2) % 49 = 0) ∧
      (∀ m, m % 343 = 341 → (m + 2) % 343 = 0) ∧
      (∀ m, m % 2401 = 2399 → (m + 2) % 2401 = 0) ∧
      (∀ m, m % 16807 = 16805 → (m + 2) % 16807 = 0) := by
  exact ⟨mod_add_two_eq_zero_of_mod7_eq5,
    mod_add_two_eq_zero_of_mod49_eq47,
    mod_add_two_eq_zero_of_mod343_eq341,
    mod_add_two_eq_zero_of_mod2401_eq2399,
    mod_add_two_eq_zero_of_mod16807_eq16805⟩

/-- Shift-to-zero residue facts for concrete mod-11 power residues. -/
theorem concrete_mod11_power_shifted_zero_mod_facts :
    (∀ m, m % 11 = 6 → (m + 5) % 11 = 0) ∧
      (∀ m, m % 121 = 116 → (m + 5) % 121 = 0) ∧
      (∀ m, m % 1331 = 1326 → (m + 5) % 1331 = 0) ∧
      (∀ m, m % 14641 = 14636 → (m + 5) % 14641 = 0) ∧
      (∀ m, m % 161051 = 161046 → (m + 5) % 161051 = 0) := by
  exact ⟨mod_add_five_eq_zero_of_mod11_eq6,
    mod_add_five_eq_zero_of_mod121_eq116,
    mod_add_five_eq_zero_of_mod1331_eq1326,
    mod_add_five_eq_zero_of_mod14641_eq14636,
    mod_add_five_eq_zero_of_mod161051_eq161046⟩

/-- If `m+c` has zero residue modulo `q`, and `r+c=q`, then `m` has residue
`r` modulo `q`. -/
theorem mod_eq_of_mod_add_eq_zero {q r c m : ℕ}
    (hq : 0 < q) (hc_pos : 0 < c) (hc : c < q) (hmod : r + c = q)
    (hzero : (m + c) % q = 0) :
    m % q = r := by
  have hsum : (m % q + c) % q = 0 := by
    have h := Nat.add_mod m c q
    rw [Nat.mod_eq_of_lt hc] at h
    omega
  have hltm := Nat.mod_lt m hq
  have hsum_ge : q ≤ m % q + c := by
    by_contra hcontra
    have hlt : m % q + c < q := by omega
    have hz : (m % q + c) % q = m % q + c := Nat.mod_eq_of_lt hlt
    omega
  have hsum_le : m % q + c ≤ q := by
    by_contra hcontra
    have hlt_sub : m % q + c - q < q := by omega
    have hmod_sub : (m % q + c) % q = (m % q + c - q) % q := by
      exact Nat.mod_eq_sub_mod (by omega)
    have hz : (m % q + c - q) % q = m % q + c - q := Nat.mod_eq_of_lt hlt_sub
    omega
  omega

/-- Zero residue of `m+1` modulo `5` gives `m` residue `4 mod 5`. -/
theorem mod5_eq4_of_mod_add_one_eq_zero (m : ℕ) (h : (m + 1) % 5 = 0) :
    m % 5 = 4 := by
  exact mod_eq_of_mod_add_eq_zero (q := 5) (r := 4) (c := 1)
    (by decide) (by decide) (by decide) (by decide) h

/-- Zero residue of `m+1` modulo `25` gives `m` residue `24 mod 25`. -/
theorem mod25_eq24_of_mod_add_one_eq_zero (m : ℕ) (h : (m + 1) % 25 = 0) :
    m % 25 = 24 := by
  exact mod_eq_of_mod_add_eq_zero (q := 25) (r := 24) (c := 1)
    (by decide) (by decide) (by decide) (by decide) h

/-- Zero residue of `m+1` modulo `125` gives `m` residue `124 mod 125`. -/
theorem mod125_eq124_of_mod_add_one_eq_zero (m : ℕ)
    (h : (m + 1) % 125 = 0) :
    m % 125 = 124 := by
  exact mod_eq_of_mod_add_eq_zero (q := 125) (r := 124) (c := 1)
    (by decide) (by decide) (by decide) (by decide) h

/-- Zero residue of `m+1` modulo `625` gives `m` residue `624 mod 625`. -/
theorem mod625_eq624_of_mod_add_one_eq_zero (m : ℕ)
    (h : (m + 1) % 625 = 0) :
    m % 625 = 624 := by
  exact mod_eq_of_mod_add_eq_zero (q := 625) (r := 624) (c := 1)
    (by decide) (by decide) (by decide) (by decide) h

/-- Zero residue of `m+1` modulo `3125` gives `m` residue `3124 mod 3125`. -/
theorem mod3125_eq3124_of_mod_add_one_eq_zero (m : ℕ)
    (h : (m + 1) % 3125 = 0) :
    m % 3125 = 3124 := by
  exact mod_eq_of_mod_add_eq_zero (q := 3125) (r := 3124) (c := 1)
    (by decide) (by decide) (by decide) (by decide) h

/-- Zero residue of `m+2` modulo `7` gives `m` residue `5 mod 7`. -/
theorem mod7_eq5_of_mod_add_two_eq_zero (m : ℕ) (h : (m + 2) % 7 = 0) :
    m % 7 = 5 := by
  exact mod_eq_of_mod_add_eq_zero (q := 7) (r := 5) (c := 2)
    (by decide) (by decide) (by decide) (by decide) h

/-- Zero residue of `m+2` modulo `49` gives `m` residue `47 mod 49`. -/
theorem mod49_eq47_of_mod_add_two_eq_zero (m : ℕ) (h : (m + 2) % 49 = 0) :
    m % 49 = 47 := by
  exact mod_eq_of_mod_add_eq_zero (q := 49) (r := 47) (c := 2)
    (by decide) (by decide) (by decide) (by decide) h

/-- Zero residue of `m+2` modulo `343` gives `m` residue `341 mod 343`. -/
theorem mod343_eq341_of_mod_add_two_eq_zero (m : ℕ)
    (h : (m + 2) % 343 = 0) :
    m % 343 = 341 := by
  exact mod_eq_of_mod_add_eq_zero (q := 343) (r := 341) (c := 2)
    (by decide) (by decide) (by decide) (by decide) h

/-- Zero residue of `m+2` modulo `2401` gives `m` residue `2399 mod 2401`. -/
theorem mod2401_eq2399_of_mod_add_two_eq_zero (m : ℕ)
    (h : (m + 2) % 2401 = 0) :
    m % 2401 = 2399 := by
  exact mod_eq_of_mod_add_eq_zero (q := 2401) (r := 2399) (c := 2)
    (by decide) (by decide) (by decide) (by decide) h

/-- Zero residue of `m+2` modulo `16807` gives `m` residue `16805 mod 16807`. -/
theorem mod16807_eq16805_of_mod_add_two_eq_zero (m : ℕ)
    (h : (m + 2) % 16807 = 0) :
    m % 16807 = 16805 := by
  exact mod_eq_of_mod_add_eq_zero (q := 16807) (r := 16805) (c := 2)
    (by decide) (by decide) (by decide) (by decide) h

/-- Zero residue of `m+5` modulo `11` gives `m` residue `6 mod 11`. -/
theorem mod11_eq6_of_mod_add_five_eq_zero (m : ℕ) (h : (m + 5) % 11 = 0) :
    m % 11 = 6 := by
  exact mod_eq_of_mod_add_eq_zero (q := 11) (r := 6) (c := 5)
    (by decide) (by decide) (by decide) (by decide) h

/-- Zero residue of `m+5` modulo `121` gives `m` residue `116 mod 121`. -/
theorem mod121_eq116_of_mod_add_five_eq_zero (m : ℕ)
    (h : (m + 5) % 121 = 0) :
    m % 121 = 116 := by
  exact mod_eq_of_mod_add_eq_zero (q := 121) (r := 116) (c := 5)
    (by decide) (by decide) (by decide) (by decide) h

/-- Zero residue of `m+5` modulo `1331` gives `m` residue `1326 mod 1331`. -/
theorem mod1331_eq1326_of_mod_add_five_eq_zero (m : ℕ)
    (h : (m + 5) % 1331 = 0) :
    m % 1331 = 1326 := by
  exact mod_eq_of_mod_add_eq_zero (q := 1331) (r := 1326) (c := 5)
    (by decide) (by decide) (by decide) (by decide) h

/-- Zero residue of `m+5` modulo `14641` gives `m` residue `14636 mod 14641`. -/
theorem mod14641_eq14636_of_mod_add_five_eq_zero (m : ℕ)
    (h : (m + 5) % 14641 = 0) :
    m % 14641 = 14636 := by
  exact mod_eq_of_mod_add_eq_zero (q := 14641) (r := 14636) (c := 5)
    (by decide) (by decide) (by decide) (by decide) h

/-- Zero residue of `m+5` modulo `161051` gives `m` residue
`161046 mod 161051`. -/
theorem mod161051_eq161046_of_mod_add_five_eq_zero (m : ℕ)
    (h : (m + 5) % 161051 = 0) :
    m % 161051 = 161046 := by
  exact mod_eq_of_mod_add_eq_zero (q := 161051) (r := 161046) (c := 5)
    (by decide) (by decide) (by decide) (by decide) h

/-- Shift-to-zero iff facts for concrete mod-5 power residues. -/
theorem concrete_mod5_power_residue_iff_shifted_zero_mod_facts :
    (∀ m, m % 5 = 4 ↔ (m + 1) % 5 = 0) ∧
      (∀ m, m % 25 = 24 ↔ (m + 1) % 25 = 0) ∧
      (∀ m, m % 125 = 124 ↔ (m + 1) % 125 = 0) ∧
      (∀ m, m % 625 = 624 ↔ (m + 1) % 625 = 0) ∧
      (∀ m, m % 3125 = 3124 ↔ (m + 1) % 3125 = 0) := by
  exact ⟨fun m => ⟨mod_add_one_eq_zero_of_mod5_eq4 m,
      mod5_eq4_of_mod_add_one_eq_zero m⟩,
    fun m => ⟨mod_add_one_eq_zero_of_mod25_eq24 m,
      mod25_eq24_of_mod_add_one_eq_zero m⟩,
    fun m => ⟨mod_add_one_eq_zero_of_mod125_eq124 m,
      mod125_eq124_of_mod_add_one_eq_zero m⟩,
    fun m => ⟨mod_add_one_eq_zero_of_mod625_eq624 m,
      mod625_eq624_of_mod_add_one_eq_zero m⟩,
    fun m => ⟨mod_add_one_eq_zero_of_mod3125_eq3124 m,
      mod3125_eq3124_of_mod_add_one_eq_zero m⟩⟩

/-- Shift-to-zero iff facts for concrete mod-7 power residues. -/
theorem concrete_mod7_power_residue_iff_shifted_zero_mod_facts :
    (∀ m, m % 7 = 5 ↔ (m + 2) % 7 = 0) ∧
      (∀ m, m % 49 = 47 ↔ (m + 2) % 49 = 0) ∧
      (∀ m, m % 343 = 341 ↔ (m + 2) % 343 = 0) ∧
      (∀ m, m % 2401 = 2399 ↔ (m + 2) % 2401 = 0) ∧
      (∀ m, m % 16807 = 16805 ↔ (m + 2) % 16807 = 0) := by
  exact ⟨fun m => ⟨mod_add_two_eq_zero_of_mod7_eq5 m,
      mod7_eq5_of_mod_add_two_eq_zero m⟩,
    fun m => ⟨mod_add_two_eq_zero_of_mod49_eq47 m,
      mod49_eq47_of_mod_add_two_eq_zero m⟩,
    fun m => ⟨mod_add_two_eq_zero_of_mod343_eq341 m,
      mod343_eq341_of_mod_add_two_eq_zero m⟩,
    fun m => ⟨mod_add_two_eq_zero_of_mod2401_eq2399 m,
      mod2401_eq2399_of_mod_add_two_eq_zero m⟩,
    fun m => ⟨mod_add_two_eq_zero_of_mod16807_eq16805 m,
      mod16807_eq16805_of_mod_add_two_eq_zero m⟩⟩

/-- Shift-to-zero iff facts for concrete mod-11 power residues. -/
theorem concrete_mod11_power_residue_iff_shifted_zero_mod_facts :
    (∀ m, m % 11 = 6 ↔ (m + 5) % 11 = 0) ∧
      (∀ m, m % 121 = 116 ↔ (m + 5) % 121 = 0) ∧
      (∀ m, m % 1331 = 1326 ↔ (m + 5) % 1331 = 0) ∧
      (∀ m, m % 14641 = 14636 ↔ (m + 5) % 14641 = 0) ∧
      (∀ m, m % 161051 = 161046 ↔ (m + 5) % 161051 = 0) := by
  exact ⟨fun m => ⟨mod_add_five_eq_zero_of_mod11_eq6 m,
      mod11_eq6_of_mod_add_five_eq_zero m⟩,
    fun m => ⟨mod_add_five_eq_zero_of_mod121_eq116 m,
      mod121_eq116_of_mod_add_five_eq_zero m⟩,
    fun m => ⟨mod_add_five_eq_zero_of_mod1331_eq1326 m,
      mod1331_eq1326_of_mod_add_five_eq_zero m⟩,
    fun m => ⟨mod_add_five_eq_zero_of_mod14641_eq14636 m,
      mod14641_eq14636_of_mod_add_five_eq_zero m⟩,
    fun m => ⟨mod_add_five_eq_zero_of_mod161051_eq161046 m,
      mod161051_eq161046_of_mod_add_five_eq_zero m⟩⟩

/-- Divisibility by a larger modulus implies divisibility by any divisor of
that modulus. -/
theorem dvd_add_of_dvd_modulus {a b t m : ℕ} (hab : a ∣ b) (h : b ∣ m + t) :
    a ∣ m + t := by
  exact dvd_trans hab h

/-- If `25` divides `m+1`, then `5` divides `m+1`. -/
theorem dvd_add_one_by_25_implies_dvd_add_one_by_5 (m : ℕ)
    (h : 25 ∣ m + 1) :
    5 ∣ m + 1 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 5 ∣ 25) h

/-- If `125` divides `m+1`, then `25` divides `m+1`. -/
theorem dvd_add_one_by_125_implies_dvd_add_one_by_25 (m : ℕ)
    (h : 125 ∣ m + 1) :
    25 ∣ m + 1 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 25 ∣ 125) h

/-- If `125` divides `m+1`, then `5` divides `m+1`. -/
theorem dvd_add_one_by_125_implies_dvd_add_one_by_5 (m : ℕ)
    (h : 125 ∣ m + 1) :
    5 ∣ m + 1 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 5 ∣ 125) h

/-- If `625` divides `m+1`, then `125` divides `m+1`. -/
theorem dvd_add_one_by_625_implies_dvd_add_one_by_125 (m : ℕ)
    (h : 625 ∣ m + 1) :
    125 ∣ m + 1 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 125 ∣ 625) h

/-- If `625` divides `m+1`, then `25` divides `m+1`. -/
theorem dvd_add_one_by_625_implies_dvd_add_one_by_25 (m : ℕ)
    (h : 625 ∣ m + 1) :
    25 ∣ m + 1 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 25 ∣ 625) h

/-- If `625` divides `m+1`, then `5` divides `m+1`. -/
theorem dvd_add_one_by_625_implies_dvd_add_one_by_5 (m : ℕ)
    (h : 625 ∣ m + 1) :
    5 ∣ m + 1 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 5 ∣ 625) h

/-- If `3125` divides `m+1`, then `625` divides `m+1`. -/
theorem dvd_add_one_by_3125_implies_dvd_add_one_by_625 (m : ℕ)
    (h : 3125 ∣ m + 1) :
    625 ∣ m + 1 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 625 ∣ 3125) h

/-- If `3125` divides `m+1`, then `125` divides `m+1`. -/
theorem dvd_add_one_by_3125_implies_dvd_add_one_by_125 (m : ℕ)
    (h : 3125 ∣ m + 1) :
    125 ∣ m + 1 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 125 ∣ 3125) h

/-- If `3125` divides `m+1`, then `25` divides `m+1`. -/
theorem dvd_add_one_by_3125_implies_dvd_add_one_by_25 (m : ℕ)
    (h : 3125 ∣ m + 1) :
    25 ∣ m + 1 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 25 ∣ 3125) h

/-- If `3125` divides `m+1`, then `5` divides `m+1`. -/
theorem dvd_add_one_by_3125_implies_dvd_add_one_by_5 (m : ℕ)
    (h : 3125 ∣ m + 1) :
    5 ∣ m + 1 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 5 ∣ 3125) h

/-- If `49` divides `m+2`, then `7` divides `m+2`. -/
theorem dvd_add_two_by_49_implies_dvd_add_two_by_7 (m : ℕ)
    (h : 49 ∣ m + 2) :
    7 ∣ m + 2 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 7 ∣ 49) h

/-- If `343` divides `m+2`, then `49` divides `m+2`. -/
theorem dvd_add_two_by_343_implies_dvd_add_two_by_49 (m : ℕ)
    (h : 343 ∣ m + 2) :
    49 ∣ m + 2 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 49 ∣ 343) h

/-- If `343` divides `m+2`, then `7` divides `m+2`. -/
theorem dvd_add_two_by_343_implies_dvd_add_two_by_7 (m : ℕ)
    (h : 343 ∣ m + 2) :
    7 ∣ m + 2 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 7 ∣ 343) h

/-- If `2401` divides `m+2`, then `343` divides `m+2`. -/
theorem dvd_add_two_by_2401_implies_dvd_add_two_by_343 (m : ℕ)
    (h : 2401 ∣ m + 2) :
    343 ∣ m + 2 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 343 ∣ 2401) h

/-- If `2401` divides `m+2`, then `49` divides `m+2`. -/
theorem dvd_add_two_by_2401_implies_dvd_add_two_by_49 (m : ℕ)
    (h : 2401 ∣ m + 2) :
    49 ∣ m + 2 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 49 ∣ 2401) h

/-- If `2401` divides `m+2`, then `7` divides `m+2`. -/
theorem dvd_add_two_by_2401_implies_dvd_add_two_by_7 (m : ℕ)
    (h : 2401 ∣ m + 2) :
    7 ∣ m + 2 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 7 ∣ 2401) h

/-- If `16807` divides `m+2`, then `2401` divides `m+2`. -/
theorem dvd_add_two_by_16807_implies_dvd_add_two_by_2401 (m : ℕ)
    (h : 16807 ∣ m + 2) :
    2401 ∣ m + 2 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 2401 ∣ 16807) h

/-- If `16807` divides `m+2`, then `343` divides `m+2`. -/
theorem dvd_add_two_by_16807_implies_dvd_add_two_by_343 (m : ℕ)
    (h : 16807 ∣ m + 2) :
    343 ∣ m + 2 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 343 ∣ 16807) h

/-- If `16807` divides `m+2`, then `49` divides `m+2`. -/
theorem dvd_add_two_by_16807_implies_dvd_add_two_by_49 (m : ℕ)
    (h : 16807 ∣ m + 2) :
    49 ∣ m + 2 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 49 ∣ 16807) h

/-- If `16807` divides `m+2`, then `7` divides `m+2`. -/
theorem dvd_add_two_by_16807_implies_dvd_add_two_by_7 (m : ℕ)
    (h : 16807 ∣ m + 2) :
    7 ∣ m + 2 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 7 ∣ 16807) h

/-- If `121` divides `m+5`, then `11` divides `m+5`. -/
theorem dvd_add_five_by_121_implies_dvd_add_five_by_11 (m : ℕ)
    (h : 121 ∣ m + 5) :
    11 ∣ m + 5 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 11 ∣ 121) h

/-- If `1331` divides `m+5`, then `121` divides `m+5`. -/
theorem dvd_add_five_by_1331_implies_dvd_add_five_by_121 (m : ℕ)
    (h : 1331 ∣ m + 5) :
    121 ∣ m + 5 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 121 ∣ 1331) h

/-- If `1331` divides `m+5`, then `11` divides `m+5`. -/
theorem dvd_add_five_by_1331_implies_dvd_add_five_by_11 (m : ℕ)
    (h : 1331 ∣ m + 5) :
    11 ∣ m + 5 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 11 ∣ 1331) h

/-- If `14641` divides `m+5`, then `1331` divides `m+5`. -/
theorem dvd_add_five_by_14641_implies_dvd_add_five_by_1331 (m : ℕ)
    (h : 14641 ∣ m + 5) :
    1331 ∣ m + 5 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 1331 ∣ 14641) h

/-- If `14641` divides `m+5`, then `121` divides `m+5`. -/
theorem dvd_add_five_by_14641_implies_dvd_add_five_by_121 (m : ℕ)
    (h : 14641 ∣ m + 5) :
    121 ∣ m + 5 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 121 ∣ 14641) h

/-- If `14641` divides `m+5`, then `11` divides `m+5`. -/
theorem dvd_add_five_by_14641_implies_dvd_add_five_by_11 (m : ℕ)
    (h : 14641 ∣ m + 5) :
    11 ∣ m + 5 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 11 ∣ 14641) h

/-- If `161051` divides `m+5`, then `14641` divides `m+5`. -/
theorem dvd_add_five_by_161051_implies_dvd_add_five_by_14641 (m : ℕ)
    (h : 161051 ∣ m + 5) :
    14641 ∣ m + 5 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 14641 ∣ 161051) h

/-- If `161051` divides `m+5`, then `1331` divides `m+5`. -/
theorem dvd_add_five_by_161051_implies_dvd_add_five_by_1331 (m : ℕ)
    (h : 161051 ∣ m + 5) :
    1331 ∣ m + 5 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 1331 ∣ 161051) h

/-- If `161051` divides `m+5`, then `121` divides `m+5`. -/
theorem dvd_add_five_by_161051_implies_dvd_add_five_by_121 (m : ℕ)
    (h : 161051 ∣ m + 5) :
    121 ∣ m + 5 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 121 ∣ 161051) h

/-- If `161051` divides `m+5`, then `11` divides `m+5`. -/
theorem dvd_add_five_by_161051_implies_dvd_add_five_by_11 (m : ℕ)
    (h : 161051 ∣ m + 5) :
    11 ∣ m + 5 := by
  exact dvd_add_of_dvd_modulus (by norm_num : 11 ∣ 161051) h

/-- Divisibility projection facts for the concrete mod-5 power shifts. -/
theorem concrete_mod5_power_dvd_projection_facts :
    (∀ m, 25 ∣ m + 1 → 5 ∣ m + 1) ∧
      (∀ m, 125 ∣ m + 1 → 25 ∣ m + 1) ∧
      (∀ m, 125 ∣ m + 1 → 5 ∣ m + 1) ∧
      (∀ m, 625 ∣ m + 1 → 125 ∣ m + 1) ∧
      (∀ m, 625 ∣ m + 1 → 25 ∣ m + 1) ∧
      (∀ m, 625 ∣ m + 1 → 5 ∣ m + 1) ∧
      (∀ m, 3125 ∣ m + 1 → 625 ∣ m + 1) ∧
      (∀ m, 3125 ∣ m + 1 → 125 ∣ m + 1) ∧
      (∀ m, 3125 ∣ m + 1 → 25 ∣ m + 1) ∧
      (∀ m, 3125 ∣ m + 1 → 5 ∣ m + 1) := by
  exact ⟨dvd_add_one_by_25_implies_dvd_add_one_by_5,
    dvd_add_one_by_125_implies_dvd_add_one_by_25,
    dvd_add_one_by_125_implies_dvd_add_one_by_5,
    dvd_add_one_by_625_implies_dvd_add_one_by_125,
    dvd_add_one_by_625_implies_dvd_add_one_by_25,
    dvd_add_one_by_625_implies_dvd_add_one_by_5,
    dvd_add_one_by_3125_implies_dvd_add_one_by_625,
    dvd_add_one_by_3125_implies_dvd_add_one_by_125,
    dvd_add_one_by_3125_implies_dvd_add_one_by_25,
    dvd_add_one_by_3125_implies_dvd_add_one_by_5⟩

/-- Divisibility projection facts for the concrete mod-7 power shifts. -/
theorem concrete_mod7_power_dvd_projection_facts :
    (∀ m, 49 ∣ m + 2 → 7 ∣ m + 2) ∧
      (∀ m, 343 ∣ m + 2 → 49 ∣ m + 2) ∧
      (∀ m, 343 ∣ m + 2 → 7 ∣ m + 2) ∧
      (∀ m, 2401 ∣ m + 2 → 343 ∣ m + 2) ∧
      (∀ m, 2401 ∣ m + 2 → 49 ∣ m + 2) ∧
      (∀ m, 2401 ∣ m + 2 → 7 ∣ m + 2) ∧
      (∀ m, 16807 ∣ m + 2 → 2401 ∣ m + 2) ∧
      (∀ m, 16807 ∣ m + 2 → 343 ∣ m + 2) ∧
      (∀ m, 16807 ∣ m + 2 → 49 ∣ m + 2) ∧
      (∀ m, 16807 ∣ m + 2 → 7 ∣ m + 2) := by
  exact ⟨dvd_add_two_by_49_implies_dvd_add_two_by_7,
    dvd_add_two_by_343_implies_dvd_add_two_by_49,
    dvd_add_two_by_343_implies_dvd_add_two_by_7,
    dvd_add_two_by_2401_implies_dvd_add_two_by_343,
    dvd_add_two_by_2401_implies_dvd_add_two_by_49,
    dvd_add_two_by_2401_implies_dvd_add_two_by_7,
    dvd_add_two_by_16807_implies_dvd_add_two_by_2401,
    dvd_add_two_by_16807_implies_dvd_add_two_by_343,
    dvd_add_two_by_16807_implies_dvd_add_two_by_49,
    dvd_add_two_by_16807_implies_dvd_add_two_by_7⟩

/-- Divisibility projection facts for the concrete mod-11 power shifts. -/
theorem concrete_mod11_power_dvd_projection_facts :
    (∀ m, 121 ∣ m + 5 → 11 ∣ m + 5) ∧
      (∀ m, 1331 ∣ m + 5 → 121 ∣ m + 5) ∧
      (∀ m, 1331 ∣ m + 5 → 11 ∣ m + 5) ∧
      (∀ m, 14641 ∣ m + 5 → 1331 ∣ m + 5) ∧
      (∀ m, 14641 ∣ m + 5 → 121 ∣ m + 5) ∧
      (∀ m, 14641 ∣ m + 5 → 11 ∣ m + 5) ∧
      (∀ m, 161051 ∣ m + 5 → 14641 ∣ m + 5) ∧
      (∀ m, 161051 ∣ m + 5 → 1331 ∣ m + 5) ∧
      (∀ m, 161051 ∣ m + 5 → 121 ∣ m + 5) ∧
      (∀ m, 161051 ∣ m + 5 → 11 ∣ m + 5) := by
  exact ⟨dvd_add_five_by_121_implies_dvd_add_five_by_11,
    dvd_add_five_by_1331_implies_dvd_add_five_by_121,
    dvd_add_five_by_1331_implies_dvd_add_five_by_11,
    dvd_add_five_by_14641_implies_dvd_add_five_by_1331,
    dvd_add_five_by_14641_implies_dvd_add_five_by_121,
    dvd_add_five_by_14641_implies_dvd_add_five_by_11,
    dvd_add_five_by_161051_implies_dvd_add_five_by_14641,
    dvd_add_five_by_161051_implies_dvd_add_five_by_1331,
    dvd_add_five_by_161051_implies_dvd_add_five_by_121,
    dvd_add_five_by_161051_implies_dvd_add_five_by_11⟩

/-- A nonzero residue modulo `q` rules out divisibility by `q`. -/
theorem not_dvd_of_mod_eq_ne_zero {q r m : ℕ} (hm : m % q = r) (hr : r ≠ 0) :
    ¬ q ∣ m := by
  intro h
  have hz : m % q = 0 := Nat.mod_eq_zero_of_dvd h
  rw [hm] at hz
  exact hr hz

/-- A `4 mod 5` number is not divisible by `5`. -/
theorem not_dvd_of_mod5_eq4 (m : ℕ) (hm : m % 5 = 4) :
    ¬ 5 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- A `24 mod 25` number is not divisible by `25`. -/
theorem not_dvd_of_mod25_eq24 (m : ℕ) (hm : m % 25 = 24) :
    ¬ 25 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- A `124 mod 125` number is not divisible by `125`. -/
theorem not_dvd_of_mod125_eq124 (m : ℕ) (hm : m % 125 = 124) :
    ¬ 125 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- A `624 mod 625` number is not divisible by `625`. -/
theorem not_dvd_of_mod625_eq624 (m : ℕ) (hm : m % 625 = 624) :
    ¬ 625 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- A `3124 mod 3125` number is not divisible by `3125`. -/
theorem not_dvd_of_mod3125_eq3124 (m : ℕ) (hm : m % 3125 = 3124) :
    ¬ 3125 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- A `5 mod 7` number is not divisible by `7`. -/
theorem not_dvd_of_mod7_eq5 (m : ℕ) (hm : m % 7 = 5) :
    ¬ 7 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- A `47 mod 49` number is not divisible by `49`. -/
theorem not_dvd_of_mod49_eq47 (m : ℕ) (hm : m % 49 = 47) :
    ¬ 49 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- A `341 mod 343` number is not divisible by `343`. -/
theorem not_dvd_of_mod343_eq341 (m : ℕ) (hm : m % 343 = 341) :
    ¬ 343 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- A `2399 mod 2401` number is not divisible by `2401`. -/
theorem not_dvd_of_mod2401_eq2399 (m : ℕ) (hm : m % 2401 = 2399) :
    ¬ 2401 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- A `16805 mod 16807` number is not divisible by `16807`. -/
theorem not_dvd_of_mod16807_eq16805 (m : ℕ) (hm : m % 16807 = 16805) :
    ¬ 16807 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- A `6 mod 11` number is not divisible by `11`. -/
theorem not_dvd_of_mod11_eq6 (m : ℕ) (hm : m % 11 = 6) :
    ¬ 11 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- A `116 mod 121` number is not divisible by `121`. -/
theorem not_dvd_of_mod121_eq116 (m : ℕ) (hm : m % 121 = 116) :
    ¬ 121 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- A `1326 mod 1331` number is not divisible by `1331`. -/
theorem not_dvd_of_mod1331_eq1326 (m : ℕ) (hm : m % 1331 = 1326) :
    ¬ 1331 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- A `14636 mod 14641` number is not divisible by `14641`. -/
theorem not_dvd_of_mod14641_eq14636 (m : ℕ) (hm : m % 14641 = 14636) :
    ¬ 14641 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- A `161046 mod 161051` number is not divisible by `161051`. -/
theorem not_dvd_of_mod161051_eq161046 (m : ℕ)
    (hm : m % 161051 = 161046) :
    ¬ 161051 ∣ m := by
  exact not_dvd_of_mod_eq_ne_zero hm (by decide)

/-- Non-divisibility facts for concrete mod-5 power residues. -/
theorem concrete_mod5_power_not_dvd_facts :
    (∀ m, m % 5 = 4 → ¬ 5 ∣ m) ∧
      (∀ m, m % 25 = 24 → ¬ 25 ∣ m) ∧
      (∀ m, m % 125 = 124 → ¬ 125 ∣ m) ∧
      (∀ m, m % 625 = 624 → ¬ 625 ∣ m) ∧
      (∀ m, m % 3125 = 3124 → ¬ 3125 ∣ m) := by
  exact ⟨not_dvd_of_mod5_eq4,
    not_dvd_of_mod25_eq24,
    not_dvd_of_mod125_eq124,
    not_dvd_of_mod625_eq624,
    not_dvd_of_mod3125_eq3124⟩

/-- Non-divisibility facts for concrete mod-7 power residues. -/
theorem concrete_mod7_power_not_dvd_facts :
    (∀ m, m % 7 = 5 → ¬ 7 ∣ m) ∧
      (∀ m, m % 49 = 47 → ¬ 49 ∣ m) ∧
      (∀ m, m % 343 = 341 → ¬ 343 ∣ m) ∧
      (∀ m, m % 2401 = 2399 → ¬ 2401 ∣ m) ∧
      (∀ m, m % 16807 = 16805 → ¬ 16807 ∣ m) := by
  exact ⟨not_dvd_of_mod7_eq5,
    not_dvd_of_mod49_eq47,
    not_dvd_of_mod343_eq341,
    not_dvd_of_mod2401_eq2399,
    not_dvd_of_mod16807_eq16805⟩

/-- Non-divisibility facts for concrete mod-11 power residues. -/
theorem concrete_mod11_power_not_dvd_facts :
    (∀ m, m % 11 = 6 → ¬ 11 ∣ m) ∧
      (∀ m, m % 121 = 116 → ¬ 121 ∣ m) ∧
      (∀ m, m % 1331 = 1326 → ¬ 1331 ∣ m) ∧
      (∀ m, m % 14641 = 14636 → ¬ 14641 ∣ m) ∧
      (∀ m, m % 161051 = 161046 → ¬ 161051 ∣ m) := by
  exact ⟨not_dvd_of_mod11_eq6,
    not_dvd_of_mod121_eq116,
    not_dvd_of_mod1331_eq1326,
    not_dvd_of_mod14641_eq14636,
    not_dvd_of_mod161051_eq161046⟩

/-- A `24 mod 25` number is not divisible by `5`. -/
theorem not_dvd_by_5_of_mod25_eq24 (m : ℕ) (hm : m % 25 = 24) :
    ¬ 5 ∣ m := by
  exact not_dvd_of_mod5_eq4 m (mod_25_eq_24_implies_mod_5_eq_4 hm)

/-- A `124 mod 125` number is not divisible by `25`. -/
theorem not_dvd_by_25_of_mod125_eq124 (m : ℕ) (hm : m % 125 = 124) :
    ¬ 25 ∣ m := by
  exact not_dvd_of_mod25_eq24 m (mod_125_eq_124_implies_mod_25_eq_24 hm)

/-- A `124 mod 125` number is not divisible by `5`. -/
theorem not_dvd_by_5_of_mod125_eq124 (m : ℕ) (hm : m % 125 = 124) :
    ¬ 5 ∣ m := by
  exact not_dvd_of_mod5_eq4 m (mod_125_eq_124_implies_mod_5_eq_4 hm)

/-- A `624 mod 625` number is not divisible by `125`. -/
theorem not_dvd_by_125_of_mod625_eq624 (m : ℕ) (hm : m % 625 = 624) :
    ¬ 125 ∣ m := by
  exact not_dvd_of_mod125_eq124 m (mod_625_eq_624_implies_mod_125_eq_124 hm)

/-- A `624 mod 625` number is not divisible by `25`. -/
theorem not_dvd_by_25_of_mod625_eq624 (m : ℕ) (hm : m % 625 = 624) :
    ¬ 25 ∣ m := by
  exact not_dvd_of_mod25_eq24 m (mod_625_eq_624_implies_mod_25_eq_24 hm)

/-- A `624 mod 625` number is not divisible by `5`. -/
theorem not_dvd_by_5_of_mod625_eq624 (m : ℕ) (hm : m % 625 = 624) :
    ¬ 5 ∣ m := by
  exact not_dvd_of_mod5_eq4 m (mod_625_eq_624_implies_mod_5_eq_4 hm)

/-- A `3124 mod 3125` number is not divisible by `625`. -/
theorem not_dvd_by_625_of_mod3125_eq3124 (m : ℕ)
    (hm : m % 3125 = 3124) :
    ¬ 625 ∣ m := by
  exact not_dvd_of_mod625_eq624 m
    (mod_3125_eq_3124_implies_mod_625_eq_624 hm)

/-- A `3124 mod 3125` number is not divisible by `125`. -/
theorem not_dvd_by_125_of_mod3125_eq3124 (m : ℕ)
    (hm : m % 3125 = 3124) :
    ¬ 125 ∣ m := by
  exact not_dvd_of_mod125_eq124 m
    (mod_3125_eq_3124_implies_mod_125_eq_124 hm)

/-- A `3124 mod 3125` number is not divisible by `25`. -/
theorem not_dvd_by_25_of_mod3125_eq3124 (m : ℕ)
    (hm : m % 3125 = 3124) :
    ¬ 25 ∣ m := by
  exact not_dvd_of_mod25_eq24 m
    (mod_3125_eq_3124_implies_mod_25_eq_24 hm)

/-- A `3124 mod 3125` number is not divisible by `5`. -/
theorem not_dvd_by_5_of_mod3125_eq3124 (m : ℕ)
    (hm : m % 3125 = 3124) :
    ¬ 5 ∣ m := by
  exact not_dvd_of_mod5_eq4 m (mod_3125_eq_3124_implies_mod_5_eq_4 hm)

/-- A `47 mod 49` number is not divisible by `7`. -/
theorem not_dvd_by_7_of_mod49_eq47 (m : ℕ) (hm : m % 49 = 47) :
    ¬ 7 ∣ m := by
  exact not_dvd_of_mod7_eq5 m (mod_49_eq_47_implies_mod_7_eq_5 hm)

/-- A `341 mod 343` number is not divisible by `49`. -/
theorem not_dvd_by_49_of_mod343_eq341 (m : ℕ) (hm : m % 343 = 341) :
    ¬ 49 ∣ m := by
  exact not_dvd_of_mod49_eq47 m (mod_343_eq_341_implies_mod_49_eq_47 hm)

/-- A `341 mod 343` number is not divisible by `7`. -/
theorem not_dvd_by_7_of_mod343_eq341 (m : ℕ) (hm : m % 343 = 341) :
    ¬ 7 ∣ m := by
  exact not_dvd_of_mod7_eq5 m (mod_343_eq_341_implies_mod_7_eq_5 hm)

/-- A `2399 mod 2401` number is not divisible by `343`. -/
theorem not_dvd_by_343_of_mod2401_eq2399 (m : ℕ)
    (hm : m % 2401 = 2399) :
    ¬ 343 ∣ m := by
  exact not_dvd_of_mod343_eq341 m
    (mod_2401_eq_2399_implies_mod_343_eq_341 hm)

/-- A `2399 mod 2401` number is not divisible by `49`. -/
theorem not_dvd_by_49_of_mod2401_eq2399 (m : ℕ)
    (hm : m % 2401 = 2399) :
    ¬ 49 ∣ m := by
  exact not_dvd_of_mod49_eq47 m (mod_2401_eq_2399_implies_mod_49_eq_47 hm)

/-- A `2399 mod 2401` number is not divisible by `7`. -/
theorem not_dvd_by_7_of_mod2401_eq2399 (m : ℕ)
    (hm : m % 2401 = 2399) :
    ¬ 7 ∣ m := by
  exact not_dvd_of_mod7_eq5 m (mod_2401_eq_2399_implies_mod_7_eq_5 hm)

/-- A `16805 mod 16807` number is not divisible by `2401`. -/
theorem not_dvd_by_2401_of_mod16807_eq16805 (m : ℕ)
    (hm : m % 16807 = 16805) :
    ¬ 2401 ∣ m := by
  exact not_dvd_of_mod2401_eq2399 m
    (mod_16807_eq_16805_implies_mod_2401_eq_2399 hm)

/-- A `16805 mod 16807` number is not divisible by `343`. -/
theorem not_dvd_by_343_of_mod16807_eq16805 (m : ℕ)
    (hm : m % 16807 = 16805) :
    ¬ 343 ∣ m := by
  exact not_dvd_of_mod343_eq341 m
    (mod_16807_eq_16805_implies_mod_343_eq_341 hm)

/-- A `16805 mod 16807` number is not divisible by `49`. -/
theorem not_dvd_by_49_of_mod16807_eq16805 (m : ℕ)
    (hm : m % 16807 = 16805) :
    ¬ 49 ∣ m := by
  exact not_dvd_of_mod49_eq47 m (mod_16807_eq_16805_implies_mod_49_eq_47 hm)

/-- A `16805 mod 16807` number is not divisible by `7`. -/
theorem not_dvd_by_7_of_mod16807_eq16805 (m : ℕ)
    (hm : m % 16807 = 16805) :
    ¬ 7 ∣ m := by
  exact not_dvd_of_mod7_eq5 m (mod_16807_eq_16805_implies_mod_7_eq_5 hm)

/-- A `116 mod 121` number is not divisible by `11`. -/
theorem not_dvd_by_11_of_mod121_eq116 (m : ℕ) (hm : m % 121 = 116) :
    ¬ 11 ∣ m := by
  exact not_dvd_of_mod11_eq6 m (mod_121_eq_116_implies_mod_11_eq_6 hm)

/-- A `1326 mod 1331` number is not divisible by `121`. -/
theorem not_dvd_by_121_of_mod1331_eq1326 (m : ℕ)
    (hm : m % 1331 = 1326) :
    ¬ 121 ∣ m := by
  exact not_dvd_of_mod121_eq116 m
    (mod_1331_eq_1326_implies_mod_121_eq_116 hm)

/-- A `1326 mod 1331` number is not divisible by `11`. -/
theorem not_dvd_by_11_of_mod1331_eq1326 (m : ℕ)
    (hm : m % 1331 = 1326) :
    ¬ 11 ∣ m := by
  exact not_dvd_of_mod11_eq6 m (mod_1331_eq_1326_implies_mod_11_eq_6 hm)

/-- A `14636 mod 14641` number is not divisible by `1331`. -/
theorem not_dvd_by_1331_of_mod14641_eq14636 (m : ℕ)
    (hm : m % 14641 = 14636) :
    ¬ 1331 ∣ m := by
  exact not_dvd_of_mod1331_eq1326 m
    (mod_14641_eq_14636_implies_mod_1331_eq_1326 hm)

/-- A `14636 mod 14641` number is not divisible by `121`. -/
theorem not_dvd_by_121_of_mod14641_eq14636 (m : ℕ)
    (hm : m % 14641 = 14636) :
    ¬ 121 ∣ m := by
  exact not_dvd_of_mod121_eq116 m
    (mod_14641_eq_14636_implies_mod_121_eq_116 hm)

/-- A `14636 mod 14641` number is not divisible by `11`. -/
theorem not_dvd_by_11_of_mod14641_eq14636 (m : ℕ)
    (hm : m % 14641 = 14636) :
    ¬ 11 ∣ m := by
  exact not_dvd_of_mod11_eq6 m (mod_14641_eq_14636_implies_mod_11_eq_6 hm)

/-- A `161046 mod 161051` number is not divisible by `14641`. -/
theorem not_dvd_by_14641_of_mod161051_eq161046 (m : ℕ)
    (hm : m % 161051 = 161046) :
    ¬ 14641 ∣ m := by
  exact not_dvd_of_mod14641_eq14636 m
    (mod_161051_eq_161046_implies_mod_14641_eq_14636 hm)

/-- A `161046 mod 161051` number is not divisible by `1331`. -/
theorem not_dvd_by_1331_of_mod161051_eq161046 (m : ℕ)
    (hm : m % 161051 = 161046) :
    ¬ 1331 ∣ m := by
  exact not_dvd_of_mod1331_eq1326 m
    (mod_161051_eq_161046_implies_mod_1331_eq_1326 hm)

/-- A `161046 mod 161051` number is not divisible by `121`. -/
theorem not_dvd_by_121_of_mod161051_eq161046 (m : ℕ)
    (hm : m % 161051 = 161046) :
    ¬ 121 ∣ m := by
  exact not_dvd_of_mod121_eq116 m
    (mod_161051_eq_161046_implies_mod_121_eq_116 hm)

/-- A `161046 mod 161051` number is not divisible by `11`. -/
theorem not_dvd_by_11_of_mod161051_eq161046 (m : ℕ)
    (hm : m % 161051 = 161046) :
    ¬ 11 ∣ m := by
  exact not_dvd_of_mod11_eq6 m (mod_161051_eq_161046_implies_mod_11_eq_6 hm)

/-- Lower-power non-divisibility facts for concrete mod-5 power residues. -/
theorem concrete_mod5_power_lower_not_dvd_facts :
    (∀ m, m % 25 = 24 → ¬ 5 ∣ m) ∧
      (∀ m, m % 125 = 124 → ¬ 25 ∣ m) ∧
      (∀ m, m % 125 = 124 → ¬ 5 ∣ m) ∧
      (∀ m, m % 625 = 624 → ¬ 125 ∣ m) ∧
      (∀ m, m % 625 = 624 → ¬ 25 ∣ m) ∧
      (∀ m, m % 625 = 624 → ¬ 5 ∣ m) ∧
      (∀ m, m % 3125 = 3124 → ¬ 625 ∣ m) ∧
      (∀ m, m % 3125 = 3124 → ¬ 125 ∣ m) ∧
      (∀ m, m % 3125 = 3124 → ¬ 25 ∣ m) ∧
      (∀ m, m % 3125 = 3124 → ¬ 5 ∣ m) := by
  exact ⟨not_dvd_by_5_of_mod25_eq24,
    not_dvd_by_25_of_mod125_eq124,
    not_dvd_by_5_of_mod125_eq124,
    not_dvd_by_125_of_mod625_eq624,
    not_dvd_by_25_of_mod625_eq624,
    not_dvd_by_5_of_mod625_eq624,
    not_dvd_by_625_of_mod3125_eq3124,
    not_dvd_by_125_of_mod3125_eq3124,
    not_dvd_by_25_of_mod3125_eq3124,
    not_dvd_by_5_of_mod3125_eq3124⟩

/-- Lower-power non-divisibility facts for concrete mod-7 power residues. -/
theorem concrete_mod7_power_lower_not_dvd_facts :
    (∀ m, m % 49 = 47 → ¬ 7 ∣ m) ∧
      (∀ m, m % 343 = 341 → ¬ 49 ∣ m) ∧
      (∀ m, m % 343 = 341 → ¬ 7 ∣ m) ∧
      (∀ m, m % 2401 = 2399 → ¬ 343 ∣ m) ∧
      (∀ m, m % 2401 = 2399 → ¬ 49 ∣ m) ∧
      (∀ m, m % 2401 = 2399 → ¬ 7 ∣ m) ∧
      (∀ m, m % 16807 = 16805 → ¬ 2401 ∣ m) ∧
      (∀ m, m % 16807 = 16805 → ¬ 343 ∣ m) ∧
      (∀ m, m % 16807 = 16805 → ¬ 49 ∣ m) ∧
      (∀ m, m % 16807 = 16805 → ¬ 7 ∣ m) := by
  exact ⟨not_dvd_by_7_of_mod49_eq47,
    not_dvd_by_49_of_mod343_eq341,
    not_dvd_by_7_of_mod343_eq341,
    not_dvd_by_343_of_mod2401_eq2399,
    not_dvd_by_49_of_mod2401_eq2399,
    not_dvd_by_7_of_mod2401_eq2399,
    not_dvd_by_2401_of_mod16807_eq16805,
    not_dvd_by_343_of_mod16807_eq16805,
    not_dvd_by_49_of_mod16807_eq16805,
    not_dvd_by_7_of_mod16807_eq16805⟩

/-- Lower-power non-divisibility facts for concrete mod-11 power residues. -/
theorem concrete_mod11_power_lower_not_dvd_facts :
    (∀ m, m % 121 = 116 → ¬ 11 ∣ m) ∧
      (∀ m, m % 1331 = 1326 → ¬ 121 ∣ m) ∧
      (∀ m, m % 1331 = 1326 → ¬ 11 ∣ m) ∧
      (∀ m, m % 14641 = 14636 → ¬ 1331 ∣ m) ∧
      (∀ m, m % 14641 = 14636 → ¬ 121 ∣ m) ∧
      (∀ m, m % 14641 = 14636 → ¬ 11 ∣ m) ∧
      (∀ m, m % 161051 = 161046 → ¬ 14641 ∣ m) ∧
      (∀ m, m % 161051 = 161046 → ¬ 1331 ∣ m) ∧
      (∀ m, m % 161051 = 161046 → ¬ 121 ∣ m) ∧
      (∀ m, m % 161051 = 161046 → ¬ 11 ∣ m) := by
  exact ⟨not_dvd_by_11_of_mod121_eq116,
    not_dvd_by_121_of_mod1331_eq1326,
    not_dvd_by_11_of_mod1331_eq1326,
    not_dvd_by_1331_of_mod14641_eq14636,
    not_dvd_by_121_of_mod14641_eq14636,
    not_dvd_by_11_of_mod14641_eq14636,
    not_dvd_by_14641_of_mod161051_eq161046,
    not_dvd_by_1331_of_mod161051_eq161046,
    not_dvd_by_121_of_mod161051_eq161046,
    not_dvd_by_11_of_mod161051_eq161046⟩

/-- Shifting `5n+4` by `1` gives the next multiple of `5`. -/
theorem shift_5n_plus_4_add_one_eq_5_mul_succ (n : ℕ) :
    (5 * n + 4) + 1 = 5 * (n + 1) := by
  omega

/-- Shifting `25n+24` by `1` gives the next multiple of `25`. -/
theorem shift_25n_plus_24_add_one_eq_25_mul_succ (n : ℕ) :
    (25 * n + 24) + 1 = 25 * (n + 1) := by
  omega

/-- Shifting `125n+124` by `1` gives the next multiple of `125`. -/
theorem shift_125n_plus_124_add_one_eq_125_mul_succ (n : ℕ) :
    (125 * n + 124) + 1 = 125 * (n + 1) := by
  omega

/-- Shifting `625n+624` by `1` gives the next multiple of `625`. -/
theorem shift_625n_plus_624_add_one_eq_625_mul_succ (n : ℕ) :
    (625 * n + 624) + 1 = 625 * (n + 1) := by
  omega

/-- Shifting `3125n+3124` by `1` gives the next multiple of `3125`. -/
theorem shift_3125n_plus_3124_add_one_eq_3125_mul_succ (n : ℕ) :
    (3125 * n + 3124) + 1 = 3125 * (n + 1) := by
  omega

/-- Shifting `7n+5` by `2` gives the next multiple of `7`. -/
theorem shift_7n_plus_5_add_two_eq_7_mul_succ (n : ℕ) :
    (7 * n + 5) + 2 = 7 * (n + 1) := by
  omega

/-- Shifting `49n+47` by `2` gives the next multiple of `49`. -/
theorem shift_49n_plus_47_add_two_eq_49_mul_succ (n : ℕ) :
    (49 * n + 47) + 2 = 49 * (n + 1) := by
  omega

/-- Shifting `343n+341` by `2` gives the next multiple of `343`. -/
theorem shift_343n_plus_341_add_two_eq_343_mul_succ (n : ℕ) :
    (343 * n + 341) + 2 = 343 * (n + 1) := by
  omega

/-- Shifting `2401n+2399` by `2` gives the next multiple of `2401`. -/
theorem shift_2401n_plus_2399_add_two_eq_2401_mul_succ (n : ℕ) :
    (2401 * n + 2399) + 2 = 2401 * (n + 1) := by
  omega

/-- Shifting `16807n+16805` by `2` gives the next multiple of `16807`. -/
theorem shift_16807n_plus_16805_add_two_eq_16807_mul_succ (n : ℕ) :
    (16807 * n + 16805) + 2 = 16807 * (n + 1) := by
  omega

/-- Shifting `11n+6` by `5` gives the next multiple of `11`. -/
theorem shift_11n_plus_6_add_five_eq_11_mul_succ (n : ℕ) :
    (11 * n + 6) + 5 = 11 * (n + 1) := by
  omega

/-- Shifting `121n+116` by `5` gives the next multiple of `121`. -/
theorem shift_121n_plus_116_add_five_eq_121_mul_succ (n : ℕ) :
    (121 * n + 116) + 5 = 121 * (n + 1) := by
  omega

/-- Shifting `1331n+1326` by `5` gives the next multiple of `1331`. -/
theorem shift_1331n_plus_1326_add_five_eq_1331_mul_succ (n : ℕ) :
    (1331 * n + 1326) + 5 = 1331 * (n + 1) := by
  omega

/-- Shifting `14641n+14636` by `5` gives the next multiple of `14641`. -/
theorem shift_14641n_plus_14636_add_five_eq_14641_mul_succ (n : ℕ) :
    (14641 * n + 14636) + 5 = 14641 * (n + 1) := by
  omega

/-- Shifting `161051n+161046` by `5` gives the next multiple of `161051`. -/
theorem shift_161051n_plus_161046_add_five_eq_161051_mul_succ (n : ℕ) :
    (161051 * n + 161046) + 5 = 161051 * (n + 1) := by
  omega

/-- Shifted multiple facts for concrete mod-5 power progressions. -/
theorem concrete_mod5_power_shifted_multiple_facts :
    (∀ n, (5 * n + 4) + 1 = 5 * (n + 1)) ∧
      (∀ n, (25 * n + 24) + 1 = 25 * (n + 1)) ∧
      (∀ n, (125 * n + 124) + 1 = 125 * (n + 1)) ∧
      (∀ n, (625 * n + 624) + 1 = 625 * (n + 1)) ∧
      (∀ n, (3125 * n + 3124) + 1 = 3125 * (n + 1)) := by
  exact ⟨shift_5n_plus_4_add_one_eq_5_mul_succ,
    shift_25n_plus_24_add_one_eq_25_mul_succ,
    shift_125n_plus_124_add_one_eq_125_mul_succ,
    shift_625n_plus_624_add_one_eq_625_mul_succ,
    shift_3125n_plus_3124_add_one_eq_3125_mul_succ⟩

/-- Shifted multiple facts for concrete mod-7 power progressions. -/
theorem concrete_mod7_power_shifted_multiple_facts :
    (∀ n, (7 * n + 5) + 2 = 7 * (n + 1)) ∧
      (∀ n, (49 * n + 47) + 2 = 49 * (n + 1)) ∧
      (∀ n, (343 * n + 341) + 2 = 343 * (n + 1)) ∧
      (∀ n, (2401 * n + 2399) + 2 = 2401 * (n + 1)) ∧
      (∀ n, (16807 * n + 16805) + 2 = 16807 * (n + 1)) := by
  exact ⟨shift_7n_plus_5_add_two_eq_7_mul_succ,
    shift_49n_plus_47_add_two_eq_49_mul_succ,
    shift_343n_plus_341_add_two_eq_343_mul_succ,
    shift_2401n_plus_2399_add_two_eq_2401_mul_succ,
    shift_16807n_plus_16805_add_two_eq_16807_mul_succ⟩

/-- Shifted multiple facts for concrete mod-11 power progressions. -/
theorem concrete_mod11_power_shifted_multiple_facts :
    (∀ n, (11 * n + 6) + 5 = 11 * (n + 1)) ∧
      (∀ n, (121 * n + 116) + 5 = 121 * (n + 1)) ∧
      (∀ n, (1331 * n + 1326) + 5 = 1331 * (n + 1)) ∧
      (∀ n, (14641 * n + 14636) + 5 = 14641 * (n + 1)) ∧
      (∀ n, (161051 * n + 161046) + 5 = 161051 * (n + 1)) := by
  exact ⟨shift_11n_plus_6_add_five_eq_11_mul_succ,
    shift_121n_plus_116_add_five_eq_121_mul_succ,
    shift_1331n_plus_1326_add_five_eq_1331_mul_succ,
    shift_14641n_plus_14636_add_five_eq_14641_mul_succ,
    shift_161051n_plus_161046_add_five_eq_161051_mul_succ⟩

/-- Shifted quotient of `5n+4`. -/
theorem div_shift_5n_plus_4_add_one_by_5_eq_succ (n : ℕ) :
    ((5 * n + 4) + 1) / 5 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (5 * n + 4) + 1) (q := 5) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient of `25n+24`. -/
theorem div_shift_25n_plus_24_add_one_by_25_eq_succ (n : ℕ) :
    ((25 * n + 24) + 1) / 25 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (25 * n + 24) + 1) (q := 25) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient of `125n+124`. -/
theorem div_shift_125n_plus_124_add_one_by_125_eq_succ (n : ℕ) :
    ((125 * n + 124) + 1) / 125 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (125 * n + 124) + 1) (q := 125) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient of `625n+624`. -/
theorem div_shift_625n_plus_624_add_one_by_625_eq_succ (n : ℕ) :
    ((625 * n + 624) + 1) / 625 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (625 * n + 624) + 1) (q := 625) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient of `3125n+3124`. -/
theorem div_shift_3125n_plus_3124_add_one_by_3125_eq_succ (n : ℕ) :
    ((3125 * n + 3124) + 1) / 3125 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (3125 * n + 3124) + 1) (q := 3125) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient of `7n+5`. -/
theorem div_shift_7n_plus_5_add_two_by_7_eq_succ (n : ℕ) :
    ((7 * n + 5) + 2) / 7 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (7 * n + 5) + 2) (q := 7) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient of `49n+47`. -/
theorem div_shift_49n_plus_47_add_two_by_49_eq_succ (n : ℕ) :
    ((49 * n + 47) + 2) / 49 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (49 * n + 47) + 2) (q := 49) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient of `343n+341`. -/
theorem div_shift_343n_plus_341_add_two_by_343_eq_succ (n : ℕ) :
    ((343 * n + 341) + 2) / 343 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (343 * n + 341) + 2) (q := 343) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient of `2401n+2399`. -/
theorem div_shift_2401n_plus_2399_add_two_by_2401_eq_succ (n : ℕ) :
    ((2401 * n + 2399) + 2) / 2401 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (2401 * n + 2399) + 2) (q := 2401) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient of `16807n+16805`. -/
theorem div_shift_16807n_plus_16805_add_two_by_16807_eq_succ (n : ℕ) :
    ((16807 * n + 16805) + 2) / 16807 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (16807 * n + 16805) + 2) (q := 16807) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient of `11n+6`. -/
theorem div_shift_11n_plus_6_add_five_by_11_eq_succ (n : ℕ) :
    ((11 * n + 6) + 5) / 11 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (11 * n + 6) + 5) (q := 11) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient of `121n+116`. -/
theorem div_shift_121n_plus_116_add_five_by_121_eq_succ (n : ℕ) :
    ((121 * n + 116) + 5) / 121 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (121 * n + 116) + 5) (q := 121) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient of `1331n+1326`. -/
theorem div_shift_1331n_plus_1326_add_five_by_1331_eq_succ (n : ℕ) :
    ((1331 * n + 1326) + 5) / 1331 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (1331 * n + 1326) + 5) (q := 1331) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient of `14641n+14636`. -/
theorem div_shift_14641n_plus_14636_add_five_by_14641_eq_succ (n : ℕ) :
    ((14641 * n + 14636) + 5) / 14641 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (14641 * n + 14636) + 5) (q := 14641) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient of `161051n+161046`. -/
theorem div_shift_161051n_plus_161046_add_five_by_161051_eq_succ (n : ℕ) :
    ((161051 * n + 161046) + 5) / 161051 = n + 1 := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (161051 * n + 161046) + 5) (q := 161051) (y := n + 1) (r := 0)
    (by omega) (by decide)

/-- Shifted quotient facts for explicit concrete mod-5 power progressions. -/
theorem concrete_mod5_power_explicit_shifted_quotient_facts :
    (∀ n, ((5 * n + 4) + 1) / 5 = n + 1) ∧
      (∀ n, ((25 * n + 24) + 1) / 25 = n + 1) ∧
      (∀ n, ((125 * n + 124) + 1) / 125 = n + 1) ∧
      (∀ n, ((625 * n + 624) + 1) / 625 = n + 1) ∧
      (∀ n, ((3125 * n + 3124) + 1) / 3125 = n + 1) := by
  exact ⟨div_shift_5n_plus_4_add_one_by_5_eq_succ,
    div_shift_25n_plus_24_add_one_by_25_eq_succ,
    div_shift_125n_plus_124_add_one_by_125_eq_succ,
    div_shift_625n_plus_624_add_one_by_625_eq_succ,
    div_shift_3125n_plus_3124_add_one_by_3125_eq_succ⟩

/-- Shifted quotient facts for explicit concrete mod-7 power progressions. -/
theorem concrete_mod7_power_explicit_shifted_quotient_facts :
    (∀ n, ((7 * n + 5) + 2) / 7 = n + 1) ∧
      (∀ n, ((49 * n + 47) + 2) / 49 = n + 1) ∧
      (∀ n, ((343 * n + 341) + 2) / 343 = n + 1) ∧
      (∀ n, ((2401 * n + 2399) + 2) / 2401 = n + 1) ∧
      (∀ n, ((16807 * n + 16805) + 2) / 16807 = n + 1) := by
  exact ⟨div_shift_7n_plus_5_add_two_by_7_eq_succ,
    div_shift_49n_plus_47_add_two_by_49_eq_succ,
    div_shift_343n_plus_341_add_two_by_343_eq_succ,
    div_shift_2401n_plus_2399_add_two_by_2401_eq_succ,
    div_shift_16807n_plus_16805_add_two_by_16807_eq_succ⟩

/-- Shifted quotient facts for explicit concrete mod-11 power progressions. -/
theorem concrete_mod11_power_explicit_shifted_quotient_facts :
    (∀ n, ((11 * n + 6) + 5) / 11 = n + 1) ∧
      (∀ n, ((121 * n + 116) + 5) / 121 = n + 1) ∧
      (∀ n, ((1331 * n + 1326) + 5) / 1331 = n + 1) ∧
      (∀ n, ((14641 * n + 14636) + 5) / 14641 = n + 1) ∧
      (∀ n, ((161051 * n + 161046) + 5) / 161051 = n + 1) := by
  exact ⟨div_shift_11n_plus_6_add_five_by_11_eq_succ,
    div_shift_121n_plus_116_add_five_by_121_eq_succ,
    div_shift_1331n_plus_1326_add_five_by_1331_eq_succ,
    div_shift_14641n_plus_14636_add_five_by_14641_eq_succ,
    div_shift_161051n_plus_161046_add_five_by_161051_eq_succ⟩

/-- Shifted intermediate quotient from `125n+124` by `25`. -/
theorem div_shift_125n_plus_124_add_one_by_25_eq_5_mul_succ (n : ℕ) :
    ((125 * n + 124) + 1) / 25 = 5 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (125 * n + 124) + 1) (q := 25) (y := 5 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `625n+624` by `25`. -/
theorem div_shift_625n_plus_624_add_one_by_25_eq_25_mul_succ (n : ℕ) :
    ((625 * n + 624) + 1) / 25 = 25 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (625 * n + 624) + 1) (q := 25) (y := 25 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `625n+624` by `125`. -/
theorem div_shift_625n_plus_624_add_one_by_125_eq_5_mul_succ (n : ℕ) :
    ((625 * n + 624) + 1) / 125 = 5 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (625 * n + 624) + 1) (q := 125) (y := 5 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `3125n+3124` by `25`. -/
theorem div_shift_3125n_plus_3124_add_one_by_25_eq_125_mul_succ (n : ℕ) :
    ((3125 * n + 3124) + 1) / 25 = 125 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (3125 * n + 3124) + 1) (q := 25) (y := 125 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `3125n+3124` by `125`. -/
theorem div_shift_3125n_plus_3124_add_one_by_125_eq_25_mul_succ (n : ℕ) :
    ((3125 * n + 3124) + 1) / 125 = 25 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (3125 * n + 3124) + 1) (q := 125) (y := 25 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `3125n+3124` by `625`. -/
theorem div_shift_3125n_plus_3124_add_one_by_625_eq_5_mul_succ (n : ℕ) :
    ((3125 * n + 3124) + 1) / 625 = 5 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (3125 * n + 3124) + 1) (q := 625) (y := 5 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `343n+341` by `49`. -/
theorem div_shift_343n_plus_341_add_two_by_49_eq_7_mul_succ (n : ℕ) :
    ((343 * n + 341) + 2) / 49 = 7 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (343 * n + 341) + 2) (q := 49) (y := 7 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `2401n+2399` by `49`. -/
theorem div_shift_2401n_plus_2399_add_two_by_49_eq_49_mul_succ (n : ℕ) :
    ((2401 * n + 2399) + 2) / 49 = 49 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (2401 * n + 2399) + 2) (q := 49) (y := 49 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `2401n+2399` by `343`. -/
theorem div_shift_2401n_plus_2399_add_two_by_343_eq_7_mul_succ (n : ℕ) :
    ((2401 * n + 2399) + 2) / 343 = 7 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (2401 * n + 2399) + 2) (q := 343) (y := 7 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `16807n+16805` by `49`. -/
theorem div_shift_16807n_plus_16805_add_two_by_49_eq_343_mul_succ (n : ℕ) :
    ((16807 * n + 16805) + 2) / 49 = 343 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (16807 * n + 16805) + 2) (q := 49) (y := 343 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `16807n+16805` by `343`. -/
theorem div_shift_16807n_plus_16805_add_two_by_343_eq_49_mul_succ (n : ℕ) :
    ((16807 * n + 16805) + 2) / 343 = 49 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (16807 * n + 16805) + 2) (q := 343) (y := 49 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `16807n+16805` by `2401`. -/
theorem div_shift_16807n_plus_16805_add_two_by_2401_eq_7_mul_succ (n : ℕ) :
    ((16807 * n + 16805) + 2) / 2401 = 7 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (16807 * n + 16805) + 2) (q := 2401) (y := 7 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `1331n+1326` by `121`. -/
theorem div_shift_1331n_plus_1326_add_five_by_121_eq_11_mul_succ (n : ℕ) :
    ((1331 * n + 1326) + 5) / 121 = 11 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (1331 * n + 1326) + 5) (q := 121) (y := 11 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `14641n+14636` by `121`. -/
theorem div_shift_14641n_plus_14636_add_five_by_121_eq_121_mul_succ (n : ℕ) :
    ((14641 * n + 14636) + 5) / 121 = 121 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (14641 * n + 14636) + 5) (q := 121) (y := 121 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `14641n+14636` by `1331`. -/
theorem div_shift_14641n_plus_14636_add_five_by_1331_eq_11_mul_succ (n : ℕ) :
    ((14641 * n + 14636) + 5) / 1331 = 11 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (14641 * n + 14636) + 5) (q := 1331) (y := 11 * (n + 1)) (r := 0)
    (by omega) (by decide)

/-- Shifted intermediate quotient from `161051n+161046` by `121`. -/
theorem div_shift_161051n_plus_161046_add_five_by_121_eq_1331_mul_succ (n : ℕ) :
    ((161051 * n + 161046) + 5) / 121 = 1331 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (161051 * n + 161046) + 5) (q := 121) (y := 1331 * (n + 1))
    (r := 0) (by omega) (by decide)

/-- Shifted intermediate quotient from `161051n+161046` by `1331`. -/
theorem div_shift_161051n_plus_161046_add_five_by_1331_eq_121_mul_succ (n : ℕ) :
    ((161051 * n + 161046) + 5) / 1331 = 121 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (161051 * n + 161046) + 5) (q := 1331) (y := 121 * (n + 1))
    (r := 0) (by omega) (by decide)

/-- Shifted intermediate quotient from `161051n+161046` by `14641`. -/
theorem div_shift_161051n_plus_161046_add_five_by_14641_eq_11_mul_succ (n : ℕ) :
    ((161051 * n + 161046) + 5) / 14641 = 11 * (n + 1) := by
  exact div_eq_of_eq_mul_add_of_lt
    (x := (161051 * n + 161046) + 5) (q := 14641) (y := 11 * (n + 1))
    (r := 0) (by omega) (by decide)

/-- Shifted intermediate quotient facts for explicit mod-5 power progressions. -/
theorem concrete_mod5_power_explicit_shifted_intermediate_quotient_facts :
    (∀ n, ((125 * n + 124) + 1) / 25 = 5 * (n + 1)) ∧
      (∀ n, ((625 * n + 624) + 1) / 25 = 25 * (n + 1)) ∧
      (∀ n, ((625 * n + 624) + 1) / 125 = 5 * (n + 1)) ∧
      (∀ n, ((3125 * n + 3124) + 1) / 25 = 125 * (n + 1)) ∧
      (∀ n, ((3125 * n + 3124) + 1) / 125 = 25 * (n + 1)) ∧
      (∀ n, ((3125 * n + 3124) + 1) / 625 = 5 * (n + 1)) := by
  exact ⟨div_shift_125n_plus_124_add_one_by_25_eq_5_mul_succ,
    div_shift_625n_plus_624_add_one_by_25_eq_25_mul_succ,
    div_shift_625n_plus_624_add_one_by_125_eq_5_mul_succ,
    div_shift_3125n_plus_3124_add_one_by_25_eq_125_mul_succ,
    div_shift_3125n_plus_3124_add_one_by_125_eq_25_mul_succ,
    div_shift_3125n_plus_3124_add_one_by_625_eq_5_mul_succ⟩

/-- Shifted intermediate quotient facts for explicit mod-7 power progressions. -/
theorem concrete_mod7_power_explicit_shifted_intermediate_quotient_facts :
    (∀ n, ((343 * n + 341) + 2) / 49 = 7 * (n + 1)) ∧
      (∀ n, ((2401 * n + 2399) + 2) / 49 = 49 * (n + 1)) ∧
      (∀ n, ((2401 * n + 2399) + 2) / 343 = 7 * (n + 1)) ∧
      (∀ n, ((16807 * n + 16805) + 2) / 49 = 343 * (n + 1)) ∧
      (∀ n, ((16807 * n + 16805) + 2) / 343 = 49 * (n + 1)) ∧
      (∀ n, ((16807 * n + 16805) + 2) / 2401 = 7 * (n + 1)) := by
  exact ⟨div_shift_343n_plus_341_add_two_by_49_eq_7_mul_succ,
    div_shift_2401n_plus_2399_add_two_by_49_eq_49_mul_succ,
    div_shift_2401n_plus_2399_add_two_by_343_eq_7_mul_succ,
    div_shift_16807n_plus_16805_add_two_by_49_eq_343_mul_succ,
    div_shift_16807n_plus_16805_add_two_by_343_eq_49_mul_succ,
    div_shift_16807n_plus_16805_add_two_by_2401_eq_7_mul_succ⟩

/-- Shifted intermediate quotient facts for explicit mod-11 power progressions. -/
theorem concrete_mod11_power_explicit_shifted_intermediate_quotient_facts :
    (∀ n, ((1331 * n + 1326) + 5) / 121 = 11 * (n + 1)) ∧
      (∀ n, ((14641 * n + 14636) + 5) / 121 = 121 * (n + 1)) ∧
      (∀ n, ((14641 * n + 14636) + 5) / 1331 = 11 * (n + 1)) ∧
      (∀ n, ((161051 * n + 161046) + 5) / 121 = 1331 * (n + 1)) ∧
      (∀ n, ((161051 * n + 161046) + 5) / 1331 = 121 * (n + 1)) ∧
      (∀ n, ((161051 * n + 161046) + 5) / 14641 = 11 * (n + 1)) := by
  exact ⟨div_shift_1331n_plus_1326_add_five_by_121_eq_11_mul_succ,
    div_shift_14641n_plus_14636_add_five_by_121_eq_121_mul_succ,
    div_shift_14641n_plus_14636_add_five_by_1331_eq_11_mul_succ,
    div_shift_161051n_plus_161046_add_five_by_121_eq_1331_mul_succ,
    div_shift_161051n_plus_161046_add_five_by_1331_eq_121_mul_succ,
    div_shift_161051n_plus_161046_add_five_by_14641_eq_11_mul_succ⟩

/-- Membership in `q*n+r` is equivalent to the shifted multiple
`m+c=q*(n+1)` when `r+c=q`. -/
theorem exists_mul_add_iff_exists_shifted_mul_succ {q r c m : ℕ} (hmod : r + c = q) :
    (∃ n, m = q * n + r) ↔ ∃ n, m + c = q * (n + 1) := by
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    nlinarith
  · rintro ⟨n, h⟩
    refine ⟨n, ?_⟩
    have htarget : m + c = (q * n + r) + c := by
      calc
        m + c = q * (n + 1) := h
        _ = q * n + q := by ring
        _ = q * n + (r + c) := by rw [hmod]
        _ = (q * n + r) + c := by ring
    exact Nat.add_right_cancel htarget

/-- Membership in `5n+4` is equivalent to a shifted multiple of `5`. -/
theorem exists_5n_plus_4_iff_exists_add_one_eq_5_mul_succ (m : ℕ) :
    (∃ n, m = 5 * n + 4) ↔ ∃ n, m + 1 = 5 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 5) (r := 4) (c := 1)
    (by decide)

/-- Membership in `25n+24` is equivalent to a shifted multiple of `25`. -/
theorem exists_25n_plus_24_iff_exists_add_one_eq_25_mul_succ (m : ℕ) :
    (∃ n, m = 25 * n + 24) ↔ ∃ n, m + 1 = 25 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 25) (r := 24) (c := 1)
    (by decide)

/-- Membership in `125n+124` is equivalent to a shifted multiple of `125`. -/
theorem exists_125n_plus_124_iff_exists_add_one_eq_125_mul_succ (m : ℕ) :
    (∃ n, m = 125 * n + 124) ↔ ∃ n, m + 1 = 125 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 125) (r := 124) (c := 1)
    (by decide)

/-- Membership in `625n+624` is equivalent to a shifted multiple of `625`. -/
theorem exists_625n_plus_624_iff_exists_add_one_eq_625_mul_succ (m : ℕ) :
    (∃ n, m = 625 * n + 624) ↔ ∃ n, m + 1 = 625 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 625) (r := 624) (c := 1)
    (by decide)

/-- Membership in `3125n+3124` is equivalent to a shifted multiple of `3125`. -/
theorem exists_3125n_plus_3124_iff_exists_add_one_eq_3125_mul_succ (m : ℕ) :
    (∃ n, m = 3125 * n + 3124) ↔ ∃ n, m + 1 = 3125 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 3125) (r := 3124)
    (c := 1) (by decide)

/-- Membership in `7n+5` is equivalent to a shifted multiple of `7`. -/
theorem exists_7n_plus_5_iff_exists_add_two_eq_7_mul_succ (m : ℕ) :
    (∃ n, m = 7 * n + 5) ↔ ∃ n, m + 2 = 7 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 7) (r := 5) (c := 2)
    (by decide)

/-- Membership in `49n+47` is equivalent to a shifted multiple of `49`. -/
theorem exists_49n_plus_47_iff_exists_add_two_eq_49_mul_succ (m : ℕ) :
    (∃ n, m = 49 * n + 47) ↔ ∃ n, m + 2 = 49 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 49) (r := 47) (c := 2)
    (by decide)

/-- Membership in `343n+341` is equivalent to a shifted multiple of `343`. -/
theorem exists_343n_plus_341_iff_exists_add_two_eq_343_mul_succ (m : ℕ) :
    (∃ n, m = 343 * n + 341) ↔ ∃ n, m + 2 = 343 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 343) (r := 341) (c := 2)
    (by decide)

/-- Membership in `2401n+2399` is equivalent to a shifted multiple of `2401`. -/
theorem exists_2401n_plus_2399_iff_exists_add_two_eq_2401_mul_succ (m : ℕ) :
    (∃ n, m = 2401 * n + 2399) ↔ ∃ n, m + 2 = 2401 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 2401) (r := 2399)
    (c := 2) (by decide)

/-- Membership in `16807n+16805` is equivalent to a shifted multiple of
`16807`. -/
theorem exists_16807n_plus_16805_iff_exists_add_two_eq_16807_mul_succ (m : ℕ) :
    (∃ n, m = 16807 * n + 16805) ↔ ∃ n, m + 2 = 16807 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 16807) (r := 16805)
    (c := 2) (by decide)

/-- Membership in `11n+6` is equivalent to a shifted multiple of `11`. -/
theorem exists_11n_plus_6_iff_exists_add_five_eq_11_mul_succ (m : ℕ) :
    (∃ n, m = 11 * n + 6) ↔ ∃ n, m + 5 = 11 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 11) (r := 6) (c := 5)
    (by decide)

/-- Membership in `121n+116` is equivalent to a shifted multiple of `121`. -/
theorem exists_121n_plus_116_iff_exists_add_five_eq_121_mul_succ (m : ℕ) :
    (∃ n, m = 121 * n + 116) ↔ ∃ n, m + 5 = 121 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 121) (r := 116) (c := 5)
    (by decide)

/-- Membership in `1331n+1326` is equivalent to a shifted multiple of `1331`. -/
theorem exists_1331n_plus_1326_iff_exists_add_five_eq_1331_mul_succ (m : ℕ) :
    (∃ n, m = 1331 * n + 1326) ↔ ∃ n, m + 5 = 1331 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 1331) (r := 1326)
    (c := 5) (by decide)

/-- Membership in `14641n+14636` is equivalent to a shifted multiple of
`14641`. -/
theorem exists_14641n_plus_14636_iff_exists_add_five_eq_14641_mul_succ (m : ℕ) :
    (∃ n, m = 14641 * n + 14636) ↔ ∃ n, m + 5 = 14641 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 14641) (r := 14636)
    (c := 5) (by decide)

/-- Membership in `161051n+161046` is equivalent to a shifted multiple of
`161051`. -/
theorem exists_161051n_plus_161046_iff_exists_add_five_eq_161051_mul_succ
    (m : ℕ) :
    (∃ n, m = 161051 * n + 161046) ↔ ∃ n, m + 5 = 161051 * (n + 1) := by
  exact exists_mul_add_iff_exists_shifted_mul_succ (q := 161051) (r := 161046)
    (c := 5) (by decide)

/-- Shifted-multiple membership iff facts for concrete mod-5 power
progressions. -/
theorem concrete_mod5_power_shifted_multiple_membership_iff_facts :
    (∀ m, (∃ n, m = 5 * n + 4) ↔ ∃ n, m + 1 = 5 * (n + 1)) ∧
      (∀ m, (∃ n, m = 25 * n + 24) ↔ ∃ n, m + 1 = 25 * (n + 1)) ∧
      (∀ m, (∃ n, m = 125 * n + 124) ↔ ∃ n, m + 1 = 125 * (n + 1)) ∧
      (∀ m, (∃ n, m = 625 * n + 624) ↔ ∃ n, m + 1 = 625 * (n + 1)) ∧
      (∀ m, (∃ n, m = 3125 * n + 3124) ↔
        ∃ n, m + 1 = 3125 * (n + 1)) := by
  exact ⟨exists_5n_plus_4_iff_exists_add_one_eq_5_mul_succ,
    exists_25n_plus_24_iff_exists_add_one_eq_25_mul_succ,
    exists_125n_plus_124_iff_exists_add_one_eq_125_mul_succ,
    exists_625n_plus_624_iff_exists_add_one_eq_625_mul_succ,
    exists_3125n_plus_3124_iff_exists_add_one_eq_3125_mul_succ⟩

/-- Shifted-multiple membership iff facts for concrete mod-7 power
progressions. -/
theorem concrete_mod7_power_shifted_multiple_membership_iff_facts :
    (∀ m, (∃ n, m = 7 * n + 5) ↔ ∃ n, m + 2 = 7 * (n + 1)) ∧
      (∀ m, (∃ n, m = 49 * n + 47) ↔ ∃ n, m + 2 = 49 * (n + 1)) ∧
      (∀ m, (∃ n, m = 343 * n + 341) ↔ ∃ n, m + 2 = 343 * (n + 1)) ∧
      (∀ m, (∃ n, m = 2401 * n + 2399) ↔
        ∃ n, m + 2 = 2401 * (n + 1)) ∧
      (∀ m, (∃ n, m = 16807 * n + 16805) ↔
        ∃ n, m + 2 = 16807 * (n + 1)) := by
  exact ⟨exists_7n_plus_5_iff_exists_add_two_eq_7_mul_succ,
    exists_49n_plus_47_iff_exists_add_two_eq_49_mul_succ,
    exists_343n_plus_341_iff_exists_add_two_eq_343_mul_succ,
    exists_2401n_plus_2399_iff_exists_add_two_eq_2401_mul_succ,
    exists_16807n_plus_16805_iff_exists_add_two_eq_16807_mul_succ⟩

/-- Shifted-multiple membership iff facts for concrete mod-11 power
progressions. -/
theorem concrete_mod11_power_shifted_multiple_membership_iff_facts :
    (∀ m, (∃ n, m = 11 * n + 6) ↔ ∃ n, m + 5 = 11 * (n + 1)) ∧
      (∀ m, (∃ n, m = 121 * n + 116) ↔
        ∃ n, m + 5 = 121 * (n + 1)) ∧
      (∀ m, (∃ n, m = 1331 * n + 1326) ↔
        ∃ n, m + 5 = 1331 * (n + 1)) ∧
      (∀ m, (∃ n, m = 14641 * n + 14636) ↔
        ∃ n, m + 5 = 14641 * (n + 1)) ∧
      (∀ m, (∃ n, m = 161051 * n + 161046) ↔
        ∃ n, m + 5 = 161051 * (n + 1)) := by
  exact ⟨exists_11n_plus_6_iff_exists_add_five_eq_11_mul_succ,
    exists_121n_plus_116_iff_exists_add_five_eq_121_mul_succ,
    exists_1331n_plus_1326_iff_exists_add_five_eq_1331_mul_succ,
    exists_14641n_plus_14636_iff_exists_add_five_eq_14641_mul_succ,
    exists_161051n_plus_161046_iff_exists_add_five_eq_161051_mul_succ⟩

/-- Shifted positive multiples are exactly divisibility of the shifted value. -/
theorem exists_shifted_mul_succ_iff_dvd_add {q c m : ℕ} (hc : 0 < c) :
    (∃ n, m + c = q * (n + 1)) ↔ q ∣ m + c := by
  constructor
  · rintro ⟨n, h⟩
    exact ⟨n + 1, h⟩
  · rintro ⟨k, hk⟩
    have hkpos : 0 < k := by
      by_contra hzero
      have hk0 : k = 0 := by omega
      rw [hk0, Nat.mul_zero] at hk
      omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    exact ⟨n, hk⟩

/-- Shifted multiple form for `5n+4` is exactly divisibility of `m+1` by `5`. -/
theorem exists_add_one_eq_5_mul_succ_iff_dvd_add_one_by_5 (m : ℕ) :
    (∃ n, m + 1 = 5 * (n + 1)) ↔ 5 ∣ m + 1 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 5) (c := 1) (by decide)

/-- Shifted multiple form for `25n+24` is exactly divisibility of `m+1` by
`25`. -/
theorem exists_add_one_eq_25_mul_succ_iff_dvd_add_one_by_25 (m : ℕ) :
    (∃ n, m + 1 = 25 * (n + 1)) ↔ 25 ∣ m + 1 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 25) (c := 1) (by decide)

/-- Shifted multiple form for `125n+124` is exactly divisibility of `m+1` by
`125`. -/
theorem exists_add_one_eq_125_mul_succ_iff_dvd_add_one_by_125 (m : ℕ) :
    (∃ n, m + 1 = 125 * (n + 1)) ↔ 125 ∣ m + 1 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 125) (c := 1) (by decide)

/-- Shifted multiple form for `625n+624` is exactly divisibility of `m+1` by
`625`. -/
theorem exists_add_one_eq_625_mul_succ_iff_dvd_add_one_by_625 (m : ℕ) :
    (∃ n, m + 1 = 625 * (n + 1)) ↔ 625 ∣ m + 1 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 625) (c := 1) (by decide)

/-- Shifted multiple form for `3125n+3124` is exactly divisibility of `m+1` by
`3125`. -/
theorem exists_add_one_eq_3125_mul_succ_iff_dvd_add_one_by_3125 (m : ℕ) :
    (∃ n, m + 1 = 3125 * (n + 1)) ↔ 3125 ∣ m + 1 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 3125) (c := 1) (by decide)

/-- Shifted multiple form for `7n+5` is exactly divisibility of `m+2` by `7`. -/
theorem exists_add_two_eq_7_mul_succ_iff_dvd_add_two_by_7 (m : ℕ) :
    (∃ n, m + 2 = 7 * (n + 1)) ↔ 7 ∣ m + 2 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 7) (c := 2) (by decide)

/-- Shifted multiple form for `49n+47` is exactly divisibility of `m+2` by
`49`. -/
theorem exists_add_two_eq_49_mul_succ_iff_dvd_add_two_by_49 (m : ℕ) :
    (∃ n, m + 2 = 49 * (n + 1)) ↔ 49 ∣ m + 2 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 49) (c := 2) (by decide)

/-- Shifted multiple form for `343n+341` is exactly divisibility of `m+2` by
`343`. -/
theorem exists_add_two_eq_343_mul_succ_iff_dvd_add_two_by_343 (m : ℕ) :
    (∃ n, m + 2 = 343 * (n + 1)) ↔ 343 ∣ m + 2 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 343) (c := 2) (by decide)

/-- Shifted multiple form for `2401n+2399` is exactly divisibility of `m+2` by
`2401`. -/
theorem exists_add_two_eq_2401_mul_succ_iff_dvd_add_two_by_2401 (m : ℕ) :
    (∃ n, m + 2 = 2401 * (n + 1)) ↔ 2401 ∣ m + 2 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 2401) (c := 2) (by decide)

/-- Shifted multiple form for `16807n+16805` is exactly divisibility of `m+2`
by `16807`. -/
theorem exists_add_two_eq_16807_mul_succ_iff_dvd_add_two_by_16807 (m : ℕ) :
    (∃ n, m + 2 = 16807 * (n + 1)) ↔ 16807 ∣ m + 2 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 16807) (c := 2) (by decide)

/-- Shifted multiple form for `11n+6` is exactly divisibility of `m+5` by
`11`. -/
theorem exists_add_five_eq_11_mul_succ_iff_dvd_add_five_by_11 (m : ℕ) :
    (∃ n, m + 5 = 11 * (n + 1)) ↔ 11 ∣ m + 5 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 11) (c := 5) (by decide)

/-- Shifted multiple form for `121n+116` is exactly divisibility of `m+5` by
`121`. -/
theorem exists_add_five_eq_121_mul_succ_iff_dvd_add_five_by_121 (m : ℕ) :
    (∃ n, m + 5 = 121 * (n + 1)) ↔ 121 ∣ m + 5 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 121) (c := 5) (by decide)

/-- Shifted multiple form for `1331n+1326` is exactly divisibility of `m+5` by
`1331`. -/
theorem exists_add_five_eq_1331_mul_succ_iff_dvd_add_five_by_1331 (m : ℕ) :
    (∃ n, m + 5 = 1331 * (n + 1)) ↔ 1331 ∣ m + 5 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 1331) (c := 5) (by decide)

/-- Shifted multiple form for `14641n+14636` is exactly divisibility of `m+5`
by `14641`. -/
theorem exists_add_five_eq_14641_mul_succ_iff_dvd_add_five_by_14641 (m : ℕ) :
    (∃ n, m + 5 = 14641 * (n + 1)) ↔ 14641 ∣ m + 5 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 14641) (c := 5) (by decide)

/-- Shifted multiple form for `161051n+161046` is exactly divisibility of
`m+5` by `161051`. -/
theorem exists_add_five_eq_161051_mul_succ_iff_dvd_add_five_by_161051
    (m : ℕ) :
    (∃ n, m + 5 = 161051 * (n + 1)) ↔ 161051 ∣ m + 5 := by
  exact exists_shifted_mul_succ_iff_dvd_add (q := 161051) (c := 5) (by decide)

/-- Shifted-multiple divisibility iff facts for concrete mod-5 power
progressions. -/
theorem concrete_mod5_power_shifted_multiple_iff_dvd_facts :
    (∀ m, (∃ n, m + 1 = 5 * (n + 1)) ↔ 5 ∣ m + 1) ∧
      (∀ m, (∃ n, m + 1 = 25 * (n + 1)) ↔ 25 ∣ m + 1) ∧
      (∀ m, (∃ n, m + 1 = 125 * (n + 1)) ↔ 125 ∣ m + 1) ∧
      (∀ m, (∃ n, m + 1 = 625 * (n + 1)) ↔ 625 ∣ m + 1) ∧
      (∀ m, (∃ n, m + 1 = 3125 * (n + 1)) ↔ 3125 ∣ m + 1) := by
  exact ⟨exists_add_one_eq_5_mul_succ_iff_dvd_add_one_by_5,
    exists_add_one_eq_25_mul_succ_iff_dvd_add_one_by_25,
    exists_add_one_eq_125_mul_succ_iff_dvd_add_one_by_125,
    exists_add_one_eq_625_mul_succ_iff_dvd_add_one_by_625,
    exists_add_one_eq_3125_mul_succ_iff_dvd_add_one_by_3125⟩

/-- Shifted-multiple divisibility iff facts for concrete mod-7 power
progressions. -/
theorem concrete_mod7_power_shifted_multiple_iff_dvd_facts :
    (∀ m, (∃ n, m + 2 = 7 * (n + 1)) ↔ 7 ∣ m + 2) ∧
      (∀ m, (∃ n, m + 2 = 49 * (n + 1)) ↔ 49 ∣ m + 2) ∧
      (∀ m, (∃ n, m + 2 = 343 * (n + 1)) ↔ 343 ∣ m + 2) ∧
      (∀ m, (∃ n, m + 2 = 2401 * (n + 1)) ↔ 2401 ∣ m + 2) ∧
      (∀ m, (∃ n, m + 2 = 16807 * (n + 1)) ↔ 16807 ∣ m + 2) := by
  exact ⟨exists_add_two_eq_7_mul_succ_iff_dvd_add_two_by_7,
    exists_add_two_eq_49_mul_succ_iff_dvd_add_two_by_49,
    exists_add_two_eq_343_mul_succ_iff_dvd_add_two_by_343,
    exists_add_two_eq_2401_mul_succ_iff_dvd_add_two_by_2401,
    exists_add_two_eq_16807_mul_succ_iff_dvd_add_two_by_16807⟩

/-- Shifted-multiple divisibility iff facts for concrete mod-11 power
progressions. -/
theorem concrete_mod11_power_shifted_multiple_iff_dvd_facts :
    (∀ m, (∃ n, m + 5 = 11 * (n + 1)) ↔ 11 ∣ m + 5) ∧
      (∀ m, (∃ n, m + 5 = 121 * (n + 1)) ↔ 121 ∣ m + 5) ∧
      (∀ m, (∃ n, m + 5 = 1331 * (n + 1)) ↔ 1331 ∣ m + 5) ∧
      (∀ m, (∃ n, m + 5 = 14641 * (n + 1)) ↔ 14641 ∣ m + 5) ∧
      (∀ m, (∃ n, m + 5 = 161051 * (n + 1)) ↔ 161051 ∣ m + 5) := by
  exact ⟨exists_add_five_eq_11_mul_succ_iff_dvd_add_five_by_11,
    exists_add_five_eq_121_mul_succ_iff_dvd_add_five_by_121,
    exists_add_five_eq_1331_mul_succ_iff_dvd_add_five_by_1331,
    exists_add_five_eq_14641_mul_succ_iff_dvd_add_five_by_14641,
    exists_add_five_eq_161051_mul_succ_iff_dvd_add_five_by_161051⟩

/-- Negated shifted positive multiples are exactly negated divisibility of
the shifted value. -/
theorem not_exists_shifted_mul_succ_iff_not_dvd_add {q c m : ℕ} (hc : 0 < c) :
    (¬ ∃ n, m + c = q * (n + 1)) ↔ ¬ (q ∣ m + c) := by
  constructor
  · intro h hd
    exact h ((exists_shifted_mul_succ_iff_dvd_add (q := q) (c := c)
      (m := m) hc).mpr hd)
  · intro h he
    exact h ((exists_shifted_mul_succ_iff_dvd_add (q := q) (c := c)
      (m := m) hc).mp he)

/-- Shifted nonmembership form for `5n+4` is exactly nondivisibility of
`m+1` by `5`. -/
theorem not_exists_add_one_eq_5_mul_succ_iff_not_dvd_add_one_by_5 (m : ℕ) :
    (¬ ∃ n, m + 1 = 5 * (n + 1)) ↔ ¬ (5 ∣ m + 1) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 5) (c := 1) (by decide)

/-- Shifted nonmembership form for `25n+24` is exactly nondivisibility of
`m+1` by `25`. -/
theorem not_exists_add_one_eq_25_mul_succ_iff_not_dvd_add_one_by_25 (m : ℕ) :
    (¬ ∃ n, m + 1 = 25 * (n + 1)) ↔ ¬ (25 ∣ m + 1) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 25) (c := 1) (by decide)

/-- Shifted nonmembership form for `125n+124` is exactly nondivisibility of
`m+1` by `125`. -/
theorem not_exists_add_one_eq_125_mul_succ_iff_not_dvd_add_one_by_125 (m : ℕ) :
    (¬ ∃ n, m + 1 = 125 * (n + 1)) ↔ ¬ (125 ∣ m + 1) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 125) (c := 1) (by decide)

/-- Shifted nonmembership form for `625n+624` is exactly nondivisibility of
`m+1` by `625`. -/
theorem not_exists_add_one_eq_625_mul_succ_iff_not_dvd_add_one_by_625 (m : ℕ) :
    (¬ ∃ n, m + 1 = 625 * (n + 1)) ↔ ¬ (625 ∣ m + 1) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 625) (c := 1) (by decide)

/-- Shifted nonmembership form for `3125n+3124` is exactly nondivisibility of
`m+1` by `3125`. -/
theorem not_exists_add_one_eq_3125_mul_succ_iff_not_dvd_add_one_by_3125
    (m : ℕ) :
    (¬ ∃ n, m + 1 = 3125 * (n + 1)) ↔ ¬ (3125 ∣ m + 1) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 3125) (c := 1) (by decide)

/-- Shifted nonmembership form for `7n+5` is exactly nondivisibility of
`m+2` by `7`. -/
theorem not_exists_add_two_eq_7_mul_succ_iff_not_dvd_add_two_by_7 (m : ℕ) :
    (¬ ∃ n, m + 2 = 7 * (n + 1)) ↔ ¬ (7 ∣ m + 2) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 7) (c := 2) (by decide)

/-- Shifted nonmembership form for `49n+47` is exactly nondivisibility of
`m+2` by `49`. -/
theorem not_exists_add_two_eq_49_mul_succ_iff_not_dvd_add_two_by_49 (m : ℕ) :
    (¬ ∃ n, m + 2 = 49 * (n + 1)) ↔ ¬ (49 ∣ m + 2) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 49) (c := 2) (by decide)

/-- Shifted nonmembership form for `343n+341` is exactly nondivisibility of
`m+2` by `343`. -/
theorem not_exists_add_two_eq_343_mul_succ_iff_not_dvd_add_two_by_343 (m : ℕ) :
    (¬ ∃ n, m + 2 = 343 * (n + 1)) ↔ ¬ (343 ∣ m + 2) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 343) (c := 2) (by decide)

/-- Shifted nonmembership form for `2401n+2399` is exactly nondivisibility of
`m+2` by `2401`. -/
theorem not_exists_add_two_eq_2401_mul_succ_iff_not_dvd_add_two_by_2401
    (m : ℕ) :
    (¬ ∃ n, m + 2 = 2401 * (n + 1)) ↔ ¬ (2401 ∣ m + 2) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 2401) (c := 2) (by decide)

/-- Shifted nonmembership form for `16807n+16805` is exactly nondivisibility
of `m+2` by `16807`. -/
theorem not_exists_add_two_eq_16807_mul_succ_iff_not_dvd_add_two_by_16807
    (m : ℕ) :
    (¬ ∃ n, m + 2 = 16807 * (n + 1)) ↔ ¬ (16807 ∣ m + 2) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 16807) (c := 2) (by decide)

/-- Shifted nonmembership form for `11n+6` is exactly nondivisibility of
`m+5` by `11`. -/
theorem not_exists_add_five_eq_11_mul_succ_iff_not_dvd_add_five_by_11 (m : ℕ) :
    (¬ ∃ n, m + 5 = 11 * (n + 1)) ↔ ¬ (11 ∣ m + 5) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 11) (c := 5) (by decide)

/-- Shifted nonmembership form for `121n+116` is exactly nondivisibility of
`m+5` by `121`. -/
theorem not_exists_add_five_eq_121_mul_succ_iff_not_dvd_add_five_by_121
    (m : ℕ) :
    (¬ ∃ n, m + 5 = 121 * (n + 1)) ↔ ¬ (121 ∣ m + 5) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 121) (c := 5) (by decide)

/-- Shifted nonmembership form for `1331n+1326` is exactly nondivisibility of
`m+5` by `1331`. -/
theorem not_exists_add_five_eq_1331_mul_succ_iff_not_dvd_add_five_by_1331
    (m : ℕ) :
    (¬ ∃ n, m + 5 = 1331 * (n + 1)) ↔ ¬ (1331 ∣ m + 5) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 1331) (c := 5) (by decide)

/-- Shifted nonmembership form for `14641n+14636` is exactly nondivisibility
of `m+5` by `14641`. -/
theorem not_exists_add_five_eq_14641_mul_succ_iff_not_dvd_add_five_by_14641
    (m : ℕ) :
    (¬ ∃ n, m + 5 = 14641 * (n + 1)) ↔ ¬ (14641 ∣ m + 5) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 14641) (c := 5) (by decide)

/-- Shifted nonmembership form for `161051n+161046` is exactly
nondivisibility of `m+5` by `161051`. -/
theorem not_exists_add_five_eq_161051_mul_succ_iff_not_dvd_add_five_by_161051
    (m : ℕ) :
    (¬ ∃ n, m + 5 = 161051 * (n + 1)) ↔ ¬ (161051 ∣ m + 5) := by
  exact not_exists_shifted_mul_succ_iff_not_dvd_add (q := 161051) (c := 5) (by decide)

/-- Concrete mod-5 power shifted nonmembership iff shifted nondivisibility. -/
theorem concrete_mod5_power_shifted_nonmembership_iff_not_dvd_facts :
    (∀ m, (¬ ∃ n, m + 1 = 5 * (n + 1)) ↔ ¬ (5 ∣ m + 1)) ∧
      (∀ m, (¬ ∃ n, m + 1 = 25 * (n + 1)) ↔ ¬ (25 ∣ m + 1)) ∧
      (∀ m, (¬ ∃ n, m + 1 = 125 * (n + 1)) ↔ ¬ (125 ∣ m + 1)) ∧
      (∀ m, (¬ ∃ n, m + 1 = 625 * (n + 1)) ↔ ¬ (625 ∣ m + 1)) ∧
      (∀ m, (¬ ∃ n, m + 1 = 3125 * (n + 1)) ↔ ¬ (3125 ∣ m + 1)) := by
  exact ⟨not_exists_add_one_eq_5_mul_succ_iff_not_dvd_add_one_by_5,
    not_exists_add_one_eq_25_mul_succ_iff_not_dvd_add_one_by_25,
    not_exists_add_one_eq_125_mul_succ_iff_not_dvd_add_one_by_125,
    not_exists_add_one_eq_625_mul_succ_iff_not_dvd_add_one_by_625,
    not_exists_add_one_eq_3125_mul_succ_iff_not_dvd_add_one_by_3125⟩

/-- Concrete mod-7 power shifted nonmembership iff shifted nondivisibility. -/
theorem concrete_mod7_power_shifted_nonmembership_iff_not_dvd_facts :
    (∀ m, (¬ ∃ n, m + 2 = 7 * (n + 1)) ↔ ¬ (7 ∣ m + 2)) ∧
      (∀ m, (¬ ∃ n, m + 2 = 49 * (n + 1)) ↔ ¬ (49 ∣ m + 2)) ∧
      (∀ m, (¬ ∃ n, m + 2 = 343 * (n + 1)) ↔ ¬ (343 ∣ m + 2)) ∧
      (∀ m, (¬ ∃ n, m + 2 = 2401 * (n + 1)) ↔ ¬ (2401 ∣ m + 2)) ∧
      (∀ m, (¬ ∃ n, m + 2 = 16807 * (n + 1)) ↔ ¬ (16807 ∣ m + 2)) := by
  exact ⟨not_exists_add_two_eq_7_mul_succ_iff_not_dvd_add_two_by_7,
    not_exists_add_two_eq_49_mul_succ_iff_not_dvd_add_two_by_49,
    not_exists_add_two_eq_343_mul_succ_iff_not_dvd_add_two_by_343,
    not_exists_add_two_eq_2401_mul_succ_iff_not_dvd_add_two_by_2401,
    not_exists_add_two_eq_16807_mul_succ_iff_not_dvd_add_two_by_16807⟩

/-- Concrete mod-11 power shifted nonmembership iff shifted nondivisibility. -/
theorem concrete_mod11_power_shifted_nonmembership_iff_not_dvd_facts :
    (∀ m, (¬ ∃ n, m + 5 = 11 * (n + 1)) ↔ ¬ (11 ∣ m + 5)) ∧
      (∀ m, (¬ ∃ n, m + 5 = 121 * (n + 1)) ↔ ¬ (121 ∣ m + 5)) ∧
      (∀ m, (¬ ∃ n, m + 5 = 1331 * (n + 1)) ↔ ¬ (1331 ∣ m + 5)) ∧
      (∀ m, (¬ ∃ n, m + 5 = 14641 * (n + 1)) ↔ ¬ (14641 ∣ m + 5)) ∧
      (∀ m, (¬ ∃ n, m + 5 = 161051 * (n + 1)) ↔ ¬ (161051 ∣ m + 5)) := by
  exact ⟨not_exists_add_five_eq_11_mul_succ_iff_not_dvd_add_five_by_11,
    not_exists_add_five_eq_121_mul_succ_iff_not_dvd_add_five_by_121,
    not_exists_add_five_eq_1331_mul_succ_iff_not_dvd_add_five_by_1331,
    not_exists_add_five_eq_14641_mul_succ_iff_not_dvd_add_five_by_14641,
    not_exists_add_five_eq_161051_mul_succ_iff_not_dvd_add_five_by_161051⟩

/-- Membership in `q*n+r` is equivalent to divisibility of `m+c` when
`r+c=q` and `c>0`. -/
theorem exists_mul_add_iff_dvd_add {q r c m : ℕ}
    (hc : 0 < c) (hmod : r + c = q) :
    (∃ n, m = q * n + r) ↔ q ∣ m + c := by
  exact Iff.trans
    (exists_mul_add_iff_exists_shifted_mul_succ (q := q) (r := r) (c := c)
      (m := m) hmod)
    (exists_shifted_mul_succ_iff_dvd_add (q := q) (c := c) (m := m) hc)

/-- Direct membership/divisibility form for `5n+4`. -/
theorem exists_5n_plus_4_iff_dvd_add_one_by_5 (m : ℕ) :
    (∃ n, m = 5 * n + 4) ↔ 5 ∣ m + 1 := by
  exact exists_mul_add_iff_dvd_add (q := 5) (r := 4) (c := 1)
    (m := m) (by decide) (by decide)

/-- Direct membership/divisibility form for `25n+24`. -/
theorem exists_25n_plus_24_iff_dvd_add_one_by_25 (m : ℕ) :
    (∃ n, m = 25 * n + 24) ↔ 25 ∣ m + 1 := by
  exact exists_mul_add_iff_dvd_add (q := 25) (r := 24) (c := 1)
    (m := m) (by decide) (by decide)

/-- Direct membership/divisibility form for `125n+124`. -/
theorem exists_125n_plus_124_iff_dvd_add_one_by_125 (m : ℕ) :
    (∃ n, m = 125 * n + 124) ↔ 125 ∣ m + 1 := by
  exact exists_mul_add_iff_dvd_add (q := 125) (r := 124) (c := 1)
    (m := m) (by decide) (by decide)

/-- Direct membership/divisibility form for `625n+624`. -/
theorem exists_625n_plus_624_iff_dvd_add_one_by_625 (m : ℕ) :
    (∃ n, m = 625 * n + 624) ↔ 625 ∣ m + 1 := by
  exact exists_mul_add_iff_dvd_add (q := 625) (r := 624) (c := 1)
    (m := m) (by decide) (by decide)

/-- Direct membership/divisibility form for `3125n+3124`. -/
theorem exists_3125n_plus_3124_iff_dvd_add_one_by_3125 (m : ℕ) :
    (∃ n, m = 3125 * n + 3124) ↔ 3125 ∣ m + 1 := by
  exact exists_mul_add_iff_dvd_add (q := 3125) (r := 3124) (c := 1)
    (m := m) (by decide) (by decide)

/-- Direct membership/divisibility form for `7n+5`. -/
theorem exists_7n_plus_5_iff_dvd_add_two_by_7 (m : ℕ) :
    (∃ n, m = 7 * n + 5) ↔ 7 ∣ m + 2 := by
  exact exists_mul_add_iff_dvd_add (q := 7) (r := 5) (c := 2)
    (m := m) (by decide) (by decide)

/-- Direct membership/divisibility form for `49n+47`. -/
theorem exists_49n_plus_47_iff_dvd_add_two_by_49 (m : ℕ) :
    (∃ n, m = 49 * n + 47) ↔ 49 ∣ m + 2 := by
  exact exists_mul_add_iff_dvd_add (q := 49) (r := 47) (c := 2)
    (m := m) (by decide) (by decide)

/-- Direct membership/divisibility form for `343n+341`. -/
theorem exists_343n_plus_341_iff_dvd_add_two_by_343 (m : ℕ) :
    (∃ n, m = 343 * n + 341) ↔ 343 ∣ m + 2 := by
  exact exists_mul_add_iff_dvd_add (q := 343) (r := 341) (c := 2)
    (m := m) (by decide) (by decide)

/-- Direct membership/divisibility form for `2401n+2399`. -/
theorem exists_2401n_plus_2399_iff_dvd_add_two_by_2401 (m : ℕ) :
    (∃ n, m = 2401 * n + 2399) ↔ 2401 ∣ m + 2 := by
  exact exists_mul_add_iff_dvd_add (q := 2401) (r := 2399) (c := 2)
    (m := m) (by decide) (by decide)

/-- Direct membership/divisibility form for `16807n+16805`. -/
theorem exists_16807n_plus_16805_iff_dvd_add_two_by_16807 (m : ℕ) :
    (∃ n, m = 16807 * n + 16805) ↔ 16807 ∣ m + 2 := by
  exact exists_mul_add_iff_dvd_add (q := 16807) (r := 16805) (c := 2)
    (m := m) (by decide) (by decide)

/-- Direct membership/divisibility form for `11n+6`. -/
theorem exists_11n_plus_6_iff_dvd_add_five_by_11 (m : ℕ) :
    (∃ n, m = 11 * n + 6) ↔ 11 ∣ m + 5 := by
  exact exists_mul_add_iff_dvd_add (q := 11) (r := 6) (c := 5)
    (m := m) (by decide) (by decide)

/-- Direct membership/divisibility form for `121n+116`. -/
theorem exists_121n_plus_116_iff_dvd_add_five_by_121 (m : ℕ) :
    (∃ n, m = 121 * n + 116) ↔ 121 ∣ m + 5 := by
  exact exists_mul_add_iff_dvd_add (q := 121) (r := 116) (c := 5)
    (m := m) (by decide) (by decide)

/-- Direct membership/divisibility form for `1331n+1326`. -/
theorem exists_1331n_plus_1326_iff_dvd_add_five_by_1331 (m : ℕ) :
    (∃ n, m = 1331 * n + 1326) ↔ 1331 ∣ m + 5 := by
  exact exists_mul_add_iff_dvd_add (q := 1331) (r := 1326) (c := 5)
    (m := m) (by decide) (by decide)

/-- Direct membership/divisibility form for `14641n+14636`. -/
theorem exists_14641n_plus_14636_iff_dvd_add_five_by_14641 (m : ℕ) :
    (∃ n, m = 14641 * n + 14636) ↔ 14641 ∣ m + 5 := by
  exact exists_mul_add_iff_dvd_add (q := 14641) (r := 14636) (c := 5)
    (m := m) (by decide) (by decide)

/-- Direct membership/divisibility form for `161051n+161046`. -/
theorem exists_161051n_plus_161046_iff_dvd_add_five_by_161051
    (m : ℕ) :
    (∃ n, m = 161051 * n + 161046) ↔ 161051 ∣ m + 5 := by
  exact exists_mul_add_iff_dvd_add (q := 161051) (r := 161046) (c := 5)
    (m := m) (by decide) (by decide)

/-- Concrete mod-5 power membership iff divisibility by the matching shifted
number. -/
theorem concrete_mod5_power_membership_iff_dvd_add_one_facts :
    (∀ m, (∃ n, m = 5 * n + 4) ↔ 5 ∣ m + 1) ∧
      (∀ m, (∃ n, m = 25 * n + 24) ↔ 25 ∣ m + 1) ∧
      (∀ m, (∃ n, m = 125 * n + 124) ↔ 125 ∣ m + 1) ∧
      (∀ m, (∃ n, m = 625 * n + 624) ↔ 625 ∣ m + 1) ∧
      (∀ m, (∃ n, m = 3125 * n + 3124) ↔ 3125 ∣ m + 1) := by
  exact ⟨exists_5n_plus_4_iff_dvd_add_one_by_5,
    exists_25n_plus_24_iff_dvd_add_one_by_25,
    exists_125n_plus_124_iff_dvd_add_one_by_125,
    exists_625n_plus_624_iff_dvd_add_one_by_625,
    exists_3125n_plus_3124_iff_dvd_add_one_by_3125⟩

/-- Concrete mod-7 power membership iff divisibility by the matching shifted
number. -/
theorem concrete_mod7_power_membership_iff_dvd_add_two_facts :
    (∀ m, (∃ n, m = 7 * n + 5) ↔ 7 ∣ m + 2) ∧
      (∀ m, (∃ n, m = 49 * n + 47) ↔ 49 ∣ m + 2) ∧
      (∀ m, (∃ n, m = 343 * n + 341) ↔ 343 ∣ m + 2) ∧
      (∀ m, (∃ n, m = 2401 * n + 2399) ↔ 2401 ∣ m + 2) ∧
      (∀ m, (∃ n, m = 16807 * n + 16805) ↔ 16807 ∣ m + 2) := by
  exact ⟨exists_7n_plus_5_iff_dvd_add_two_by_7,
    exists_49n_plus_47_iff_dvd_add_two_by_49,
    exists_343n_plus_341_iff_dvd_add_two_by_343,
    exists_2401n_plus_2399_iff_dvd_add_two_by_2401,
    exists_16807n_plus_16805_iff_dvd_add_two_by_16807⟩

/-- Concrete mod-11 power membership iff divisibility by the matching shifted
number. -/
theorem concrete_mod11_power_membership_iff_dvd_add_five_facts :
    (∀ m, (∃ n, m = 11 * n + 6) ↔ 11 ∣ m + 5) ∧
      (∀ m, (∃ n, m = 121 * n + 116) ↔ 121 ∣ m + 5) ∧
      (∀ m, (∃ n, m = 1331 * n + 1326) ↔ 1331 ∣ m + 5) ∧
      (∀ m, (∃ n, m = 14641 * n + 14636) ↔ 14641 ∣ m + 5) ∧
      (∀ m, (∃ n, m = 161051 * n + 161046) ↔ 161051 ∣ m + 5) := by
  exact ⟨exists_11n_plus_6_iff_dvd_add_five_by_11,
    exists_121n_plus_116_iff_dvd_add_five_by_121,
    exists_1331n_plus_1326_iff_dvd_add_five_by_1331,
    exists_14641n_plus_14636_iff_dvd_add_five_by_14641,
    exists_161051n_plus_161046_iff_dvd_add_five_by_161051⟩

/-- Negated membership in `q*n+r` is equivalent to negated divisibility of
`m+c` when `r+c=q` and `c>0`. -/
theorem not_exists_mul_add_iff_not_dvd_add {q r c m : ℕ}
    (hc : 0 < c) (hmod : r + c = q) :
    (¬ ∃ n, m = q * n + r) ↔ ¬ (q ∣ m + c) := by
  constructor
  · intro h hd
    exact h ((exists_mul_add_iff_dvd_add (q := q) (r := r) (c := c)
      (m := m) hc hmod).mpr hd)
  · intro h he
    exact h ((exists_mul_add_iff_dvd_add (q := q) (r := r) (c := c)
      (m := m) hc hmod).mp he)

/-- Nonmembership in `5n+4` iff `5 ∤ m+1`. -/
theorem not_exists_5n_plus_4_iff_not_dvd_add_one_by_5 (m : ℕ) :
    (¬ ∃ n, m = 5 * n + 4) ↔ ¬ (5 ∣ m + 1) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 5) (r := 4) (c := 1)
    (m := m) (by decide) (by decide)

/-- Nonmembership in `25n+24` iff `25 ∤ m+1`. -/
theorem not_exists_25n_plus_24_iff_not_dvd_add_one_by_25 (m : ℕ) :
    (¬ ∃ n, m = 25 * n + 24) ↔ ¬ (25 ∣ m + 1) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 25) (r := 24) (c := 1)
    (m := m) (by decide) (by decide)

/-- Nonmembership in `125n+124` iff `125 ∤ m+1`. -/
theorem not_exists_125n_plus_124_iff_not_dvd_add_one_by_125 (m : ℕ) :
    (¬ ∃ n, m = 125 * n + 124) ↔ ¬ (125 ∣ m + 1) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 125) (r := 124) (c := 1)
    (m := m) (by decide) (by decide)

/-- Nonmembership in `625n+624` iff `625 ∤ m+1`. -/
theorem not_exists_625n_plus_624_iff_not_dvd_add_one_by_625 (m : ℕ) :
    (¬ ∃ n, m = 625 * n + 624) ↔ ¬ (625 ∣ m + 1) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 625) (r := 624) (c := 1)
    (m := m) (by decide) (by decide)

/-- Nonmembership in `3125n+3124` iff `3125 ∤ m+1`. -/
theorem not_exists_3125n_plus_3124_iff_not_dvd_add_one_by_3125 (m : ℕ) :
    (¬ ∃ n, m = 3125 * n + 3124) ↔ ¬ (3125 ∣ m + 1) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 3125) (r := 3124) (c := 1)
    (m := m) (by decide) (by decide)

/-- Nonmembership in `7n+5` iff `7 ∤ m+2`. -/
theorem not_exists_7n_plus_5_iff_not_dvd_add_two_by_7 (m : ℕ) :
    (¬ ∃ n, m = 7 * n + 5) ↔ ¬ (7 ∣ m + 2) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 7) (r := 5) (c := 2)
    (m := m) (by decide) (by decide)

/-- Nonmembership in `49n+47` iff `49 ∤ m+2`. -/
theorem not_exists_49n_plus_47_iff_not_dvd_add_two_by_49 (m : ℕ) :
    (¬ ∃ n, m = 49 * n + 47) ↔ ¬ (49 ∣ m + 2) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 49) (r := 47) (c := 2)
    (m := m) (by decide) (by decide)

/-- Nonmembership in `343n+341` iff `343 ∤ m+2`. -/
theorem not_exists_343n_plus_341_iff_not_dvd_add_two_by_343 (m : ℕ) :
    (¬ ∃ n, m = 343 * n + 341) ↔ ¬ (343 ∣ m + 2) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 343) (r := 341) (c := 2)
    (m := m) (by decide) (by decide)

/-- Nonmembership in `2401n+2399` iff `2401 ∤ m+2`. -/
theorem not_exists_2401n_plus_2399_iff_not_dvd_add_two_by_2401 (m : ℕ) :
    (¬ ∃ n, m = 2401 * n + 2399) ↔ ¬ (2401 ∣ m + 2) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 2401) (r := 2399) (c := 2)
    (m := m) (by decide) (by decide)

/-- Nonmembership in `16807n+16805` iff `16807 ∤ m+2`. -/
theorem not_exists_16807n_plus_16805_iff_not_dvd_add_two_by_16807 (m : ℕ) :
    (¬ ∃ n, m = 16807 * n + 16805) ↔ ¬ (16807 ∣ m + 2) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 16807) (r := 16805) (c := 2)
    (m := m) (by decide) (by decide)

/-- Nonmembership in `11n+6` iff `11 ∤ m+5`. -/
theorem not_exists_11n_plus_6_iff_not_dvd_add_five_by_11 (m : ℕ) :
    (¬ ∃ n, m = 11 * n + 6) ↔ ¬ (11 ∣ m + 5) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 11) (r := 6) (c := 5)
    (m := m) (by decide) (by decide)

/-- Nonmembership in `121n+116` iff `121 ∤ m+5`. -/
theorem not_exists_121n_plus_116_iff_not_dvd_add_five_by_121 (m : ℕ) :
    (¬ ∃ n, m = 121 * n + 116) ↔ ¬ (121 ∣ m + 5) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 121) (r := 116) (c := 5)
    (m := m) (by decide) (by decide)

/-- Nonmembership in `1331n+1326` iff `1331 ∤ m+5`. -/
theorem not_exists_1331n_plus_1326_iff_not_dvd_add_five_by_1331 (m : ℕ) :
    (¬ ∃ n, m = 1331 * n + 1326) ↔ ¬ (1331 ∣ m + 5) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 1331) (r := 1326) (c := 5)
    (m := m) (by decide) (by decide)

/-- Nonmembership in `14641n+14636` iff `14641 ∤ m+5`. -/
theorem not_exists_14641n_plus_14636_iff_not_dvd_add_five_by_14641 (m : ℕ) :
    (¬ ∃ n, m = 14641 * n + 14636) ↔ ¬ (14641 ∣ m + 5) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 14641) (r := 14636) (c := 5)
    (m := m) (by decide) (by decide)

/-- Nonmembership in `161051n+161046` iff `161051 ∤ m+5`. -/
theorem not_exists_161051n_plus_161046_iff_not_dvd_add_five_by_161051
    (m : ℕ) :
    (¬ ∃ n, m = 161051 * n + 161046) ↔ ¬ (161051 ∣ m + 5) := by
  exact not_exists_mul_add_iff_not_dvd_add (q := 161051) (r := 161046) (c := 5)
    (m := m) (by decide) (by decide)

/-- Concrete mod-5 power nonmembership iff shifted nondivisibility. -/
theorem concrete_mod5_power_nonmembership_iff_not_dvd_add_one_facts :
    (∀ m, (¬ ∃ n, m = 5 * n + 4) ↔ ¬ (5 ∣ m + 1)) ∧
      (∀ m, (¬ ∃ n, m = 25 * n + 24) ↔ ¬ (25 ∣ m + 1)) ∧
      (∀ m, (¬ ∃ n, m = 125 * n + 124) ↔ ¬ (125 ∣ m + 1)) ∧
      (∀ m, (¬ ∃ n, m = 625 * n + 624) ↔ ¬ (625 ∣ m + 1)) ∧
      (∀ m, (¬ ∃ n, m = 3125 * n + 3124) ↔ ¬ (3125 ∣ m + 1)) := by
  exact ⟨not_exists_5n_plus_4_iff_not_dvd_add_one_by_5,
    not_exists_25n_plus_24_iff_not_dvd_add_one_by_25,
    not_exists_125n_plus_124_iff_not_dvd_add_one_by_125,
    not_exists_625n_plus_624_iff_not_dvd_add_one_by_625,
    not_exists_3125n_plus_3124_iff_not_dvd_add_one_by_3125⟩

/-- Concrete mod-7 power nonmembership iff shifted nondivisibility. -/
theorem concrete_mod7_power_nonmembership_iff_not_dvd_add_two_facts :
    (∀ m, (¬ ∃ n, m = 7 * n + 5) ↔ ¬ (7 ∣ m + 2)) ∧
      (∀ m, (¬ ∃ n, m = 49 * n + 47) ↔ ¬ (49 ∣ m + 2)) ∧
      (∀ m, (¬ ∃ n, m = 343 * n + 341) ↔ ¬ (343 ∣ m + 2)) ∧
      (∀ m, (¬ ∃ n, m = 2401 * n + 2399) ↔ ¬ (2401 ∣ m + 2)) ∧
      (∀ m, (¬ ∃ n, m = 16807 * n + 16805) ↔ ¬ (16807 ∣ m + 2)) := by
  exact ⟨not_exists_7n_plus_5_iff_not_dvd_add_two_by_7,
    not_exists_49n_plus_47_iff_not_dvd_add_two_by_49,
    not_exists_343n_plus_341_iff_not_dvd_add_two_by_343,
    not_exists_2401n_plus_2399_iff_not_dvd_add_two_by_2401,
    not_exists_16807n_plus_16805_iff_not_dvd_add_two_by_16807⟩

/-- Concrete mod-11 power nonmembership iff shifted nondivisibility. -/
theorem concrete_mod11_power_nonmembership_iff_not_dvd_add_five_facts :
    (∀ m, (¬ ∃ n, m = 11 * n + 6) ↔ ¬ (11 ∣ m + 5)) ∧
      (∀ m, (¬ ∃ n, m = 121 * n + 116) ↔ ¬ (121 ∣ m + 5)) ∧
      (∀ m, (¬ ∃ n, m = 1331 * n + 1326) ↔ ¬ (1331 ∣ m + 5)) ∧
      (∀ m, (¬ ∃ n, m = 14641 * n + 14636) ↔ ¬ (14641 ∣ m + 5)) ∧
      (∀ m, (¬ ∃ n, m = 161051 * n + 161046) ↔ ¬ (161051 ∣ m + 5)) := by
  exact ⟨not_exists_11n_plus_6_iff_not_dvd_add_five_by_11,
    not_exists_121n_plus_116_iff_not_dvd_add_five_by_121,
    not_exists_1331n_plus_1326_iff_not_dvd_add_five_by_1331,
    not_exists_14641n_plus_14636_iff_not_dvd_add_five_by_14641,
    not_exists_161051n_plus_161046_iff_not_dvd_add_five_by_161051⟩

/-- Direct membership/residue form for `5n+4`. -/
theorem exists_5n_plus_4_iff_mod5_eq4 (m : ℕ) :
    (∃ n, m = 5 * n + 4) ↔ m % 5 = 4 := by
  exact exists_mul_add_iff_mod_eq (q := 5) (r := 4) (m := m) (by decide)

/-- Direct membership/residue form for `25n+24`. -/
theorem exists_25n_plus_24_iff_mod25_eq24 (m : ℕ) :
    (∃ n, m = 25 * n + 24) ↔ m % 25 = 24 := by
  exact exists_mul_add_iff_mod_eq (q := 25) (r := 24) (m := m) (by decide)

/-- Direct membership/residue form for `125n+124`. -/
theorem exists_125n_plus_124_iff_mod125_eq124 (m : ℕ) :
    (∃ n, m = 125 * n + 124) ↔ m % 125 = 124 := by
  exact exists_mul_add_iff_mod_eq (q := 125) (r := 124) (m := m) (by decide)

/-- Direct membership/residue form for `625n+624`. -/
theorem exists_625n_plus_624_iff_mod625_eq624 (m : ℕ) :
    (∃ n, m = 625 * n + 624) ↔ m % 625 = 624 := by
  exact exists_mul_add_iff_mod_eq (q := 625) (r := 624) (m := m) (by decide)

/-- Direct membership/residue form for `3125n+3124`. -/
theorem exists_3125n_plus_3124_iff_mod3125_eq3124 (m : ℕ) :
    (∃ n, m = 3125 * n + 3124) ↔ m % 3125 = 3124 := by
  exact exists_mul_add_iff_mod_eq (q := 3125) (r := 3124) (m := m) (by decide)

/-- Direct membership/residue form for `7n+5`. -/
theorem exists_7n_plus_5_iff_mod7_eq5 (m : ℕ) :
    (∃ n, m = 7 * n + 5) ↔ m % 7 = 5 := by
  exact exists_mul_add_iff_mod_eq (q := 7) (r := 5) (m := m) (by decide)

/-- Direct membership/residue form for `49n+47`. -/
theorem exists_49n_plus_47_iff_mod49_eq47 (m : ℕ) :
    (∃ n, m = 49 * n + 47) ↔ m % 49 = 47 := by
  exact exists_mul_add_iff_mod_eq (q := 49) (r := 47) (m := m) (by decide)

/-- Direct membership/residue form for `343n+341`. -/
theorem exists_343n_plus_341_iff_mod343_eq341 (m : ℕ) :
    (∃ n, m = 343 * n + 341) ↔ m % 343 = 341 := by
  exact exists_mul_add_iff_mod_eq (q := 343) (r := 341) (m := m) (by decide)

/-- Direct membership/residue form for `2401n+2399`. -/
theorem exists_2401n_plus_2399_iff_mod2401_eq2399 (m : ℕ) :
    (∃ n, m = 2401 * n + 2399) ↔ m % 2401 = 2399 := by
  exact exists_mul_add_iff_mod_eq (q := 2401) (r := 2399) (m := m) (by decide)

/-- Direct membership/residue form for `16807n+16805`. -/
theorem exists_16807n_plus_16805_iff_mod16807_eq16805 (m : ℕ) :
    (∃ n, m = 16807 * n + 16805) ↔ m % 16807 = 16805 := by
  exact exists_mul_add_iff_mod_eq (q := 16807) (r := 16805) (m := m) (by decide)

/-- Direct membership/residue form for `11n+6`. -/
theorem exists_11n_plus_6_iff_mod11_eq6 (m : ℕ) :
    (∃ n, m = 11 * n + 6) ↔ m % 11 = 6 := by
  exact exists_mul_add_iff_mod_eq (q := 11) (r := 6) (m := m) (by decide)

/-- Direct membership/residue form for `121n+116`. -/
theorem exists_121n_plus_116_iff_mod121_eq116 (m : ℕ) :
    (∃ n, m = 121 * n + 116) ↔ m % 121 = 116 := by
  exact exists_mul_add_iff_mod_eq (q := 121) (r := 116) (m := m) (by decide)

/-- Direct membership/residue form for `1331n+1326`. -/
theorem exists_1331n_plus_1326_iff_mod1331_eq1326 (m : ℕ) :
    (∃ n, m = 1331 * n + 1326) ↔ m % 1331 = 1326 := by
  exact exists_mul_add_iff_mod_eq (q := 1331) (r := 1326) (m := m) (by decide)

/-- Direct membership/residue form for `14641n+14636`. -/
theorem exists_14641n_plus_14636_iff_mod14641_eq14636 (m : ℕ) :
    (∃ n, m = 14641 * n + 14636) ↔ m % 14641 = 14636 := by
  exact exists_mul_add_iff_mod_eq (q := 14641) (r := 14636) (m := m) (by decide)

/-- Direct membership/residue form for `161051n+161046`. -/
theorem exists_161051n_plus_161046_iff_mod161051_eq161046
    (m : ℕ) :
    (∃ n, m = 161051 * n + 161046) ↔ m % 161051 = 161046 := by
  exact exists_mul_add_iff_mod_eq (q := 161051) (r := 161046) (m := m) (by decide)

/-- Nonmembership in a residue progression is equivalent to not having the
corresponding modular residue. -/
theorem not_exists_mul_add_iff_mod_ne {q r m : ℕ} (hr : r < q) :
    (¬ ∃ n, m = q * n + r) ↔ m % q ≠ r := by
  exact not_congr (exists_mul_add_iff_mod_eq (q := q) (r := r) (m := m) hr)

/-- Nonmembership in `5n+4` iff the residue is not `4 mod 5`. -/
theorem not_exists_5n_plus_4_iff_mod5_ne4 (m : ℕ) :
    (¬ ∃ n, m = 5 * n + 4) ↔ m % 5 ≠ 4 := by
  exact not_exists_mul_add_iff_mod_ne (q := 5) (r := 4) (m := m) (by decide)

/-- Nonmembership in `25n+24` iff the residue is not `24 mod 25`. -/
theorem not_exists_25n_plus_24_iff_mod25_ne24 (m : ℕ) :
    (¬ ∃ n, m = 25 * n + 24) ↔ m % 25 ≠ 24 := by
  exact not_exists_mul_add_iff_mod_ne (q := 25) (r := 24) (m := m) (by decide)

/-- Nonmembership in `125n+124` iff the residue is not `124 mod 125`. -/
theorem not_exists_125n_plus_124_iff_mod125_ne124 (m : ℕ) :
    (¬ ∃ n, m = 125 * n + 124) ↔ m % 125 ≠ 124 := by
  exact not_exists_mul_add_iff_mod_ne (q := 125) (r := 124) (m := m) (by decide)

/-- Nonmembership in `625n+624` iff the residue is not `624 mod 625`. -/
theorem not_exists_625n_plus_624_iff_mod625_ne624 (m : ℕ) :
    (¬ ∃ n, m = 625 * n + 624) ↔ m % 625 ≠ 624 := by
  exact not_exists_mul_add_iff_mod_ne (q := 625) (r := 624) (m := m) (by decide)

/-- Nonmembership in `3125n+3124` iff the residue is not `3124 mod 3125`. -/
theorem not_exists_3125n_plus_3124_iff_mod3125_ne3124 (m : ℕ) :
    (¬ ∃ n, m = 3125 * n + 3124) ↔ m % 3125 ≠ 3124 := by
  exact not_exists_mul_add_iff_mod_ne (q := 3125) (r := 3124) (m := m) (by decide)

/-- Nonmembership in `7n+5` iff the residue is not `5 mod 7`. -/
theorem not_exists_7n_plus_5_iff_mod7_ne5 (m : ℕ) :
    (¬ ∃ n, m = 7 * n + 5) ↔ m % 7 ≠ 5 := by
  exact not_exists_mul_add_iff_mod_ne (q := 7) (r := 5) (m := m) (by decide)

/-- Nonmembership in `49n+47` iff the residue is not `47 mod 49`. -/
theorem not_exists_49n_plus_47_iff_mod49_ne47 (m : ℕ) :
    (¬ ∃ n, m = 49 * n + 47) ↔ m % 49 ≠ 47 := by
  exact not_exists_mul_add_iff_mod_ne (q := 49) (r := 47) (m := m) (by decide)

/-- Nonmembership in `343n+341` iff the residue is not `341 mod 343`. -/
theorem not_exists_343n_plus_341_iff_mod343_ne341 (m : ℕ) :
    (¬ ∃ n, m = 343 * n + 341) ↔ m % 343 ≠ 341 := by
  exact not_exists_mul_add_iff_mod_ne (q := 343) (r := 341) (m := m) (by decide)

/-- Nonmembership in `2401n+2399` iff the residue is not `2399 mod 2401`. -/
theorem not_exists_2401n_plus_2399_iff_mod2401_ne2399 (m : ℕ) :
    (¬ ∃ n, m = 2401 * n + 2399) ↔ m % 2401 ≠ 2399 := by
  exact not_exists_mul_add_iff_mod_ne (q := 2401) (r := 2399) (m := m) (by decide)

/-- Nonmembership in `16807n+16805` iff the residue is not `16805 mod
`16807`. -/
theorem not_exists_16807n_plus_16805_iff_mod16807_ne16805 (m : ℕ) :
    (¬ ∃ n, m = 16807 * n + 16805) ↔ m % 16807 ≠ 16805 := by
  exact not_exists_mul_add_iff_mod_ne (q := 16807) (r := 16805) (m := m) (by decide)

/-- Nonmembership in `11n+6` iff the residue is not `6 mod 11`. -/
theorem not_exists_11n_plus_6_iff_mod11_ne6 (m : ℕ) :
    (¬ ∃ n, m = 11 * n + 6) ↔ m % 11 ≠ 6 := by
  exact not_exists_mul_add_iff_mod_ne (q := 11) (r := 6) (m := m) (by decide)

/-- Nonmembership in `121n+116` iff the residue is not `116 mod 121`. -/
theorem not_exists_121n_plus_116_iff_mod121_ne116 (m : ℕ) :
    (¬ ∃ n, m = 121 * n + 116) ↔ m % 121 ≠ 116 := by
  exact not_exists_mul_add_iff_mod_ne (q := 121) (r := 116) (m := m) (by decide)

/-- Nonmembership in `1331n+1326` iff the residue is not `1326 mod 1331`. -/
theorem not_exists_1331n_plus_1326_iff_mod1331_ne1326 (m : ℕ) :
    (¬ ∃ n, m = 1331 * n + 1326) ↔ m % 1331 ≠ 1326 := by
  exact not_exists_mul_add_iff_mod_ne (q := 1331) (r := 1326) (m := m) (by decide)

/-- Nonmembership in `14641n+14636` iff the residue is not `14636 mod 14641`. -/
theorem not_exists_14641n_plus_14636_iff_mod14641_ne14636 (m : ℕ) :
    (¬ ∃ n, m = 14641 * n + 14636) ↔ m % 14641 ≠ 14636 := by
  exact not_exists_mul_add_iff_mod_ne (q := 14641) (r := 14636) (m := m) (by decide)

/-- Nonmembership in `161051n+161046` iff the residue is not `161046 mod
`161051`. -/
theorem not_exists_161051n_plus_161046_iff_mod161051_ne161046
    (m : ℕ) :
    (¬ ∃ n, m = 161051 * n + 161046) ↔ m % 161051 ≠ 161046 := by
  exact not_exists_mul_add_iff_mod_ne (q := 161051) (r := 161046) (m := m) (by decide)

/-- Concrete mod-5 power nonmembership iff residue inequality facts. -/
theorem concrete_mod5_power_nonmembership_iff_residue_ne_facts :
    (∀ m, (¬ ∃ n, m = 5 * n + 4) ↔ m % 5 ≠ 4) ∧
      (∀ m, (¬ ∃ n, m = 25 * n + 24) ↔ m % 25 ≠ 24) ∧
      (∀ m, (¬ ∃ n, m = 125 * n + 124) ↔ m % 125 ≠ 124) ∧
      (∀ m, (¬ ∃ n, m = 625 * n + 624) ↔ m % 625 ≠ 624) ∧
      (∀ m, (¬ ∃ n, m = 3125 * n + 3124) ↔ m % 3125 ≠ 3124) := by
  exact ⟨not_exists_5n_plus_4_iff_mod5_ne4,
    not_exists_25n_plus_24_iff_mod25_ne24,
    not_exists_125n_plus_124_iff_mod125_ne124,
    not_exists_625n_plus_624_iff_mod625_ne624,
    not_exists_3125n_plus_3124_iff_mod3125_ne3124⟩

/-- Concrete mod-7 power nonmembership iff residue inequality facts. -/
theorem concrete_mod7_power_nonmembership_iff_residue_ne_facts :
    (∀ m, (¬ ∃ n, m = 7 * n + 5) ↔ m % 7 ≠ 5) ∧
      (∀ m, (¬ ∃ n, m = 49 * n + 47) ↔ m % 49 ≠ 47) ∧
      (∀ m, (¬ ∃ n, m = 343 * n + 341) ↔ m % 343 ≠ 341) ∧
      (∀ m, (¬ ∃ n, m = 2401 * n + 2399) ↔ m % 2401 ≠ 2399) ∧
      (∀ m, (¬ ∃ n, m = 16807 * n + 16805) ↔ m % 16807 ≠ 16805) := by
  exact ⟨not_exists_7n_plus_5_iff_mod7_ne5,
    not_exists_49n_plus_47_iff_mod49_ne47,
    not_exists_343n_plus_341_iff_mod343_ne341,
    not_exists_2401n_plus_2399_iff_mod2401_ne2399,
    not_exists_16807n_plus_16805_iff_mod16807_ne16805⟩

/-- Concrete mod-11 power nonmembership iff residue inequality facts. -/
theorem concrete_mod11_power_nonmembership_iff_residue_ne_facts :
    (∀ m, (¬ ∃ n, m = 11 * n + 6) ↔ m % 11 ≠ 6) ∧
      (∀ m, (¬ ∃ n, m = 121 * n + 116) ↔ m % 121 ≠ 116) ∧
      (∀ m, (¬ ∃ n, m = 1331 * n + 1326) ↔ m % 1331 ≠ 1326) ∧
      (∀ m, (¬ ∃ n, m = 14641 * n + 14636) ↔ m % 14641 ≠ 14636) ∧
      (∀ m, (¬ ∃ n, m = 161051 * n + 161046) ↔ m % 161051 ≠ 161046) := by
  exact ⟨not_exists_11n_plus_6_iff_mod11_ne6,
    not_exists_121n_plus_116_iff_mod121_ne116,
    not_exists_1331n_plus_1326_iff_mod1331_ne1326,
    not_exists_14641n_plus_14636_iff_mod14641_ne14636,
    not_exists_161051n_plus_161046_iff_mod161051_ne161046⟩

/-- Residue-first membership form for `5n+4`. -/
theorem mod5_eq4_iff_exists_5n_plus_4 (m : ℕ) :
    m % 5 = 4 ↔ ∃ n, m = 5 * n + 4 := by
  exact (exists_5n_plus_4_iff_mod5_eq4 m).symm

/-- Residue-first membership form for `25n+24`. -/
theorem mod25_eq24_iff_exists_25n_plus_24 (m : ℕ) :
    m % 25 = 24 ↔ ∃ n, m = 25 * n + 24 := by
  exact (exists_25n_plus_24_iff_mod25_eq24 m).symm

/-- Residue-first membership form for `125n+124`. -/
theorem mod125_eq124_iff_exists_125n_plus_124 (m : ℕ) :
    m % 125 = 124 ↔ ∃ n, m = 125 * n + 124 := by
  exact (exists_125n_plus_124_iff_mod125_eq124 m).symm

/-- Residue-first membership form for `625n+624`. -/
theorem mod625_eq624_iff_exists_625n_plus_624 (m : ℕ) :
    m % 625 = 624 ↔ ∃ n, m = 625 * n + 624 := by
  exact (exists_625n_plus_624_iff_mod625_eq624 m).symm

/-- Residue-first membership form for `3125n+3124`. -/
theorem mod3125_eq3124_iff_exists_3125n_plus_3124 (m : ℕ) :
    m % 3125 = 3124 ↔ ∃ n, m = 3125 * n + 3124 := by
  exact (exists_3125n_plus_3124_iff_mod3125_eq3124 m).symm

/-- Residue-first membership form for `7n+5`. -/
theorem mod7_eq5_iff_exists_7n_plus_5 (m : ℕ) :
    m % 7 = 5 ↔ ∃ n, m = 7 * n + 5 := by
  exact (exists_7n_plus_5_iff_mod7_eq5 m).symm

/-- Residue-first membership form for `49n+47`. -/
theorem mod49_eq47_iff_exists_49n_plus_47 (m : ℕ) :
    m % 49 = 47 ↔ ∃ n, m = 49 * n + 47 := by
  exact (exists_49n_plus_47_iff_mod49_eq47 m).symm

/-- Residue-first membership form for `343n+341`. -/
theorem mod343_eq341_iff_exists_343n_plus_341 (m : ℕ) :
    m % 343 = 341 ↔ ∃ n, m = 343 * n + 341 := by
  exact (exists_343n_plus_341_iff_mod343_eq341 m).symm

/-- Residue-first membership form for `2401n+2399`. -/
theorem mod2401_eq2399_iff_exists_2401n_plus_2399 (m : ℕ) :
    m % 2401 = 2399 ↔ ∃ n, m = 2401 * n + 2399 := by
  exact (exists_2401n_plus_2399_iff_mod2401_eq2399 m).symm

/-- Residue-first membership form for `16807n+16805`. -/
theorem mod16807_eq16805_iff_exists_16807n_plus_16805 (m : ℕ) :
    m % 16807 = 16805 ↔ ∃ n, m = 16807 * n + 16805 := by
  exact (exists_16807n_plus_16805_iff_mod16807_eq16805 m).symm

/-- Residue-first membership form for `11n+6`. -/
theorem mod11_eq6_iff_exists_11n_plus_6 (m : ℕ) :
    m % 11 = 6 ↔ ∃ n, m = 11 * n + 6 := by
  exact (exists_11n_plus_6_iff_mod11_eq6 m).symm

/-- Residue-first membership form for `121n+116`. -/
theorem mod121_eq116_iff_exists_121n_plus_116 (m : ℕ) :
    m % 121 = 116 ↔ ∃ n, m = 121 * n + 116 := by
  exact (exists_121n_plus_116_iff_mod121_eq116 m).symm

/-- Residue-first membership form for `1331n+1326`. -/
theorem mod1331_eq1326_iff_exists_1331n_plus_1326 (m : ℕ) :
    m % 1331 = 1326 ↔ ∃ n, m = 1331 * n + 1326 := by
  exact (exists_1331n_plus_1326_iff_mod1331_eq1326 m).symm

/-- Residue-first membership form for `14641n+14636`. -/
theorem mod14641_eq14636_iff_exists_14641n_plus_14636 (m : ℕ) :
    m % 14641 = 14636 ↔ ∃ n, m = 14641 * n + 14636 := by
  exact (exists_14641n_plus_14636_iff_mod14641_eq14636 m).symm

/-- Residue-first membership form for `161051n+161046`. -/
theorem mod161051_eq161046_iff_exists_161051n_plus_161046
    (m : ℕ) :
    m % 161051 = 161046 ↔ ∃ n, m = 161051 * n + 161046 := by
  exact (exists_161051n_plus_161046_iff_mod161051_eq161046 m).symm

/-- Concrete mod-5 power residue-first membership facts. -/
theorem concrete_mod5_power_residue_iff_short_membership_facts :
    (∀ m, m % 5 = 4 ↔ ∃ n, m = 5 * n + 4) ∧
      (∀ m, m % 25 = 24 ↔ ∃ n, m = 25 * n + 24) ∧
      (∀ m, m % 125 = 124 ↔ ∃ n, m = 125 * n + 124) ∧
      (∀ m, m % 625 = 624 ↔ ∃ n, m = 625 * n + 624) ∧
      (∀ m, m % 3125 = 3124 ↔ ∃ n, m = 3125 * n + 3124) := by
  exact ⟨mod5_eq4_iff_exists_5n_plus_4,
    mod25_eq24_iff_exists_25n_plus_24,
    mod125_eq124_iff_exists_125n_plus_124,
    mod625_eq624_iff_exists_625n_plus_624,
    mod3125_eq3124_iff_exists_3125n_plus_3124⟩

/-- Concrete mod-7 power residue-first membership facts. -/
theorem concrete_mod7_power_residue_iff_short_membership_facts :
    (∀ m, m % 7 = 5 ↔ ∃ n, m = 7 * n + 5) ∧
      (∀ m, m % 49 = 47 ↔ ∃ n, m = 49 * n + 47) ∧
      (∀ m, m % 343 = 341 ↔ ∃ n, m = 343 * n + 341) ∧
      (∀ m, m % 2401 = 2399 ↔ ∃ n, m = 2401 * n + 2399) ∧
      (∀ m, m % 16807 = 16805 ↔ ∃ n, m = 16807 * n + 16805) := by
  exact ⟨mod7_eq5_iff_exists_7n_plus_5,
    mod49_eq47_iff_exists_49n_plus_47,
    mod343_eq341_iff_exists_343n_plus_341,
    mod2401_eq2399_iff_exists_2401n_plus_2399,
    mod16807_eq16805_iff_exists_16807n_plus_16805⟩

/-- Concrete mod-11 power residue-first membership facts. -/
theorem concrete_mod11_power_residue_iff_short_membership_facts :
    (∀ m, m % 11 = 6 ↔ ∃ n, m = 11 * n + 6) ∧
      (∀ m, m % 121 = 116 ↔ ∃ n, m = 121 * n + 116) ∧
      (∀ m, m % 1331 = 1326 ↔ ∃ n, m = 1331 * n + 1326) ∧
      (∀ m, m % 14641 = 14636 ↔ ∃ n, m = 14641 * n + 14636) ∧
      (∀ m, m % 161051 = 161046 ↔ ∃ n, m = 161051 * n + 161046) := by
  exact ⟨mod11_eq6_iff_exists_11n_plus_6,
    mod121_eq116_iff_exists_121n_plus_116,
    mod1331_eq1326_iff_exists_1331n_plus_1326,
    mod14641_eq14636_iff_exists_14641n_plus_14636,
    mod161051_eq161046_iff_exists_161051n_plus_161046⟩

/-- Residue inequality-first nonmembership form for `5n+4`. -/
theorem mod5_ne4_iff_not_exists_5n_plus_4 (m : ℕ) :
    m % 5 ≠ 4 ↔ ¬ ∃ n, m = 5 * n + 4 := by
  exact (not_exists_5n_plus_4_iff_mod5_ne4 m).symm

/-- Residue inequality-first nonmembership form for `25n+24`. -/
theorem mod25_ne24_iff_not_exists_25n_plus_24 (m : ℕ) :
    m % 25 ≠ 24 ↔ ¬ ∃ n, m = 25 * n + 24 := by
  exact (not_exists_25n_plus_24_iff_mod25_ne24 m).symm

/-- Residue inequality-first nonmembership form for `125n+124`. -/
theorem mod125_ne124_iff_not_exists_125n_plus_124 (m : ℕ) :
    m % 125 ≠ 124 ↔ ¬ ∃ n, m = 125 * n + 124 := by
  exact (not_exists_125n_plus_124_iff_mod125_ne124 m).symm

/-- Residue inequality-first nonmembership form for `625n+624`. -/
theorem mod625_ne624_iff_not_exists_625n_plus_624 (m : ℕ) :
    m % 625 ≠ 624 ↔ ¬ ∃ n, m = 625 * n + 624 := by
  exact (not_exists_625n_plus_624_iff_mod625_ne624 m).symm

/-- Residue inequality-first nonmembership form for `3125n+3124`. -/
theorem mod3125_ne3124_iff_not_exists_3125n_plus_3124 (m : ℕ) :
    m % 3125 ≠ 3124 ↔ ¬ ∃ n, m = 3125 * n + 3124 := by
  exact (not_exists_3125n_plus_3124_iff_mod3125_ne3124 m).symm

/-- Residue inequality-first nonmembership form for `7n+5`. -/
theorem mod7_ne5_iff_not_exists_7n_plus_5 (m : ℕ) :
    m % 7 ≠ 5 ↔ ¬ ∃ n, m = 7 * n + 5 := by
  exact (not_exists_7n_plus_5_iff_mod7_ne5 m).symm

/-- Residue inequality-first nonmembership form for `49n+47`. -/
theorem mod49_ne47_iff_not_exists_49n_plus_47 (m : ℕ) :
    m % 49 ≠ 47 ↔ ¬ ∃ n, m = 49 * n + 47 := by
  exact (not_exists_49n_plus_47_iff_mod49_ne47 m).symm

/-- Residue inequality-first nonmembership form for `343n+341`. -/
theorem mod343_ne341_iff_not_exists_343n_plus_341 (m : ℕ) :
    m % 343 ≠ 341 ↔ ¬ ∃ n, m = 343 * n + 341 := by
  exact (not_exists_343n_plus_341_iff_mod343_ne341 m).symm

/-- Residue inequality-first nonmembership form for `2401n+2399`. -/
theorem mod2401_ne2399_iff_not_exists_2401n_plus_2399 (m : ℕ) :
    m % 2401 ≠ 2399 ↔ ¬ ∃ n, m = 2401 * n + 2399 := by
  exact (not_exists_2401n_plus_2399_iff_mod2401_ne2399 m).symm

/-- Residue inequality-first nonmembership form for `16807n+16805`. -/
theorem mod16807_ne16805_iff_not_exists_16807n_plus_16805
    (m : ℕ) :
    m % 16807 ≠ 16805 ↔ ¬ ∃ n, m = 16807 * n + 16805 := by
  exact (not_exists_16807n_plus_16805_iff_mod16807_ne16805 m).symm

/-- Residue inequality-first nonmembership form for `11n+6`. -/
theorem mod11_ne6_iff_not_exists_11n_plus_6 (m : ℕ) :
    m % 11 ≠ 6 ↔ ¬ ∃ n, m = 11 * n + 6 := by
  exact (not_exists_11n_plus_6_iff_mod11_ne6 m).symm

/-- Residue inequality-first nonmembership form for `121n+116`. -/
theorem mod121_ne116_iff_not_exists_121n_plus_116 (m : ℕ) :
    m % 121 ≠ 116 ↔ ¬ ∃ n, m = 121 * n + 116 := by
  exact (not_exists_121n_plus_116_iff_mod121_ne116 m).symm

/-- Residue inequality-first nonmembership form for `1331n+1326`. -/
theorem mod1331_ne1326_iff_not_exists_1331n_plus_1326 (m : ℕ) :
    m % 1331 ≠ 1326 ↔ ¬ ∃ n, m = 1331 * n + 1326 := by
  exact (not_exists_1331n_plus_1326_iff_mod1331_ne1326 m).symm

/-- Residue inequality-first nonmembership form for `14641n+14636`. -/
theorem mod14641_ne14636_iff_not_exists_14641n_plus_14636 (m : ℕ) :
    m % 14641 ≠ 14636 ↔ ¬ ∃ n, m = 14641 * n + 14636 := by
  exact (not_exists_14641n_plus_14636_iff_mod14641_ne14636 m).symm

/-- Residue inequality-first nonmembership form for `161051n+161046`. -/
theorem mod161051_ne161046_iff_not_exists_161051n_plus_161046
    (m : ℕ) :
    m % 161051 ≠ 161046 ↔ ¬ ∃ n, m = 161051 * n + 161046 := by
  exact (not_exists_161051n_plus_161046_iff_mod161051_ne161046 m).symm

/-- Concrete mod-5 power residue inequality-first nonmembership facts. -/
theorem concrete_mod5_power_residue_ne_iff_short_nonmembership_facts :
    (∀ m, m % 5 ≠ 4 ↔ ¬ ∃ n, m = 5 * n + 4) ∧
      (∀ m, m % 25 ≠ 24 ↔ ¬ ∃ n, m = 25 * n + 24) ∧
      (∀ m, m % 125 ≠ 124 ↔ ¬ ∃ n, m = 125 * n + 124) ∧
      (∀ m, m % 625 ≠ 624 ↔ ¬ ∃ n, m = 625 * n + 624) ∧
      (∀ m, m % 3125 ≠ 3124 ↔ ¬ ∃ n, m = 3125 * n + 3124) := by
  exact ⟨mod5_ne4_iff_not_exists_5n_plus_4,
    mod25_ne24_iff_not_exists_25n_plus_24,
    mod125_ne124_iff_not_exists_125n_plus_124,
    mod625_ne624_iff_not_exists_625n_plus_624,
    mod3125_ne3124_iff_not_exists_3125n_plus_3124⟩

/-- Concrete mod-7 power residue inequality-first nonmembership facts. -/
theorem concrete_mod7_power_residue_ne_iff_short_nonmembership_facts :
    (∀ m, m % 7 ≠ 5 ↔ ¬ ∃ n, m = 7 * n + 5) ∧
      (∀ m, m % 49 ≠ 47 ↔ ¬ ∃ n, m = 49 * n + 47) ∧
      (∀ m, m % 343 ≠ 341 ↔ ¬ ∃ n, m = 343 * n + 341) ∧
      (∀ m, m % 2401 ≠ 2399 ↔ ¬ ∃ n, m = 2401 * n + 2399) ∧
      (∀ m, m % 16807 ≠ 16805 ↔ ¬ ∃ n, m = 16807 * n + 16805) := by
  exact ⟨mod7_ne5_iff_not_exists_7n_plus_5,
    mod49_ne47_iff_not_exists_49n_plus_47,
    mod343_ne341_iff_not_exists_343n_plus_341,
    mod2401_ne2399_iff_not_exists_2401n_plus_2399,
    mod16807_ne16805_iff_not_exists_16807n_plus_16805⟩

/-- Concrete mod-11 power residue inequality-first nonmembership facts. -/
theorem concrete_mod11_power_residue_ne_iff_short_nonmembership_facts :
    (∀ m, m % 11 ≠ 6 ↔ ¬ ∃ n, m = 11 * n + 6) ∧
      (∀ m, m % 121 ≠ 116 ↔ ¬ ∃ n, m = 121 * n + 116) ∧
      (∀ m, m % 1331 ≠ 1326 ↔ ¬ ∃ n, m = 1331 * n + 1326) ∧
      (∀ m, m % 14641 ≠ 14636 ↔ ¬ ∃ n, m = 14641 * n + 14636) ∧
      (∀ m, m % 161051 ≠ 161046 ↔ ¬ ∃ n, m = 161051 * n + 161046) := by
  exact ⟨mod11_ne6_iff_not_exists_11n_plus_6,
    mod121_ne116_iff_not_exists_121n_plus_116,
    mod1331_ne1326_iff_not_exists_1331n_plus_1326,
    mod14641_ne14636_iff_not_exists_14641n_plus_14636,
    mod161051_ne161046_iff_not_exists_161051n_plus_161046⟩

/-- A `Nat.ModEq` to a reduced residue is the same as a direct `%` equality. -/
theorem modEq_iff_mod_eq_of_lt {q r m : ℕ} (hr : r < q) :
    m ≡ r [MOD q] ↔ m % q = r := by
  rw [Nat.ModEq]
  rw [Nat.mod_eq_of_lt hr]

/-- `Nat.ModEq` form: `m ≡ 4 mod 5` iff `5 ∣ m+1`. -/
theorem modEq_four_mod5_iff_dvd_add_one (m : ℕ) :
    m ≡ 4 [MOD 5] ↔ 5 ∣ m + 1 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 5) (r := 4) (by decide)]
  exact ⟨dvd_add_one_of_mod5_eq4 m, mod5_eq4_of_dvd_add_one m⟩

/-- `Nat.ModEq` form: `m ≡ 24 mod 25` iff `25 ∣ m+1`. -/
theorem modEq_twentyfour_mod25_iff_dvd_add_one (m : ℕ) :
    m ≡ 24 [MOD 25] ↔ 25 ∣ m + 1 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 25) (r := 24) (by decide)]
  exact ⟨dvd_add_one_of_mod25_eq24 m, mod25_eq24_of_dvd_add_one m⟩

/-- `Nat.ModEq` form: `m ≡ 124 mod 125` iff `125 ∣ m+1`. -/
theorem modEq_onetwentyfour_mod125_iff_dvd_add_one (m : ℕ) :
    m ≡ 124 [MOD 125] ↔ 125 ∣ m + 1 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 125) (r := 124) (by decide)]
  exact ⟨dvd_add_one_of_mod125_eq124 m, mod125_eq124_of_dvd_add_one m⟩

/-- `Nat.ModEq` form: `m ≡ 624 mod 625` iff `625 ∣ m+1`. -/
theorem modEq_sixtwentyfour_mod625_iff_dvd_add_one (m : ℕ) :
    m ≡ 624 [MOD 625] ↔ 625 ∣ m + 1 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 625) (r := 624) (by decide)]
  exact ⟨dvd_add_one_of_mod625_eq624 m, mod625_eq624_of_dvd_add_one m⟩

/-- `Nat.ModEq` form: `m ≡ 3124 mod 3125` iff `3125 ∣ m+1`. -/
theorem modEq_thirtyonetwentyfour_mod3125_iff_dvd_add_one (m : ℕ) :
    m ≡ 3124 [MOD 3125] ↔ 3125 ∣ m + 1 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 3125) (r := 3124) (by decide)]
  exact ⟨dvd_add_one_of_mod3125_eq3124 m, mod3125_eq3124_of_dvd_add_one m⟩

/-- `Nat.ModEq` form: `m ≡ 5 mod 7` iff `7 ∣ m+2`. -/
theorem modEq_five_mod7_iff_dvd_add_two (m : ℕ) :
    m ≡ 5 [MOD 7] ↔ 7 ∣ m + 2 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 7) (r := 5) (by decide)]
  exact ⟨dvd_add_two_of_mod7_eq5 m, mod7_eq5_of_dvd_add_two m⟩

/-- `Nat.ModEq` form: `m ≡ 47 mod 49` iff `49 ∣ m+2`. -/
theorem modEq_fortyseven_mod49_iff_dvd_add_two (m : ℕ) :
    m ≡ 47 [MOD 49] ↔ 49 ∣ m + 2 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 49) (r := 47) (by decide)]
  exact ⟨dvd_add_two_of_mod49_eq47 m, mod49_eq47_of_dvd_add_two m⟩

/-- `Nat.ModEq` form: `m ≡ 341 mod 343` iff `343 ∣ m+2`. -/
theorem modEq_threefourtyone_mod343_iff_dvd_add_two (m : ℕ) :
    m ≡ 341 [MOD 343] ↔ 343 ∣ m + 2 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 343) (r := 341) (by decide)]
  exact ⟨dvd_add_two_of_mod343_eq341 m, mod343_eq341_of_dvd_add_two m⟩

/-- `Nat.ModEq` form: `m ≡ 2399 mod 2401` iff `2401 ∣ m+2`. -/
theorem modEq_twentythreeninetynine_mod2401_iff_dvd_add_two (m : ℕ) :
    m ≡ 2399 [MOD 2401] ↔ 2401 ∣ m + 2 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 2401) (r := 2399) (by decide)]
  exact ⟨dvd_add_two_of_mod2401_eq2399 m, mod2401_eq2399_of_dvd_add_two m⟩

/-- `Nat.ModEq` form: `m ≡ 16805 mod 16807` iff `16807 ∣ m+2`. -/
theorem modEq_sixteeneightofive_mod16807_iff_dvd_add_two (m : ℕ) :
    m ≡ 16805 [MOD 16807] ↔ 16807 ∣ m + 2 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 16807) (r := 16805) (by decide)]
  exact ⟨dvd_add_two_of_mod16807_eq16805 m, mod16807_eq16805_of_dvd_add_two m⟩

/-- `Nat.ModEq` form: `m ≡ 6 mod 11` iff `11 ∣ m+5`. -/
theorem modEq_six_mod11_iff_dvd_add_five (m : ℕ) :
    m ≡ 6 [MOD 11] ↔ 11 ∣ m + 5 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 11) (r := 6) (by decide)]
  exact ⟨dvd_add_five_of_mod11_eq6 m, mod11_eq6_of_dvd_add_five m⟩

/-- `Nat.ModEq` form: `m ≡ 116 mod 121` iff `121 ∣ m+5`. -/
theorem modEq_onesixteen_mod121_iff_dvd_add_five (m : ℕ) :
    m ≡ 116 [MOD 121] ↔ 121 ∣ m + 5 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 121) (r := 116) (by decide)]
  exact ⟨dvd_add_five_of_mod121_eq116 m, mod121_eq116_of_dvd_add_five m⟩

/-- `Nat.ModEq` form: `m ≡ 1326 mod 1331` iff `1331 ∣ m+5`. -/
theorem modEq_thirteentwentysix_mod1331_iff_dvd_add_five (m : ℕ) :
    m ≡ 1326 [MOD 1331] ↔ 1331 ∣ m + 5 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 1331) (r := 1326) (by decide)]
  exact ⟨dvd_add_five_of_mod1331_eq1326 m, mod1331_eq1326_of_dvd_add_five m⟩

/-- `Nat.ModEq` form: `m ≡ 14636 mod 14641` iff `14641 ∣ m+5`. -/
theorem modEq_fourteensixthirtysix_mod14641_iff_dvd_add_five (m : ℕ) :
    m ≡ 14636 [MOD 14641] ↔ 14641 ∣ m + 5 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 14641) (r := 14636) (by decide)]
  exact ⟨dvd_add_five_of_mod14641_eq14636 m, mod14641_eq14636_of_dvd_add_five m⟩

/-- `Nat.ModEq` form: `m ≡ 161046 mod 161051` iff `161051 ∣ m+5`. -/
theorem modEq_onesixtyonezero46_mod161051_iff_dvd_add_five (m : ℕ) :
    m ≡ 161046 [MOD 161051] ↔ 161051 ∣ m + 5 := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := 161051) (r := 161046) (by decide)]
  exact ⟨dvd_add_five_of_mod161051_eq161046 m, mod161051_eq161046_of_dvd_add_five m⟩

/-- Concrete mod-5 power `Nat.ModEq` iff shifted-divisibility facts. -/
theorem concrete_mod5_power_modEq_iff_dvd_add_one_facts :
    (∀ m, m ≡ 4 [MOD 5] ↔ 5 ∣ m + 1) ∧
      (∀ m, m ≡ 24 [MOD 25] ↔ 25 ∣ m + 1) ∧
      (∀ m, m ≡ 124 [MOD 125] ↔ 125 ∣ m + 1) ∧
      (∀ m, m ≡ 624 [MOD 625] ↔ 625 ∣ m + 1) ∧
      (∀ m, m ≡ 3124 [MOD 3125] ↔ 3125 ∣ m + 1) := by
  exact ⟨modEq_four_mod5_iff_dvd_add_one,
    modEq_twentyfour_mod25_iff_dvd_add_one,
    modEq_onetwentyfour_mod125_iff_dvd_add_one,
    modEq_sixtwentyfour_mod625_iff_dvd_add_one,
    modEq_thirtyonetwentyfour_mod3125_iff_dvd_add_one⟩

/-- Concrete mod-7 power `Nat.ModEq` iff shifted-divisibility facts. -/
theorem concrete_mod7_power_modEq_iff_dvd_add_two_facts :
    (∀ m, m ≡ 5 [MOD 7] ↔ 7 ∣ m + 2) ∧
      (∀ m, m ≡ 47 [MOD 49] ↔ 49 ∣ m + 2) ∧
      (∀ m, m ≡ 341 [MOD 343] ↔ 343 ∣ m + 2) ∧
      (∀ m, m ≡ 2399 [MOD 2401] ↔ 2401 ∣ m + 2) ∧
      (∀ m, m ≡ 16805 [MOD 16807] ↔ 16807 ∣ m + 2) := by
  exact ⟨modEq_five_mod7_iff_dvd_add_two,
    modEq_fortyseven_mod49_iff_dvd_add_two,
    modEq_threefourtyone_mod343_iff_dvd_add_two,
    modEq_twentythreeninetynine_mod2401_iff_dvd_add_two,
    modEq_sixteeneightofive_mod16807_iff_dvd_add_two⟩

/-- Concrete mod-11 power `Nat.ModEq` iff shifted-divisibility facts. -/
theorem concrete_mod11_power_modEq_iff_dvd_add_five_facts :
    (∀ m, m ≡ 6 [MOD 11] ↔ 11 ∣ m + 5) ∧
      (∀ m, m ≡ 116 [MOD 121] ↔ 121 ∣ m + 5) ∧
      (∀ m, m ≡ 1326 [MOD 1331] ↔ 1331 ∣ m + 5) ∧
      (∀ m, m ≡ 14636 [MOD 14641] ↔ 14641 ∣ m + 5) ∧
      (∀ m, m ≡ 161046 [MOD 161051] ↔ 161051 ∣ m + 5) := by
  exact ⟨modEq_six_mod11_iff_dvd_add_five,
    modEq_onesixteen_mod121_iff_dvd_add_five,
    modEq_thirteentwentysix_mod1331_iff_dvd_add_five,
    modEq_fourteensixthirtysix_mod14641_iff_dvd_add_five,
    modEq_onesixtyonezero46_mod161051_iff_dvd_add_five⟩

/-- Negated `Nat.ModEq` form: not `m ≡ 4 mod 5` iff `5 ∤ m+1`. -/
theorem not_modEq_four_mod5_iff_not_dvd_add_one (m : ℕ) :
    (¬ (m ≡ 4 [MOD 5])) ↔ ¬ (5 ∣ m + 1) := by
  exact not_congr (modEq_four_mod5_iff_dvd_add_one m)

/-- Negated `Nat.ModEq` form: not `m ≡ 24 mod 25` iff `25 ∤ m+1`. -/
theorem not_modEq_twentyfour_mod25_iff_not_dvd_add_one (m : ℕ) :
    (¬ (m ≡ 24 [MOD 25])) ↔ ¬ (25 ∣ m + 1) := by
  exact not_congr (modEq_twentyfour_mod25_iff_dvd_add_one m)

/-- Negated `Nat.ModEq` form: not `m ≡ 124 mod 125` iff `125 ∤ m+1`. -/
theorem not_modEq_onetwentyfour_mod125_iff_not_dvd_add_one (m : ℕ) :
    (¬ (m ≡ 124 [MOD 125])) ↔ ¬ (125 ∣ m + 1) := by
  exact not_congr (modEq_onetwentyfour_mod125_iff_dvd_add_one m)

/-- Negated `Nat.ModEq` form: not `m ≡ 624 mod 625` iff `625 ∤ m+1`. -/
theorem not_modEq_sixtwentyfour_mod625_iff_not_dvd_add_one (m : ℕ) :
    (¬ (m ≡ 624 [MOD 625])) ↔ ¬ (625 ∣ m + 1) := by
  exact not_congr (modEq_sixtwentyfour_mod625_iff_dvd_add_one m)

/-- Negated `Nat.ModEq` form: not `m ≡ 3124 mod 3125` iff `3125 ∤ m+1`. -/
theorem not_modEq_thirtyonetwentyfour_mod3125_iff_not_dvd_add_one (m : ℕ) :
    (¬ (m ≡ 3124 [MOD 3125])) ↔ ¬ (3125 ∣ m + 1) := by
  exact not_congr (modEq_thirtyonetwentyfour_mod3125_iff_dvd_add_one m)

/-- Negated `Nat.ModEq` form: not `m ≡ 5 mod 7` iff `7 ∤ m+2`. -/
theorem not_modEq_five_mod7_iff_not_dvd_add_two (m : ℕ) :
    (¬ (m ≡ 5 [MOD 7])) ↔ ¬ (7 ∣ m + 2) := by
  exact not_congr (modEq_five_mod7_iff_dvd_add_two m)

/-- Negated `Nat.ModEq` form: not `m ≡ 47 mod 49` iff `49 ∤ m+2`. -/
theorem not_modEq_fortyseven_mod49_iff_not_dvd_add_two (m : ℕ) :
    (¬ (m ≡ 47 [MOD 49])) ↔ ¬ (49 ∣ m + 2) := by
  exact not_congr (modEq_fortyseven_mod49_iff_dvd_add_two m)

/-- Negated `Nat.ModEq` form: not `m ≡ 341 mod 343` iff `343 ∤ m+2`. -/
theorem not_modEq_threefourtyone_mod343_iff_not_dvd_add_two (m : ℕ) :
    (¬ (m ≡ 341 [MOD 343])) ↔ ¬ (343 ∣ m + 2) := by
  exact not_congr (modEq_threefourtyone_mod343_iff_dvd_add_two m)

/-- Negated `Nat.ModEq` form: not `m ≡ 2399 mod 2401` iff `2401 ∤ m+2`. -/
theorem not_modEq_twentythreeninetynine_mod2401_iff_not_dvd_add_two (m : ℕ) :
    (¬ (m ≡ 2399 [MOD 2401])) ↔ ¬ (2401 ∣ m + 2) := by
  exact not_congr (modEq_twentythreeninetynine_mod2401_iff_dvd_add_two m)

/-- Negated `Nat.ModEq` form: not `m ≡ 16805 mod 16807` iff `16807 ∤ m+2`. -/
theorem not_modEq_sixteeneightofive_mod16807_iff_not_dvd_add_two (m : ℕ) :
    (¬ (m ≡ 16805 [MOD 16807])) ↔ ¬ (16807 ∣ m + 2) := by
  exact not_congr (modEq_sixteeneightofive_mod16807_iff_dvd_add_two m)

/-- Negated `Nat.ModEq` form: not `m ≡ 6 mod 11` iff `11 ∤ m+5`. -/
theorem not_modEq_six_mod11_iff_not_dvd_add_five (m : ℕ) :
    (¬ (m ≡ 6 [MOD 11])) ↔ ¬ (11 ∣ m + 5) := by
  exact not_congr (modEq_six_mod11_iff_dvd_add_five m)

/-- Negated `Nat.ModEq` form: not `m ≡ 116 mod 121` iff `121 ∤ m+5`. -/
theorem not_modEq_onesixteen_mod121_iff_not_dvd_add_five (m : ℕ) :
    (¬ (m ≡ 116 [MOD 121])) ↔ ¬ (121 ∣ m + 5) := by
  exact not_congr (modEq_onesixteen_mod121_iff_dvd_add_five m)

/-- Negated `Nat.ModEq` form: not `m ≡ 1326 mod 1331` iff `1331 ∤ m+5`. -/
theorem not_modEq_thirteentwentysix_mod1331_iff_not_dvd_add_five (m : ℕ) :
    (¬ (m ≡ 1326 [MOD 1331])) ↔ ¬ (1331 ∣ m + 5) := by
  exact not_congr (modEq_thirteentwentysix_mod1331_iff_dvd_add_five m)

/-- Negated `Nat.ModEq` form: not `m ≡ 14636 mod 14641` iff `14641 ∤ m+5`. -/
theorem not_modEq_fourteensixthirtysix_mod14641_iff_not_dvd_add_five (m : ℕ) :
    (¬ (m ≡ 14636 [MOD 14641])) ↔ ¬ (14641 ∣ m + 5) := by
  exact not_congr (modEq_fourteensixthirtysix_mod14641_iff_dvd_add_five m)

/-- Negated `Nat.ModEq` form: not `m ≡ 161046 mod 161051` iff `161051 ∤ m+5`. -/
theorem not_modEq_onesixtyonezero46_mod161051_iff_not_dvd_add_five (m : ℕ) :
    (¬ (m ≡ 161046 [MOD 161051])) ↔ ¬ (161051 ∣ m + 5) := by
  exact not_congr (modEq_onesixtyonezero46_mod161051_iff_dvd_add_five m)

/-- Concrete mod-5 power negated `Nat.ModEq` iff shifted nondivisibility facts. -/
theorem concrete_mod5_power_not_modEq_iff_not_dvd_add_one_facts :
    (∀ m, (¬ (m ≡ 4 [MOD 5])) ↔ ¬ (5 ∣ m + 1)) ∧
      (∀ m, (¬ (m ≡ 24 [MOD 25])) ↔ ¬ (25 ∣ m + 1)) ∧
      (∀ m, (¬ (m ≡ 124 [MOD 125])) ↔ ¬ (125 ∣ m + 1)) ∧
      (∀ m, (¬ (m ≡ 624 [MOD 625])) ↔ ¬ (625 ∣ m + 1)) ∧
      (∀ m, (¬ (m ≡ 3124 [MOD 3125])) ↔ ¬ (3125 ∣ m + 1)) := by
  exact ⟨not_modEq_four_mod5_iff_not_dvd_add_one,
    not_modEq_twentyfour_mod25_iff_not_dvd_add_one,
    not_modEq_onetwentyfour_mod125_iff_not_dvd_add_one,
    not_modEq_sixtwentyfour_mod625_iff_not_dvd_add_one,
    not_modEq_thirtyonetwentyfour_mod3125_iff_not_dvd_add_one⟩

/-- Concrete mod-7 power negated `Nat.ModEq` iff shifted nondivisibility facts. -/
theorem concrete_mod7_power_not_modEq_iff_not_dvd_add_two_facts :
    (∀ m, (¬ (m ≡ 5 [MOD 7])) ↔ ¬ (7 ∣ m + 2)) ∧
      (∀ m, (¬ (m ≡ 47 [MOD 49])) ↔ ¬ (49 ∣ m + 2)) ∧
      (∀ m, (¬ (m ≡ 341 [MOD 343])) ↔ ¬ (343 ∣ m + 2)) ∧
      (∀ m, (¬ (m ≡ 2399 [MOD 2401])) ↔ ¬ (2401 ∣ m + 2)) ∧
      (∀ m, (¬ (m ≡ 16805 [MOD 16807])) ↔ ¬ (16807 ∣ m + 2)) := by
  exact ⟨not_modEq_five_mod7_iff_not_dvd_add_two,
    not_modEq_fortyseven_mod49_iff_not_dvd_add_two,
    not_modEq_threefourtyone_mod343_iff_not_dvd_add_two,
    not_modEq_twentythreeninetynine_mod2401_iff_not_dvd_add_two,
    not_modEq_sixteeneightofive_mod16807_iff_not_dvd_add_two⟩

/-- Concrete mod-11 power negated `Nat.ModEq` iff shifted nondivisibility facts. -/
theorem concrete_mod11_power_not_modEq_iff_not_dvd_add_five_facts :
    (∀ m, (¬ (m ≡ 6 [MOD 11])) ↔ ¬ (11 ∣ m + 5)) ∧
      (∀ m, (¬ (m ≡ 116 [MOD 121])) ↔ ¬ (121 ∣ m + 5)) ∧
      (∀ m, (¬ (m ≡ 1326 [MOD 1331])) ↔ ¬ (1331 ∣ m + 5)) ∧
      (∀ m, (¬ (m ≡ 14636 [MOD 14641])) ↔ ¬ (14641 ∣ m + 5)) ∧
      (∀ m, (¬ (m ≡ 161046 [MOD 161051])) ↔ ¬ (161051 ∣ m + 5)) := by
  exact ⟨not_modEq_six_mod11_iff_not_dvd_add_five,
    not_modEq_onesixteen_mod121_iff_not_dvd_add_five,
    not_modEq_thirteentwentysix_mod1331_iff_not_dvd_add_five,
    not_modEq_fourteensixthirtysix_mod14641_iff_not_dvd_add_five,
    not_modEq_onesixtyonezero46_mod161051_iff_not_dvd_add_five⟩

/-- Shifted-divisibility-first membership form for `5n+4`. -/
theorem dvd_add_one_by_5_iff_exists_5n_plus_4 (m : ℕ) :
    5 ∣ m + 1 ↔ ∃ n, m = 5 * n + 4 := by
  exact (exists_5n_plus_4_iff_dvd_add_one_by_5 m).symm

/-- Shifted-divisibility-first membership form for `25n+24`. -/
theorem dvd_add_one_by_25_iff_exists_25n_plus_24 (m : ℕ) :
    25 ∣ m + 1 ↔ ∃ n, m = 25 * n + 24 := by
  exact (exists_25n_plus_24_iff_dvd_add_one_by_25 m).symm

/-- Shifted-divisibility-first membership form for `125n+124`. -/
theorem dvd_add_one_by_125_iff_exists_125n_plus_124 (m : ℕ) :
    125 ∣ m + 1 ↔ ∃ n, m = 125 * n + 124 := by
  exact (exists_125n_plus_124_iff_dvd_add_one_by_125 m).symm

/-- Shifted-divisibility-first membership form for `625n+624`. -/
theorem dvd_add_one_by_625_iff_exists_625n_plus_624 (m : ℕ) :
    625 ∣ m + 1 ↔ ∃ n, m = 625 * n + 624 := by
  exact (exists_625n_plus_624_iff_dvd_add_one_by_625 m).symm

/-- Shifted-divisibility-first membership form for `3125n+3124`. -/
theorem dvd_add_one_by_3125_iff_exists_3125n_plus_3124 (m : ℕ) :
    3125 ∣ m + 1 ↔ ∃ n, m = 3125 * n + 3124 := by
  exact (exists_3125n_plus_3124_iff_dvd_add_one_by_3125 m).symm

/-- Shifted-divisibility-first membership form for `7n+5`. -/
theorem dvd_add_two_by_7_iff_exists_7n_plus_5 (m : ℕ) :
    7 ∣ m + 2 ↔ ∃ n, m = 7 * n + 5 := by
  exact (exists_7n_plus_5_iff_dvd_add_two_by_7 m).symm

/-- Shifted-divisibility-first membership form for `49n+47`. -/
theorem dvd_add_two_by_49_iff_exists_49n_plus_47 (m : ℕ) :
    49 ∣ m + 2 ↔ ∃ n, m = 49 * n + 47 := by
  exact (exists_49n_plus_47_iff_dvd_add_two_by_49 m).symm

/-- Shifted-divisibility-first membership form for `343n+341`. -/
theorem dvd_add_two_by_343_iff_exists_343n_plus_341 (m : ℕ) :
    343 ∣ m + 2 ↔ ∃ n, m = 343 * n + 341 := by
  exact (exists_343n_plus_341_iff_dvd_add_two_by_343 m).symm

/-- Shifted-divisibility-first membership form for `2401n+2399`. -/
theorem dvd_add_two_by_2401_iff_exists_2401n_plus_2399 (m : ℕ) :
    2401 ∣ m + 2 ↔ ∃ n, m = 2401 * n + 2399 := by
  exact (exists_2401n_plus_2399_iff_dvd_add_two_by_2401 m).symm

/-- Shifted-divisibility-first membership form for `16807n+16805`. -/
theorem dvd_add_two_by_16807_iff_exists_16807n_plus_16805 (m : ℕ) :
    16807 ∣ m + 2 ↔ ∃ n, m = 16807 * n + 16805 := by
  exact (exists_16807n_plus_16805_iff_dvd_add_two_by_16807 m).symm

/-- Shifted-divisibility-first membership form for `11n+6`. -/
theorem dvd_add_five_by_11_iff_exists_11n_plus_6 (m : ℕ) :
    11 ∣ m + 5 ↔ ∃ n, m = 11 * n + 6 := by
  exact (exists_11n_plus_6_iff_dvd_add_five_by_11 m).symm

/-- Shifted-divisibility-first membership form for `121n+116`. -/
theorem dvd_add_five_by_121_iff_exists_121n_plus_116 (m : ℕ) :
    121 ∣ m + 5 ↔ ∃ n, m = 121 * n + 116 := by
  exact (exists_121n_plus_116_iff_dvd_add_five_by_121 m).symm

/-- Shifted-divisibility-first membership form for `1331n+1326`. -/
theorem dvd_add_five_by_1331_iff_exists_1331n_plus_1326 (m : ℕ) :
    1331 ∣ m + 5 ↔ ∃ n, m = 1331 * n + 1326 := by
  exact (exists_1331n_plus_1326_iff_dvd_add_five_by_1331 m).symm

/-- Shifted-divisibility-first membership form for `14641n+14636`. -/
theorem dvd_add_five_by_14641_iff_exists_14641n_plus_14636 (m : ℕ) :
    14641 ∣ m + 5 ↔ ∃ n, m = 14641 * n + 14636 := by
  exact (exists_14641n_plus_14636_iff_dvd_add_five_by_14641 m).symm

/-- Shifted-divisibility-first membership form for `161051n+161046`. -/
theorem dvd_add_five_by_161051_iff_exists_161051n_plus_161046
    (m : ℕ) :
    161051 ∣ m + 5 ↔ ∃ n, m = 161051 * n + 161046 := by
  exact (exists_161051n_plus_161046_iff_dvd_add_five_by_161051 m).symm

/-- Concrete mod-5 power shifted-divisibility-first membership facts. -/
theorem concrete_mod5_power_dvd_add_one_iff_short_membership_facts :
    (∀ m, 5 ∣ m + 1 ↔ ∃ n, m = 5 * n + 4) ∧
      (∀ m, 25 ∣ m + 1 ↔ ∃ n, m = 25 * n + 24) ∧
      (∀ m, 125 ∣ m + 1 ↔ ∃ n, m = 125 * n + 124) ∧
      (∀ m, 625 ∣ m + 1 ↔ ∃ n, m = 625 * n + 624) ∧
      (∀ m, 3125 ∣ m + 1 ↔ ∃ n, m = 3125 * n + 3124) := by
  exact ⟨dvd_add_one_by_5_iff_exists_5n_plus_4,
    dvd_add_one_by_25_iff_exists_25n_plus_24,
    dvd_add_one_by_125_iff_exists_125n_plus_124,
    dvd_add_one_by_625_iff_exists_625n_plus_624,
    dvd_add_one_by_3125_iff_exists_3125n_plus_3124⟩

/-- Concrete mod-7 power shifted-divisibility-first membership facts. -/
theorem concrete_mod7_power_dvd_add_two_iff_short_membership_facts :
    (∀ m, 7 ∣ m + 2 ↔ ∃ n, m = 7 * n + 5) ∧
      (∀ m, 49 ∣ m + 2 ↔ ∃ n, m = 49 * n + 47) ∧
      (∀ m, 343 ∣ m + 2 ↔ ∃ n, m = 343 * n + 341) ∧
      (∀ m, 2401 ∣ m + 2 ↔ ∃ n, m = 2401 * n + 2399) ∧
      (∀ m, 16807 ∣ m + 2 ↔ ∃ n, m = 16807 * n + 16805) := by
  exact ⟨dvd_add_two_by_7_iff_exists_7n_plus_5,
    dvd_add_two_by_49_iff_exists_49n_plus_47,
    dvd_add_two_by_343_iff_exists_343n_plus_341,
    dvd_add_two_by_2401_iff_exists_2401n_plus_2399,
    dvd_add_two_by_16807_iff_exists_16807n_plus_16805⟩

/-- Concrete mod-11 power shifted-divisibility-first membership facts. -/
theorem concrete_mod11_power_dvd_add_five_iff_short_membership_facts :
    (∀ m, 11 ∣ m + 5 ↔ ∃ n, m = 11 * n + 6) ∧
      (∀ m, 121 ∣ m + 5 ↔ ∃ n, m = 121 * n + 116) ∧
      (∀ m, 1331 ∣ m + 5 ↔ ∃ n, m = 1331 * n + 1326) ∧
      (∀ m, 14641 ∣ m + 5 ↔ ∃ n, m = 14641 * n + 14636) ∧
      (∀ m, 161051 ∣ m + 5 ↔ ∃ n, m = 161051 * n + 161046) := by
  exact ⟨dvd_add_five_by_11_iff_exists_11n_plus_6,
    dvd_add_five_by_121_iff_exists_121n_plus_116,
    dvd_add_five_by_1331_iff_exists_1331n_plus_1326,
    dvd_add_five_by_14641_iff_exists_14641n_plus_14636,
    dvd_add_five_by_161051_iff_exists_161051n_plus_161046⟩

/-- Divisibility-first `Nat.ModEq` form: `5 ∣ m+1` iff `m ≡ 4 mod 5`. -/
theorem dvd_add_one_iff_modEq_four_mod5 (m : ℕ) :
    5 ∣ m + 1 ↔ m ≡ 4 [MOD 5] :=
  (modEq_four_mod5_iff_dvd_add_one m).symm

/-- Divisibility-first `Nat.ModEq` form: `25 ∣ m+1` iff `m ≡ 24 mod 25`. -/
theorem dvd_add_one_iff_modEq_twentyfour_mod25 (m : ℕ) :
    25 ∣ m + 1 ↔ m ≡ 24 [MOD 25] :=
  (modEq_twentyfour_mod25_iff_dvd_add_one m).symm

/-- Divisibility-first `Nat.ModEq` form: `125 ∣ m+1` iff `m ≡ 124 mod 125`. -/
theorem dvd_add_one_iff_modEq_onetwentyfour_mod125 (m : ℕ) :
    125 ∣ m + 1 ↔ m ≡ 124 [MOD 125] :=
  (modEq_onetwentyfour_mod125_iff_dvd_add_one m).symm

/-- Divisibility-first `Nat.ModEq` form: `625 ∣ m+1` iff `m ≡ 624 mod 625`. -/
theorem dvd_add_one_iff_modEq_sixtwentyfour_mod625 (m : ℕ) :
    625 ∣ m + 1 ↔ m ≡ 624 [MOD 625] :=
  (modEq_sixtwentyfour_mod625_iff_dvd_add_one m).symm

/-- Divisibility-first `Nat.ModEq` form: `3125 ∣ m+1` iff `m ≡ 3124 mod 3125`. -/
theorem dvd_add_one_iff_modEq_thirtyonetwentyfour_mod3125 (m : ℕ) :
    3125 ∣ m + 1 ↔ m ≡ 3124 [MOD 3125] :=
  (modEq_thirtyonetwentyfour_mod3125_iff_dvd_add_one m).symm

/-- Divisibility-first `Nat.ModEq` form: `7 ∣ m+2` iff `m ≡ 5 mod 7`. -/
theorem dvd_add_two_iff_modEq_five_mod7 (m : ℕ) :
    7 ∣ m + 2 ↔ m ≡ 5 [MOD 7] :=
  (modEq_five_mod7_iff_dvd_add_two m).symm

/-- Divisibility-first `Nat.ModEq` form: `49 ∣ m+2` iff `m ≡ 47 mod 49`. -/
theorem dvd_add_two_iff_modEq_fortyseven_mod49 (m : ℕ) :
    49 ∣ m + 2 ↔ m ≡ 47 [MOD 49] :=
  (modEq_fortyseven_mod49_iff_dvd_add_two m).symm

/-- Divisibility-first `Nat.ModEq` form: `343 ∣ m+2` iff `m ≡ 341 mod 343`. -/
theorem dvd_add_two_iff_modEq_threefourtyone_mod343 (m : ℕ) :
    343 ∣ m + 2 ↔ m ≡ 341 [MOD 343] :=
  (modEq_threefourtyone_mod343_iff_dvd_add_two m).symm

/-- Divisibility-first `Nat.ModEq` form: `2401 ∣ m+2` iff `m ≡ 2399 mod 2401`. -/
theorem dvd_add_two_iff_modEq_twentythreeninetynine_mod2401 (m : ℕ) :
    2401 ∣ m + 2 ↔ m ≡ 2399 [MOD 2401] :=
  (modEq_twentythreeninetynine_mod2401_iff_dvd_add_two m).symm

/-- Divisibility-first `Nat.ModEq` form: `16807 ∣ m+2` iff `m ≡ 16805 mod 16807`. -/
theorem dvd_add_two_iff_modEq_sixteeneightofive_mod16807 (m : ℕ) :
    16807 ∣ m + 2 ↔ m ≡ 16805 [MOD 16807] :=
  (modEq_sixteeneightofive_mod16807_iff_dvd_add_two m).symm

/-- Divisibility-first `Nat.ModEq` form: `11 ∣ m+5` iff `m ≡ 6 mod 11`. -/
theorem dvd_add_five_iff_modEq_six_mod11 (m : ℕ) :
    11 ∣ m + 5 ↔ m ≡ 6 [MOD 11] :=
  (modEq_six_mod11_iff_dvd_add_five m).symm

/-- Divisibility-first `Nat.ModEq` form: `121 ∣ m+5` iff `m ≡ 116 mod 121`. -/
theorem dvd_add_five_iff_modEq_onesixteen_mod121 (m : ℕ) :
    121 ∣ m + 5 ↔ m ≡ 116 [MOD 121] :=
  (modEq_onesixteen_mod121_iff_dvd_add_five m).symm

/-- Divisibility-first `Nat.ModEq` form: `1331 ∣ m+5` iff `m ≡ 1326 mod 1331`. -/
theorem dvd_add_five_iff_modEq_thirteentwentysix_mod1331 (m : ℕ) :
    1331 ∣ m + 5 ↔ m ≡ 1326 [MOD 1331] :=
  (modEq_thirteentwentysix_mod1331_iff_dvd_add_five m).symm

/-- Divisibility-first `Nat.ModEq` form: `14641 ∣ m+5` iff `m ≡ 14636 mod 14641`. -/
theorem dvd_add_five_iff_modEq_fourteensixthirtysix_mod14641 (m : ℕ) :
    14641 ∣ m + 5 ↔ m ≡ 14636 [MOD 14641] :=
  (modEq_fourteensixthirtysix_mod14641_iff_dvd_add_five m).symm

/-- Divisibility-first `Nat.ModEq` form: `161051 ∣ m+5` iff `m ≡ 161046 mod 161051`. -/
theorem dvd_add_five_iff_modEq_onesixtyonezero46_mod161051 (m : ℕ) :
    161051 ∣ m + 5 ↔ m ≡ 161046 [MOD 161051] :=
  (modEq_onesixtyonezero46_mod161051_iff_dvd_add_five m).symm

/-- Concrete mod-5 power shifted-divisibility-first `Nat.ModEq` facts. -/
theorem concrete_mod5_power_dvd_add_one_iff_modEq_facts :
    (∀ m, 5 ∣ m + 1 ↔ m ≡ 4 [MOD 5]) ∧
      (∀ m, 25 ∣ m + 1 ↔ m ≡ 24 [MOD 25]) ∧
      (∀ m, 125 ∣ m + 1 ↔ m ≡ 124 [MOD 125]) ∧
      (∀ m, 625 ∣ m + 1 ↔ m ≡ 624 [MOD 625]) ∧
      (∀ m, 3125 ∣ m + 1 ↔ m ≡ 3124 [MOD 3125]) := by
  exact ⟨dvd_add_one_iff_modEq_four_mod5,
    dvd_add_one_iff_modEq_twentyfour_mod25,
    dvd_add_one_iff_modEq_onetwentyfour_mod125,
    dvd_add_one_iff_modEq_sixtwentyfour_mod625,
    dvd_add_one_iff_modEq_thirtyonetwentyfour_mod3125⟩

/-- Concrete mod-7 power shifted-divisibility-first `Nat.ModEq` facts. -/
theorem concrete_mod7_power_dvd_add_two_iff_modEq_facts :
    (∀ m, 7 ∣ m + 2 ↔ m ≡ 5 [MOD 7]) ∧
      (∀ m, 49 ∣ m + 2 ↔ m ≡ 47 [MOD 49]) ∧
      (∀ m, 343 ∣ m + 2 ↔ m ≡ 341 [MOD 343]) ∧
      (∀ m, 2401 ∣ m + 2 ↔ m ≡ 2399 [MOD 2401]) ∧
      (∀ m, 16807 ∣ m + 2 ↔ m ≡ 16805 [MOD 16807]) := by
  exact ⟨dvd_add_two_iff_modEq_five_mod7,
    dvd_add_two_iff_modEq_fortyseven_mod49,
    dvd_add_two_iff_modEq_threefourtyone_mod343,
    dvd_add_two_iff_modEq_twentythreeninetynine_mod2401,
    dvd_add_two_iff_modEq_sixteeneightofive_mod16807⟩

/-- Concrete mod-11 power shifted-divisibility-first `Nat.ModEq` facts. -/
theorem concrete_mod11_power_dvd_add_five_iff_modEq_facts :
    (∀ m, 11 ∣ m + 5 ↔ m ≡ 6 [MOD 11]) ∧
      (∀ m, 121 ∣ m + 5 ↔ m ≡ 116 [MOD 121]) ∧
      (∀ m, 1331 ∣ m + 5 ↔ m ≡ 1326 [MOD 1331]) ∧
      (∀ m, 14641 ∣ m + 5 ↔ m ≡ 14636 [MOD 14641]) ∧
      (∀ m, 161051 ∣ m + 5 ↔ m ≡ 161046 [MOD 161051]) := by
  exact ⟨dvd_add_five_iff_modEq_six_mod11,
    dvd_add_five_iff_modEq_onesixteen_mod121,
    dvd_add_five_iff_modEq_thirteentwentysix_mod1331,
    dvd_add_five_iff_modEq_fourteensixthirtysix_mod14641,
    dvd_add_five_iff_modEq_onesixtyonezero46_mod161051⟩

/-- Shifted nondivisibility-first form for `5 ∤ m+1`. -/
theorem not_dvd_add_one_iff_not_modEq_four_mod5 (m : ℕ) :
    (¬ (5 ∣ m + 1)) ↔ ¬ (m ≡ 4 [MOD 5]) :=
  (not_modEq_four_mod5_iff_not_dvd_add_one m).symm

/-- Shifted nondivisibility-first form for `25 ∤ m+1`. -/
theorem not_dvd_add_one_iff_not_modEq_twentyfour_mod25 (m : ℕ) :
    (¬ (25 ∣ m + 1)) ↔ ¬ (m ≡ 24 [MOD 25]) :=
  (not_modEq_twentyfour_mod25_iff_not_dvd_add_one m).symm

/-- Shifted nondivisibility-first form for `125 ∤ m+1`. -/
theorem not_dvd_add_one_iff_not_modEq_onetwentyfour_mod125 (m : ℕ) :
    (¬ (125 ∣ m + 1)) ↔ ¬ (m ≡ 124 [MOD 125]) :=
  (not_modEq_onetwentyfour_mod125_iff_not_dvd_add_one m).symm

/-- Shifted nondivisibility-first form for `625 ∤ m+1`. -/
theorem not_dvd_add_one_iff_not_modEq_sixtwentyfour_mod625 (m : ℕ) :
    (¬ (625 ∣ m + 1)) ↔ ¬ (m ≡ 624 [MOD 625]) :=
  (not_modEq_sixtwentyfour_mod625_iff_not_dvd_add_one m).symm

/-- Shifted nondivisibility-first form for `3125 ∤ m+1`. -/
theorem not_dvd_add_one_iff_not_modEq_thirtyonetwentyfour_mod3125 (m : ℕ) :
    (¬ (3125 ∣ m + 1)) ↔ ¬ (m ≡ 3124 [MOD 3125]) :=
  (not_modEq_thirtyonetwentyfour_mod3125_iff_not_dvd_add_one m).symm

/-- Shifted nondivisibility-first form for `7 ∤ m+2`. -/
theorem not_dvd_add_two_iff_not_modEq_five_mod7 (m : ℕ) :
    (¬ (7 ∣ m + 2)) ↔ ¬ (m ≡ 5 [MOD 7]) :=
  (not_modEq_five_mod7_iff_not_dvd_add_two m).symm

/-- Shifted nondivisibility-first form for `49 ∤ m+2`. -/
theorem not_dvd_add_two_iff_not_modEq_fortyseven_mod49 (m : ℕ) :
    (¬ (49 ∣ m + 2)) ↔ ¬ (m ≡ 47 [MOD 49]) :=
  (not_modEq_fortyseven_mod49_iff_not_dvd_add_two m).symm

/-- Shifted nondivisibility-first form for `343 ∤ m+2`. -/
theorem not_dvd_add_two_iff_not_modEq_threefourtyone_mod343 (m : ℕ) :
    (¬ (343 ∣ m + 2)) ↔ ¬ (m ≡ 341 [MOD 343]) :=
  (not_modEq_threefourtyone_mod343_iff_not_dvd_add_two m).symm

/-- Shifted nondivisibility-first form for `2401 ∤ m+2`. -/
theorem not_dvd_add_two_iff_not_modEq_twentythreeninetynine_mod2401 (m : ℕ) :
    (¬ (2401 ∣ m + 2)) ↔ ¬ (m ≡ 2399 [MOD 2401]) :=
  (not_modEq_twentythreeninetynine_mod2401_iff_not_dvd_add_two m).symm

/-- Shifted nondivisibility-first form for `16807 ∤ m+2`. -/
theorem not_dvd_add_two_iff_not_modEq_sixteeneightofive_mod16807 (m : ℕ) :
    (¬ (16807 ∣ m + 2)) ↔ ¬ (m ≡ 16805 [MOD 16807]) :=
  (not_modEq_sixteeneightofive_mod16807_iff_not_dvd_add_two m).symm

/-- Shifted nondivisibility-first form for `11 ∤ m+5`. -/
theorem not_dvd_add_five_iff_not_modEq_six_mod11 (m : ℕ) :
    (¬ (11 ∣ m + 5)) ↔ ¬ (m ≡ 6 [MOD 11]) :=
  (not_modEq_six_mod11_iff_not_dvd_add_five m).symm

/-- Shifted nondivisibility-first form for `121 ∤ m+5`. -/
theorem not_dvd_add_five_iff_not_modEq_onesixteen_mod121 (m : ℕ) :
    (¬ (121 ∣ m + 5)) ↔ ¬ (m ≡ 116 [MOD 121]) :=
  (not_modEq_onesixteen_mod121_iff_not_dvd_add_five m).symm

/-- Shifted nondivisibility-first form for `1331 ∤ m+5`. -/
theorem not_dvd_add_five_iff_not_modEq_thirteentwentysix_mod1331 (m : ℕ) :
    (¬ (1331 ∣ m + 5)) ↔ ¬ (m ≡ 1326 [MOD 1331]) :=
  (not_modEq_thirteentwentysix_mod1331_iff_not_dvd_add_five m).symm

/-- Shifted nondivisibility-first form for `14641 ∤ m+5`. -/
theorem not_dvd_add_five_iff_not_modEq_fourteensixthirtysix_mod14641 (m : ℕ) :
    (¬ (14641 ∣ m + 5)) ↔ ¬ (m ≡ 14636 [MOD 14641]) :=
  (not_modEq_fourteensixthirtysix_mod14641_iff_not_dvd_add_five m).symm

/-- Shifted nondivisibility-first form for `161051 ∤ m+5`. -/
theorem not_dvd_add_five_iff_not_modEq_onesixtyonezero46_mod161051 (m : ℕ) :
    (¬ (161051 ∣ m + 5)) ↔ ¬ (m ≡ 161046 [MOD 161051]) :=
  (not_modEq_onesixtyonezero46_mod161051_iff_not_dvd_add_five m).symm

/-- Concrete mod-5 power shifted-nondivisibility-first `Nat.ModEq` facts. -/
theorem concrete_mod5_power_not_dvd_add_one_iff_not_modEq_facts :
    (∀ m, (¬ (5 ∣ m + 1)) ↔ ¬ (m ≡ 4 [MOD 5])) ∧
      (∀ m, (¬ (25 ∣ m + 1)) ↔ ¬ (m ≡ 24 [MOD 25])) ∧
      (∀ m, (¬ (125 ∣ m + 1)) ↔ ¬ (m ≡ 124 [MOD 125])) ∧
      (∀ m, (¬ (625 ∣ m + 1)) ↔ ¬ (m ≡ 624 [MOD 625])) ∧
      (∀ m, (¬ (3125 ∣ m + 1)) ↔ ¬ (m ≡ 3124 [MOD 3125])) := by
  exact ⟨not_dvd_add_one_iff_not_modEq_four_mod5,
    not_dvd_add_one_iff_not_modEq_twentyfour_mod25,
    not_dvd_add_one_iff_not_modEq_onetwentyfour_mod125,
    not_dvd_add_one_iff_not_modEq_sixtwentyfour_mod625,
    not_dvd_add_one_iff_not_modEq_thirtyonetwentyfour_mod3125⟩

/-- Concrete mod-7 power shifted-nondivisibility-first `Nat.ModEq` facts. -/
theorem concrete_mod7_power_not_dvd_add_two_iff_not_modEq_facts :
    (∀ m, (¬ (7 ∣ m + 2)) ↔ ¬ (m ≡ 5 [MOD 7])) ∧
      (∀ m, (¬ (49 ∣ m + 2)) ↔ ¬ (m ≡ 47 [MOD 49])) ∧
      (∀ m, (¬ (343 ∣ m + 2)) ↔ ¬ (m ≡ 341 [MOD 343])) ∧
      (∀ m, (¬ (2401 ∣ m + 2)) ↔ ¬ (m ≡ 2399 [MOD 2401])) ∧
      (∀ m, (¬ (16807 ∣ m + 2)) ↔ ¬ (m ≡ 16805 [MOD 16807])) := by
  exact ⟨not_dvd_add_two_iff_not_modEq_five_mod7,
    not_dvd_add_two_iff_not_modEq_fortyseven_mod49,
    not_dvd_add_two_iff_not_modEq_threefourtyone_mod343,
    not_dvd_add_two_iff_not_modEq_twentythreeninetynine_mod2401,
    not_dvd_add_two_iff_not_modEq_sixteeneightofive_mod16807⟩

/-- Concrete mod-11 power shifted-nondivisibility-first `Nat.ModEq` facts. -/
theorem concrete_mod11_power_not_dvd_add_five_iff_not_modEq_facts :
    (∀ m, (¬ (11 ∣ m + 5)) ↔ ¬ (m ≡ 6 [MOD 11])) ∧
      (∀ m, (¬ (121 ∣ m + 5)) ↔ ¬ (m ≡ 116 [MOD 121])) ∧
      (∀ m, (¬ (1331 ∣ m + 5)) ↔ ¬ (m ≡ 1326 [MOD 1331])) ∧
      (∀ m, (¬ (14641 ∣ m + 5)) ↔ ¬ (m ≡ 14636 [MOD 14641])) ∧
      (∀ m, (¬ (161051 ∣ m + 5)) ↔ ¬ (m ≡ 161046 [MOD 161051])) := by
  exact ⟨not_dvd_add_five_iff_not_modEq_six_mod11,
    not_dvd_add_five_iff_not_modEq_onesixteen_mod121,
    not_dvd_add_five_iff_not_modEq_thirteentwentysix_mod1331,
    not_dvd_add_five_iff_not_modEq_fourteensixthirtysix_mod14641,
    not_dvd_add_five_iff_not_modEq_onesixtyonezero46_mod161051⟩

/-- Shifted-nondivisibility-first nonmembership form for a residue progression. -/
theorem not_dvd_add_iff_not_exists_mul_add {q r c m : ℕ}
    (hc : 0 < c) (hmod : r + c = q) :
    ¬ (q ∣ m + c) ↔ ¬ ∃ n, m = q * n + r := by
  exact (not_exists_mul_add_iff_not_dvd_add (q := q) (r := r) (c := c)
    (m := m) hc hmod).symm

/-- Shifted-nondivisibility-first nonmembership form for `5n+4`. -/
theorem not_dvd_add_one_by_5_iff_not_exists_5n_plus_4 (m : ℕ) :
    ¬ (5 ∣ m + 1) ↔ ¬ ∃ n, m = 5 * n + 4 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 5) (r := 4) (c := 1)
    (m := m) (by decide) (by decide)

/-- Shifted-nondivisibility-first nonmembership form for `25n+24`. -/
theorem not_dvd_add_one_by_25_iff_not_exists_25n_plus_24 (m : ℕ) :
    ¬ (25 ∣ m + 1) ↔ ¬ ∃ n, m = 25 * n + 24 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 25) (r := 24) (c := 1)
    (m := m) (by decide) (by decide)

/-- Shifted-nondivisibility-first nonmembership form for `125n+124`. -/
theorem not_dvd_add_one_by_125_iff_not_exists_125n_plus_124 (m : ℕ) :
    ¬ (125 ∣ m + 1) ↔ ¬ ∃ n, m = 125 * n + 124 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 125) (r := 124) (c := 1)
    (m := m) (by decide) (by decide)

/-- Shifted-nondivisibility-first nonmembership form for `625n+624`. -/
theorem not_dvd_add_one_by_625_iff_not_exists_625n_plus_624 (m : ℕ) :
    ¬ (625 ∣ m + 1) ↔ ¬ ∃ n, m = 625 * n + 624 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 625) (r := 624) (c := 1)
    (m := m) (by decide) (by decide)

/-- Shifted-nondivisibility-first nonmembership form for `3125n+3124`. -/
theorem not_dvd_add_one_by_3125_iff_not_exists_3125n_plus_3124 (m : ℕ) :
    ¬ (3125 ∣ m + 1) ↔ ¬ ∃ n, m = 3125 * n + 3124 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 3125) (r := 3124) (c := 1)
    (m := m) (by decide) (by decide)

/-- Shifted-nondivisibility-first nonmembership form for `7n+5`. -/
theorem not_dvd_add_two_by_7_iff_not_exists_7n_plus_5 (m : ℕ) :
    ¬ (7 ∣ m + 2) ↔ ¬ ∃ n, m = 7 * n + 5 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 7) (r := 5) (c := 2)
    (m := m) (by decide) (by decide)

/-- Shifted-nondivisibility-first nonmembership form for `49n+47`. -/
theorem not_dvd_add_two_by_49_iff_not_exists_49n_plus_47 (m : ℕ) :
    ¬ (49 ∣ m + 2) ↔ ¬ ∃ n, m = 49 * n + 47 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 49) (r := 47) (c := 2)
    (m := m) (by decide) (by decide)

/-- Shifted-nondivisibility-first nonmembership form for `343n+341`. -/
theorem not_dvd_add_two_by_343_iff_not_exists_343n_plus_341 (m : ℕ) :
    ¬ (343 ∣ m + 2) ↔ ¬ ∃ n, m = 343 * n + 341 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 343) (r := 341) (c := 2)
    (m := m) (by decide) (by decide)

/-- Shifted-nondivisibility-first nonmembership form for `2401n+2399`. -/
theorem not_dvd_add_two_by_2401_iff_not_exists_2401n_plus_2399 (m : ℕ) :
    ¬ (2401 ∣ m + 2) ↔ ¬ ∃ n, m = 2401 * n + 2399 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 2401) (r := 2399) (c := 2)
    (m := m) (by decide) (by decide)

/-- Shifted-nondivisibility-first nonmembership form for `16807n+16805`. -/
theorem not_dvd_add_two_by_16807_iff_not_exists_16807n_plus_16805
    (m : ℕ) :
    ¬ (16807 ∣ m + 2) ↔ ¬ ∃ n, m = 16807 * n + 16805 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 16807) (r := 16805) (c := 2)
    (m := m) (by decide) (by decide)

/-- Shifted-nondivisibility-first nonmembership form for `11n+6`. -/
theorem not_dvd_add_five_by_11_iff_not_exists_11n_plus_6 (m : ℕ) :
    ¬ (11 ∣ m + 5) ↔ ¬ ∃ n, m = 11 * n + 6 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 11) (r := 6) (c := 5)
    (m := m) (by decide) (by decide)

/-- Shifted-nondivisibility-first nonmembership form for `121n+116`. -/
theorem not_dvd_add_five_by_121_iff_not_exists_121n_plus_116 (m : ℕ) :
    ¬ (121 ∣ m + 5) ↔ ¬ ∃ n, m = 121 * n + 116 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 121) (r := 116) (c := 5)
    (m := m) (by decide) (by decide)

/-- Shifted-nondivisibility-first nonmembership form for `1331n+1326`. -/
theorem not_dvd_add_five_by_1331_iff_not_exists_1331n_plus_1326 (m : ℕ) :
    ¬ (1331 ∣ m + 5) ↔ ¬ ∃ n, m = 1331 * n + 1326 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 1331) (r := 1326) (c := 5)
    (m := m) (by decide) (by decide)

/-- Shifted-nondivisibility-first nonmembership form for `14641n+14636`. -/
theorem not_dvd_add_five_by_14641_iff_not_exists_14641n_plus_14636 (m : ℕ) :
    ¬ (14641 ∣ m + 5) ↔ ¬ ∃ n, m = 14641 * n + 14636 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 14641) (r := 14636) (c := 5)
    (m := m) (by decide) (by decide)

/-- Shifted-nondivisibility-first nonmembership form for `161051n+161046`. -/
theorem not_dvd_add_five_by_161051_iff_not_exists_161051n_plus_161046
    (m : ℕ) :
    ¬ (161051 ∣ m + 5) ↔ ¬ ∃ n, m = 161051 * n + 161046 := by
  exact not_dvd_add_iff_not_exists_mul_add (q := 161051) (r := 161046) (c := 5)
    (m := m) (by decide) (by decide)

/-- Concrete mod-5 power shifted-nondivisibility-first nonmembership facts. -/
theorem concrete_mod5_power_not_dvd_add_one_iff_short_nonmembership_facts :
    (∀ m, ¬ (5 ∣ m + 1) ↔ ¬ ∃ n, m = 5 * n + 4) ∧
      (∀ m, ¬ (25 ∣ m + 1) ↔ ¬ ∃ n, m = 25 * n + 24) ∧
      (∀ m, ¬ (125 ∣ m + 1) ↔ ¬ ∃ n, m = 125 * n + 124) ∧
      (∀ m, ¬ (625 ∣ m + 1) ↔ ¬ ∃ n, m = 625 * n + 624) ∧
      (∀ m, ¬ (3125 ∣ m + 1) ↔ ¬ ∃ n, m = 3125 * n + 3124) := by
  exact ⟨not_dvd_add_one_by_5_iff_not_exists_5n_plus_4,
    not_dvd_add_one_by_25_iff_not_exists_25n_plus_24,
    not_dvd_add_one_by_125_iff_not_exists_125n_plus_124,
    not_dvd_add_one_by_625_iff_not_exists_625n_plus_624,
    not_dvd_add_one_by_3125_iff_not_exists_3125n_plus_3124⟩

/-- Concrete mod-7 power shifted-nondivisibility-first nonmembership facts. -/
theorem concrete_mod7_power_not_dvd_add_two_iff_short_nonmembership_facts :
    (∀ m, ¬ (7 ∣ m + 2) ↔ ¬ ∃ n, m = 7 * n + 5) ∧
      (∀ m, ¬ (49 ∣ m + 2) ↔ ¬ ∃ n, m = 49 * n + 47) ∧
      (∀ m, ¬ (343 ∣ m + 2) ↔ ¬ ∃ n, m = 343 * n + 341) ∧
      (∀ m, ¬ (2401 ∣ m + 2) ↔ ¬ ∃ n, m = 2401 * n + 2399) ∧
      (∀ m, ¬ (16807 ∣ m + 2) ↔ ¬ ∃ n, m = 16807 * n + 16805) := by
  exact ⟨not_dvd_add_two_by_7_iff_not_exists_7n_plus_5,
    not_dvd_add_two_by_49_iff_not_exists_49n_plus_47,
    not_dvd_add_two_by_343_iff_not_exists_343n_plus_341,
    not_dvd_add_two_by_2401_iff_not_exists_2401n_plus_2399,
    not_dvd_add_two_by_16807_iff_not_exists_16807n_plus_16805⟩

/-- Concrete mod-11 power shifted-nondivisibility-first nonmembership facts. -/
theorem concrete_mod11_power_not_dvd_add_five_iff_short_nonmembership_facts :
    (∀ m, ¬ (11 ∣ m + 5) ↔ ¬ ∃ n, m = 11 * n + 6) ∧
      (∀ m, ¬ (121 ∣ m + 5) ↔ ¬ ∃ n, m = 121 * n + 116) ∧
      (∀ m, ¬ (1331 ∣ m + 5) ↔ ¬ ∃ n, m = 1331 * n + 1326) ∧
      (∀ m, ¬ (14641 ∣ m + 5) ↔ ¬ ∃ n, m = 14641 * n + 14636) ∧
      (∀ m, ¬ (161051 ∣ m + 5) ↔ ¬ ∃ n, m = 161051 * n + 161046) := by
  exact ⟨not_dvd_add_five_by_11_iff_not_exists_11n_plus_6,
    not_dvd_add_five_by_121_iff_not_exists_121n_plus_116,
    not_dvd_add_five_by_1331_iff_not_exists_1331n_plus_1326,
    not_dvd_add_five_by_14641_iff_not_exists_14641n_plus_14636,
    not_dvd_add_five_by_161051_iff_not_exists_161051n_plus_161046⟩

/-- Generic `Nat.ModEq` bridge for reduced arithmetic progressions. -/
theorem modEq_iff_exists_mul_add_of_lt {q r m : ℕ} (hr : r < q) :
    m ≡ r [MOD q] ↔ ∃ n, m = q * n + r := by
  rw [modEq_iff_mod_eq_of_lt (m := m) (q := q) (r := r) hr]
  exact (exists_mul_add_iff_mod_eq (q := q) (r := r) (m := m) hr).symm

/-- Generic progression-first `Nat.ModEq` bridge for reduced residues. -/
theorem exists_mul_add_iff_modEq_of_lt {q r m : ℕ} (hr : r < q) :
    (∃ n, m = q * n + r) ↔ m ≡ r [MOD q] :=
  (modEq_iff_exists_mul_add_of_lt (m := m) hr).symm

/-- Negated generic `Nat.ModEq` bridge for reduced arithmetic progressions. -/
theorem not_modEq_iff_not_exists_mul_add_of_lt {q r m : ℕ} (hr : r < q) :
    (¬ (m ≡ r [MOD q])) ↔ ¬ ∃ n, m = q * n + r :=
  not_congr (modEq_iff_exists_mul_add_of_lt (m := m) hr)

/-- Negated progression-first `Nat.ModEq` bridge for reduced residues. -/
theorem not_exists_mul_add_iff_not_modEq_of_lt {q r m : ℕ} (hr : r < q) :
    (¬ ∃ n, m = q * n + r) ↔ ¬ (m ≡ r [MOD q]) :=
  (not_modEq_iff_not_exists_mul_add_of_lt (m := m) hr).symm

/-- Concrete `Nat.ModEq` membership form for `5n+4`. -/
theorem modEq_four_mod5_iff_exists_5n_plus_4 (m : ℕ) :
    m ≡ 4 [MOD 5] ↔ ∃ n, m = 5 * n + 4 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 5) (r := 4) (m := m) (by decide)

/-- Concrete `Nat.ModEq` membership form for `25n+24`. -/
theorem modEq_twentyfour_mod25_iff_exists_25n_plus_24 (m : ℕ) :
    m ≡ 24 [MOD 25] ↔ ∃ n, m = 25 * n + 24 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 25) (r := 24) (m := m) (by decide)

/-- Concrete `Nat.ModEq` membership form for `125n+124`. -/
theorem modEq_onetwentyfour_mod125_iff_exists_125n_plus_124 (m : ℕ) :
    m ≡ 124 [MOD 125] ↔ ∃ n, m = 125 * n + 124 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 125) (r := 124) (m := m) (by decide)

/-- Concrete `Nat.ModEq` membership form for `625n+624`. -/
theorem modEq_sixtwentyfour_mod625_iff_exists_625n_plus_624 (m : ℕ) :
    m ≡ 624 [MOD 625] ↔ ∃ n, m = 625 * n + 624 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 625) (r := 624) (m := m) (by decide)

/-- Concrete `Nat.ModEq` membership form for `3125n+3124`. -/
theorem modEq_thirtyonetwentyfour_mod3125_iff_exists_3125n_plus_3124 (m : ℕ) :
    m ≡ 3124 [MOD 3125] ↔ ∃ n, m = 3125 * n + 3124 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 3125) (r := 3124) (m := m) (by decide)

/-- Concrete `Nat.ModEq` membership form for `7n+5`. -/
theorem modEq_five_mod7_iff_exists_7n_plus_5 (m : ℕ) :
    m ≡ 5 [MOD 7] ↔ ∃ n, m = 7 * n + 5 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 7) (r := 5) (m := m) (by decide)

/-- Concrete `Nat.ModEq` membership form for `49n+47`. -/
theorem modEq_fortyseven_mod49_iff_exists_49n_plus_47 (m : ℕ) :
    m ≡ 47 [MOD 49] ↔ ∃ n, m = 49 * n + 47 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 49) (r := 47) (m := m) (by decide)

/-- Concrete `Nat.ModEq` membership form for `343n+341`. -/
theorem modEq_threefourtyone_mod343_iff_exists_343n_plus_341 (m : ℕ) :
    m ≡ 341 [MOD 343] ↔ ∃ n, m = 343 * n + 341 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 343) (r := 341) (m := m) (by decide)

/-- Concrete `Nat.ModEq` membership form for `2401n+2399`. -/
theorem modEq_twentythreeninetynine_mod2401_iff_exists_2401n_plus_2399 (m : ℕ) :
    m ≡ 2399 [MOD 2401] ↔ ∃ n, m = 2401 * n + 2399 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 2401) (r := 2399) (m := m) (by decide)

/-- Concrete `Nat.ModEq` membership form for `16807n+16805`. -/
theorem modEq_sixteeneightofive_mod16807_iff_exists_16807n_plus_16805
    (m : ℕ) :
    m ≡ 16805 [MOD 16807] ↔ ∃ n, m = 16807 * n + 16805 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 16807) (r := 16805) (m := m) (by decide)

/-- Concrete `Nat.ModEq` membership form for `11n+6`. -/
theorem modEq_six_mod11_iff_exists_11n_plus_6 (m : ℕ) :
    m ≡ 6 [MOD 11] ↔ ∃ n, m = 11 * n + 6 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 11) (r := 6) (m := m) (by decide)

/-- Concrete `Nat.ModEq` membership form for `121n+116`. -/
theorem modEq_onesixteen_mod121_iff_exists_121n_plus_116 (m : ℕ) :
    m ≡ 116 [MOD 121] ↔ ∃ n, m = 121 * n + 116 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 121) (r := 116) (m := m) (by decide)

/-- Concrete `Nat.ModEq` membership form for `1331n+1326`. -/
theorem modEq_thirteentwentysix_mod1331_iff_exists_1331n_plus_1326 (m : ℕ) :
    m ≡ 1326 [MOD 1331] ↔ ∃ n, m = 1331 * n + 1326 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 1331) (r := 1326) (m := m) (by decide)

/-- Concrete `Nat.ModEq` membership form for `14641n+14636`. -/
theorem modEq_fourteensixthirtysix_mod14641_iff_exists_14641n_plus_14636
    (m : ℕ) :
    m ≡ 14636 [MOD 14641] ↔ ∃ n, m = 14641 * n + 14636 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 14641) (r := 14636) (m := m) (by decide)

/-- Concrete `Nat.ModEq` membership form for `161051n+161046`. -/
theorem modEq_onesixtyonezero46_mod161051_iff_exists_161051n_plus_161046
    (m : ℕ) :
    m ≡ 161046 [MOD 161051] ↔ ∃ n, m = 161051 * n + 161046 := by
  exact modEq_iff_exists_mul_add_of_lt (q := 161051) (r := 161046) (m := m) (by decide)

/-- Concrete mod-5 power `Nat.ModEq` membership facts. -/
theorem concrete_mod5_power_modEq_iff_short_membership_facts :
    (∀ m, m ≡ 4 [MOD 5] ↔ ∃ n, m = 5 * n + 4) ∧
      (∀ m, m ≡ 24 [MOD 25] ↔ ∃ n, m = 25 * n + 24) ∧
      (∀ m, m ≡ 124 [MOD 125] ↔ ∃ n, m = 125 * n + 124) ∧
      (∀ m, m ≡ 624 [MOD 625] ↔ ∃ n, m = 625 * n + 624) ∧
      (∀ m, m ≡ 3124 [MOD 3125] ↔ ∃ n, m = 3125 * n + 3124) := by
  exact ⟨modEq_four_mod5_iff_exists_5n_plus_4,
    modEq_twentyfour_mod25_iff_exists_25n_plus_24,
    modEq_onetwentyfour_mod125_iff_exists_125n_plus_124,
    modEq_sixtwentyfour_mod625_iff_exists_625n_plus_624,
    modEq_thirtyonetwentyfour_mod3125_iff_exists_3125n_plus_3124⟩

/-- Concrete mod-7 power `Nat.ModEq` membership facts. -/
theorem concrete_mod7_power_modEq_iff_short_membership_facts :
    (∀ m, m ≡ 5 [MOD 7] ↔ ∃ n, m = 7 * n + 5) ∧
      (∀ m, m ≡ 47 [MOD 49] ↔ ∃ n, m = 49 * n + 47) ∧
      (∀ m, m ≡ 341 [MOD 343] ↔ ∃ n, m = 343 * n + 341) ∧
      (∀ m, m ≡ 2399 [MOD 2401] ↔ ∃ n, m = 2401 * n + 2399) ∧
      (∀ m, m ≡ 16805 [MOD 16807] ↔ ∃ n, m = 16807 * n + 16805) := by
  exact ⟨modEq_five_mod7_iff_exists_7n_plus_5,
    modEq_fortyseven_mod49_iff_exists_49n_plus_47,
    modEq_threefourtyone_mod343_iff_exists_343n_plus_341,
    modEq_twentythreeninetynine_mod2401_iff_exists_2401n_plus_2399,
    modEq_sixteeneightofive_mod16807_iff_exists_16807n_plus_16805⟩

/-- Concrete mod-11 power `Nat.ModEq` membership facts. -/
theorem concrete_mod11_power_modEq_iff_short_membership_facts :
    (∀ m, m ≡ 6 [MOD 11] ↔ ∃ n, m = 11 * n + 6) ∧
      (∀ m, m ≡ 116 [MOD 121] ↔ ∃ n, m = 121 * n + 116) ∧
      (∀ m, m ≡ 1326 [MOD 1331] ↔ ∃ n, m = 1331 * n + 1326) ∧
      (∀ m, m ≡ 14636 [MOD 14641] ↔ ∃ n, m = 14641 * n + 14636) ∧
      (∀ m, m ≡ 161046 [MOD 161051] ↔ ∃ n, m = 161051 * n + 161046) := by
  exact ⟨modEq_six_mod11_iff_exists_11n_plus_6,
    modEq_onesixteen_mod121_iff_exists_121n_plus_116,
    modEq_thirteentwentysix_mod1331_iff_exists_1331n_plus_1326,
    modEq_fourteensixthirtysix_mod14641_iff_exists_14641n_plus_14636,
    modEq_onesixtyonezero46_mod161051_iff_exists_161051n_plus_161046⟩

/-- Concrete progression-first `Nat.ModEq` form for `5n+4`. -/
theorem exists_5n_plus_4_iff_modEq_four_mod5 (m : ℕ) :
    (∃ n, m = 5 * n + 4) ↔ m ≡ 4 [MOD 5] := by
  exact (modEq_four_mod5_iff_exists_5n_plus_4 m).symm

/-- Concrete progression-first `Nat.ModEq` form for `25n+24`. -/
theorem exists_25n_plus_24_iff_modEq_twentyfour_mod25 (m : ℕ) :
    (∃ n, m = 25 * n + 24) ↔ m ≡ 24 [MOD 25] := by
  exact (modEq_twentyfour_mod25_iff_exists_25n_plus_24 m).symm

/-- Concrete progression-first `Nat.ModEq` form for `125n+124`. -/
theorem exists_125n_plus_124_iff_modEq_onetwentyfour_mod125 (m : ℕ) :
    (∃ n, m = 125 * n + 124) ↔ m ≡ 124 [MOD 125] := by
  exact (modEq_onetwentyfour_mod125_iff_exists_125n_plus_124 m).symm

/-- Concrete progression-first `Nat.ModEq` form for `625n+624`. -/
theorem exists_625n_plus_624_iff_modEq_sixtwentyfour_mod625 (m : ℕ) :
    (∃ n, m = 625 * n + 624) ↔ m ≡ 624 [MOD 625] := by
  exact (modEq_sixtwentyfour_mod625_iff_exists_625n_plus_624 m).symm

/-- Concrete progression-first `Nat.ModEq` form for `3125n+3124`. -/
theorem exists_3125n_plus_3124_iff_modEq_thirtyonetwentyfour_mod3125 (m : ℕ) :
    (∃ n, m = 3125 * n + 3124) ↔ m ≡ 3124 [MOD 3125] := by
  exact (modEq_thirtyonetwentyfour_mod3125_iff_exists_3125n_plus_3124 m).symm

/-- Concrete progression-first `Nat.ModEq` form for `7n+5`. -/
theorem exists_7n_plus_5_iff_modEq_five_mod7 (m : ℕ) :
    (∃ n, m = 7 * n + 5) ↔ m ≡ 5 [MOD 7] := by
  exact (modEq_five_mod7_iff_exists_7n_plus_5 m).symm

/-- Concrete progression-first `Nat.ModEq` form for `49n+47`. -/
theorem exists_49n_plus_47_iff_modEq_fortyseven_mod49 (m : ℕ) :
    (∃ n, m = 49 * n + 47) ↔ m ≡ 47 [MOD 49] := by
  exact (modEq_fortyseven_mod49_iff_exists_49n_plus_47 m).symm

/-- Concrete progression-first `Nat.ModEq` form for `343n+341`. -/
theorem exists_343n_plus_341_iff_modEq_threefourtyone_mod343 (m : ℕ) :
    (∃ n, m = 343 * n + 341) ↔ m ≡ 341 [MOD 343] := by
  exact (modEq_threefourtyone_mod343_iff_exists_343n_plus_341 m).symm

/-- Concrete progression-first `Nat.ModEq` form for `2401n+2399`. -/
theorem exists_2401n_plus_2399_iff_modEq_twentythreeninetynine_mod2401 (m : ℕ) :
    (∃ n, m = 2401 * n + 2399) ↔ m ≡ 2399 [MOD 2401] := by
  exact (modEq_twentythreeninetynine_mod2401_iff_exists_2401n_plus_2399 m).symm

/-- Concrete progression-first `Nat.ModEq` form for `16807n+16805`. -/
theorem exists_16807n_plus_16805_iff_modEq_sixteeneightofive_mod16807
    (m : ℕ) :
    (∃ n, m = 16807 * n + 16805) ↔ m ≡ 16805 [MOD 16807] := by
  exact (modEq_sixteeneightofive_mod16807_iff_exists_16807n_plus_16805 m).symm

/-- Concrete progression-first `Nat.ModEq` form for `11n+6`. -/
theorem exists_11n_plus_6_iff_modEq_six_mod11 (m : ℕ) :
    (∃ n, m = 11 * n + 6) ↔ m ≡ 6 [MOD 11] := by
  exact (modEq_six_mod11_iff_exists_11n_plus_6 m).symm

/-- Concrete progression-first `Nat.ModEq` form for `121n+116`. -/
theorem exists_121n_plus_116_iff_modEq_onesixteen_mod121 (m : ℕ) :
    (∃ n, m = 121 * n + 116) ↔ m ≡ 116 [MOD 121] := by
  exact (modEq_onesixteen_mod121_iff_exists_121n_plus_116 m).symm

/-- Concrete progression-first `Nat.ModEq` form for `1331n+1326`. -/
theorem exists_1331n_plus_1326_iff_modEq_thirteentwentysix_mod1331 (m : ℕ) :
    (∃ n, m = 1331 * n + 1326) ↔ m ≡ 1326 [MOD 1331] := by
  exact (modEq_thirteentwentysix_mod1331_iff_exists_1331n_plus_1326 m).symm

/-- Concrete progression-first `Nat.ModEq` form for `14641n+14636`. -/
theorem exists_14641n_plus_14636_iff_modEq_fourteensixthirtysix_mod14641
    (m : ℕ) :
    (∃ n, m = 14641 * n + 14636) ↔ m ≡ 14636 [MOD 14641] := by
  exact (modEq_fourteensixthirtysix_mod14641_iff_exists_14641n_plus_14636 m).symm

/-- Concrete progression-first `Nat.ModEq` form for `161051n+161046`. -/
theorem exists_161051n_plus_161046_iff_modEq_onesixtyonezero46_mod161051
    (m : ℕ) :
    (∃ n, m = 161051 * n + 161046) ↔ m ≡ 161046 [MOD 161051] := by
  exact (modEq_onesixtyonezero46_mod161051_iff_exists_161051n_plus_161046 m).symm

/-- Concrete mod-5 power progression-first `Nat.ModEq` facts. -/
theorem concrete_mod5_power_short_membership_iff_modEq_facts :
    (∀ m, (∃ n, m = 5 * n + 4) ↔ m ≡ 4 [MOD 5]) ∧
      (∀ m, (∃ n, m = 25 * n + 24) ↔ m ≡ 24 [MOD 25]) ∧
      (∀ m, (∃ n, m = 125 * n + 124) ↔ m ≡ 124 [MOD 125]) ∧
      (∀ m, (∃ n, m = 625 * n + 624) ↔ m ≡ 624 [MOD 625]) ∧
      (∀ m, (∃ n, m = 3125 * n + 3124) ↔ m ≡ 3124 [MOD 3125]) := by
  exact ⟨exists_5n_plus_4_iff_modEq_four_mod5,
    exists_25n_plus_24_iff_modEq_twentyfour_mod25,
    exists_125n_plus_124_iff_modEq_onetwentyfour_mod125,
    exists_625n_plus_624_iff_modEq_sixtwentyfour_mod625,
    exists_3125n_plus_3124_iff_modEq_thirtyonetwentyfour_mod3125⟩

/-- Concrete mod-7 power progression-first `Nat.ModEq` facts. -/
theorem concrete_mod7_power_short_membership_iff_modEq_facts :
    (∀ m, (∃ n, m = 7 * n + 5) ↔ m ≡ 5 [MOD 7]) ∧
      (∀ m, (∃ n, m = 49 * n + 47) ↔ m ≡ 47 [MOD 49]) ∧
      (∀ m, (∃ n, m = 343 * n + 341) ↔ m ≡ 341 [MOD 343]) ∧
      (∀ m, (∃ n, m = 2401 * n + 2399) ↔ m ≡ 2399 [MOD 2401]) ∧
      (∀ m, (∃ n, m = 16807 * n + 16805) ↔ m ≡ 16805 [MOD 16807]) := by
  exact ⟨exists_7n_plus_5_iff_modEq_five_mod7,
    exists_49n_plus_47_iff_modEq_fortyseven_mod49,
    exists_343n_plus_341_iff_modEq_threefourtyone_mod343,
    exists_2401n_plus_2399_iff_modEq_twentythreeninetynine_mod2401,
    exists_16807n_plus_16805_iff_modEq_sixteeneightofive_mod16807⟩

/-- Concrete mod-11 power progression-first `Nat.ModEq` facts. -/
theorem concrete_mod11_power_short_membership_iff_modEq_facts :
    (∀ m, (∃ n, m = 11 * n + 6) ↔ m ≡ 6 [MOD 11]) ∧
      (∀ m, (∃ n, m = 121 * n + 116) ↔ m ≡ 116 [MOD 121]) ∧
      (∀ m, (∃ n, m = 1331 * n + 1326) ↔ m ≡ 1326 [MOD 1331]) ∧
      (∀ m, (∃ n, m = 14641 * n + 14636) ↔ m ≡ 14636 [MOD 14641]) ∧
      (∀ m, (∃ n, m = 161051 * n + 161046) ↔ m ≡ 161046 [MOD 161051]) := by
  exact ⟨exists_11n_plus_6_iff_modEq_six_mod11,
    exists_121n_plus_116_iff_modEq_onesixteen_mod121,
    exists_1331n_plus_1326_iff_modEq_thirteentwentysix_mod1331,
    exists_14641n_plus_14636_iff_modEq_fourteensixthirtysix_mod14641,
    exists_161051n_plus_161046_iff_modEq_onesixtyonezero46_mod161051⟩

/-- Concrete negated progression-first `Nat.ModEq` form for `5n+4`. -/
theorem not_exists_5n_plus_4_iff_not_modEq_four_mod5 (m : ℕ) :
    (¬ ∃ n, m = 5 * n + 4) ↔ ¬ (m ≡ 4 [MOD 5]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 5) (r := 4) (m := m) (by decide)

/-- Concrete negated progression-first `Nat.ModEq` form for `25n+24`. -/
theorem not_exists_25n_plus_24_iff_not_modEq_twentyfour_mod25 (m : ℕ) :
    (¬ ∃ n, m = 25 * n + 24) ↔ ¬ (m ≡ 24 [MOD 25]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 25) (r := 24) (m := m) (by decide)

/-- Concrete negated progression-first `Nat.ModEq` form for `125n+124`. -/
theorem not_exists_125n_plus_124_iff_not_modEq_onetwentyfour_mod125 (m : ℕ) :
    (¬ ∃ n, m = 125 * n + 124) ↔ ¬ (m ≡ 124 [MOD 125]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 125) (r := 124) (m := m) (by decide)

/-- Concrete negated progression-first `Nat.ModEq` form for `625n+624`. -/
theorem not_exists_625n_plus_624_iff_not_modEq_sixtwentyfour_mod625 (m : ℕ) :
    (¬ ∃ n, m = 625 * n + 624) ↔ ¬ (m ≡ 624 [MOD 625]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 625) (r := 624) (m := m) (by decide)

/-- Concrete negated progression-first `Nat.ModEq` form for `3125n+3124`. -/
theorem not_exists_3125n_plus_3124_iff_not_modEq_thirtyonetwentyfour_mod3125
    (m : ℕ) :
    (¬ ∃ n, m = 3125 * n + 3124) ↔ ¬ (m ≡ 3124 [MOD 3125]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 3125) (r := 3124) (m := m)
    (by decide)

/-- Concrete negated progression-first `Nat.ModEq` form for `7n+5`. -/
theorem not_exists_7n_plus_5_iff_not_modEq_five_mod7 (m : ℕ) :
    (¬ ∃ n, m = 7 * n + 5) ↔ ¬ (m ≡ 5 [MOD 7]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 7) (r := 5) (m := m) (by decide)

/-- Concrete negated progression-first `Nat.ModEq` form for `49n+47`. -/
theorem not_exists_49n_plus_47_iff_not_modEq_fortyseven_mod49 (m : ℕ) :
    (¬ ∃ n, m = 49 * n + 47) ↔ ¬ (m ≡ 47 [MOD 49]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 49) (r := 47) (m := m) (by decide)

/-- Concrete negated progression-first `Nat.ModEq` form for `343n+341`. -/
theorem not_exists_343n_plus_341_iff_not_modEq_threefourtyone_mod343 (m : ℕ) :
    (¬ ∃ n, m = 343 * n + 341) ↔ ¬ (m ≡ 341 [MOD 343]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 343) (r := 341) (m := m)
    (by decide)

/-- Concrete negated progression-first `Nat.ModEq` form for `2401n+2399`. -/
theorem not_exists_2401n_plus_2399_iff_not_modEq_twentythreeninetynine_mod2401
    (m : ℕ) :
    (¬ ∃ n, m = 2401 * n + 2399) ↔ ¬ (m ≡ 2399 [MOD 2401]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 2401) (r := 2399) (m := m)
    (by decide)

/-- Concrete negated progression-first `Nat.ModEq` form for `16807n+16805`. -/
theorem not_exists_16807n_plus_16805_iff_not_modEq_sixteeneightofive_mod16807
    (m : ℕ) :
    (¬ ∃ n, m = 16807 * n + 16805) ↔ ¬ (m ≡ 16805 [MOD 16807]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 16807) (r := 16805) (m := m)
    (by decide)

/-- Concrete negated progression-first `Nat.ModEq` form for `11n+6`. -/
theorem not_exists_11n_plus_6_iff_not_modEq_six_mod11 (m : ℕ) :
    (¬ ∃ n, m = 11 * n + 6) ↔ ¬ (m ≡ 6 [MOD 11]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 11) (r := 6) (m := m) (by decide)

/-- Concrete negated progression-first `Nat.ModEq` form for `121n+116`. -/
theorem not_exists_121n_plus_116_iff_not_modEq_onesixteen_mod121 (m : ℕ) :
    (¬ ∃ n, m = 121 * n + 116) ↔ ¬ (m ≡ 116 [MOD 121]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 121) (r := 116) (m := m)
    (by decide)

/-- Concrete negated progression-first `Nat.ModEq` form for `1331n+1326`. -/
theorem not_exists_1331n_plus_1326_iff_not_modEq_thirteentwentysix_mod1331
    (m : ℕ) :
    (¬ ∃ n, m = 1331 * n + 1326) ↔ ¬ (m ≡ 1326 [MOD 1331]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 1331) (r := 1326) (m := m)
    (by decide)

/-- Concrete negated progression-first `Nat.ModEq` form for `14641n+14636`. -/
theorem not_exists_14641n_plus_14636_iff_not_modEq_fourteensixthirtysix_mod14641
    (m : ℕ) :
    (¬ ∃ n, m = 14641 * n + 14636) ↔ ¬ (m ≡ 14636 [MOD 14641]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 14641) (r := 14636) (m := m)
    (by decide)

/-- Concrete negated progression-first `Nat.ModEq` form for `161051n+161046`. -/
theorem not_exists_161051n_plus_161046_iff_not_modEq_onesixtyonezero46_mod161051
    (m : ℕ) :
    (¬ ∃ n, m = 161051 * n + 161046) ↔ ¬ (m ≡ 161046 [MOD 161051]) :=
  not_exists_mul_add_iff_not_modEq_of_lt (q := 161051) (r := 161046) (m := m)
    (by decide)

/-- Concrete mod-5 power negated progression-first `Nat.ModEq` facts. -/
theorem concrete_mod5_power_short_nonmembership_iff_not_modEq_facts :
    (∀ m, (¬ ∃ n, m = 5 * n + 4) ↔ ¬ (m ≡ 4 [MOD 5])) ∧
      (∀ m, (¬ ∃ n, m = 25 * n + 24) ↔ ¬ (m ≡ 24 [MOD 25])) ∧
      (∀ m, (¬ ∃ n, m = 125 * n + 124) ↔ ¬ (m ≡ 124 [MOD 125])) ∧
      (∀ m, (¬ ∃ n, m = 625 * n + 624) ↔ ¬ (m ≡ 624 [MOD 625])) ∧
      (∀ m, (¬ ∃ n, m = 3125 * n + 3124) ↔ ¬ (m ≡ 3124 [MOD 3125])) := by
  exact ⟨not_exists_5n_plus_4_iff_not_modEq_four_mod5,
    not_exists_25n_plus_24_iff_not_modEq_twentyfour_mod25,
    not_exists_125n_plus_124_iff_not_modEq_onetwentyfour_mod125,
    not_exists_625n_plus_624_iff_not_modEq_sixtwentyfour_mod625,
    not_exists_3125n_plus_3124_iff_not_modEq_thirtyonetwentyfour_mod3125⟩

/-- Concrete mod-7 power negated progression-first `Nat.ModEq` facts. -/
theorem concrete_mod7_power_short_nonmembership_iff_not_modEq_facts :
    (∀ m, (¬ ∃ n, m = 7 * n + 5) ↔ ¬ (m ≡ 5 [MOD 7])) ∧
      (∀ m, (¬ ∃ n, m = 49 * n + 47) ↔ ¬ (m ≡ 47 [MOD 49])) ∧
      (∀ m, (¬ ∃ n, m = 343 * n + 341) ↔ ¬ (m ≡ 341 [MOD 343])) ∧
      (∀ m, (¬ ∃ n, m = 2401 * n + 2399) ↔ ¬ (m ≡ 2399 [MOD 2401])) ∧
      (∀ m, (¬ ∃ n, m = 16807 * n + 16805) ↔ ¬ (m ≡ 16805 [MOD 16807])) := by
  exact ⟨not_exists_7n_plus_5_iff_not_modEq_five_mod7,
    not_exists_49n_plus_47_iff_not_modEq_fortyseven_mod49,
    not_exists_343n_plus_341_iff_not_modEq_threefourtyone_mod343,
    not_exists_2401n_plus_2399_iff_not_modEq_twentythreeninetynine_mod2401,
    not_exists_16807n_plus_16805_iff_not_modEq_sixteeneightofive_mod16807⟩

/-- Concrete mod-11 power negated progression-first `Nat.ModEq` facts. -/
theorem concrete_mod11_power_short_nonmembership_iff_not_modEq_facts :
    (∀ m, (¬ ∃ n, m = 11 * n + 6) ↔ ¬ (m ≡ 6 [MOD 11])) ∧
      (∀ m, (¬ ∃ n, m = 121 * n + 116) ↔ ¬ (m ≡ 116 [MOD 121])) ∧
      (∀ m, (¬ ∃ n, m = 1331 * n + 1326) ↔ ¬ (m ≡ 1326 [MOD 1331])) ∧
      (∀ m, (¬ ∃ n, m = 14641 * n + 14636) ↔ ¬ (m ≡ 14636 [MOD 14641])) ∧
      (∀ m, (¬ ∃ n, m = 161051 * n + 161046) ↔ ¬ (m ≡ 161046 [MOD 161051])) := by
  exact ⟨not_exists_11n_plus_6_iff_not_modEq_six_mod11,
    not_exists_121n_plus_116_iff_not_modEq_onesixteen_mod121,
    not_exists_1331n_plus_1326_iff_not_modEq_thirteentwentysix_mod1331,
    not_exists_14641n_plus_14636_iff_not_modEq_fourteensixthirtysix_mod14641,
    not_exists_161051n_plus_161046_iff_not_modEq_onesixtyonezero46_mod161051⟩

/-- Concrete negated `Nat.ModEq`-first nonmembership form for `5n+4`. -/
theorem not_modEq_four_mod5_iff_not_exists_5n_plus_4 (m : ℕ) :
    ¬ (m ≡ 4 [MOD 5]) ↔ ¬ ∃ n, m = 5 * n + 4 := by
  exact (not_exists_5n_plus_4_iff_not_modEq_four_mod5 m).symm

/-- Concrete negated `Nat.ModEq`-first nonmembership form for `25n+24`. -/
theorem not_modEq_twentyfour_mod25_iff_not_exists_25n_plus_24 (m : ℕ) :
    ¬ (m ≡ 24 [MOD 25]) ↔ ¬ ∃ n, m = 25 * n + 24 := by
  exact (not_exists_25n_plus_24_iff_not_modEq_twentyfour_mod25 m).symm

/-- Concrete negated `Nat.ModEq`-first nonmembership form for `125n+124`. -/
theorem not_modEq_onetwentyfour_mod125_iff_not_exists_125n_plus_124 (m : ℕ) :
    ¬ (m ≡ 124 [MOD 125]) ↔ ¬ ∃ n, m = 125 * n + 124 := by
  exact (not_exists_125n_plus_124_iff_not_modEq_onetwentyfour_mod125 m).symm

/-- Concrete negated `Nat.ModEq`-first nonmembership form for `625n+624`. -/
theorem not_modEq_sixtwentyfour_mod625_iff_not_exists_625n_plus_624 (m : ℕ) :
    ¬ (m ≡ 624 [MOD 625]) ↔ ¬ ∃ n, m = 625 * n + 624 := by
  exact (not_exists_625n_plus_624_iff_not_modEq_sixtwentyfour_mod625 m).symm

/-- Concrete negated `Nat.ModEq`-first nonmembership form for `3125n+3124`. -/
theorem not_modEq_thirtyonetwentyfour_mod3125_iff_not_exists_3125n_plus_3124
    (m : ℕ) :
    ¬ (m ≡ 3124 [MOD 3125]) ↔ ¬ ∃ n, m = 3125 * n + 3124 := by
  exact (not_exists_3125n_plus_3124_iff_not_modEq_thirtyonetwentyfour_mod3125 m).symm

/-- Concrete negated `Nat.ModEq`-first nonmembership form for `7n+5`. -/
theorem not_modEq_five_mod7_iff_not_exists_7n_plus_5 (m : ℕ) :
    ¬ (m ≡ 5 [MOD 7]) ↔ ¬ ∃ n, m = 7 * n + 5 := by
  exact (not_exists_7n_plus_5_iff_not_modEq_five_mod7 m).symm

/-- Concrete negated `Nat.ModEq`-first nonmembership form for `49n+47`. -/
theorem not_modEq_fortyseven_mod49_iff_not_exists_49n_plus_47 (m : ℕ) :
    ¬ (m ≡ 47 [MOD 49]) ↔ ¬ ∃ n, m = 49 * n + 47 := by
  exact (not_exists_49n_plus_47_iff_not_modEq_fortyseven_mod49 m).symm

/-- Concrete negated `Nat.ModEq`-first nonmembership form for `343n+341`. -/
theorem not_modEq_threefourtyone_mod343_iff_not_exists_343n_plus_341 (m : ℕ) :
    ¬ (m ≡ 341 [MOD 343]) ↔ ¬ ∃ n, m = 343 * n + 341 := by
  exact (not_exists_343n_plus_341_iff_not_modEq_threefourtyone_mod343 m).symm

/-- Concrete negated `Nat.ModEq`-first nonmembership form for `2401n+2399`. -/
theorem not_modEq_twentythreeninetynine_mod2401_iff_not_exists_2401n_plus_2399
    (m : ℕ) :
    ¬ (m ≡ 2399 [MOD 2401]) ↔ ¬ ∃ n, m = 2401 * n + 2399 := by
  exact (not_exists_2401n_plus_2399_iff_not_modEq_twentythreeninetynine_mod2401 m).symm

/-- Concrete negated `Nat.ModEq`-first nonmembership form for `16807n+16805`. -/
theorem not_modEq_sixteeneightofive_mod16807_iff_not_exists_16807n_plus_16805
    (m : ℕ) :
    ¬ (m ≡ 16805 [MOD 16807]) ↔ ¬ ∃ n, m = 16807 * n + 16805 := by
  exact (not_exists_16807n_plus_16805_iff_not_modEq_sixteeneightofive_mod16807 m).symm

/-- Concrete negated `Nat.ModEq`-first nonmembership form for `11n+6`. -/
theorem not_modEq_six_mod11_iff_not_exists_11n_plus_6 (m : ℕ) :
    ¬ (m ≡ 6 [MOD 11]) ↔ ¬ ∃ n, m = 11 * n + 6 := by
  exact (not_exists_11n_plus_6_iff_not_modEq_six_mod11 m).symm

/-- Concrete negated `Nat.ModEq`-first nonmembership form for `121n+116`. -/
theorem not_modEq_onesixteen_mod121_iff_not_exists_121n_plus_116 (m : ℕ) :
    ¬ (m ≡ 116 [MOD 121]) ↔ ¬ ∃ n, m = 121 * n + 116 := by
  exact (not_exists_121n_plus_116_iff_not_modEq_onesixteen_mod121 m).symm

/-- Concrete negated `Nat.ModEq`-first nonmembership form for `1331n+1326`. -/
theorem not_modEq_thirteentwentysix_mod1331_iff_not_exists_1331n_plus_1326
    (m : ℕ) :
    ¬ (m ≡ 1326 [MOD 1331]) ↔ ¬ ∃ n, m = 1331 * n + 1326 := by
  exact (not_exists_1331n_plus_1326_iff_not_modEq_thirteentwentysix_mod1331 m).symm

/-- Concrete negated `Nat.ModEq`-first nonmembership form for `14641n+14636`. -/
theorem not_modEq_fourteensixthirtysix_mod14641_iff_not_exists_14641n_plus_14636
    (m : ℕ) :
    ¬ (m ≡ 14636 [MOD 14641]) ↔ ¬ ∃ n, m = 14641 * n + 14636 := by
  exact (not_exists_14641n_plus_14636_iff_not_modEq_fourteensixthirtysix_mod14641 m).symm

/-- Concrete negated `Nat.ModEq`-first nonmembership form for
`161051n+161046`. -/
theorem not_modEq_onesixtyonezero46_mod161051_iff_not_exists_161051n_plus_161046
    (m : ℕ) :
    ¬ (m ≡ 161046 [MOD 161051]) ↔ ¬ ∃ n, m = 161051 * n + 161046 := by
  exact (not_exists_161051n_plus_161046_iff_not_modEq_onesixtyonezero46_mod161051 m).symm

/-- Concrete mod-5 power negated `Nat.ModEq`-first nonmembership facts. -/
theorem concrete_mod5_power_not_modEq_iff_short_nonmembership_facts :
    (∀ m, ¬ (m ≡ 4 [MOD 5]) ↔ ¬ ∃ n, m = 5 * n + 4) ∧
      (∀ m, ¬ (m ≡ 24 [MOD 25]) ↔ ¬ ∃ n, m = 25 * n + 24) ∧
      (∀ m, ¬ (m ≡ 124 [MOD 125]) ↔ ¬ ∃ n, m = 125 * n + 124) ∧
      (∀ m, ¬ (m ≡ 624 [MOD 625]) ↔ ¬ ∃ n, m = 625 * n + 624) ∧
      (∀ m, ¬ (m ≡ 3124 [MOD 3125]) ↔ ¬ ∃ n, m = 3125 * n + 3124) := by
  exact ⟨not_modEq_four_mod5_iff_not_exists_5n_plus_4,
    not_modEq_twentyfour_mod25_iff_not_exists_25n_plus_24,
    not_modEq_onetwentyfour_mod125_iff_not_exists_125n_plus_124,
    not_modEq_sixtwentyfour_mod625_iff_not_exists_625n_plus_624,
    not_modEq_thirtyonetwentyfour_mod3125_iff_not_exists_3125n_plus_3124⟩

/-- Concrete mod-7 power negated `Nat.ModEq`-first nonmembership facts. -/
theorem concrete_mod7_power_not_modEq_iff_short_nonmembership_facts :
    (∀ m, ¬ (m ≡ 5 [MOD 7]) ↔ ¬ ∃ n, m = 7 * n + 5) ∧
      (∀ m, ¬ (m ≡ 47 [MOD 49]) ↔ ¬ ∃ n, m = 49 * n + 47) ∧
      (∀ m, ¬ (m ≡ 341 [MOD 343]) ↔ ¬ ∃ n, m = 343 * n + 341) ∧
      (∀ m, ¬ (m ≡ 2399 [MOD 2401]) ↔ ¬ ∃ n, m = 2401 * n + 2399) ∧
      (∀ m, ¬ (m ≡ 16805 [MOD 16807]) ↔ ¬ ∃ n, m = 16807 * n + 16805) := by
  exact ⟨not_modEq_five_mod7_iff_not_exists_7n_plus_5,
    not_modEq_fortyseven_mod49_iff_not_exists_49n_plus_47,
    not_modEq_threefourtyone_mod343_iff_not_exists_343n_plus_341,
    not_modEq_twentythreeninetynine_mod2401_iff_not_exists_2401n_plus_2399,
    not_modEq_sixteeneightofive_mod16807_iff_not_exists_16807n_plus_16805⟩

/-- Concrete mod-11 power negated `Nat.ModEq`-first nonmembership facts. -/
theorem concrete_mod11_power_not_modEq_iff_short_nonmembership_facts :
    (∀ m, ¬ (m ≡ 6 [MOD 11]) ↔ ¬ ∃ n, m = 11 * n + 6) ∧
      (∀ m, ¬ (m ≡ 116 [MOD 121]) ↔ ¬ ∃ n, m = 121 * n + 116) ∧
      (∀ m, ¬ (m ≡ 1326 [MOD 1331]) ↔ ¬ ∃ n, m = 1331 * n + 1326) ∧
      (∀ m, ¬ (m ≡ 14636 [MOD 14641]) ↔ ¬ ∃ n, m = 14641 * n + 14636) ∧
      (∀ m, ¬ (m ≡ 161046 [MOD 161051]) ↔ ¬ ∃ n, m = 161051 * n + 161046) := by
  exact ⟨not_modEq_six_mod11_iff_not_exists_11n_plus_6,
    not_modEq_onesixteen_mod121_iff_not_exists_121n_plus_116,
    not_modEq_thirteentwentysix_mod1331_iff_not_exists_1331n_plus_1326,
    not_modEq_fourteensixthirtysix_mod14641_iff_not_exists_14641n_plus_14636,
    not_modEq_onesixtyonezero46_mod161051_iff_not_exists_161051n_plus_161046⟩

/-- A direct `%` equality to a reduced residue is the same as `Nat.ModEq`. -/
theorem mod_eq_iff_modEq_of_lt {q r m : ℕ} (hr : r < q) :
    m % q = r ↔ m ≡ r [MOD q] :=
  (modEq_iff_mod_eq_of_lt (m := m) hr).symm

/-- Concrete `Nat.ModEq`/residue form for `4 mod 5`. -/
theorem modEq_four_mod5_iff_mod5_eq4 (m : ℕ) :
    m ≡ 4 [MOD 5] ↔ m % 5 = 4 := by
  exact modEq_iff_mod_eq_of_lt (q := 5) (r := 4) (m := m) (by decide)

/-- Concrete `Nat.ModEq`/residue form for `24 mod 25`. -/
theorem modEq_twentyfour_mod25_iff_mod25_eq24 (m : ℕ) :
    m ≡ 24 [MOD 25] ↔ m % 25 = 24 := by
  exact modEq_iff_mod_eq_of_lt (q := 25) (r := 24) (m := m) (by decide)

/-- Concrete `Nat.ModEq`/residue form for `124 mod 125`. -/
theorem modEq_onetwentyfour_mod125_iff_mod125_eq124 (m : ℕ) :
    m ≡ 124 [MOD 125] ↔ m % 125 = 124 := by
  exact modEq_iff_mod_eq_of_lt (q := 125) (r := 124) (m := m) (by decide)

/-- Concrete `Nat.ModEq`/residue form for `624 mod 625`. -/
theorem modEq_sixtwentyfour_mod625_iff_mod625_eq624 (m : ℕ) :
    m ≡ 624 [MOD 625] ↔ m % 625 = 624 := by
  exact modEq_iff_mod_eq_of_lt (q := 625) (r := 624) (m := m) (by decide)

/-- Concrete `Nat.ModEq`/residue form for `3124 mod 3125`. -/
theorem modEq_thirtyonetwentyfour_mod3125_iff_mod3125_eq3124 (m : ℕ) :
    m ≡ 3124 [MOD 3125] ↔ m % 3125 = 3124 := by
  exact modEq_iff_mod_eq_of_lt (q := 3125) (r := 3124) (m := m) (by decide)

/-- Concrete `Nat.ModEq`/residue form for `5 mod 7`. -/
theorem modEq_five_mod7_iff_mod7_eq5 (m : ℕ) :
    m ≡ 5 [MOD 7] ↔ m % 7 = 5 := by
  exact modEq_iff_mod_eq_of_lt (q := 7) (r := 5) (m := m) (by decide)

/-- Concrete `Nat.ModEq`/residue form for `47 mod 49`. -/
theorem modEq_fortyseven_mod49_iff_mod49_eq47 (m : ℕ) :
    m ≡ 47 [MOD 49] ↔ m % 49 = 47 := by
  exact modEq_iff_mod_eq_of_lt (q := 49) (r := 47) (m := m) (by decide)

/-- Concrete `Nat.ModEq`/residue form for `341 mod 343`. -/
theorem modEq_threefourtyone_mod343_iff_mod343_eq341 (m : ℕ) :
    m ≡ 341 [MOD 343] ↔ m % 343 = 341 := by
  exact modEq_iff_mod_eq_of_lt (q := 343) (r := 341) (m := m) (by decide)

/-- Concrete `Nat.ModEq`/residue form for `2399 mod 2401`. -/
theorem modEq_twentythreeninetynine_mod2401_iff_mod2401_eq2399 (m : ℕ) :
    m ≡ 2399 [MOD 2401] ↔ m % 2401 = 2399 := by
  exact modEq_iff_mod_eq_of_lt (q := 2401) (r := 2399) (m := m) (by decide)

/-- Concrete `Nat.ModEq`/residue form for `16805 mod 16807`. -/
theorem modEq_sixteeneightofive_mod16807_iff_mod16807_eq16805 (m : ℕ) :
    m ≡ 16805 [MOD 16807] ↔ m % 16807 = 16805 := by
  exact modEq_iff_mod_eq_of_lt (q := 16807) (r := 16805) (m := m) (by decide)

/-- Concrete `Nat.ModEq`/residue form for `6 mod 11`. -/
theorem modEq_six_mod11_iff_mod11_eq6 (m : ℕ) :
    m ≡ 6 [MOD 11] ↔ m % 11 = 6 := by
  exact modEq_iff_mod_eq_of_lt (q := 11) (r := 6) (m := m) (by decide)

/-- Concrete `Nat.ModEq`/residue form for `116 mod 121`. -/
theorem modEq_onesixteen_mod121_iff_mod121_eq116 (m : ℕ) :
    m ≡ 116 [MOD 121] ↔ m % 121 = 116 := by
  exact modEq_iff_mod_eq_of_lt (q := 121) (r := 116) (m := m) (by decide)

/-- Concrete `Nat.ModEq`/residue form for `1326 mod 1331`. -/
theorem modEq_thirteentwentysix_mod1331_iff_mod1331_eq1326 (m : ℕ) :
    m ≡ 1326 [MOD 1331] ↔ m % 1331 = 1326 := by
  exact modEq_iff_mod_eq_of_lt (q := 1331) (r := 1326) (m := m) (by decide)

/-- Concrete `Nat.ModEq`/residue form for `14636 mod 14641`. -/
theorem modEq_fourteensixthirtysix_mod14641_iff_mod14641_eq14636 (m : ℕ) :
    m ≡ 14636 [MOD 14641] ↔ m % 14641 = 14636 := by
  exact modEq_iff_mod_eq_of_lt (q := 14641) (r := 14636) (m := m) (by decide)

/-- Concrete `Nat.ModEq`/residue form for `161046 mod 161051`. -/
theorem modEq_onesixtyonezero46_mod161051_iff_mod161051_eq161046 (m : ℕ) :
    m ≡ 161046 [MOD 161051] ↔ m % 161051 = 161046 := by
  exact modEq_iff_mod_eq_of_lt (q := 161051) (r := 161046) (m := m) (by decide)

/-- Concrete mod-5 power `Nat.ModEq` iff direct residue facts. -/
theorem concrete_mod5_power_modEq_iff_residue_facts :
    (∀ m, m ≡ 4 [MOD 5] ↔ m % 5 = 4) ∧
      (∀ m, m ≡ 24 [MOD 25] ↔ m % 25 = 24) ∧
      (∀ m, m ≡ 124 [MOD 125] ↔ m % 125 = 124) ∧
      (∀ m, m ≡ 624 [MOD 625] ↔ m % 625 = 624) ∧
      (∀ m, m ≡ 3124 [MOD 3125] ↔ m % 3125 = 3124) := by
  exact ⟨modEq_four_mod5_iff_mod5_eq4,
    modEq_twentyfour_mod25_iff_mod25_eq24,
    modEq_onetwentyfour_mod125_iff_mod125_eq124,
    modEq_sixtwentyfour_mod625_iff_mod625_eq624,
    modEq_thirtyonetwentyfour_mod3125_iff_mod3125_eq3124⟩

/-- Concrete mod-7 power `Nat.ModEq` iff direct residue facts. -/
theorem concrete_mod7_power_modEq_iff_residue_facts :
    (∀ m, m ≡ 5 [MOD 7] ↔ m % 7 = 5) ∧
      (∀ m, m ≡ 47 [MOD 49] ↔ m % 49 = 47) ∧
      (∀ m, m ≡ 341 [MOD 343] ↔ m % 343 = 341) ∧
      (∀ m, m ≡ 2399 [MOD 2401] ↔ m % 2401 = 2399) ∧
      (∀ m, m ≡ 16805 [MOD 16807] ↔ m % 16807 = 16805) := by
  exact ⟨modEq_five_mod7_iff_mod7_eq5,
    modEq_fortyseven_mod49_iff_mod49_eq47,
    modEq_threefourtyone_mod343_iff_mod343_eq341,
    modEq_twentythreeninetynine_mod2401_iff_mod2401_eq2399,
    modEq_sixteeneightofive_mod16807_iff_mod16807_eq16805⟩

/-- Concrete mod-11 power `Nat.ModEq` iff direct residue facts. -/
theorem concrete_mod11_power_modEq_iff_residue_facts :
    (∀ m, m ≡ 6 [MOD 11] ↔ m % 11 = 6) ∧
      (∀ m, m ≡ 116 [MOD 121] ↔ m % 121 = 116) ∧
      (∀ m, m ≡ 1326 [MOD 1331] ↔ m % 1331 = 1326) ∧
      (∀ m, m ≡ 14636 [MOD 14641] ↔ m % 14641 = 14636) ∧
      (∀ m, m ≡ 161046 [MOD 161051] ↔ m % 161051 = 161046) := by
  exact ⟨modEq_six_mod11_iff_mod11_eq6,
    modEq_onesixteen_mod121_iff_mod121_eq116,
    modEq_thirteentwentysix_mod1331_iff_mod1331_eq1326,
    modEq_fourteensixthirtysix_mod14641_iff_mod14641_eq14636,
    modEq_onesixtyonezero46_mod161051_iff_mod161051_eq161046⟩

/-- Concrete residue/`Nat.ModEq` form for `4 mod 5`. -/
theorem mod5_eq4_iff_modEq_four_mod5 (m : ℕ) :
    m % 5 = 4 ↔ m ≡ 4 [MOD 5] := by
  exact (modEq_four_mod5_iff_mod5_eq4 m).symm

/-- Concrete residue/`Nat.ModEq` form for `24 mod 25`. -/
theorem mod25_eq24_iff_modEq_twentyfour_mod25 (m : ℕ) :
    m % 25 = 24 ↔ m ≡ 24 [MOD 25] := by
  exact (modEq_twentyfour_mod25_iff_mod25_eq24 m).symm

/-- Concrete residue/`Nat.ModEq` form for `124 mod 125`. -/
theorem mod125_eq124_iff_modEq_onetwentyfour_mod125 (m : ℕ) :
    m % 125 = 124 ↔ m ≡ 124 [MOD 125] := by
  exact (modEq_onetwentyfour_mod125_iff_mod125_eq124 m).symm

/-- Concrete residue/`Nat.ModEq` form for `624 mod 625`. -/
theorem mod625_eq624_iff_modEq_sixtwentyfour_mod625 (m : ℕ) :
    m % 625 = 624 ↔ m ≡ 624 [MOD 625] := by
  exact (modEq_sixtwentyfour_mod625_iff_mod625_eq624 m).symm

/-- Concrete residue/`Nat.ModEq` form for `3124 mod 3125`. -/
theorem mod3125_eq3124_iff_modEq_thirtyonetwentyfour_mod3125 (m : ℕ) :
    m % 3125 = 3124 ↔ m ≡ 3124 [MOD 3125] := by
  exact (modEq_thirtyonetwentyfour_mod3125_iff_mod3125_eq3124 m).symm

/-- Concrete residue/`Nat.ModEq` form for `5 mod 7`. -/
theorem mod7_eq5_iff_modEq_five_mod7 (m : ℕ) :
    m % 7 = 5 ↔ m ≡ 5 [MOD 7] := by
  exact (modEq_five_mod7_iff_mod7_eq5 m).symm

/-- Concrete residue/`Nat.ModEq` form for `47 mod 49`. -/
theorem mod49_eq47_iff_modEq_fortyseven_mod49 (m : ℕ) :
    m % 49 = 47 ↔ m ≡ 47 [MOD 49] := by
  exact (modEq_fortyseven_mod49_iff_mod49_eq47 m).symm

/-- Concrete residue/`Nat.ModEq` form for `341 mod 343`. -/
theorem mod343_eq341_iff_modEq_threefourtyone_mod343 (m : ℕ) :
    m % 343 = 341 ↔ m ≡ 341 [MOD 343] := by
  exact (modEq_threefourtyone_mod343_iff_mod343_eq341 m).symm

/-- Concrete residue/`Nat.ModEq` form for `2399 mod 2401`. -/
theorem mod2401_eq2399_iff_modEq_twentythreeninetynine_mod2401 (m : ℕ) :
    m % 2401 = 2399 ↔ m ≡ 2399 [MOD 2401] := by
  exact (modEq_twentythreeninetynine_mod2401_iff_mod2401_eq2399 m).symm

/-- Concrete residue/`Nat.ModEq` form for `16805 mod 16807`. -/
theorem mod16807_eq16805_iff_modEq_sixteeneightofive_mod16807 (m : ℕ) :
    m % 16807 = 16805 ↔ m ≡ 16805 [MOD 16807] := by
  exact (modEq_sixteeneightofive_mod16807_iff_mod16807_eq16805 m).symm

/-- Concrete residue/`Nat.ModEq` form for `6 mod 11`. -/
theorem mod11_eq6_iff_modEq_six_mod11 (m : ℕ) :
    m % 11 = 6 ↔ m ≡ 6 [MOD 11] := by
  exact (modEq_six_mod11_iff_mod11_eq6 m).symm

/-- Concrete residue/`Nat.ModEq` form for `116 mod 121`. -/
theorem mod121_eq116_iff_modEq_onesixteen_mod121 (m : ℕ) :
    m % 121 = 116 ↔ m ≡ 116 [MOD 121] := by
  exact (modEq_onesixteen_mod121_iff_mod121_eq116 m).symm

/-- Concrete residue/`Nat.ModEq` form for `1326 mod 1331`. -/
theorem mod1331_eq1326_iff_modEq_thirteentwentysix_mod1331 (m : ℕ) :
    m % 1331 = 1326 ↔ m ≡ 1326 [MOD 1331] := by
  exact (modEq_thirteentwentysix_mod1331_iff_mod1331_eq1326 m).symm

/-- Concrete residue/`Nat.ModEq` form for `14636 mod 14641`. -/
theorem mod14641_eq14636_iff_modEq_fourteensixthirtysix_mod14641 (m : ℕ) :
    m % 14641 = 14636 ↔ m ≡ 14636 [MOD 14641] := by
  exact (modEq_fourteensixthirtysix_mod14641_iff_mod14641_eq14636 m).symm

/-- Concrete residue/`Nat.ModEq` form for `161046 mod 161051`. -/
theorem mod161051_eq161046_iff_modEq_onesixtyonezero46_mod161051 (m : ℕ) :
    m % 161051 = 161046 ↔ m ≡ 161046 [MOD 161051] := by
  exact (modEq_onesixtyonezero46_mod161051_iff_mod161051_eq161046 m).symm

/-- Concrete mod-5 power residue iff `Nat.ModEq` facts. -/
theorem concrete_mod5_power_residue_iff_modEq_facts :
    (∀ m, m % 5 = 4 ↔ m ≡ 4 [MOD 5]) ∧
      (∀ m, m % 25 = 24 ↔ m ≡ 24 [MOD 25]) ∧
      (∀ m, m % 125 = 124 ↔ m ≡ 124 [MOD 125]) ∧
      (∀ m, m % 625 = 624 ↔ m ≡ 624 [MOD 625]) ∧
      (∀ m, m % 3125 = 3124 ↔ m ≡ 3124 [MOD 3125]) := by
  exact ⟨mod5_eq4_iff_modEq_four_mod5,
    mod25_eq24_iff_modEq_twentyfour_mod25,
    mod125_eq124_iff_modEq_onetwentyfour_mod125,
    mod625_eq624_iff_modEq_sixtwentyfour_mod625,
    mod3125_eq3124_iff_modEq_thirtyonetwentyfour_mod3125⟩

/-- Concrete mod-7 power residue iff `Nat.ModEq` facts. -/
theorem concrete_mod7_power_residue_iff_modEq_facts :
    (∀ m, m % 7 = 5 ↔ m ≡ 5 [MOD 7]) ∧
      (∀ m, m % 49 = 47 ↔ m ≡ 47 [MOD 49]) ∧
      (∀ m, m % 343 = 341 ↔ m ≡ 341 [MOD 343]) ∧
      (∀ m, m % 2401 = 2399 ↔ m ≡ 2399 [MOD 2401]) ∧
      (∀ m, m % 16807 = 16805 ↔ m ≡ 16805 [MOD 16807]) := by
  exact ⟨mod7_eq5_iff_modEq_five_mod7,
    mod49_eq47_iff_modEq_fortyseven_mod49,
    mod343_eq341_iff_modEq_threefourtyone_mod343,
    mod2401_eq2399_iff_modEq_twentythreeninetynine_mod2401,
    mod16807_eq16805_iff_modEq_sixteeneightofive_mod16807⟩

/-- Concrete mod-11 power residue iff `Nat.ModEq` facts. -/
theorem concrete_mod11_power_residue_iff_modEq_facts :
    (∀ m, m % 11 = 6 ↔ m ≡ 6 [MOD 11]) ∧
      (∀ m, m % 121 = 116 ↔ m ≡ 116 [MOD 121]) ∧
      (∀ m, m % 1331 = 1326 ↔ m ≡ 1326 [MOD 1331]) ∧
      (∀ m, m % 14641 = 14636 ↔ m ≡ 14636 [MOD 14641]) ∧
      (∀ m, m % 161051 = 161046 ↔ m ≡ 161046 [MOD 161051]) := by
  exact ⟨mod11_eq6_iff_modEq_six_mod11,
    mod121_eq116_iff_modEq_onesixteen_mod121,
    mod1331_eq1326_iff_modEq_thirteentwentysix_mod1331,
    mod14641_eq14636_iff_modEq_fourteensixthirtysix_mod14641,
    mod161051_eq161046_iff_modEq_onesixtyonezero46_mod161051⟩

/-- A negated `Nat.ModEq` to a reduced residue is the same as direct `%`
inequality. -/
theorem not_modEq_iff_mod_ne_of_lt {q r m : ℕ} (hr : r < q) :
    ¬ (m ≡ r [MOD q]) ↔ m % q ≠ r :=
  not_congr (modEq_iff_mod_eq_of_lt (m := m) hr)

/-- Direct `%` inequality to a reduced residue is the same as negated
`Nat.ModEq`. -/
theorem mod_ne_iff_not_modEq_of_lt {q r m : ℕ} (hr : r < q) :
    m % q ≠ r ↔ ¬ (m ≡ r [MOD q]) :=
  (not_modEq_iff_mod_ne_of_lt (m := m) hr).symm

/-- Concrete negated `Nat.ModEq`/residue inequality form for `4 mod 5`. -/
theorem not_modEq_four_mod5_iff_mod5_ne4 (m : ℕ) :
    ¬ (m ≡ 4 [MOD 5]) ↔ m % 5 ≠ 4 :=
  not_modEq_iff_mod_ne_of_lt (q := 5) (r := 4) (m := m) (by decide)

/-- Concrete negated `Nat.ModEq`/residue inequality form for `24 mod 25`. -/
theorem not_modEq_twentyfour_mod25_iff_mod25_ne24 (m : ℕ) :
    ¬ (m ≡ 24 [MOD 25]) ↔ m % 25 ≠ 24 :=
  not_modEq_iff_mod_ne_of_lt (q := 25) (r := 24) (m := m) (by decide)

/-- Concrete negated `Nat.ModEq`/residue inequality form for `124 mod 125`. -/
theorem not_modEq_onetwentyfour_mod125_iff_mod125_ne124 (m : ℕ) :
    ¬ (m ≡ 124 [MOD 125]) ↔ m % 125 ≠ 124 :=
  not_modEq_iff_mod_ne_of_lt (q := 125) (r := 124) (m := m) (by decide)

/-- Concrete negated `Nat.ModEq`/residue inequality form for `624 mod 625`. -/
theorem not_modEq_sixtwentyfour_mod625_iff_mod625_ne624 (m : ℕ) :
    ¬ (m ≡ 624 [MOD 625]) ↔ m % 625 ≠ 624 :=
  not_modEq_iff_mod_ne_of_lt (q := 625) (r := 624) (m := m) (by decide)

/-- Concrete negated `Nat.ModEq`/residue inequality form for `3124 mod 3125`. -/
theorem not_modEq_thirtyonetwentyfour_mod3125_iff_mod3125_ne3124 (m : ℕ) :
    ¬ (m ≡ 3124 [MOD 3125]) ↔ m % 3125 ≠ 3124 :=
  not_modEq_iff_mod_ne_of_lt (q := 3125) (r := 3124) (m := m) (by decide)

/-- Concrete negated `Nat.ModEq`/residue inequality form for `5 mod 7`. -/
theorem not_modEq_five_mod7_iff_mod7_ne5 (m : ℕ) :
    ¬ (m ≡ 5 [MOD 7]) ↔ m % 7 ≠ 5 :=
  not_modEq_iff_mod_ne_of_lt (q := 7) (r := 5) (m := m) (by decide)

/-- Concrete negated `Nat.ModEq`/residue inequality form for `47 mod 49`. -/
theorem not_modEq_fortyseven_mod49_iff_mod49_ne47 (m : ℕ) :
    ¬ (m ≡ 47 [MOD 49]) ↔ m % 49 ≠ 47 :=
  not_modEq_iff_mod_ne_of_lt (q := 49) (r := 47) (m := m) (by decide)

/-- Concrete negated `Nat.ModEq`/residue inequality form for `341 mod 343`. -/
theorem not_modEq_threefourtyone_mod343_iff_mod343_ne341 (m : ℕ) :
    ¬ (m ≡ 341 [MOD 343]) ↔ m % 343 ≠ 341 :=
  not_modEq_iff_mod_ne_of_lt (q := 343) (r := 341) (m := m) (by decide)

/-- Concrete negated `Nat.ModEq`/residue inequality form for `2399 mod 2401`. -/
theorem not_modEq_twentythreeninetynine_mod2401_iff_mod2401_ne2399 (m : ℕ) :
    ¬ (m ≡ 2399 [MOD 2401]) ↔ m % 2401 ≠ 2399 :=
  not_modEq_iff_mod_ne_of_lt (q := 2401) (r := 2399) (m := m) (by decide)

/-- Concrete negated `Nat.ModEq`/residue inequality form for `16805 mod
`16807`. -/
theorem not_modEq_sixteeneightofive_mod16807_iff_mod16807_ne16805 (m : ℕ) :
    ¬ (m ≡ 16805 [MOD 16807]) ↔ m % 16807 ≠ 16805 :=
  not_modEq_iff_mod_ne_of_lt (q := 16807) (r := 16805) (m := m) (by decide)

/-- Concrete negated `Nat.ModEq`/residue inequality form for `6 mod 11`. -/
theorem not_modEq_six_mod11_iff_mod11_ne6 (m : ℕ) :
    ¬ (m ≡ 6 [MOD 11]) ↔ m % 11 ≠ 6 :=
  not_modEq_iff_mod_ne_of_lt (q := 11) (r := 6) (m := m) (by decide)

/-- Concrete negated `Nat.ModEq`/residue inequality form for `116 mod 121`. -/
theorem not_modEq_onesixteen_mod121_iff_mod121_ne116 (m : ℕ) :
    ¬ (m ≡ 116 [MOD 121]) ↔ m % 121 ≠ 116 :=
  not_modEq_iff_mod_ne_of_lt (q := 121) (r := 116) (m := m) (by decide)

/-- Concrete negated `Nat.ModEq`/residue inequality form for `1326 mod 1331`. -/
theorem not_modEq_thirteentwentysix_mod1331_iff_mod1331_ne1326 (m : ℕ) :
    ¬ (m ≡ 1326 [MOD 1331]) ↔ m % 1331 ≠ 1326 :=
  not_modEq_iff_mod_ne_of_lt (q := 1331) (r := 1326) (m := m) (by decide)

/-- Concrete negated `Nat.ModEq`/residue inequality form for `14636 mod
`14641`. -/
theorem not_modEq_fourteensixthirtysix_mod14641_iff_mod14641_ne14636 (m : ℕ) :
    ¬ (m ≡ 14636 [MOD 14641]) ↔ m % 14641 ≠ 14636 :=
  not_modEq_iff_mod_ne_of_lt (q := 14641) (r := 14636) (m := m) (by decide)

/-- Concrete negated `Nat.ModEq`/residue inequality form for `161046 mod
`161051`. -/
theorem not_modEq_onesixtyonezero46_mod161051_iff_mod161051_ne161046 (m : ℕ) :
    ¬ (m ≡ 161046 [MOD 161051]) ↔ m % 161051 ≠ 161046 :=
  not_modEq_iff_mod_ne_of_lt (q := 161051) (r := 161046) (m := m) (by decide)

/-- Concrete mod-5 power negated `Nat.ModEq` iff residue inequality facts. -/
theorem concrete_mod5_power_not_modEq_iff_residue_ne_facts :
    (∀ m, ¬ (m ≡ 4 [MOD 5]) ↔ m % 5 ≠ 4) ∧
      (∀ m, ¬ (m ≡ 24 [MOD 25]) ↔ m % 25 ≠ 24) ∧
      (∀ m, ¬ (m ≡ 124 [MOD 125]) ↔ m % 125 ≠ 124) ∧
      (∀ m, ¬ (m ≡ 624 [MOD 625]) ↔ m % 625 ≠ 624) ∧
      (∀ m, ¬ (m ≡ 3124 [MOD 3125]) ↔ m % 3125 ≠ 3124) := by
  exact ⟨not_modEq_four_mod5_iff_mod5_ne4,
    not_modEq_twentyfour_mod25_iff_mod25_ne24,
    not_modEq_onetwentyfour_mod125_iff_mod125_ne124,
    not_modEq_sixtwentyfour_mod625_iff_mod625_ne624,
    not_modEq_thirtyonetwentyfour_mod3125_iff_mod3125_ne3124⟩

/-- Concrete mod-7 power negated `Nat.ModEq` iff residue inequality facts. -/
theorem concrete_mod7_power_not_modEq_iff_residue_ne_facts :
    (∀ m, ¬ (m ≡ 5 [MOD 7]) ↔ m % 7 ≠ 5) ∧
      (∀ m, ¬ (m ≡ 47 [MOD 49]) ↔ m % 49 ≠ 47) ∧
      (∀ m, ¬ (m ≡ 341 [MOD 343]) ↔ m % 343 ≠ 341) ∧
      (∀ m, ¬ (m ≡ 2399 [MOD 2401]) ↔ m % 2401 ≠ 2399) ∧
      (∀ m, ¬ (m ≡ 16805 [MOD 16807]) ↔ m % 16807 ≠ 16805) := by
  exact ⟨not_modEq_five_mod7_iff_mod7_ne5,
    not_modEq_fortyseven_mod49_iff_mod49_ne47,
    not_modEq_threefourtyone_mod343_iff_mod343_ne341,
    not_modEq_twentythreeninetynine_mod2401_iff_mod2401_ne2399,
    not_modEq_sixteeneightofive_mod16807_iff_mod16807_ne16805⟩

/-- Concrete mod-11 power negated `Nat.ModEq` iff residue inequality facts. -/
theorem concrete_mod11_power_not_modEq_iff_residue_ne_facts :
    (∀ m, ¬ (m ≡ 6 [MOD 11]) ↔ m % 11 ≠ 6) ∧
      (∀ m, ¬ (m ≡ 116 [MOD 121]) ↔ m % 121 ≠ 116) ∧
      (∀ m, ¬ (m ≡ 1326 [MOD 1331]) ↔ m % 1331 ≠ 1326) ∧
      (∀ m, ¬ (m ≡ 14636 [MOD 14641]) ↔ m % 14641 ≠ 14636) ∧
      (∀ m, ¬ (m ≡ 161046 [MOD 161051]) ↔ m % 161051 ≠ 161046) := by
  exact ⟨not_modEq_six_mod11_iff_mod11_ne6,
    not_modEq_onesixteen_mod121_iff_mod121_ne116,
    not_modEq_thirteentwentysix_mod1331_iff_mod1331_ne1326,
    not_modEq_fourteensixthirtysix_mod14641_iff_mod14641_ne14636,
    not_modEq_onesixtyonezero46_mod161051_iff_mod161051_ne161046⟩

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `4 mod 5`. -/
theorem mod5_ne4_iff_not_modEq_four_mod5 (m : ℕ) :
    m % 5 ≠ 4 ↔ ¬ (m ≡ 4 [MOD 5]) :=
  (not_modEq_four_mod5_iff_mod5_ne4 m).symm

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `24 mod 25`. -/
theorem mod25_ne24_iff_not_modEq_twentyfour_mod25 (m : ℕ) :
    m % 25 ≠ 24 ↔ ¬ (m ≡ 24 [MOD 25]) :=
  (not_modEq_twentyfour_mod25_iff_mod25_ne24 m).symm

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `124 mod 125`. -/
theorem mod125_ne124_iff_not_modEq_onetwentyfour_mod125 (m : ℕ) :
    m % 125 ≠ 124 ↔ ¬ (m ≡ 124 [MOD 125]) :=
  (not_modEq_onetwentyfour_mod125_iff_mod125_ne124 m).symm

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `624 mod 625`. -/
theorem mod625_ne624_iff_not_modEq_sixtwentyfour_mod625 (m : ℕ) :
    m % 625 ≠ 624 ↔ ¬ (m ≡ 624 [MOD 625]) :=
  (not_modEq_sixtwentyfour_mod625_iff_mod625_ne624 m).symm

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `3124 mod
`3125`. -/
theorem mod3125_ne3124_iff_not_modEq_thirtyonetwentyfour_mod3125 (m : ℕ) :
    m % 3125 ≠ 3124 ↔ ¬ (m ≡ 3124 [MOD 3125]) :=
  (not_modEq_thirtyonetwentyfour_mod3125_iff_mod3125_ne3124 m).symm

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `5 mod 7`. -/
theorem mod7_ne5_iff_not_modEq_five_mod7 (m : ℕ) :
    m % 7 ≠ 5 ↔ ¬ (m ≡ 5 [MOD 7]) :=
  (not_modEq_five_mod7_iff_mod7_ne5 m).symm

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `47 mod 49`. -/
theorem mod49_ne47_iff_not_modEq_fortyseven_mod49 (m : ℕ) :
    m % 49 ≠ 47 ↔ ¬ (m ≡ 47 [MOD 49]) :=
  (not_modEq_fortyseven_mod49_iff_mod49_ne47 m).symm

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `341 mod 343`. -/
theorem mod343_ne341_iff_not_modEq_threefourtyone_mod343 (m : ℕ) :
    m % 343 ≠ 341 ↔ ¬ (m ≡ 341 [MOD 343]) :=
  (not_modEq_threefourtyone_mod343_iff_mod343_ne341 m).symm

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `2399 mod
`2401`. -/
theorem mod2401_ne2399_iff_not_modEq_twentythreeninetynine_mod2401 (m : ℕ) :
    m % 2401 ≠ 2399 ↔ ¬ (m ≡ 2399 [MOD 2401]) :=
  (not_modEq_twentythreeninetynine_mod2401_iff_mod2401_ne2399 m).symm

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `16805 mod
`16807`. -/
theorem mod16807_ne16805_iff_not_modEq_sixteeneightofive_mod16807 (m : ℕ) :
    m % 16807 ≠ 16805 ↔ ¬ (m ≡ 16805 [MOD 16807]) :=
  (not_modEq_sixteeneightofive_mod16807_iff_mod16807_ne16805 m).symm

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `6 mod 11`. -/
theorem mod11_ne6_iff_not_modEq_six_mod11 (m : ℕ) :
    m % 11 ≠ 6 ↔ ¬ (m ≡ 6 [MOD 11]) :=
  (not_modEq_six_mod11_iff_mod11_ne6 m).symm

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `116 mod 121`. -/
theorem mod121_ne116_iff_not_modEq_onesixteen_mod121 (m : ℕ) :
    m % 121 ≠ 116 ↔ ¬ (m ≡ 116 [MOD 121]) :=
  (not_modEq_onesixteen_mod121_iff_mod121_ne116 m).symm

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `1326 mod
`1331`. -/
theorem mod1331_ne1326_iff_not_modEq_thirteentwentysix_mod1331 (m : ℕ) :
    m % 1331 ≠ 1326 ↔ ¬ (m ≡ 1326 [MOD 1331]) :=
  (not_modEq_thirteentwentysix_mod1331_iff_mod1331_ne1326 m).symm

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `14636 mod
`14641`. -/
theorem mod14641_ne14636_iff_not_modEq_fourteensixthirtysix_mod14641 (m : ℕ) :
    m % 14641 ≠ 14636 ↔ ¬ (m ≡ 14636 [MOD 14641]) :=
  (not_modEq_fourteensixthirtysix_mod14641_iff_mod14641_ne14636 m).symm

/-- Concrete residue inequality iff negated `Nat.ModEq` form for `161046 mod
`161051`. -/
theorem mod161051_ne161046_iff_not_modEq_onesixtyonezero46_mod161051 (m : ℕ) :
    m % 161051 ≠ 161046 ↔ ¬ (m ≡ 161046 [MOD 161051]) :=
  (not_modEq_onesixtyonezero46_mod161051_iff_mod161051_ne161046 m).symm

/-- Concrete mod-5 power residue inequality iff negated `Nat.ModEq` facts. -/
theorem concrete_mod5_power_residue_ne_iff_not_modEq_facts :
    (∀ m, m % 5 ≠ 4 ↔ ¬ (m ≡ 4 [MOD 5])) ∧
      (∀ m, m % 25 ≠ 24 ↔ ¬ (m ≡ 24 [MOD 25])) ∧
      (∀ m, m % 125 ≠ 124 ↔ ¬ (m ≡ 124 [MOD 125])) ∧
      (∀ m, m % 625 ≠ 624 ↔ ¬ (m ≡ 624 [MOD 625])) ∧
      (∀ m, m % 3125 ≠ 3124 ↔ ¬ (m ≡ 3124 [MOD 3125])) := by
  exact ⟨mod5_ne4_iff_not_modEq_four_mod5,
    mod25_ne24_iff_not_modEq_twentyfour_mod25,
    mod125_ne124_iff_not_modEq_onetwentyfour_mod125,
    mod625_ne624_iff_not_modEq_sixtwentyfour_mod625,
    mod3125_ne3124_iff_not_modEq_thirtyonetwentyfour_mod3125⟩

/-- Concrete mod-7 power residue inequality iff negated `Nat.ModEq` facts. -/
theorem concrete_mod7_power_residue_ne_iff_not_modEq_facts :
    (∀ m, m % 7 ≠ 5 ↔ ¬ (m ≡ 5 [MOD 7])) ∧
      (∀ m, m % 49 ≠ 47 ↔ ¬ (m ≡ 47 [MOD 49])) ∧
      (∀ m, m % 343 ≠ 341 ↔ ¬ (m ≡ 341 [MOD 343])) ∧
      (∀ m, m % 2401 ≠ 2399 ↔ ¬ (m ≡ 2399 [MOD 2401])) ∧
      (∀ m, m % 16807 ≠ 16805 ↔ ¬ (m ≡ 16805 [MOD 16807])) := by
  exact ⟨mod7_ne5_iff_not_modEq_five_mod7,
    mod49_ne47_iff_not_modEq_fortyseven_mod49,
    mod343_ne341_iff_not_modEq_threefourtyone_mod343,
    mod2401_ne2399_iff_not_modEq_twentythreeninetynine_mod2401,
    mod16807_ne16805_iff_not_modEq_sixteeneightofive_mod16807⟩

/-- Concrete mod-11 power residue inequality iff negated `Nat.ModEq` facts. -/
theorem concrete_mod11_power_residue_ne_iff_not_modEq_facts :
    (∀ m, m % 11 ≠ 6 ↔ ¬ (m ≡ 6 [MOD 11])) ∧
      (∀ m, m % 121 ≠ 116 ↔ ¬ (m ≡ 116 [MOD 121])) ∧
      (∀ m, m % 1331 ≠ 1326 ↔ ¬ (m ≡ 1326 [MOD 1331])) ∧
      (∀ m, m % 14641 ≠ 14636 ↔ ¬ (m ≡ 14636 [MOD 14641])) ∧
      (∀ m, m % 161051 ≠ 161046 ↔ ¬ (m ≡ 161046 [MOD 161051])) := by
  exact ⟨mod11_ne6_iff_not_modEq_six_mod11,
    mod121_ne116_iff_not_modEq_onesixteen_mod121,
    mod1331_ne1326_iff_not_modEq_thirteentwentysix_mod1331,
    mod14641_ne14636_iff_not_modEq_fourteensixthirtysix_mod14641,
    mod161051_ne161046_iff_not_modEq_onesixtyonezero46_mod161051⟩

/-- Convert a direct `%` equality to the corresponding reduced `Nat.ModEq`. -/
theorem modEq_of_mod_eq_of_lt {q r m : ℕ} (hr : r < q) (hm : m % q = r) :
    m ≡ r [MOD q] :=
  (modEq_iff_mod_eq_of_lt (m := m) hr).2 hm

/-- Convert a reduced `Nat.ModEq` to the corresponding direct `%` equality. -/
theorem mod_eq_of_modEq_of_lt {q r m : ℕ} (hr : r < q) (hm : m ≡ r [MOD q]) :
    m % q = r :=
  (modEq_iff_mod_eq_of_lt (m := m) hr).1 hm

/-- Convert direct `%` inequality to negated reduced `Nat.ModEq`. -/
theorem not_modEq_of_mod_ne_of_lt {q r m : ℕ} (hr : r < q) (hm : m % q ≠ r) :
    ¬ (m ≡ r [MOD q]) :=
  (not_modEq_iff_mod_ne_of_lt (m := m) hr).2 hm

/-- Convert negated reduced `Nat.ModEq` to direct `%` inequality. -/
theorem mod_ne_of_not_modEq_of_lt {q r m : ℕ} (hr : r < q)
    (hm : ¬ (m ≡ r [MOD q])) :
    m % q ≠ r :=
  (not_modEq_iff_mod_ne_of_lt (m := m) hr).1 hm

/-- Direct residue equality implies `m ≡ 4 mod 5`. -/
theorem modEq_four_mod5_of_mod5_eq4 (m : ℕ) (hm : m % 5 = 4) :
    m ≡ 4 [MOD 5] :=
  modEq_of_mod_eq_of_lt (q := 5) (r := 4) (m := m) (by decide) hm

/-- Direct residue equality implies `m ≡ 24 mod 25`. -/
theorem modEq_twentyfour_mod25_of_mod25_eq24 (m : ℕ) (hm : m % 25 = 24) :
    m ≡ 24 [MOD 25] :=
  modEq_of_mod_eq_of_lt (q := 25) (r := 24) (m := m) (by decide) hm

/-- Direct residue equality implies `m ≡ 124 mod 125`. -/
theorem modEq_onetwentyfour_mod125_of_mod125_eq124 (m : ℕ)
    (hm : m % 125 = 124) :
    m ≡ 124 [MOD 125] :=
  modEq_of_mod_eq_of_lt (q := 125) (r := 124) (m := m) (by decide) hm

/-- Direct residue equality implies `m ≡ 624 mod 625`. -/
theorem modEq_sixtwentyfour_mod625_of_mod625_eq624 (m : ℕ)
    (hm : m % 625 = 624) :
    m ≡ 624 [MOD 625] :=
  modEq_of_mod_eq_of_lt (q := 625) (r := 624) (m := m) (by decide) hm

/-- Direct residue equality implies `m ≡ 3124 mod 3125`. -/
theorem modEq_thirtyonetwentyfour_mod3125_of_mod3125_eq3124 (m : ℕ)
    (hm : m % 3125 = 3124) :
    m ≡ 3124 [MOD 3125] :=
  modEq_of_mod_eq_of_lt (q := 3125) (r := 3124) (m := m) (by decide) hm

/-- Direct residue equality implies `m ≡ 5 mod 7`. -/
theorem modEq_five_mod7_of_mod7_eq5 (m : ℕ) (hm : m % 7 = 5) :
    m ≡ 5 [MOD 7] :=
  modEq_of_mod_eq_of_lt (q := 7) (r := 5) (m := m) (by decide) hm

/-- Direct residue equality implies `m ≡ 47 mod 49`. -/
theorem modEq_fortyseven_mod49_of_mod49_eq47 (m : ℕ) (hm : m % 49 = 47) :
    m ≡ 47 [MOD 49] :=
  modEq_of_mod_eq_of_lt (q := 49) (r := 47) (m := m) (by decide) hm

/-- Direct residue equality implies `m ≡ 341 mod 343`. -/
theorem modEq_threefourtyone_mod343_of_mod343_eq341 (m : ℕ)
    (hm : m % 343 = 341) :
    m ≡ 341 [MOD 343] :=
  modEq_of_mod_eq_of_lt (q := 343) (r := 341) (m := m) (by decide) hm

/-- Direct residue equality implies `m ≡ 2399 mod 2401`. -/
theorem modEq_twentythreeninetynine_mod2401_of_mod2401_eq2399 (m : ℕ)
    (hm : m % 2401 = 2399) :
    m ≡ 2399 [MOD 2401] :=
  modEq_of_mod_eq_of_lt (q := 2401) (r := 2399) (m := m) (by decide) hm

/-- Direct residue equality implies `m ≡ 16805 mod 16807`. -/
theorem modEq_sixteeneightofive_mod16807_of_mod16807_eq16805 (m : ℕ)
    (hm : m % 16807 = 16805) :
    m ≡ 16805 [MOD 16807] :=
  modEq_of_mod_eq_of_lt (q := 16807) (r := 16805) (m := m) (by decide) hm

/-- Direct residue equality implies `m ≡ 6 mod 11`. -/
theorem modEq_six_mod11_of_mod11_eq6 (m : ℕ) (hm : m % 11 = 6) :
    m ≡ 6 [MOD 11] :=
  modEq_of_mod_eq_of_lt (q := 11) (r := 6) (m := m) (by decide) hm

/-- Direct residue equality implies `m ≡ 116 mod 121`. -/
theorem modEq_onesixteen_mod121_of_mod121_eq116 (m : ℕ)
    (hm : m % 121 = 116) :
    m ≡ 116 [MOD 121] :=
  modEq_of_mod_eq_of_lt (q := 121) (r := 116) (m := m) (by decide) hm

/-- Direct residue equality implies `m ≡ 1326 mod 1331`. -/
theorem modEq_thirteentwentysix_mod1331_of_mod1331_eq1326 (m : ℕ)
    (hm : m % 1331 = 1326) :
    m ≡ 1326 [MOD 1331] :=
  modEq_of_mod_eq_of_lt (q := 1331) (r := 1326) (m := m) (by decide) hm

/-- Direct residue equality implies `m ≡ 14636 mod 14641`. -/
theorem modEq_fourteensixthirtysix_mod14641_of_mod14641_eq14636 (m : ℕ)
    (hm : m % 14641 = 14636) :
    m ≡ 14636 [MOD 14641] :=
  modEq_of_mod_eq_of_lt (q := 14641) (r := 14636) (m := m) (by decide) hm

/-- Direct residue equality implies `m ≡ 161046 mod 161051`. -/
theorem modEq_onesixtyonezero46_mod161051_of_mod161051_eq161046 (m : ℕ)
    (hm : m % 161051 = 161046) :
    m ≡ 161046 [MOD 161051] :=
  modEq_of_mod_eq_of_lt (q := 161051) (r := 161046) (m := m) (by decide) hm

/-- `m ≡ 4 mod 5` implies direct residue equality. -/
theorem mod5_eq4_of_modEq_four_mod5 (m : ℕ) (hm : m ≡ 4 [MOD 5]) :
    m % 5 = 4 :=
  mod_eq_of_modEq_of_lt (q := 5) (r := 4) (m := m) (by decide) hm

/-- `m ≡ 24 mod 25` implies direct residue equality. -/
theorem mod25_eq24_of_modEq_twentyfour_mod25 (m : ℕ) (hm : m ≡ 24 [MOD 25]) :
    m % 25 = 24 :=
  mod_eq_of_modEq_of_lt (q := 25) (r := 24) (m := m) (by decide) hm

/-- `m ≡ 124 mod 125` implies direct residue equality. -/
theorem mod125_eq124_of_modEq_onetwentyfour_mod125 (m : ℕ)
    (hm : m ≡ 124 [MOD 125]) :
    m % 125 = 124 :=
  mod_eq_of_modEq_of_lt (q := 125) (r := 124) (m := m) (by decide) hm

/-- `m ≡ 624 mod 625` implies direct residue equality. -/
theorem mod625_eq624_of_modEq_sixtwentyfour_mod625 (m : ℕ)
    (hm : m ≡ 624 [MOD 625]) :
    m % 625 = 624 :=
  mod_eq_of_modEq_of_lt (q := 625) (r := 624) (m := m) (by decide) hm

/-- `m ≡ 3124 mod 3125` implies direct residue equality. -/
theorem mod3125_eq3124_of_modEq_thirtyonetwentyfour_mod3125 (m : ℕ)
    (hm : m ≡ 3124 [MOD 3125]) :
    m % 3125 = 3124 :=
  mod_eq_of_modEq_of_lt (q := 3125) (r := 3124) (m := m) (by decide) hm

/-- `m ≡ 5 mod 7` implies direct residue equality. -/
theorem mod7_eq5_of_modEq_five_mod7 (m : ℕ) (hm : m ≡ 5 [MOD 7]) :
    m % 7 = 5 :=
  mod_eq_of_modEq_of_lt (q := 7) (r := 5) (m := m) (by decide) hm

/-- `m ≡ 47 mod 49` implies direct residue equality. -/
theorem mod49_eq47_of_modEq_fortyseven_mod49 (m : ℕ) (hm : m ≡ 47 [MOD 49]) :
    m % 49 = 47 :=
  mod_eq_of_modEq_of_lt (q := 49) (r := 47) (m := m) (by decide) hm

/-- `m ≡ 341 mod 343` implies direct residue equality. -/
theorem mod343_eq341_of_modEq_threefourtyone_mod343 (m : ℕ)
    (hm : m ≡ 341 [MOD 343]) :
    m % 343 = 341 :=
  mod_eq_of_modEq_of_lt (q := 343) (r := 341) (m := m) (by decide) hm

/-- `m ≡ 2399 mod 2401` implies direct residue equality. -/
theorem mod2401_eq2399_of_modEq_twentythreeninetynine_mod2401 (m : ℕ)
    (hm : m ≡ 2399 [MOD 2401]) :
    m % 2401 = 2399 :=
  mod_eq_of_modEq_of_lt (q := 2401) (r := 2399) (m := m) (by decide) hm

/-- `m ≡ 16805 mod 16807` implies direct residue equality. -/
theorem mod16807_eq16805_of_modEq_sixteeneightofive_mod16807 (m : ℕ)
    (hm : m ≡ 16805 [MOD 16807]) :
    m % 16807 = 16805 :=
  mod_eq_of_modEq_of_lt (q := 16807) (r := 16805) (m := m) (by decide) hm

/-- `m ≡ 6 mod 11` implies direct residue equality. -/
theorem mod11_eq6_of_modEq_six_mod11 (m : ℕ) (hm : m ≡ 6 [MOD 11]) :
    m % 11 = 6 :=
  mod_eq_of_modEq_of_lt (q := 11) (r := 6) (m := m) (by decide) hm

/-- `m ≡ 116 mod 121` implies direct residue equality. -/
theorem mod121_eq116_of_modEq_onesixteen_mod121 (m : ℕ)
    (hm : m ≡ 116 [MOD 121]) :
    m % 121 = 116 :=
  mod_eq_of_modEq_of_lt (q := 121) (r := 116) (m := m) (by decide) hm

/-- `m ≡ 1326 mod 1331` implies direct residue equality. -/
theorem mod1331_eq1326_of_modEq_thirteentwentysix_mod1331 (m : ℕ)
    (hm : m ≡ 1326 [MOD 1331]) :
    m % 1331 = 1326 :=
  mod_eq_of_modEq_of_lt (q := 1331) (r := 1326) (m := m) (by decide) hm

/-- `m ≡ 14636 mod 14641` implies direct residue equality. -/
theorem mod14641_eq14636_of_modEq_fourteensixthirtysix_mod14641 (m : ℕ)
    (hm : m ≡ 14636 [MOD 14641]) :
    m % 14641 = 14636 :=
  mod_eq_of_modEq_of_lt (q := 14641) (r := 14636) (m := m) (by decide) hm

/-- `m ≡ 161046 mod 161051` implies direct residue equality. -/
theorem mod161051_eq161046_of_modEq_onesixtyonezero46_mod161051 (m : ℕ)
    (hm : m ≡ 161046 [MOD 161051]) :
    m % 161051 = 161046 :=
  mod_eq_of_modEq_of_lt (q := 161051) (r := 161046) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 4 mod 5`. -/
theorem not_modEq_four_mod5_of_mod5_ne4 (m : ℕ) (hm : m % 5 ≠ 4) :
    ¬ (m ≡ 4 [MOD 5]) :=
  not_modEq_of_mod_ne_of_lt (q := 5) (r := 4) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 24 mod 25`. -/
theorem not_modEq_twentyfour_mod25_of_mod25_ne24 (m : ℕ) (hm : m % 25 ≠ 24) :
    ¬ (m ≡ 24 [MOD 25]) :=
  not_modEq_of_mod_ne_of_lt (q := 25) (r := 24) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 124 mod 125`. -/
theorem not_modEq_onetwentyfour_mod125_of_mod125_ne124 (m : ℕ)
    (hm : m % 125 ≠ 124) :
    ¬ (m ≡ 124 [MOD 125]) :=
  not_modEq_of_mod_ne_of_lt (q := 125) (r := 124) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 624 mod 625`. -/
theorem not_modEq_sixtwentyfour_mod625_of_mod625_ne624 (m : ℕ)
    (hm : m % 625 ≠ 624) :
    ¬ (m ≡ 624 [MOD 625]) :=
  not_modEq_of_mod_ne_of_lt (q := 625) (r := 624) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 3124 mod 3125`. -/
theorem not_modEq_thirtyonetwentyfour_mod3125_of_mod3125_ne3124 (m : ℕ)
    (hm : m % 3125 ≠ 3124) :
    ¬ (m ≡ 3124 [MOD 3125]) :=
  not_modEq_of_mod_ne_of_lt (q := 3125) (r := 3124) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 5 mod 7`. -/
theorem not_modEq_five_mod7_of_mod7_ne5 (m : ℕ) (hm : m % 7 ≠ 5) :
    ¬ (m ≡ 5 [MOD 7]) :=
  not_modEq_of_mod_ne_of_lt (q := 7) (r := 5) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 47 mod 49`. -/
theorem not_modEq_fortyseven_mod49_of_mod49_ne47 (m : ℕ) (hm : m % 49 ≠ 47) :
    ¬ (m ≡ 47 [MOD 49]) :=
  not_modEq_of_mod_ne_of_lt (q := 49) (r := 47) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 341 mod 343`. -/
theorem not_modEq_threefourtyone_mod343_of_mod343_ne341 (m : ℕ)
    (hm : m % 343 ≠ 341) :
    ¬ (m ≡ 341 [MOD 343]) :=
  not_modEq_of_mod_ne_of_lt (q := 343) (r := 341) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 2399 mod 2401`. -/
theorem not_modEq_twentythreeninetynine_mod2401_of_mod2401_ne2399 (m : ℕ)
    (hm : m % 2401 ≠ 2399) :
    ¬ (m ≡ 2399 [MOD 2401]) :=
  not_modEq_of_mod_ne_of_lt (q := 2401) (r := 2399) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 16805 mod 16807`. -/
theorem not_modEq_sixteeneightofive_mod16807_of_mod16807_ne16805 (m : ℕ)
    (hm : m % 16807 ≠ 16805) :
    ¬ (m ≡ 16805 [MOD 16807]) :=
  not_modEq_of_mod_ne_of_lt (q := 16807) (r := 16805) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 6 mod 11`. -/
theorem not_modEq_six_mod11_of_mod11_ne6 (m : ℕ) (hm : m % 11 ≠ 6) :
    ¬ (m ≡ 6 [MOD 11]) :=
  not_modEq_of_mod_ne_of_lt (q := 11) (r := 6) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 116 mod 121`. -/
theorem not_modEq_onesixteen_mod121_of_mod121_ne116 (m : ℕ)
    (hm : m % 121 ≠ 116) :
    ¬ (m ≡ 116 [MOD 121]) :=
  not_modEq_of_mod_ne_of_lt (q := 121) (r := 116) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 1326 mod 1331`. -/
theorem not_modEq_thirteentwentysix_mod1331_of_mod1331_ne1326 (m : ℕ)
    (hm : m % 1331 ≠ 1326) :
    ¬ (m ≡ 1326 [MOD 1331]) :=
  not_modEq_of_mod_ne_of_lt (q := 1331) (r := 1326) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 14636 mod 14641`. -/
theorem not_modEq_fourteensixthirtysix_mod14641_of_mod14641_ne14636 (m : ℕ)
    (hm : m % 14641 ≠ 14636) :
    ¬ (m ≡ 14636 [MOD 14641]) :=
  not_modEq_of_mod_ne_of_lt (q := 14641) (r := 14636) (m := m) (by decide) hm

/-- Direct residue inequality implies `¬ m ≡ 161046 mod 161051`. -/
theorem not_modEq_onesixtyonezero46_mod161051_of_mod161051_ne161046 (m : ℕ)
    (hm : m % 161051 ≠ 161046) :
    ¬ (m ≡ 161046 [MOD 161051]) :=
  not_modEq_of_mod_ne_of_lt (q := 161051) (r := 161046) (m := m) (by decide) hm

/-- Negated `m ≡ 4 mod 5` implies direct residue inequality. -/
theorem mod5_ne4_of_not_modEq_four_mod5 (m : ℕ) (hm : ¬ (m ≡ 4 [MOD 5])) :
    m % 5 ≠ 4 :=
  mod_ne_of_not_modEq_of_lt (q := 5) (r := 4) (m := m) (by decide) hm

/-- Negated `m ≡ 24 mod 25` implies direct residue inequality. -/
theorem mod25_ne24_of_not_modEq_twentyfour_mod25 (m : ℕ)
    (hm : ¬ (m ≡ 24 [MOD 25])) :
    m % 25 ≠ 24 :=
  mod_ne_of_not_modEq_of_lt (q := 25) (r := 24) (m := m) (by decide) hm

/-- Negated `m ≡ 124 mod 125` implies direct residue inequality. -/
theorem mod125_ne124_of_not_modEq_onetwentyfour_mod125 (m : ℕ)
    (hm : ¬ (m ≡ 124 [MOD 125])) :
    m % 125 ≠ 124 :=
  mod_ne_of_not_modEq_of_lt (q := 125) (r := 124) (m := m) (by decide) hm

/-- Negated `m ≡ 624 mod 625` implies direct residue inequality. -/
theorem mod625_ne624_of_not_modEq_sixtwentyfour_mod625 (m : ℕ)
    (hm : ¬ (m ≡ 624 [MOD 625])) :
    m % 625 ≠ 624 :=
  mod_ne_of_not_modEq_of_lt (q := 625) (r := 624) (m := m) (by decide) hm

/-- Negated `m ≡ 3124 mod 3125` implies direct residue inequality. -/
theorem mod3125_ne3124_of_not_modEq_thirtyonetwentyfour_mod3125 (m : ℕ)
    (hm : ¬ (m ≡ 3124 [MOD 3125])) :
    m % 3125 ≠ 3124 :=
  mod_ne_of_not_modEq_of_lt (q := 3125) (r := 3124) (m := m) (by decide) hm

/-- Negated `m ≡ 5 mod 7` implies direct residue inequality. -/
theorem mod7_ne5_of_not_modEq_five_mod7 (m : ℕ) (hm : ¬ (m ≡ 5 [MOD 7])) :
    m % 7 ≠ 5 :=
  mod_ne_of_not_modEq_of_lt (q := 7) (r := 5) (m := m) (by decide) hm

/-- Negated `m ≡ 47 mod 49` implies direct residue inequality. -/
theorem mod49_ne47_of_not_modEq_fortyseven_mod49 (m : ℕ)
    (hm : ¬ (m ≡ 47 [MOD 49])) :
    m % 49 ≠ 47 :=
  mod_ne_of_not_modEq_of_lt (q := 49) (r := 47) (m := m) (by decide) hm

/-- Negated `m ≡ 341 mod 343` implies direct residue inequality. -/
theorem mod343_ne341_of_not_modEq_threefourtyone_mod343 (m : ℕ)
    (hm : ¬ (m ≡ 341 [MOD 343])) :
    m % 343 ≠ 341 :=
  mod_ne_of_not_modEq_of_lt (q := 343) (r := 341) (m := m) (by decide) hm

/-- Negated `m ≡ 2399 mod 2401` implies direct residue inequality. -/
theorem mod2401_ne2399_of_not_modEq_twentythreeninetynine_mod2401 (m : ℕ)
    (hm : ¬ (m ≡ 2399 [MOD 2401])) :
    m % 2401 ≠ 2399 :=
  mod_ne_of_not_modEq_of_lt (q := 2401) (r := 2399) (m := m) (by decide) hm

/-- Negated `m ≡ 16805 mod 16807` implies direct residue inequality. -/
theorem mod16807_ne16805_of_not_modEq_sixteeneightofive_mod16807 (m : ℕ)
    (hm : ¬ (m ≡ 16805 [MOD 16807])) :
    m % 16807 ≠ 16805 :=
  mod_ne_of_not_modEq_of_lt (q := 16807) (r := 16805) (m := m) (by decide) hm

/-- Negated `m ≡ 6 mod 11` implies direct residue inequality. -/
theorem mod11_ne6_of_not_modEq_six_mod11 (m : ℕ) (hm : ¬ (m ≡ 6 [MOD 11])) :
    m % 11 ≠ 6 :=
  mod_ne_of_not_modEq_of_lt (q := 11) (r := 6) (m := m) (by decide) hm

/-- Negated `m ≡ 116 mod 121` implies direct residue inequality. -/
theorem mod121_ne116_of_not_modEq_onesixteen_mod121 (m : ℕ)
    (hm : ¬ (m ≡ 116 [MOD 121])) :
    m % 121 ≠ 116 :=
  mod_ne_of_not_modEq_of_lt (q := 121) (r := 116) (m := m) (by decide) hm

/-- Negated `m ≡ 1326 mod 1331` implies direct residue inequality. -/
theorem mod1331_ne1326_of_not_modEq_thirteentwentysix_mod1331 (m : ℕ)
    (hm : ¬ (m ≡ 1326 [MOD 1331])) :
    m % 1331 ≠ 1326 :=
  mod_ne_of_not_modEq_of_lt (q := 1331) (r := 1326) (m := m) (by decide) hm

/-- Negated `m ≡ 14636 mod 14641` implies direct residue inequality. -/
theorem mod14641_ne14636_of_not_modEq_fourteensixthirtysix_mod14641 (m : ℕ)
    (hm : ¬ (m ≡ 14636 [MOD 14641])) :
    m % 14641 ≠ 14636 :=
  mod_ne_of_not_modEq_of_lt (q := 14641) (r := 14636) (m := m) (by decide) hm

/-- Negated `m ≡ 161046 mod 161051` implies direct residue inequality. -/
theorem mod161051_ne161046_of_not_modEq_onesixtyonezero46_mod161051 (m : ℕ)
    (hm : ¬ (m ≡ 161046 [MOD 161051])) :
    m % 161051 ≠ 161046 :=
  mod_ne_of_not_modEq_of_lt (q := 161051) (r := 161046) (m := m) (by decide) hm

/-- Concrete mod-5 power facts: direct residue equality gives `Nat.ModEq`. -/
theorem concrete_mod5_power_residue_eq_to_modEq_facts :
    (∀ m, m % 5 = 4 → m ≡ 4 [MOD 5]) ∧
      (∀ m, m % 25 = 24 → m ≡ 24 [MOD 25]) ∧
      (∀ m, m % 125 = 124 → m ≡ 124 [MOD 125]) ∧
      (∀ m, m % 625 = 624 → m ≡ 624 [MOD 625]) ∧
      (∀ m, m % 3125 = 3124 → m ≡ 3124 [MOD 3125]) := by
  exact ⟨modEq_four_mod5_of_mod5_eq4,
    modEq_twentyfour_mod25_of_mod25_eq24,
    modEq_onetwentyfour_mod125_of_mod125_eq124,
    modEq_sixtwentyfour_mod625_of_mod625_eq624,
    modEq_thirtyonetwentyfour_mod3125_of_mod3125_eq3124⟩

/-- Concrete mod-7 power facts: direct residue equality gives `Nat.ModEq`. -/
theorem concrete_mod7_power_residue_eq_to_modEq_facts :
    (∀ m, m % 7 = 5 → m ≡ 5 [MOD 7]) ∧
      (∀ m, m % 49 = 47 → m ≡ 47 [MOD 49]) ∧
      (∀ m, m % 343 = 341 → m ≡ 341 [MOD 343]) ∧
      (∀ m, m % 2401 = 2399 → m ≡ 2399 [MOD 2401]) ∧
      (∀ m, m % 16807 = 16805 → m ≡ 16805 [MOD 16807]) := by
  exact ⟨modEq_five_mod7_of_mod7_eq5,
    modEq_fortyseven_mod49_of_mod49_eq47,
    modEq_threefourtyone_mod343_of_mod343_eq341,
    modEq_twentythreeninetynine_mod2401_of_mod2401_eq2399,
    modEq_sixteeneightofive_mod16807_of_mod16807_eq16805⟩

/-- Concrete mod-11 power facts: direct residue equality gives `Nat.ModEq`. -/
theorem concrete_mod11_power_residue_eq_to_modEq_facts :
    (∀ m, m % 11 = 6 → m ≡ 6 [MOD 11]) ∧
      (∀ m, m % 121 = 116 → m ≡ 116 [MOD 121]) ∧
      (∀ m, m % 1331 = 1326 → m ≡ 1326 [MOD 1331]) ∧
      (∀ m, m % 14641 = 14636 → m ≡ 14636 [MOD 14641]) ∧
      (∀ m, m % 161051 = 161046 → m ≡ 161046 [MOD 161051]) := by
  exact ⟨modEq_six_mod11_of_mod11_eq6,
    modEq_onesixteen_mod121_of_mod121_eq116,
    modEq_thirteentwentysix_mod1331_of_mod1331_eq1326,
    modEq_fourteensixthirtysix_mod14641_of_mod14641_eq14636,
    modEq_onesixtyonezero46_mod161051_of_mod161051_eq161046⟩

/-- Concrete mod-5 power facts: `Nat.ModEq` gives direct residue equality. -/
theorem concrete_mod5_power_modEq_to_residue_eq_facts :
    (∀ m, m ≡ 4 [MOD 5] → m % 5 = 4) ∧
      (∀ m, m ≡ 24 [MOD 25] → m % 25 = 24) ∧
      (∀ m, m ≡ 124 [MOD 125] → m % 125 = 124) ∧
      (∀ m, m ≡ 624 [MOD 625] → m % 625 = 624) ∧
      (∀ m, m ≡ 3124 [MOD 3125] → m % 3125 = 3124) := by
  exact ⟨mod5_eq4_of_modEq_four_mod5,
    mod25_eq24_of_modEq_twentyfour_mod25,
    mod125_eq124_of_modEq_onetwentyfour_mod125,
    mod625_eq624_of_modEq_sixtwentyfour_mod625,
    mod3125_eq3124_of_modEq_thirtyonetwentyfour_mod3125⟩

/-- Concrete mod-7 power facts: `Nat.ModEq` gives direct residue equality. -/
theorem concrete_mod7_power_modEq_to_residue_eq_facts :
    (∀ m, m ≡ 5 [MOD 7] → m % 7 = 5) ∧
      (∀ m, m ≡ 47 [MOD 49] → m % 49 = 47) ∧
      (∀ m, m ≡ 341 [MOD 343] → m % 343 = 341) ∧
      (∀ m, m ≡ 2399 [MOD 2401] → m % 2401 = 2399) ∧
      (∀ m, m ≡ 16805 [MOD 16807] → m % 16807 = 16805) := by
  exact ⟨mod7_eq5_of_modEq_five_mod7,
    mod49_eq47_of_modEq_fortyseven_mod49,
    mod343_eq341_of_modEq_threefourtyone_mod343,
    mod2401_eq2399_of_modEq_twentythreeninetynine_mod2401,
    mod16807_eq16805_of_modEq_sixteeneightofive_mod16807⟩

/-- Concrete mod-11 power facts: `Nat.ModEq` gives direct residue equality. -/
theorem concrete_mod11_power_modEq_to_residue_eq_facts :
    (∀ m, m ≡ 6 [MOD 11] → m % 11 = 6) ∧
      (∀ m, m ≡ 116 [MOD 121] → m % 121 = 116) ∧
      (∀ m, m ≡ 1326 [MOD 1331] → m % 1331 = 1326) ∧
      (∀ m, m ≡ 14636 [MOD 14641] → m % 14641 = 14636) ∧
      (∀ m, m ≡ 161046 [MOD 161051] → m % 161051 = 161046) := by
  exact ⟨mod11_eq6_of_modEq_six_mod11,
    mod121_eq116_of_modEq_onesixteen_mod121,
    mod1331_eq1326_of_modEq_thirteentwentysix_mod1331,
    mod14641_eq14636_of_modEq_fourteensixthirtysix_mod14641,
    mod161051_eq161046_of_modEq_onesixtyonezero46_mod161051⟩

/-- Concrete mod-5 power facts: residue inequality gives negated `Nat.ModEq`. -/
theorem concrete_mod5_power_residue_ne_to_not_modEq_facts :
    (∀ m, m % 5 ≠ 4 → ¬ (m ≡ 4 [MOD 5])) ∧
      (∀ m, m % 25 ≠ 24 → ¬ (m ≡ 24 [MOD 25])) ∧
      (∀ m, m % 125 ≠ 124 → ¬ (m ≡ 124 [MOD 125])) ∧
      (∀ m, m % 625 ≠ 624 → ¬ (m ≡ 624 [MOD 625])) ∧
      (∀ m, m % 3125 ≠ 3124 → ¬ (m ≡ 3124 [MOD 3125])) := by
  exact ⟨not_modEq_four_mod5_of_mod5_ne4,
    not_modEq_twentyfour_mod25_of_mod25_ne24,
    not_modEq_onetwentyfour_mod125_of_mod125_ne124,
    not_modEq_sixtwentyfour_mod625_of_mod625_ne624,
    not_modEq_thirtyonetwentyfour_mod3125_of_mod3125_ne3124⟩

/-- Concrete mod-7 power facts: residue inequality gives negated `Nat.ModEq`. -/
theorem concrete_mod7_power_residue_ne_to_not_modEq_facts :
    (∀ m, m % 7 ≠ 5 → ¬ (m ≡ 5 [MOD 7])) ∧
      (∀ m, m % 49 ≠ 47 → ¬ (m ≡ 47 [MOD 49])) ∧
      (∀ m, m % 343 ≠ 341 → ¬ (m ≡ 341 [MOD 343])) ∧
      (∀ m, m % 2401 ≠ 2399 → ¬ (m ≡ 2399 [MOD 2401])) ∧
      (∀ m, m % 16807 ≠ 16805 → ¬ (m ≡ 16805 [MOD 16807])) := by
  exact ⟨not_modEq_five_mod7_of_mod7_ne5,
    not_modEq_fortyseven_mod49_of_mod49_ne47,
    not_modEq_threefourtyone_mod343_of_mod343_ne341,
    not_modEq_twentythreeninetynine_mod2401_of_mod2401_ne2399,
    not_modEq_sixteeneightofive_mod16807_of_mod16807_ne16805⟩

/-- Concrete mod-11 power facts: residue inequality gives negated `Nat.ModEq`. -/
theorem concrete_mod11_power_residue_ne_to_not_modEq_facts :
    (∀ m, m % 11 ≠ 6 → ¬ (m ≡ 6 [MOD 11])) ∧
      (∀ m, m % 121 ≠ 116 → ¬ (m ≡ 116 [MOD 121])) ∧
      (∀ m, m % 1331 ≠ 1326 → ¬ (m ≡ 1326 [MOD 1331])) ∧
      (∀ m, m % 14641 ≠ 14636 → ¬ (m ≡ 14636 [MOD 14641])) ∧
      (∀ m, m % 161051 ≠ 161046 → ¬ (m ≡ 161046 [MOD 161051])) := by
  exact ⟨not_modEq_six_mod11_of_mod11_ne6,
    not_modEq_onesixteen_mod121_of_mod121_ne116,
    not_modEq_thirteentwentysix_mod1331_of_mod1331_ne1326,
    not_modEq_fourteensixthirtysix_mod14641_of_mod14641_ne14636,
    not_modEq_onesixtyonezero46_mod161051_of_mod161051_ne161046⟩

/-- Concrete mod-5 power facts: negated `Nat.ModEq` gives residue inequality. -/
theorem concrete_mod5_power_not_modEq_to_residue_ne_facts :
    (∀ m, ¬ (m ≡ 4 [MOD 5]) → m % 5 ≠ 4) ∧
      (∀ m, ¬ (m ≡ 24 [MOD 25]) → m % 25 ≠ 24) ∧
      (∀ m, ¬ (m ≡ 124 [MOD 125]) → m % 125 ≠ 124) ∧
      (∀ m, ¬ (m ≡ 624 [MOD 625]) → m % 625 ≠ 624) ∧
      (∀ m, ¬ (m ≡ 3124 [MOD 3125]) → m % 3125 ≠ 3124) := by
  exact ⟨mod5_ne4_of_not_modEq_four_mod5,
    mod25_ne24_of_not_modEq_twentyfour_mod25,
    mod125_ne124_of_not_modEq_onetwentyfour_mod125,
    mod625_ne624_of_not_modEq_sixtwentyfour_mod625,
    mod3125_ne3124_of_not_modEq_thirtyonetwentyfour_mod3125⟩

/-- Concrete mod-7 power facts: negated `Nat.ModEq` gives residue inequality. -/
theorem concrete_mod7_power_not_modEq_to_residue_ne_facts :
    (∀ m, ¬ (m ≡ 5 [MOD 7]) → m % 7 ≠ 5) ∧
      (∀ m, ¬ (m ≡ 47 [MOD 49]) → m % 49 ≠ 47) ∧
      (∀ m, ¬ (m ≡ 341 [MOD 343]) → m % 343 ≠ 341) ∧
      (∀ m, ¬ (m ≡ 2399 [MOD 2401]) → m % 2401 ≠ 2399) ∧
      (∀ m, ¬ (m ≡ 16805 [MOD 16807]) → m % 16807 ≠ 16805) := by
  exact ⟨mod7_ne5_of_not_modEq_five_mod7,
    mod49_ne47_of_not_modEq_fortyseven_mod49,
    mod343_ne341_of_not_modEq_threefourtyone_mod343,
    mod2401_ne2399_of_not_modEq_twentythreeninetynine_mod2401,
    mod16807_ne16805_of_not_modEq_sixteeneightofive_mod16807⟩

/-- Concrete mod-11 power facts: negated `Nat.ModEq` gives residue inequality. -/
theorem concrete_mod11_power_not_modEq_to_residue_ne_facts :
    (∀ m, ¬ (m ≡ 6 [MOD 11]) → m % 11 ≠ 6) ∧
      (∀ m, ¬ (m ≡ 116 [MOD 121]) → m % 121 ≠ 116) ∧
      (∀ m, ¬ (m ≡ 1326 [MOD 1331]) → m % 1331 ≠ 1326) ∧
      (∀ m, ¬ (m ≡ 14636 [MOD 14641]) → m % 14641 ≠ 14636) ∧
      (∀ m, ¬ (m ≡ 161046 [MOD 161051]) → m % 161051 ≠ 161046) := by
  exact ⟨mod11_ne6_of_not_modEq_six_mod11,
    mod121_ne116_of_not_modEq_onesixteen_mod121,
    mod1331_ne1326_of_not_modEq_thirteentwentysix_mod1331,
    mod14641_ne14636_of_not_modEq_fourteensixthirtysix_mod14641,
    mod161051_ne161046_of_not_modEq_onesixtyonezero46_mod161051⟩

/-- Shifted divisibility by `5` gives the `4 mod 5` `Nat.ModEq`. -/
theorem modEq_four_mod5_of_dvd_add_one (m : ℕ) (hm : 5 ∣ m + 1) :
    m ≡ 4 [MOD 5] :=
  (modEq_four_mod5_iff_dvd_add_one m).2 hm

/-- Shifted divisibility by `25` gives the `24 mod 25` `Nat.ModEq`. -/
theorem modEq_twentyfour_mod25_of_dvd_add_one (m : ℕ) (hm : 25 ∣ m + 1) :
    m ≡ 24 [MOD 25] :=
  (modEq_twentyfour_mod25_iff_dvd_add_one m).2 hm

/-- Shifted divisibility by `125` gives the `124 mod 125` `Nat.ModEq`. -/
theorem modEq_onetwentyfour_mod125_of_dvd_add_one (m : ℕ)
    (hm : 125 ∣ m + 1) :
    m ≡ 124 [MOD 125] :=
  (modEq_onetwentyfour_mod125_iff_dvd_add_one m).2 hm

/-- Shifted divisibility by `625` gives the `624 mod 625` `Nat.ModEq`. -/
theorem modEq_sixtwentyfour_mod625_of_dvd_add_one (m : ℕ)
    (hm : 625 ∣ m + 1) :
    m ≡ 624 [MOD 625] :=
  (modEq_sixtwentyfour_mod625_iff_dvd_add_one m).2 hm

/-- Shifted divisibility by `3125` gives the `3124 mod 3125` `Nat.ModEq`. -/
theorem modEq_thirtyonetwentyfour_mod3125_of_dvd_add_one (m : ℕ)
    (hm : 3125 ∣ m + 1) :
    m ≡ 3124 [MOD 3125] :=
  (modEq_thirtyonetwentyfour_mod3125_iff_dvd_add_one m).2 hm

/-- Shifted divisibility by `7` gives the `5 mod 7` `Nat.ModEq`. -/
theorem modEq_five_mod7_of_dvd_add_two (m : ℕ) (hm : 7 ∣ m + 2) :
    m ≡ 5 [MOD 7] :=
  (modEq_five_mod7_iff_dvd_add_two m).2 hm

/-- Shifted divisibility by `49` gives the `47 mod 49` `Nat.ModEq`. -/
theorem modEq_fortyseven_mod49_of_dvd_add_two (m : ℕ) (hm : 49 ∣ m + 2) :
    m ≡ 47 [MOD 49] :=
  (modEq_fortyseven_mod49_iff_dvd_add_two m).2 hm

/-- Shifted divisibility by `343` gives the `341 mod 343` `Nat.ModEq`. -/
theorem modEq_threefourtyone_mod343_of_dvd_add_two (m : ℕ)
    (hm : 343 ∣ m + 2) :
    m ≡ 341 [MOD 343] :=
  (modEq_threefourtyone_mod343_iff_dvd_add_two m).2 hm

/-- Shifted divisibility by `2401` gives the `2399 mod 2401` `Nat.ModEq`. -/
theorem modEq_twentythreeninetynine_mod2401_of_dvd_add_two (m : ℕ)
    (hm : 2401 ∣ m + 2) :
    m ≡ 2399 [MOD 2401] :=
  (modEq_twentythreeninetynine_mod2401_iff_dvd_add_two m).2 hm

/-- Shifted divisibility by `16807` gives the `16805 mod 16807` `Nat.ModEq`. -/
theorem modEq_sixteeneightofive_mod16807_of_dvd_add_two (m : ℕ)
    (hm : 16807 ∣ m + 2) :
    m ≡ 16805 [MOD 16807] :=
  (modEq_sixteeneightofive_mod16807_iff_dvd_add_two m).2 hm

/-- Shifted divisibility by `11` gives the `6 mod 11` `Nat.ModEq`. -/
theorem modEq_six_mod11_of_dvd_add_five (m : ℕ) (hm : 11 ∣ m + 5) :
    m ≡ 6 [MOD 11] :=
  (modEq_six_mod11_iff_dvd_add_five m).2 hm

/-- Shifted divisibility by `121` gives the `116 mod 121` `Nat.ModEq`. -/
theorem modEq_onesixteen_mod121_of_dvd_add_five (m : ℕ)
    (hm : 121 ∣ m + 5) :
    m ≡ 116 [MOD 121] :=
  (modEq_onesixteen_mod121_iff_dvd_add_five m).2 hm

/-- Shifted divisibility by `1331` gives the `1326 mod 1331` `Nat.ModEq`. -/
theorem modEq_thirteentwentysix_mod1331_of_dvd_add_five (m : ℕ)
    (hm : 1331 ∣ m + 5) :
    m ≡ 1326 [MOD 1331] :=
  (modEq_thirteentwentysix_mod1331_iff_dvd_add_five m).2 hm

/-- Shifted divisibility by `14641` gives the `14636 mod 14641` `Nat.ModEq`. -/
theorem modEq_fourteensixthirtysix_mod14641_of_dvd_add_five (m : ℕ)
    (hm : 14641 ∣ m + 5) :
    m ≡ 14636 [MOD 14641] :=
  (modEq_fourteensixthirtysix_mod14641_iff_dvd_add_five m).2 hm

/-- Shifted divisibility by `161051` gives the `161046 mod 161051` `Nat.ModEq`. -/
theorem modEq_onesixtyonezero46_mod161051_of_dvd_add_five (m : ℕ)
    (hm : 161051 ∣ m + 5) :
    m ≡ 161046 [MOD 161051] :=
  (modEq_onesixtyonezero46_mod161051_iff_dvd_add_five m).2 hm

/-- The `4 mod 5` `Nat.ModEq` gives shifted divisibility by `5`. -/
theorem dvd_add_one_of_modEq_four_mod5 (m : ℕ) (hm : m ≡ 4 [MOD 5]) :
    5 ∣ m + 1 :=
  (modEq_four_mod5_iff_dvd_add_one m).1 hm

/-- The `24 mod 25` `Nat.ModEq` gives shifted divisibility by `25`. -/
theorem dvd_add_one_of_modEq_twentyfour_mod25 (m : ℕ) (hm : m ≡ 24 [MOD 25]) :
    25 ∣ m + 1 :=
  (modEq_twentyfour_mod25_iff_dvd_add_one m).1 hm

/-- The `124 mod 125` `Nat.ModEq` gives shifted divisibility by `125`. -/
theorem dvd_add_one_of_modEq_onetwentyfour_mod125 (m : ℕ)
    (hm : m ≡ 124 [MOD 125]) :
    125 ∣ m + 1 :=
  (modEq_onetwentyfour_mod125_iff_dvd_add_one m).1 hm

/-- The `624 mod 625` `Nat.ModEq` gives shifted divisibility by `625`. -/
theorem dvd_add_one_of_modEq_sixtwentyfour_mod625 (m : ℕ)
    (hm : m ≡ 624 [MOD 625]) :
    625 ∣ m + 1 :=
  (modEq_sixtwentyfour_mod625_iff_dvd_add_one m).1 hm

/-- The `3124 mod 3125` `Nat.ModEq` gives shifted divisibility by `3125`. -/
theorem dvd_add_one_of_modEq_thirtyonetwentyfour_mod3125 (m : ℕ)
    (hm : m ≡ 3124 [MOD 3125]) :
    3125 ∣ m + 1 :=
  (modEq_thirtyonetwentyfour_mod3125_iff_dvd_add_one m).1 hm

/-- The `5 mod 7` `Nat.ModEq` gives shifted divisibility by `7`. -/
theorem dvd_add_two_of_modEq_five_mod7 (m : ℕ) (hm : m ≡ 5 [MOD 7]) :
    7 ∣ m + 2 :=
  (modEq_five_mod7_iff_dvd_add_two m).1 hm

/-- The `47 mod 49` `Nat.ModEq` gives shifted divisibility by `49`. -/
theorem dvd_add_two_of_modEq_fortyseven_mod49 (m : ℕ) (hm : m ≡ 47 [MOD 49]) :
    49 ∣ m + 2 :=
  (modEq_fortyseven_mod49_iff_dvd_add_two m).1 hm

/-- The `341 mod 343` `Nat.ModEq` gives shifted divisibility by `343`. -/
theorem dvd_add_two_of_modEq_threefourtyone_mod343 (m : ℕ)
    (hm : m ≡ 341 [MOD 343]) :
    343 ∣ m + 2 :=
  (modEq_threefourtyone_mod343_iff_dvd_add_two m).1 hm

/-- The `2399 mod 2401` `Nat.ModEq` gives shifted divisibility by `2401`. -/
theorem dvd_add_two_of_modEq_twentythreeninetynine_mod2401 (m : ℕ)
    (hm : m ≡ 2399 [MOD 2401]) :
    2401 ∣ m + 2 :=
  (modEq_twentythreeninetynine_mod2401_iff_dvd_add_two m).1 hm

/-- The `16805 mod 16807` `Nat.ModEq` gives shifted divisibility by `16807`. -/
theorem dvd_add_two_of_modEq_sixteeneightofive_mod16807 (m : ℕ)
    (hm : m ≡ 16805 [MOD 16807]) :
    16807 ∣ m + 2 :=
  (modEq_sixteeneightofive_mod16807_iff_dvd_add_two m).1 hm

/-- The `6 mod 11` `Nat.ModEq` gives shifted divisibility by `11`. -/
theorem dvd_add_five_of_modEq_six_mod11 (m : ℕ) (hm : m ≡ 6 [MOD 11]) :
    11 ∣ m + 5 :=
  (modEq_six_mod11_iff_dvd_add_five m).1 hm

/-- The `116 mod 121` `Nat.ModEq` gives shifted divisibility by `121`. -/
theorem dvd_add_five_of_modEq_onesixteen_mod121 (m : ℕ)
    (hm : m ≡ 116 [MOD 121]) :
    121 ∣ m + 5 :=
  (modEq_onesixteen_mod121_iff_dvd_add_five m).1 hm

/-- The `1326 mod 1331` `Nat.ModEq` gives shifted divisibility by `1331`. -/
theorem dvd_add_five_of_modEq_thirteentwentysix_mod1331 (m : ℕ)
    (hm : m ≡ 1326 [MOD 1331]) :
    1331 ∣ m + 5 :=
  (modEq_thirteentwentysix_mod1331_iff_dvd_add_five m).1 hm

/-- The `14636 mod 14641` `Nat.ModEq` gives shifted divisibility by `14641`. -/
theorem dvd_add_five_of_modEq_fourteensixthirtysix_mod14641 (m : ℕ)
    (hm : m ≡ 14636 [MOD 14641]) :
    14641 ∣ m + 5 :=
  (modEq_fourteensixthirtysix_mod14641_iff_dvd_add_five m).1 hm

/-- The `161046 mod 161051` `Nat.ModEq` gives shifted divisibility by `161051`. -/
theorem dvd_add_five_of_modEq_onesixtyonezero46_mod161051 (m : ℕ)
    (hm : m ≡ 161046 [MOD 161051]) :
    161051 ∣ m + 5 :=
  (modEq_onesixtyonezero46_mod161051_iff_dvd_add_five m).1 hm

/-- Shifted nondivisibility by `5` gives negated `4 mod 5` `Nat.ModEq`. -/
theorem not_modEq_four_mod5_of_not_dvd_add_one (m : ℕ) (hm : ¬ (5 ∣ m + 1)) :
    ¬ (m ≡ 4 [MOD 5]) :=
  (not_modEq_four_mod5_iff_not_dvd_add_one m).2 hm

/-- Shifted nondivisibility by `25` gives negated `24 mod 25` `Nat.ModEq`. -/
theorem not_modEq_twentyfour_mod25_of_not_dvd_add_one (m : ℕ)
    (hm : ¬ (25 ∣ m + 1)) :
    ¬ (m ≡ 24 [MOD 25]) :=
  (not_modEq_twentyfour_mod25_iff_not_dvd_add_one m).2 hm

/-- Shifted nondivisibility by `125` gives negated `124 mod 125` `Nat.ModEq`. -/
theorem not_modEq_onetwentyfour_mod125_of_not_dvd_add_one (m : ℕ)
    (hm : ¬ (125 ∣ m + 1)) :
    ¬ (m ≡ 124 [MOD 125]) :=
  (not_modEq_onetwentyfour_mod125_iff_not_dvd_add_one m).2 hm

/-- Shifted nondivisibility by `625` gives negated `624 mod 625` `Nat.ModEq`. -/
theorem not_modEq_sixtwentyfour_mod625_of_not_dvd_add_one (m : ℕ)
    (hm : ¬ (625 ∣ m + 1)) :
    ¬ (m ≡ 624 [MOD 625]) :=
  (not_modEq_sixtwentyfour_mod625_iff_not_dvd_add_one m).2 hm

/-- Shifted nondivisibility by `3125` gives negated `3124 mod 3125` `Nat.ModEq`. -/
theorem not_modEq_thirtyonetwentyfour_mod3125_of_not_dvd_add_one (m : ℕ)
    (hm : ¬ (3125 ∣ m + 1)) :
    ¬ (m ≡ 3124 [MOD 3125]) :=
  (not_modEq_thirtyonetwentyfour_mod3125_iff_not_dvd_add_one m).2 hm

/-- Shifted nondivisibility by `7` gives negated `5 mod 7` `Nat.ModEq`. -/
theorem not_modEq_five_mod7_of_not_dvd_add_two (m : ℕ) (hm : ¬ (7 ∣ m + 2)) :
    ¬ (m ≡ 5 [MOD 7]) :=
  (not_modEq_five_mod7_iff_not_dvd_add_two m).2 hm

/-- Shifted nondivisibility by `49` gives negated `47 mod 49` `Nat.ModEq`. -/
theorem not_modEq_fortyseven_mod49_of_not_dvd_add_two (m : ℕ)
    (hm : ¬ (49 ∣ m + 2)) :
    ¬ (m ≡ 47 [MOD 49]) :=
  (not_modEq_fortyseven_mod49_iff_not_dvd_add_two m).2 hm

/-- Shifted nondivisibility by `343` gives negated `341 mod 343` `Nat.ModEq`. -/
theorem not_modEq_threefourtyone_mod343_of_not_dvd_add_two (m : ℕ)
    (hm : ¬ (343 ∣ m + 2)) :
    ¬ (m ≡ 341 [MOD 343]) :=
  (not_modEq_threefourtyone_mod343_iff_not_dvd_add_two m).2 hm

/-- Shifted nondivisibility by `2401` gives negated `2399 mod 2401` `Nat.ModEq`. -/
theorem not_modEq_twentythreeninetynine_mod2401_of_not_dvd_add_two (m : ℕ)
    (hm : ¬ (2401 ∣ m + 2)) :
    ¬ (m ≡ 2399 [MOD 2401]) :=
  (not_modEq_twentythreeninetynine_mod2401_iff_not_dvd_add_two m).2 hm

/-- Shifted nondivisibility by `16807` gives negated `16805 mod 16807` `Nat.ModEq`. -/
theorem not_modEq_sixteeneightofive_mod16807_of_not_dvd_add_two (m : ℕ)
    (hm : ¬ (16807 ∣ m + 2)) :
    ¬ (m ≡ 16805 [MOD 16807]) :=
  (not_modEq_sixteeneightofive_mod16807_iff_not_dvd_add_two m).2 hm

/-- Shifted nondivisibility by `11` gives negated `6 mod 11` `Nat.ModEq`. -/
theorem not_modEq_six_mod11_of_not_dvd_add_five (m : ℕ)
    (hm : ¬ (11 ∣ m + 5)) :
    ¬ (m ≡ 6 [MOD 11]) :=
  (not_modEq_six_mod11_iff_not_dvd_add_five m).2 hm

/-- Shifted nondivisibility by `121` gives negated `116 mod 121` `Nat.ModEq`. -/
theorem not_modEq_onesixteen_mod121_of_not_dvd_add_five (m : ℕ)
    (hm : ¬ (121 ∣ m + 5)) :
    ¬ (m ≡ 116 [MOD 121]) :=
  (not_modEq_onesixteen_mod121_iff_not_dvd_add_five m).2 hm

/-- Shifted nondivisibility by `1331` gives negated `1326 mod 1331` `Nat.ModEq`. -/
theorem not_modEq_thirteentwentysix_mod1331_of_not_dvd_add_five (m : ℕ)
    (hm : ¬ (1331 ∣ m + 5)) :
    ¬ (m ≡ 1326 [MOD 1331]) :=
  (not_modEq_thirteentwentysix_mod1331_iff_not_dvd_add_five m).2 hm

/-- Shifted nondivisibility by `14641` gives negated `14636 mod 14641` `Nat.ModEq`. -/
theorem not_modEq_fourteensixthirtysix_mod14641_of_not_dvd_add_five (m : ℕ)
    (hm : ¬ (14641 ∣ m + 5)) :
    ¬ (m ≡ 14636 [MOD 14641]) :=
  (not_modEq_fourteensixthirtysix_mod14641_iff_not_dvd_add_five m).2 hm

/-- Shifted nondivisibility by `161051` gives negated `161046 mod 161051` `Nat.ModEq`. -/
theorem not_modEq_onesixtyonezero46_mod161051_of_not_dvd_add_five (m : ℕ)
    (hm : ¬ (161051 ∣ m + 5)) :
    ¬ (m ≡ 161046 [MOD 161051]) :=
  (not_modEq_onesixtyonezero46_mod161051_iff_not_dvd_add_five m).2 hm

/-- Negated `4 mod 5` `Nat.ModEq` gives shifted nondivisibility by `5`. -/
theorem not_dvd_add_one_of_not_modEq_four_mod5 (m : ℕ) (hm : ¬ (m ≡ 4 [MOD 5])) :
    ¬ (5 ∣ m + 1) :=
  (not_modEq_four_mod5_iff_not_dvd_add_one m).1 hm

/-- Negated `24 mod 25` `Nat.ModEq` gives shifted nondivisibility by `25`. -/
theorem not_dvd_add_one_of_not_modEq_twentyfour_mod25 (m : ℕ)
    (hm : ¬ (m ≡ 24 [MOD 25])) :
    ¬ (25 ∣ m + 1) :=
  (not_modEq_twentyfour_mod25_iff_not_dvd_add_one m).1 hm

/-- Negated `124 mod 125` `Nat.ModEq` gives shifted nondivisibility by `125`. -/
theorem not_dvd_add_one_of_not_modEq_onetwentyfour_mod125 (m : ℕ)
    (hm : ¬ (m ≡ 124 [MOD 125])) :
    ¬ (125 ∣ m + 1) :=
  (not_modEq_onetwentyfour_mod125_iff_not_dvd_add_one m).1 hm

/-- Negated `624 mod 625` `Nat.ModEq` gives shifted nondivisibility by `625`. -/
theorem not_dvd_add_one_of_not_modEq_sixtwentyfour_mod625 (m : ℕ)
    (hm : ¬ (m ≡ 624 [MOD 625])) :
    ¬ (625 ∣ m + 1) :=
  (not_modEq_sixtwentyfour_mod625_iff_not_dvd_add_one m).1 hm

/-- Negated `3124 mod 3125` `Nat.ModEq` gives shifted nondivisibility by `3125`. -/
theorem not_dvd_add_one_of_not_modEq_thirtyonetwentyfour_mod3125 (m : ℕ)
    (hm : ¬ (m ≡ 3124 [MOD 3125])) :
    ¬ (3125 ∣ m + 1) :=
  (not_modEq_thirtyonetwentyfour_mod3125_iff_not_dvd_add_one m).1 hm

/-- Negated `5 mod 7` `Nat.ModEq` gives shifted nondivisibility by `7`. -/
theorem not_dvd_add_two_of_not_modEq_five_mod7 (m : ℕ) (hm : ¬ (m ≡ 5 [MOD 7])) :
    ¬ (7 ∣ m + 2) :=
  (not_modEq_five_mod7_iff_not_dvd_add_two m).1 hm

/-- Negated `47 mod 49` `Nat.ModEq` gives shifted nondivisibility by `49`. -/
theorem not_dvd_add_two_of_not_modEq_fortyseven_mod49 (m : ℕ)
    (hm : ¬ (m ≡ 47 [MOD 49])) :
    ¬ (49 ∣ m + 2) :=
  (not_modEq_fortyseven_mod49_iff_not_dvd_add_two m).1 hm

/-- Negated `341 mod 343` `Nat.ModEq` gives shifted nondivisibility by `343`. -/
theorem not_dvd_add_two_of_not_modEq_threefourtyone_mod343 (m : ℕ)
    (hm : ¬ (m ≡ 341 [MOD 343])) :
    ¬ (343 ∣ m + 2) :=
  (not_modEq_threefourtyone_mod343_iff_not_dvd_add_two m).1 hm

/-- Negated `2399 mod 2401` `Nat.ModEq` gives shifted nondivisibility by `2401`. -/
theorem not_dvd_add_two_of_not_modEq_twentythreeninetynine_mod2401 (m : ℕ)
    (hm : ¬ (m ≡ 2399 [MOD 2401])) :
    ¬ (2401 ∣ m + 2) :=
  (not_modEq_twentythreeninetynine_mod2401_iff_not_dvd_add_two m).1 hm

/-- Negated `16805 mod 16807` `Nat.ModEq` gives shifted nondivisibility by `16807`. -/
theorem not_dvd_add_two_of_not_modEq_sixteeneightofive_mod16807 (m : ℕ)
    (hm : ¬ (m ≡ 16805 [MOD 16807])) :
    ¬ (16807 ∣ m + 2) :=
  (not_modEq_sixteeneightofive_mod16807_iff_not_dvd_add_two m).1 hm

/-- Negated `6 mod 11` `Nat.ModEq` gives shifted nondivisibility by `11`. -/
theorem not_dvd_add_five_of_not_modEq_six_mod11 (m : ℕ)
    (hm : ¬ (m ≡ 6 [MOD 11])) :
    ¬ (11 ∣ m + 5) :=
  (not_modEq_six_mod11_iff_not_dvd_add_five m).1 hm

/-- Negated `116 mod 121` `Nat.ModEq` gives shifted nondivisibility by `121`. -/
theorem not_dvd_add_five_of_not_modEq_onesixteen_mod121 (m : ℕ)
    (hm : ¬ (m ≡ 116 [MOD 121])) :
    ¬ (121 ∣ m + 5) :=
  (not_modEq_onesixteen_mod121_iff_not_dvd_add_five m).1 hm

/-- Negated `1326 mod 1331` `Nat.ModEq` gives shifted nondivisibility by `1331`. -/
theorem not_dvd_add_five_of_not_modEq_thirteentwentysix_mod1331 (m : ℕ)
    (hm : ¬ (m ≡ 1326 [MOD 1331])) :
    ¬ (1331 ∣ m + 5) :=
  (not_modEq_thirteentwentysix_mod1331_iff_not_dvd_add_five m).1 hm

/-- Negated `14636 mod 14641` `Nat.ModEq` gives shifted nondivisibility by `14641`. -/
theorem not_dvd_add_five_of_not_modEq_fourteensixthirtysix_mod14641 (m : ℕ)
    (hm : ¬ (m ≡ 14636 [MOD 14641])) :
    ¬ (14641 ∣ m + 5) :=
  (not_modEq_fourteensixthirtysix_mod14641_iff_not_dvd_add_five m).1 hm

/-- Negated `161046 mod 161051` `Nat.ModEq` gives shifted nondivisibility by `161051`. -/
theorem not_dvd_add_five_of_not_modEq_onesixtyonezero46_mod161051 (m : ℕ)
    (hm : ¬ (m ≡ 161046 [MOD 161051])) :
    ¬ (161051 ∣ m + 5) :=
  (not_modEq_onesixtyonezero46_mod161051_iff_not_dvd_add_five m).1 hm

/-- Concrete mod-5 power facts: shifted divisibility gives `Nat.ModEq`. -/
theorem concrete_mod5_power_dvd_add_one_to_modEq_facts :
    (∀ m, 5 ∣ m + 1 → m ≡ 4 [MOD 5]) ∧
      (∀ m, 25 ∣ m + 1 → m ≡ 24 [MOD 25]) ∧
      (∀ m, 125 ∣ m + 1 → m ≡ 124 [MOD 125]) ∧
      (∀ m, 625 ∣ m + 1 → m ≡ 624 [MOD 625]) ∧
      (∀ m, 3125 ∣ m + 1 → m ≡ 3124 [MOD 3125]) := by
  exact ⟨modEq_four_mod5_of_dvd_add_one,
    modEq_twentyfour_mod25_of_dvd_add_one,
    modEq_onetwentyfour_mod125_of_dvd_add_one,
    modEq_sixtwentyfour_mod625_of_dvd_add_one,
    modEq_thirtyonetwentyfour_mod3125_of_dvd_add_one⟩

/-- Concrete mod-7 power facts: shifted divisibility gives `Nat.ModEq`. -/
theorem concrete_mod7_power_dvd_add_two_to_modEq_facts :
    (∀ m, 7 ∣ m + 2 → m ≡ 5 [MOD 7]) ∧
      (∀ m, 49 ∣ m + 2 → m ≡ 47 [MOD 49]) ∧
      (∀ m, 343 ∣ m + 2 → m ≡ 341 [MOD 343]) ∧
      (∀ m, 2401 ∣ m + 2 → m ≡ 2399 [MOD 2401]) ∧
      (∀ m, 16807 ∣ m + 2 → m ≡ 16805 [MOD 16807]) := by
  exact ⟨modEq_five_mod7_of_dvd_add_two,
    modEq_fortyseven_mod49_of_dvd_add_two,
    modEq_threefourtyone_mod343_of_dvd_add_two,
    modEq_twentythreeninetynine_mod2401_of_dvd_add_two,
    modEq_sixteeneightofive_mod16807_of_dvd_add_two⟩

/-- Concrete mod-11 power facts: shifted divisibility gives `Nat.ModEq`. -/
theorem concrete_mod11_power_dvd_add_five_to_modEq_facts :
    (∀ m, 11 ∣ m + 5 → m ≡ 6 [MOD 11]) ∧
      (∀ m, 121 ∣ m + 5 → m ≡ 116 [MOD 121]) ∧
      (∀ m, 1331 ∣ m + 5 → m ≡ 1326 [MOD 1331]) ∧
      (∀ m, 14641 ∣ m + 5 → m ≡ 14636 [MOD 14641]) ∧
      (∀ m, 161051 ∣ m + 5 → m ≡ 161046 [MOD 161051]) := by
  exact ⟨modEq_six_mod11_of_dvd_add_five,
    modEq_onesixteen_mod121_of_dvd_add_five,
    modEq_thirteentwentysix_mod1331_of_dvd_add_five,
    modEq_fourteensixthirtysix_mod14641_of_dvd_add_five,
    modEq_onesixtyonezero46_mod161051_of_dvd_add_five⟩

/-- Concrete mod-5 power facts: `Nat.ModEq` gives shifted divisibility. -/
theorem concrete_mod5_power_modEq_to_dvd_add_one_facts :
    (∀ m, m ≡ 4 [MOD 5] → 5 ∣ m + 1) ∧
      (∀ m, m ≡ 24 [MOD 25] → 25 ∣ m + 1) ∧
      (∀ m, m ≡ 124 [MOD 125] → 125 ∣ m + 1) ∧
      (∀ m, m ≡ 624 [MOD 625] → 625 ∣ m + 1) ∧
      (∀ m, m ≡ 3124 [MOD 3125] → 3125 ∣ m + 1) := by
  exact ⟨dvd_add_one_of_modEq_four_mod5,
    dvd_add_one_of_modEq_twentyfour_mod25,
    dvd_add_one_of_modEq_onetwentyfour_mod125,
    dvd_add_one_of_modEq_sixtwentyfour_mod625,
    dvd_add_one_of_modEq_thirtyonetwentyfour_mod3125⟩

/-- Concrete mod-7 power facts: `Nat.ModEq` gives shifted divisibility. -/
theorem concrete_mod7_power_modEq_to_dvd_add_two_facts :
    (∀ m, m ≡ 5 [MOD 7] → 7 ∣ m + 2) ∧
      (∀ m, m ≡ 47 [MOD 49] → 49 ∣ m + 2) ∧
      (∀ m, m ≡ 341 [MOD 343] → 343 ∣ m + 2) ∧
      (∀ m, m ≡ 2399 [MOD 2401] → 2401 ∣ m + 2) ∧
      (∀ m, m ≡ 16805 [MOD 16807] → 16807 ∣ m + 2) := by
  exact ⟨dvd_add_two_of_modEq_five_mod7,
    dvd_add_two_of_modEq_fortyseven_mod49,
    dvd_add_two_of_modEq_threefourtyone_mod343,
    dvd_add_two_of_modEq_twentythreeninetynine_mod2401,
    dvd_add_two_of_modEq_sixteeneightofive_mod16807⟩

/-- Concrete mod-11 power facts: `Nat.ModEq` gives shifted divisibility. -/
theorem concrete_mod11_power_modEq_to_dvd_add_five_facts :
    (∀ m, m ≡ 6 [MOD 11] → 11 ∣ m + 5) ∧
      (∀ m, m ≡ 116 [MOD 121] → 121 ∣ m + 5) ∧
      (∀ m, m ≡ 1326 [MOD 1331] → 1331 ∣ m + 5) ∧
      (∀ m, m ≡ 14636 [MOD 14641] → 14641 ∣ m + 5) ∧
      (∀ m, m ≡ 161046 [MOD 161051] → 161051 ∣ m + 5) := by
  exact ⟨dvd_add_five_of_modEq_six_mod11,
    dvd_add_five_of_modEq_onesixteen_mod121,
    dvd_add_five_of_modEq_thirteentwentysix_mod1331,
    dvd_add_five_of_modEq_fourteensixthirtysix_mod14641,
    dvd_add_five_of_modEq_onesixtyonezero46_mod161051⟩

/-- Concrete mod-5 power facts: shifted nondivisibility gives negated `Nat.ModEq`. -/
theorem concrete_mod5_power_not_dvd_add_one_to_not_modEq_facts :
    (∀ m, ¬ (5 ∣ m + 1) → ¬ (m ≡ 4 [MOD 5])) ∧
      (∀ m, ¬ (25 ∣ m + 1) → ¬ (m ≡ 24 [MOD 25])) ∧
      (∀ m, ¬ (125 ∣ m + 1) → ¬ (m ≡ 124 [MOD 125])) ∧
      (∀ m, ¬ (625 ∣ m + 1) → ¬ (m ≡ 624 [MOD 625])) ∧
      (∀ m, ¬ (3125 ∣ m + 1) → ¬ (m ≡ 3124 [MOD 3125])) := by
  exact ⟨not_modEq_four_mod5_of_not_dvd_add_one,
    not_modEq_twentyfour_mod25_of_not_dvd_add_one,
    not_modEq_onetwentyfour_mod125_of_not_dvd_add_one,
    not_modEq_sixtwentyfour_mod625_of_not_dvd_add_one,
    not_modEq_thirtyonetwentyfour_mod3125_of_not_dvd_add_one⟩

/-- Concrete mod-7 power facts: shifted nondivisibility gives negated `Nat.ModEq`. -/
theorem concrete_mod7_power_not_dvd_add_two_to_not_modEq_facts :
    (∀ m, ¬ (7 ∣ m + 2) → ¬ (m ≡ 5 [MOD 7])) ∧
      (∀ m, ¬ (49 ∣ m + 2) → ¬ (m ≡ 47 [MOD 49])) ∧
      (∀ m, ¬ (343 ∣ m + 2) → ¬ (m ≡ 341 [MOD 343])) ∧
      (∀ m, ¬ (2401 ∣ m + 2) → ¬ (m ≡ 2399 [MOD 2401])) ∧
      (∀ m, ¬ (16807 ∣ m + 2) → ¬ (m ≡ 16805 [MOD 16807])) := by
  exact ⟨not_modEq_five_mod7_of_not_dvd_add_two,
    not_modEq_fortyseven_mod49_of_not_dvd_add_two,
    not_modEq_threefourtyone_mod343_of_not_dvd_add_two,
    not_modEq_twentythreeninetynine_mod2401_of_not_dvd_add_two,
    not_modEq_sixteeneightofive_mod16807_of_not_dvd_add_two⟩

/-- Concrete mod-11 power facts: shifted nondivisibility gives negated `Nat.ModEq`. -/
theorem concrete_mod11_power_not_dvd_add_five_to_not_modEq_facts :
    (∀ m, ¬ (11 ∣ m + 5) → ¬ (m ≡ 6 [MOD 11])) ∧
      (∀ m, ¬ (121 ∣ m + 5) → ¬ (m ≡ 116 [MOD 121])) ∧
      (∀ m, ¬ (1331 ∣ m + 5) → ¬ (m ≡ 1326 [MOD 1331])) ∧
      (∀ m, ¬ (14641 ∣ m + 5) → ¬ (m ≡ 14636 [MOD 14641])) ∧
      (∀ m, ¬ (161051 ∣ m + 5) → ¬ (m ≡ 161046 [MOD 161051])) := by
  exact ⟨not_modEq_six_mod11_of_not_dvd_add_five,
    not_modEq_onesixteen_mod121_of_not_dvd_add_five,
    not_modEq_thirteentwentysix_mod1331_of_not_dvd_add_five,
    not_modEq_fourteensixthirtysix_mod14641_of_not_dvd_add_five,
    not_modEq_onesixtyonezero46_mod161051_of_not_dvd_add_five⟩

/-- Concrete mod-5 power facts: negated `Nat.ModEq` gives shifted nondivisibility. -/
theorem concrete_mod5_power_not_modEq_to_not_dvd_add_one_facts :
    (∀ m, ¬ (m ≡ 4 [MOD 5]) → ¬ (5 ∣ m + 1)) ∧
      (∀ m, ¬ (m ≡ 24 [MOD 25]) → ¬ (25 ∣ m + 1)) ∧
      (∀ m, ¬ (m ≡ 124 [MOD 125]) → ¬ (125 ∣ m + 1)) ∧
      (∀ m, ¬ (m ≡ 624 [MOD 625]) → ¬ (625 ∣ m + 1)) ∧
      (∀ m, ¬ (m ≡ 3124 [MOD 3125]) → ¬ (3125 ∣ m + 1)) := by
  exact ⟨not_dvd_add_one_of_not_modEq_four_mod5,
    not_dvd_add_one_of_not_modEq_twentyfour_mod25,
    not_dvd_add_one_of_not_modEq_onetwentyfour_mod125,
    not_dvd_add_one_of_not_modEq_sixtwentyfour_mod625,
    not_dvd_add_one_of_not_modEq_thirtyonetwentyfour_mod3125⟩

/-- Concrete mod-7 power facts: negated `Nat.ModEq` gives shifted nondivisibility. -/
theorem concrete_mod7_power_not_modEq_to_not_dvd_add_two_facts :
    (∀ m, ¬ (m ≡ 5 [MOD 7]) → ¬ (7 ∣ m + 2)) ∧
      (∀ m, ¬ (m ≡ 47 [MOD 49]) → ¬ (49 ∣ m + 2)) ∧
      (∀ m, ¬ (m ≡ 341 [MOD 343]) → ¬ (343 ∣ m + 2)) ∧
      (∀ m, ¬ (m ≡ 2399 [MOD 2401]) → ¬ (2401 ∣ m + 2)) ∧
      (∀ m, ¬ (m ≡ 16805 [MOD 16807]) → ¬ (16807 ∣ m + 2)) := by
  exact ⟨not_dvd_add_two_of_not_modEq_five_mod7,
    not_dvd_add_two_of_not_modEq_fortyseven_mod49,
    not_dvd_add_two_of_not_modEq_threefourtyone_mod343,
    not_dvd_add_two_of_not_modEq_twentythreeninetynine_mod2401,
    not_dvd_add_two_of_not_modEq_sixteeneightofive_mod16807⟩

/-- Concrete mod-11 power facts: negated `Nat.ModEq` gives shifted nondivisibility. -/
theorem concrete_mod11_power_not_modEq_to_not_dvd_add_five_facts :
    (∀ m, ¬ (m ≡ 6 [MOD 11]) → ¬ (11 ∣ m + 5)) ∧
      (∀ m, ¬ (m ≡ 116 [MOD 121]) → ¬ (121 ∣ m + 5)) ∧
      (∀ m, ¬ (m ≡ 1326 [MOD 1331]) → ¬ (1331 ∣ m + 5)) ∧
      (∀ m, ¬ (m ≡ 14636 [MOD 14641]) → ¬ (14641 ∣ m + 5)) ∧
      (∀ m, ¬ (m ≡ 161046 [MOD 161051]) → ¬ (161051 ∣ m + 5)) := by
  exact ⟨not_dvd_add_five_of_not_modEq_six_mod11,
    not_dvd_add_five_of_not_modEq_onesixteen_mod121,
    not_dvd_add_five_of_not_modEq_thirteentwentysix_mod1331,
    not_dvd_add_five_of_not_modEq_fourteensixthirtysix_mod14641,
    not_dvd_add_five_of_not_modEq_onesixtyonezero46_mod161051⟩

/-- Generic shifted-divisibility bridge for complementary residues. -/
theorem modEq_iff_dvd_add_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) :
    m ≡ r [MOD q] ↔ q ∣ m + c := by
  have hr : r < q := by omega
  rw [modEq_iff_exists_mul_add_of_lt (q := q) (r := r) (m := m) hr]
  exact exists_mul_add_iff_dvd_add (q := q) (r := r) (c := c) (m := m) hc hmod

/-- Generic shifted-divisibility-first bridge for complementary residues. -/
theorem dvd_add_iff_modEq_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) :
    q ∣ m + c ↔ m ≡ r [MOD q] :=
  (modEq_iff_dvd_add_of_add_eq (q := q) (r := r) (c := c) (m := m) hc hmod).symm

/-- Negated generic shifted-divisibility bridge for complementary residues. -/
theorem not_modEq_iff_not_dvd_add_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) :
    ¬ (m ≡ r [MOD q]) ↔ ¬ (q ∣ m + c) :=
  not_congr (modEq_iff_dvd_add_of_add_eq (q := q) (r := r) (c := c) (m := m)
    hc hmod)

/-- Negated generic shifted-divisibility-first bridge for complementary
residues. -/
theorem not_dvd_add_iff_not_modEq_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) :
    ¬ (q ∣ m + c) ↔ ¬ (m ≡ r [MOD q]) :=
  (not_modEq_iff_not_dvd_add_of_add_eq (q := q) (r := r) (c := c) (m := m)
    hc hmod).symm

/-- Shifted divisibility gives the complementary-residue `Nat.ModEq`. -/
theorem modEq_of_dvd_add_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) (hm : q ∣ m + c) :
    m ≡ r [MOD q] :=
  (modEq_iff_dvd_add_of_add_eq (q := q) (r := r) (c := c) (m := m) hc hmod).2 hm

/-- Complementary-residue `Nat.ModEq` gives shifted divisibility. -/
theorem dvd_add_of_modEq_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) (hm : m ≡ r [MOD q]) :
    q ∣ m + c :=
  (modEq_iff_dvd_add_of_add_eq (q := q) (r := r) (c := c) (m := m) hc hmod).1 hm

/-- Shifted nondivisibility gives negated complementary-residue `Nat.ModEq`. -/
theorem not_modEq_of_not_dvd_add_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) (hm : ¬ (q ∣ m + c)) :
    ¬ (m ≡ r [MOD q]) :=
  (not_modEq_iff_not_dvd_add_of_add_eq (q := q) (r := r) (c := c) (m := m)
    hc hmod).2 hm

/-- Negated complementary-residue `Nat.ModEq` gives shifted nondivisibility. -/
theorem not_dvd_add_of_not_modEq_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) (hm : ¬ (m ≡ r [MOD q])) :
    ¬ (q ∣ m + c) :=
  (not_modEq_iff_not_dvd_add_of_add_eq (q := q) (r := r) (c := c) (m := m)
    hc hmod).1 hm

/-- Direct residue equality is equivalent to shifted divisibility for
complementary residues. -/
theorem mod_eq_iff_dvd_add_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) :
    m % q = r ↔ q ∣ m + c := by
  have hr : r < q := by omega
  rw [mod_eq_iff_modEq_of_lt (q := q) (r := r) (m := m) hr]
  exact modEq_iff_dvd_add_of_add_eq (q := q) (r := r) (c := c) (m := m) hc hmod

/-- Shifted-divisibility-first direct residue bridge for complementary
residues. -/
theorem dvd_add_iff_mod_eq_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) :
    q ∣ m + c ↔ m % q = r :=
  (mod_eq_iff_dvd_add_of_add_eq (q := q) (r := r) (c := c) (m := m) hc hmod).symm

/-- Direct residue inequality is equivalent to shifted nondivisibility for
complementary residues. -/
theorem mod_ne_iff_not_dvd_add_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) :
    m % q ≠ r ↔ ¬ (q ∣ m + c) := by
  have hr : r < q := by omega
  rw [mod_ne_iff_not_modEq_of_lt (q := q) (r := r) (m := m) hr]
  exact not_modEq_iff_not_dvd_add_of_add_eq (q := q) (r := r) (c := c)
    (m := m) hc hmod

/-- Shifted-nondivisibility-first direct residue inequality bridge for
complementary residues. -/
theorem not_dvd_add_iff_mod_ne_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) :
    ¬ (q ∣ m + c) ↔ m % q ≠ r :=
  (mod_ne_iff_not_dvd_add_of_add_eq (q := q) (r := r) (c := c) (m := m)
    hc hmod).symm

/-- Direct residue equality gives shifted divisibility for complementary
residues. -/
theorem dvd_add_of_mod_eq_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) (hm : m % q = r) :
    q ∣ m + c :=
  (mod_eq_iff_dvd_add_of_add_eq (q := q) (r := r) (c := c) (m := m) hc hmod).1 hm

/-- Shifted divisibility gives direct residue equality for complementary
residues. -/
theorem mod_eq_of_dvd_add_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) (hm : q ∣ m + c) :
    m % q = r :=
  (mod_eq_iff_dvd_add_of_add_eq (q := q) (r := r) (c := c) (m := m) hc hmod).2 hm

/-- Direct residue inequality gives shifted nondivisibility for complementary
residues. -/
theorem not_dvd_add_of_mod_ne_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) (hm : m % q ≠ r) :
    ¬ (q ∣ m + c) :=
  (mod_ne_iff_not_dvd_add_of_add_eq (q := q) (r := r) (c := c) (m := m)
    hc hmod).1 hm

/-- Shifted nondivisibility gives direct residue inequality for complementary
residues. -/
theorem mod_ne_of_not_dvd_add_of_add_eq {q r c m : ℕ} (hc : 0 < c)
    (hmod : r + c = q) (hm : ¬ (q ∣ m + c)) :
    m % q ≠ r :=
  (mod_ne_iff_not_dvd_add_of_add_eq (q := q) (r := r) (c := c) (m := m)
    hc hmod).2 hm

/-- Concrete mod-5 power residue inequality iff shifted nondivisibility facts. -/
theorem concrete_mod5_power_residue_ne_iff_not_dvd_add_one_facts :
    (∀ m, m % 5 ≠ 4 ↔ ¬ (5 ∣ m + 1)) ∧
      (∀ m, m % 25 ≠ 24 ↔ ¬ (25 ∣ m + 1)) ∧
      (∀ m, m % 125 ≠ 124 ↔ ¬ (125 ∣ m + 1)) ∧
      (∀ m, m % 625 ≠ 624 ↔ ¬ (625 ∣ m + 1)) ∧
      (∀ m, m % 3125 ≠ 3124 ↔ ¬ (3125 ∣ m + 1)) := by
  exact ⟨fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 5) (r := 4)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 25) (r := 24)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 125) (r := 124)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 625) (r := 624)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 3125) (r := 3124)
      (c := 1) (m := m) (by decide) (by decide)⟩

/-- Concrete mod-7 power residue inequality iff shifted nondivisibility facts. -/
theorem concrete_mod7_power_residue_ne_iff_not_dvd_add_two_facts :
    (∀ m, m % 7 ≠ 5 ↔ ¬ (7 ∣ m + 2)) ∧
      (∀ m, m % 49 ≠ 47 ↔ ¬ (49 ∣ m + 2)) ∧
      (∀ m, m % 343 ≠ 341 ↔ ¬ (343 ∣ m + 2)) ∧
      (∀ m, m % 2401 ≠ 2399 ↔ ¬ (2401 ∣ m + 2)) ∧
      (∀ m, m % 16807 ≠ 16805 ↔ ¬ (16807 ∣ m + 2)) := by
  exact ⟨fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 7) (r := 5)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 49) (r := 47)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 343) (r := 341)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 2401) (r := 2399)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 16807) (r := 16805)
      (c := 2) (m := m) (by decide) (by decide)⟩

/-- Concrete mod-11 power residue inequality iff shifted nondivisibility facts. -/
theorem concrete_mod11_power_residue_ne_iff_not_dvd_add_five_facts :
    (∀ m, m % 11 ≠ 6 ↔ ¬ (11 ∣ m + 5)) ∧
      (∀ m, m % 121 ≠ 116 ↔ ¬ (121 ∣ m + 5)) ∧
      (∀ m, m % 1331 ≠ 1326 ↔ ¬ (1331 ∣ m + 5)) ∧
      (∀ m, m % 14641 ≠ 14636 ↔ ¬ (14641 ∣ m + 5)) ∧
      (∀ m, m % 161051 ≠ 161046 ↔ ¬ (161051 ∣ m + 5)) := by
  exact ⟨fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 11) (r := 6)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 121) (r := 116)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 1331) (r := 1326)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 14641) (r := 14636)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => mod_ne_iff_not_dvd_add_of_add_eq (q := 161051) (r := 161046)
      (c := 5) (m := m) (by decide) (by decide)⟩

/-- Concrete mod-5 power shifted nondivisibility iff residue inequality facts. -/
theorem concrete_mod5_power_not_dvd_add_one_iff_residue_ne_facts :
    (∀ m, ¬ (5 ∣ m + 1) ↔ m % 5 ≠ 4) ∧
      (∀ m, ¬ (25 ∣ m + 1) ↔ m % 25 ≠ 24) ∧
      (∀ m, ¬ (125 ∣ m + 1) ↔ m % 125 ≠ 124) ∧
      (∀ m, ¬ (625 ∣ m + 1) ↔ m % 625 ≠ 624) ∧
      (∀ m, ¬ (3125 ∣ m + 1) ↔ m % 3125 ≠ 3124) := by
  exact ⟨fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 5) (r := 4)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 25) (r := 24)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 125) (r := 124)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 625) (r := 624)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 3125) (r := 3124)
      (c := 1) (m := m) (by decide) (by decide)⟩

/-- Concrete mod-7 power shifted nondivisibility iff residue inequality facts. -/
theorem concrete_mod7_power_not_dvd_add_two_iff_residue_ne_facts :
    (∀ m, ¬ (7 ∣ m + 2) ↔ m % 7 ≠ 5) ∧
      (∀ m, ¬ (49 ∣ m + 2) ↔ m % 49 ≠ 47) ∧
      (∀ m, ¬ (343 ∣ m + 2) ↔ m % 343 ≠ 341) ∧
      (∀ m, ¬ (2401 ∣ m + 2) ↔ m % 2401 ≠ 2399) ∧
      (∀ m, ¬ (16807 ∣ m + 2) ↔ m % 16807 ≠ 16805) := by
  exact ⟨fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 7) (r := 5)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 49) (r := 47)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 343) (r := 341)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 2401) (r := 2399)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 16807) (r := 16805)
      (c := 2) (m := m) (by decide) (by decide)⟩

/-- Concrete mod-11 power shifted nondivisibility iff residue inequality facts. -/
theorem concrete_mod11_power_not_dvd_add_five_iff_residue_ne_facts :
    (∀ m, ¬ (11 ∣ m + 5) ↔ m % 11 ≠ 6) ∧
      (∀ m, ¬ (121 ∣ m + 5) ↔ m % 121 ≠ 116) ∧
      (∀ m, ¬ (1331 ∣ m + 5) ↔ m % 1331 ≠ 1326) ∧
      (∀ m, ¬ (14641 ∣ m + 5) ↔ m % 14641 ≠ 14636) ∧
      (∀ m, ¬ (161051 ∣ m + 5) ↔ m % 161051 ≠ 161046) := by
  exact ⟨fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 11) (r := 6)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 121) (r := 116)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 1331) (r := 1326)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 14641) (r := 14636)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_iff_mod_ne_of_add_eq (q := 161051) (r := 161046)
      (c := 5) (m := m) (by decide) (by decide)⟩

/-- Concrete mod-5 power facts: shifted divisibility gives direct residue
equality. -/
theorem concrete_mod5_power_dvd_add_one_to_residue_eq_facts :
    (∀ m, 5 ∣ m + 1 → m % 5 = 4) ∧
      (∀ m, 25 ∣ m + 1 → m % 25 = 24) ∧
      (∀ m, 125 ∣ m + 1 → m % 125 = 124) ∧
      (∀ m, 625 ∣ m + 1 → m % 625 = 624) ∧
      (∀ m, 3125 ∣ m + 1 → m % 3125 = 3124) := by
  exact ⟨mod5_eq4_of_dvd_add_one,
    mod25_eq24_of_dvd_add_one,
    mod125_eq124_of_dvd_add_one,
    mod625_eq624_of_dvd_add_one,
    mod3125_eq3124_of_dvd_add_one⟩

/-- Concrete mod-7 power facts: shifted divisibility gives direct residue
equality. -/
theorem concrete_mod7_power_dvd_add_two_to_residue_eq_facts :
    (∀ m, 7 ∣ m + 2 → m % 7 = 5) ∧
      (∀ m, 49 ∣ m + 2 → m % 49 = 47) ∧
      (∀ m, 343 ∣ m + 2 → m % 343 = 341) ∧
      (∀ m, 2401 ∣ m + 2 → m % 2401 = 2399) ∧
      (∀ m, 16807 ∣ m + 2 → m % 16807 = 16805) := by
  exact ⟨mod7_eq5_of_dvd_add_two,
    mod49_eq47_of_dvd_add_two,
    mod343_eq341_of_dvd_add_two,
    mod2401_eq2399_of_dvd_add_two,
    mod16807_eq16805_of_dvd_add_two⟩

/-- Concrete mod-11 power facts: shifted divisibility gives direct residue
equality. -/
theorem concrete_mod11_power_dvd_add_five_to_residue_eq_facts :
    (∀ m, 11 ∣ m + 5 → m % 11 = 6) ∧
      (∀ m, 121 ∣ m + 5 → m % 121 = 116) ∧
      (∀ m, 1331 ∣ m + 5 → m % 1331 = 1326) ∧
      (∀ m, 14641 ∣ m + 5 → m % 14641 = 14636) ∧
      (∀ m, 161051 ∣ m + 5 → m % 161051 = 161046) := by
  exact ⟨mod11_eq6_of_dvd_add_five,
    mod121_eq116_of_dvd_add_five,
    mod1331_eq1326_of_dvd_add_five,
    mod14641_eq14636_of_dvd_add_five,
    mod161051_eq161046_of_dvd_add_five⟩

/-- Concrete mod-5 power facts: direct residue inequality gives shifted
nondivisibility. -/
theorem concrete_mod5_power_residue_ne_to_not_dvd_add_one_facts :
    (∀ m, m % 5 ≠ 4 → ¬ (5 ∣ m + 1)) ∧
      (∀ m, m % 25 ≠ 24 → ¬ (25 ∣ m + 1)) ∧
      (∀ m, m % 125 ≠ 124 → ¬ (125 ∣ m + 1)) ∧
      (∀ m, m % 625 ≠ 624 → ¬ (625 ∣ m + 1)) ∧
      (∀ m, m % 3125 ≠ 3124 → ¬ (3125 ∣ m + 1)) := by
  exact ⟨fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 5) (r := 4)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 25) (r := 24)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 125) (r := 124)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 625) (r := 624)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 3125) (r := 3124)
      (c := 1) (m := m) (by decide) (by decide)⟩

/-- Concrete mod-7 power facts: direct residue inequality gives shifted
nondivisibility. -/
theorem concrete_mod7_power_residue_ne_to_not_dvd_add_two_facts :
    (∀ m, m % 7 ≠ 5 → ¬ (7 ∣ m + 2)) ∧
      (∀ m, m % 49 ≠ 47 → ¬ (49 ∣ m + 2)) ∧
      (∀ m, m % 343 ≠ 341 → ¬ (343 ∣ m + 2)) ∧
      (∀ m, m % 2401 ≠ 2399 → ¬ (2401 ∣ m + 2)) ∧
      (∀ m, m % 16807 ≠ 16805 → ¬ (16807 ∣ m + 2)) := by
  exact ⟨fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 7) (r := 5)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 49) (r := 47)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 343) (r := 341)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 2401) (r := 2399)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 16807) (r := 16805)
      (c := 2) (m := m) (by decide) (by decide)⟩

/-- Concrete mod-11 power facts: direct residue inequality gives shifted
nondivisibility. -/
theorem concrete_mod11_power_residue_ne_to_not_dvd_add_five_facts :
    (∀ m, m % 11 ≠ 6 → ¬ (11 ∣ m + 5)) ∧
      (∀ m, m % 121 ≠ 116 → ¬ (121 ∣ m + 5)) ∧
      (∀ m, m % 1331 ≠ 1326 → ¬ (1331 ∣ m + 5)) ∧
      (∀ m, m % 14641 ≠ 14636 → ¬ (14641 ∣ m + 5)) ∧
      (∀ m, m % 161051 ≠ 161046 → ¬ (161051 ∣ m + 5)) := by
  exact ⟨fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 11) (r := 6)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 121) (r := 116)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 1331) (r := 1326)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 14641) (r := 14636)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => not_dvd_add_of_mod_ne_of_add_eq (q := 161051) (r := 161046)
      (c := 5) (m := m) (by decide) (by decide)⟩

/-- Concrete mod-5 power facts: shifted nondivisibility gives direct residue
inequality. -/
theorem concrete_mod5_power_not_dvd_add_one_to_residue_ne_facts :
    (∀ m, ¬ (5 ∣ m + 1) → m % 5 ≠ 4) ∧
      (∀ m, ¬ (25 ∣ m + 1) → m % 25 ≠ 24) ∧
      (∀ m, ¬ (125 ∣ m + 1) → m % 125 ≠ 124) ∧
      (∀ m, ¬ (625 ∣ m + 1) → m % 625 ≠ 624) ∧
      (∀ m, ¬ (3125 ∣ m + 1) → m % 3125 ≠ 3124) := by
  exact ⟨fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 5) (r := 4)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 25) (r := 24)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 125) (r := 124)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 625) (r := 624)
      (c := 1) (m := m) (by decide) (by decide),
    fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 3125) (r := 3124)
      (c := 1) (m := m) (by decide) (by decide)⟩

/-- Concrete mod-7 power facts: shifted nondivisibility gives direct residue
inequality. -/
theorem concrete_mod7_power_not_dvd_add_two_to_residue_ne_facts :
    (∀ m, ¬ (7 ∣ m + 2) → m % 7 ≠ 5) ∧
      (∀ m, ¬ (49 ∣ m + 2) → m % 49 ≠ 47) ∧
      (∀ m, ¬ (343 ∣ m + 2) → m % 343 ≠ 341) ∧
      (∀ m, ¬ (2401 ∣ m + 2) → m % 2401 ≠ 2399) ∧
      (∀ m, ¬ (16807 ∣ m + 2) → m % 16807 ≠ 16805) := by
  exact ⟨fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 7) (r := 5)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 49) (r := 47)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 343) (r := 341)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 2401) (r := 2399)
      (c := 2) (m := m) (by decide) (by decide),
    fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 16807) (r := 16805)
      (c := 2) (m := m) (by decide) (by decide)⟩

/-- Concrete mod-11 power facts: shifted nondivisibility gives direct residue
inequality. -/
theorem concrete_mod11_power_not_dvd_add_five_to_residue_ne_facts :
    (∀ m, ¬ (11 ∣ m + 5) → m % 11 ≠ 6) ∧
      (∀ m, ¬ (121 ∣ m + 5) → m % 121 ≠ 116) ∧
      (∀ m, ¬ (1331 ∣ m + 5) → m % 1331 ≠ 1326) ∧
      (∀ m, ¬ (14641 ∣ m + 5) → m % 14641 ≠ 14636) ∧
      (∀ m, ¬ (161051 ∣ m + 5) → m % 161051 ≠ 161046) := by
  exact ⟨fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 11) (r := 6)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 121) (r := 116)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 1331) (r := 1326)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 14641) (r := 14636)
      (c := 5) (m := m) (by decide) (by decide),
    fun m => mod_ne_of_not_dvd_add_of_add_eq (q := 161051) (r := 161046)
      (c := 5) (m := m) (by decide) (by decide)⟩

/-- A residue `q-c` is equivalent to divisibility of `m+c`. -/
theorem mod_eq_sub_iff_dvd_add_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    m % q = q - c ↔ q ∣ m + c := by
  have hmod : q - c + c = q := Nat.sub_add_cancel hcq
  exact mod_eq_iff_dvd_add_of_add_eq (q := q) (r := q - c) (c := c)
    (m := m) hc0 hmod

/-- Divisibility of `m+c` is equivalent to residue `q-c`. -/
theorem dvd_add_iff_mod_eq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    q ∣ m + c ↔ m % q = q - c :=
  (mod_eq_sub_iff_dvd_add_of_pos_le (q := q) (c := c) (m := m) hc0 hcq).symm

/-- Avoiding residue `q-c` is equivalent to nondivisibility of `m+c`. -/
theorem mod_ne_sub_iff_not_dvd_add_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    m % q ≠ q - c ↔ ¬ (q ∣ m + c) := by
  have hmod : q - c + c = q := Nat.sub_add_cancel hcq
  exact mod_ne_iff_not_dvd_add_of_add_eq (q := q) (r := q - c) (c := c)
    (m := m) hc0 hmod

/-- Nondivisibility of `m+c` is equivalent to avoiding residue `q-c`. -/
theorem not_dvd_add_iff_mod_ne_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    ¬ (q ∣ m + c) ↔ m % q ≠ q - c :=
  (mod_ne_sub_iff_not_dvd_add_of_pos_le (q := q) (c := c) (m := m) hc0 hcq).symm

/-- Residue `q-c` gives divisibility of `m+c`. -/
theorem dvd_add_of_mod_eq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : m % q = q - c) :
    q ∣ m + c :=
  (mod_eq_sub_iff_dvd_add_of_pos_le (q := q) (c := c) (m := m) hc0 hcq).1 hm

/-- Divisibility of `m+c` gives residue `q-c`. -/
theorem mod_eq_sub_of_dvd_add_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : q ∣ m + c) :
    m % q = q - c :=
  (mod_eq_sub_iff_dvd_add_of_pos_le (q := q) (c := c) (m := m) hc0 hcq).2 hm

/-- Avoiding residue `q-c` gives nondivisibility of `m+c`. -/
theorem not_dvd_add_of_mod_ne_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : m % q ≠ q - c) :
    ¬ (q ∣ m + c) :=
  (mod_ne_sub_iff_not_dvd_add_of_pos_le (q := q) (c := c) (m := m) hc0 hcq).1 hm

/-- Nondivisibility of `m+c` gives avoidance of residue `q-c`. -/
theorem mod_ne_sub_of_not_dvd_add_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : ¬ (q ∣ m + c)) :
    m % q ≠ q - c :=
  (mod_ne_sub_iff_not_dvd_add_of_pos_le (q := q) (c := c) (m := m) hc0 hcq).2 hm

/-- The predecessor residue is equivalent to divisibility of `m+1`. -/
theorem mod_eq_pred_iff_dvd_succ {q m : ℕ} (hq : 0 < q) :
    m % q = q - 1 ↔ q ∣ m + 1 :=
  mod_eq_sub_iff_dvd_add_of_pos_le (q := q) (c := 1) (m := m) (by decide) hq

/-- Divisibility of `m+1` is equivalent to the predecessor residue. -/
theorem dvd_succ_iff_mod_eq_pred {q m : ℕ} (hq : 0 < q) :
    q ∣ m + 1 ↔ m % q = q - 1 :=
  (mod_eq_pred_iff_dvd_succ (q := q) (m := m) hq).symm

/-- Avoiding the predecessor residue is equivalent to nondivisibility of `m+1`. -/
theorem mod_ne_pred_iff_not_dvd_succ {q m : ℕ} (hq : 0 < q) :
    m % q ≠ q - 1 ↔ ¬ (q ∣ m + 1) :=
  mod_ne_sub_iff_not_dvd_add_of_pos_le (q := q) (c := 1) (m := m) (by decide) hq

/-- Nondivisibility of `m+1` is equivalent to avoiding the predecessor
residue. -/
theorem not_dvd_succ_iff_mod_ne_pred {q m : ℕ} (hq : 0 < q) :
    ¬ (q ∣ m + 1) ↔ m % q ≠ q - 1 :=
  (mod_ne_pred_iff_not_dvd_succ (q := q) (m := m) hq).symm

/-- The predecessor residue gives divisibility of `m+1`. -/
theorem dvd_succ_of_mod_eq_pred {q m : ℕ} (hq : 0 < q)
    (hm : m % q = q - 1) :
    q ∣ m + 1 :=
  (mod_eq_pred_iff_dvd_succ (q := q) (m := m) hq).1 hm

/-- Divisibility of `m+1` gives the predecessor residue. -/
theorem mod_eq_pred_of_dvd_succ {q m : ℕ} (hq : 0 < q)
    (hm : q ∣ m + 1) :
    m % q = q - 1 :=
  (mod_eq_pred_iff_dvd_succ (q := q) (m := m) hq).2 hm

/-- Avoiding the predecessor residue gives nondivisibility of `m+1`. -/
theorem not_dvd_succ_of_mod_ne_pred {q m : ℕ} (hq : 0 < q)
    (hm : m % q ≠ q - 1) :
    ¬ (q ∣ m + 1) :=
  (mod_ne_pred_iff_not_dvd_succ (q := q) (m := m) hq).1 hm

/-- Nondivisibility of `m+1` gives avoidance of the predecessor residue. -/
theorem mod_ne_pred_of_not_dvd_succ {q m : ℕ} (hq : 0 < q)
    (hm : ¬ (q ∣ m + 1)) :
    m % q ≠ q - 1 :=
  (mod_ne_pred_iff_not_dvd_succ (q := q) (m := m) hq).2 hm

/-- A `Nat.ModEq` to residue `q-c` is equivalent to divisibility of `m+c`. -/
theorem modEq_sub_iff_dvd_add_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    m ≡ q - c [MOD q] ↔ q ∣ m + c := by
  have hmod : q - c + c = q := Nat.sub_add_cancel hcq
  exact modEq_iff_dvd_add_of_add_eq (q := q) (r := q - c) (c := c)
    (m := m) hc0 hmod

/-- Divisibility of `m+c` is equivalent to `Nat.ModEq` to residue `q-c`. -/
theorem dvd_add_iff_modEq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    q ∣ m + c ↔ m ≡ q - c [MOD q] :=
  (modEq_sub_iff_dvd_add_of_pos_le (q := q) (c := c) (m := m) hc0 hcq).symm

/-- Negated `Nat.ModEq` to residue `q-c` is equivalent to nondivisibility of
`m+c`. -/
theorem not_modEq_sub_iff_not_dvd_add_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    ¬ (m ≡ q - c [MOD q]) ↔ ¬ (q ∣ m + c) := by
  have hmod : q - c + c = q := Nat.sub_add_cancel hcq
  exact not_modEq_iff_not_dvd_add_of_add_eq (q := q) (r := q - c) (c := c)
    (m := m) hc0 hmod

/-- Nondivisibility of `m+c` is equivalent to negated `Nat.ModEq` to residue
`q-c`. -/
theorem not_dvd_add_iff_not_modEq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    ¬ (q ∣ m + c) ↔ ¬ (m ≡ q - c [MOD q]) :=
  (not_modEq_sub_iff_not_dvd_add_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).symm

/-- Divisibility of `m+c` gives `Nat.ModEq` to residue `q-c`. -/
theorem modEq_sub_of_dvd_add_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : q ∣ m + c) :
    m ≡ q - c [MOD q] :=
  (modEq_sub_iff_dvd_add_of_pos_le (q := q) (c := c) (m := m) hc0 hcq).2 hm

/-- `Nat.ModEq` to residue `q-c` gives divisibility of `m+c`. -/
theorem dvd_add_of_modEq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : m ≡ q - c [MOD q]) :
    q ∣ m + c :=
  (modEq_sub_iff_dvd_add_of_pos_le (q := q) (c := c) (m := m) hc0 hcq).1 hm

/-- Nondivisibility of `m+c` gives negated `Nat.ModEq` to residue `q-c`. -/
theorem not_modEq_sub_of_not_dvd_add_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : ¬ (q ∣ m + c)) :
    ¬ (m ≡ q - c [MOD q]) :=
  (not_modEq_sub_iff_not_dvd_add_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).2 hm

/-- Negated `Nat.ModEq` to residue `q-c` gives nondivisibility of `m+c`. -/
theorem not_dvd_add_of_not_modEq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : ¬ (m ≡ q - c [MOD q])) :
    ¬ (q ∣ m + c) :=
  (not_modEq_sub_iff_not_dvd_add_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).1 hm

/-- `Nat.ModEq` to the predecessor residue is equivalent to divisibility of
`m+1`. -/
theorem modEq_pred_iff_dvd_succ {q m : ℕ} (hq : 0 < q) :
    m ≡ q - 1 [MOD q] ↔ q ∣ m + 1 :=
  modEq_sub_iff_dvd_add_of_pos_le (q := q) (c := 1) (m := m) (by decide) hq

/-- Divisibility of `m+1` is equivalent to `Nat.ModEq` to the predecessor
residue. -/
theorem dvd_succ_iff_modEq_pred {q m : ℕ} (hq : 0 < q) :
    q ∣ m + 1 ↔ m ≡ q - 1 [MOD q] :=
  (modEq_pred_iff_dvd_succ (q := q) (m := m) hq).symm

/-- Negated `Nat.ModEq` to the predecessor residue is equivalent to
nondivisibility of `m+1`. -/
theorem not_modEq_pred_iff_not_dvd_succ {q m : ℕ} (hq : 0 < q) :
    ¬ (m ≡ q - 1 [MOD q]) ↔ ¬ (q ∣ m + 1) :=
  not_modEq_sub_iff_not_dvd_add_of_pos_le (q := q) (c := 1) (m := m)
    (by decide) hq

/-- Nondivisibility of `m+1` is equivalent to negated `Nat.ModEq` to the
predecessor residue. -/
theorem not_dvd_succ_iff_not_modEq_pred {q m : ℕ} (hq : 0 < q) :
    ¬ (q ∣ m + 1) ↔ ¬ (m ≡ q - 1 [MOD q]) :=
  (not_modEq_pred_iff_not_dvd_succ (q := q) (m := m) hq).symm

/-- Divisibility of `m+1` gives `Nat.ModEq` to the predecessor residue. -/
theorem modEq_pred_of_dvd_succ {q m : ℕ} (hq : 0 < q)
    (hm : q ∣ m + 1) :
    m ≡ q - 1 [MOD q] :=
  (modEq_pred_iff_dvd_succ (q := q) (m := m) hq).2 hm

/-- `Nat.ModEq` to the predecessor residue gives divisibility of `m+1`. -/
theorem dvd_succ_of_modEq_pred {q m : ℕ} (hq : 0 < q)
    (hm : m ≡ q - 1 [MOD q]) :
    q ∣ m + 1 :=
  (modEq_pred_iff_dvd_succ (q := q) (m := m) hq).1 hm

/-- Nondivisibility of `m+1` gives negated `Nat.ModEq` to the predecessor
residue. -/
theorem not_modEq_pred_of_not_dvd_succ {q m : ℕ} (hq : 0 < q)
    (hm : ¬ (q ∣ m + 1)) :
    ¬ (m ≡ q - 1 [MOD q]) :=
  (not_modEq_pred_iff_not_dvd_succ (q := q) (m := m) hq).2 hm

/-- Negated `Nat.ModEq` to the predecessor residue gives nondivisibility of
`m+1`. -/
theorem not_dvd_succ_of_not_modEq_pred {q m : ℕ} (hq : 0 < q)
    (hm : ¬ (m ≡ q - 1 [MOD q])) :
    ¬ (q ∣ m + 1) :=
  (not_modEq_pred_iff_not_dvd_succ (q := q) (m := m) hq).1 hm

/-- The residue `q-2` is equivalent to divisibility of `m+2`. -/
theorem mod_eq_sub_two_iff_dvd_add_two_of_le {q m : ℕ} (hq : 2 ≤ q) :
    m % q = q - 2 ↔ q ∣ m + 2 :=
  mod_eq_sub_iff_dvd_add_of_pos_le (q := q) (c := 2) (m := m)
    (by decide) hq

/-- Divisibility of `m+2` is equivalent to the residue `q-2`. -/
theorem dvd_add_two_iff_mod_eq_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q) :
    q ∣ m + 2 ↔ m % q = q - 2 :=
  (mod_eq_sub_two_iff_dvd_add_two_of_le (q := q) (m := m) hq).symm

/-- Avoiding residue `q-2` is equivalent to nondivisibility of `m+2`. -/
theorem mod_ne_sub_two_iff_not_dvd_add_two_of_le {q m : ℕ} (hq : 2 ≤ q) :
    m % q ≠ q - 2 ↔ ¬ (q ∣ m + 2) :=
  mod_ne_sub_iff_not_dvd_add_of_pos_le (q := q) (c := 2) (m := m)
    (by decide) hq

/-- Nondivisibility of `m+2` is equivalent to avoiding residue `q-2`. -/
theorem not_dvd_add_two_iff_mod_ne_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q) :
    ¬ (q ∣ m + 2) ↔ m % q ≠ q - 2 :=
  (mod_ne_sub_two_iff_not_dvd_add_two_of_le (q := q) (m := m) hq).symm

/-- Residue `q-2` gives divisibility of `m+2`. -/
theorem dvd_add_two_of_mod_eq_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : m % q = q - 2) :
    q ∣ m + 2 :=
  (mod_eq_sub_two_iff_dvd_add_two_of_le (q := q) (m := m) hq).1 hm

/-- Divisibility of `m+2` gives residue `q-2`. -/
theorem mod_eq_sub_two_of_dvd_add_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : q ∣ m + 2) :
    m % q = q - 2 :=
  (mod_eq_sub_two_iff_dvd_add_two_of_le (q := q) (m := m) hq).2 hm

/-- Avoiding residue `q-2` gives nondivisibility of `m+2`. -/
theorem not_dvd_add_two_of_mod_ne_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : m % q ≠ q - 2) :
    ¬ (q ∣ m + 2) :=
  (mod_ne_sub_two_iff_not_dvd_add_two_of_le (q := q) (m := m) hq).1 hm

/-- Nondivisibility of `m+2` gives avoidance of residue `q-2`. -/
theorem mod_ne_sub_two_of_not_dvd_add_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : ¬ (q ∣ m + 2)) :
    m % q ≠ q - 2 :=
  (mod_ne_sub_two_iff_not_dvd_add_two_of_le (q := q) (m := m) hq).2 hm

/-- The residue `q-5` is equivalent to divisibility of `m+5`. -/
theorem mod_eq_sub_five_iff_dvd_add_five_of_le {q m : ℕ} (hq : 5 ≤ q) :
    m % q = q - 5 ↔ q ∣ m + 5 :=
  mod_eq_sub_iff_dvd_add_of_pos_le (q := q) (c := 5) (m := m)
    (by decide) hq

/-- Divisibility of `m+5` is equivalent to the residue `q-5`. -/
theorem dvd_add_five_iff_mod_eq_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q) :
    q ∣ m + 5 ↔ m % q = q - 5 :=
  (mod_eq_sub_five_iff_dvd_add_five_of_le (q := q) (m := m) hq).symm

/-- Avoiding residue `q-5` is equivalent to nondivisibility of `m+5`. -/
theorem mod_ne_sub_five_iff_not_dvd_add_five_of_le {q m : ℕ} (hq : 5 ≤ q) :
    m % q ≠ q - 5 ↔ ¬ (q ∣ m + 5) :=
  mod_ne_sub_iff_not_dvd_add_of_pos_le (q := q) (c := 5) (m := m)
    (by decide) hq

/-- Nondivisibility of `m+5` is equivalent to avoiding residue `q-5`. -/
theorem not_dvd_add_five_iff_mod_ne_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q) :
    ¬ (q ∣ m + 5) ↔ m % q ≠ q - 5 :=
  (mod_ne_sub_five_iff_not_dvd_add_five_of_le (q := q) (m := m) hq).symm

/-- Residue `q-5` gives divisibility of `m+5`. -/
theorem dvd_add_five_of_mod_eq_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q)
    (hm : m % q = q - 5) :
    q ∣ m + 5 :=
  (mod_eq_sub_five_iff_dvd_add_five_of_le (q := q) (m := m) hq).1 hm

/-- Divisibility of `m+5` gives residue `q-5`. -/
theorem mod_eq_sub_five_of_dvd_add_five_of_le {q m : ℕ} (hq : 5 ≤ q)
    (hm : q ∣ m + 5) :
    m % q = q - 5 :=
  (mod_eq_sub_five_iff_dvd_add_five_of_le (q := q) (m := m) hq).2 hm

/-- Avoiding residue `q-5` gives nondivisibility of `m+5`. -/
theorem not_dvd_add_five_of_mod_ne_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q)
    (hm : m % q ≠ q - 5) :
    ¬ (q ∣ m + 5) :=
  (mod_ne_sub_five_iff_not_dvd_add_five_of_le (q := q) (m := m) hq).1 hm

/-- Nondivisibility of `m+5` gives avoidance of residue `q-5`. -/
theorem mod_ne_sub_five_of_not_dvd_add_five_of_le {q m : ℕ} (hq : 5 ≤ q)
    (hm : ¬ (q ∣ m + 5)) :
    m % q ≠ q - 5 :=
  (mod_ne_sub_five_iff_not_dvd_add_five_of_le (q := q) (m := m) hq).2 hm

/-- `Nat.ModEq` to residue `q-2` is equivalent to divisibility of `m+2`. -/
theorem modEq_sub_two_iff_dvd_add_two_of_le {q m : ℕ} (hq : 2 ≤ q) :
    m ≡ q - 2 [MOD q] ↔ q ∣ m + 2 :=
  modEq_sub_iff_dvd_add_of_pos_le (q := q) (c := 2) (m := m)
    (by decide) hq

/-- Divisibility of `m+2` is equivalent to `Nat.ModEq` to residue `q-2`. -/
theorem dvd_add_two_iff_modEq_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q) :
    q ∣ m + 2 ↔ m ≡ q - 2 [MOD q] :=
  (modEq_sub_two_iff_dvd_add_two_of_le (q := q) (m := m) hq).symm

/-- Negated `Nat.ModEq` to residue `q-2` is equivalent to nondivisibility of
`m+2`. -/
theorem not_modEq_sub_two_iff_not_dvd_add_two_of_le {q m : ℕ} (hq : 2 ≤ q) :
    ¬ (m ≡ q - 2 [MOD q]) ↔ ¬ (q ∣ m + 2) :=
  not_modEq_sub_iff_not_dvd_add_of_pos_le (q := q) (c := 2) (m := m)
    (by decide) hq

/-- Nondivisibility of `m+2` is equivalent to negated `Nat.ModEq` to residue
`q-2`. -/
theorem not_dvd_add_two_iff_not_modEq_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q) :
    ¬ (q ∣ m + 2) ↔ ¬ (m ≡ q - 2 [MOD q]) :=
  (not_modEq_sub_two_iff_not_dvd_add_two_of_le (q := q) (m := m) hq).symm

/-- Divisibility of `m+2` gives `Nat.ModEq` to residue `q-2`. -/
theorem modEq_sub_two_of_dvd_add_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : q ∣ m + 2) :
    m ≡ q - 2 [MOD q] :=
  (modEq_sub_two_iff_dvd_add_two_of_le (q := q) (m := m) hq).2 hm

/-- `Nat.ModEq` to residue `q-2` gives divisibility of `m+2`. -/
theorem dvd_add_two_of_modEq_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : m ≡ q - 2 [MOD q]) :
    q ∣ m + 2 :=
  (modEq_sub_two_iff_dvd_add_two_of_le (q := q) (m := m) hq).1 hm

/-- Nondivisibility of `m+2` gives negated `Nat.ModEq` to residue `q-2`. -/
theorem not_modEq_sub_two_of_not_dvd_add_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : ¬ (q ∣ m + 2)) :
    ¬ (m ≡ q - 2 [MOD q]) :=
  (not_modEq_sub_two_iff_not_dvd_add_two_of_le (q := q) (m := m) hq).2 hm

/-- Negated `Nat.ModEq` to residue `q-2` gives nondivisibility of `m+2`. -/
theorem not_dvd_add_two_of_not_modEq_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : ¬ (m ≡ q - 2 [MOD q])) :
    ¬ (q ∣ m + 2) :=
  (not_modEq_sub_two_iff_not_dvd_add_two_of_le (q := q) (m := m) hq).1 hm

/-- `Nat.ModEq` to residue `q-5` is equivalent to divisibility of `m+5`. -/
theorem modEq_sub_five_iff_dvd_add_five_of_le {q m : ℕ} (hq : 5 ≤ q) :
    m ≡ q - 5 [MOD q] ↔ q ∣ m + 5 :=
  modEq_sub_iff_dvd_add_of_pos_le (q := q) (c := 5) (m := m)
    (by decide) hq

/-- Divisibility of `m+5` is equivalent to `Nat.ModEq` to residue `q-5`. -/
theorem dvd_add_five_iff_modEq_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q) :
    q ∣ m + 5 ↔ m ≡ q - 5 [MOD q] :=
  (modEq_sub_five_iff_dvd_add_five_of_le (q := q) (m := m) hq).symm

/-- Negated `Nat.ModEq` to residue `q-5` is equivalent to nondivisibility of
`m+5`. -/
theorem not_modEq_sub_five_iff_not_dvd_add_five_of_le {q m : ℕ} (hq : 5 ≤ q) :
    ¬ (m ≡ q - 5 [MOD q]) ↔ ¬ (q ∣ m + 5) :=
  not_modEq_sub_iff_not_dvd_add_of_pos_le (q := q) (c := 5) (m := m)
    (by decide) hq

/-- Nondivisibility of `m+5` is equivalent to negated `Nat.ModEq` to residue
`q-5`. -/
theorem not_dvd_add_five_iff_not_modEq_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q) :
    ¬ (q ∣ m + 5) ↔ ¬ (m ≡ q - 5 [MOD q]) :=
  (not_modEq_sub_five_iff_not_dvd_add_five_of_le (q := q) (m := m) hq).symm

/-- Divisibility of `m+5` gives `Nat.ModEq` to residue `q-5`. -/
theorem modEq_sub_five_of_dvd_add_five_of_le {q m : ℕ} (hq : 5 ≤ q)
    (hm : q ∣ m + 5) :
    m ≡ q - 5 [MOD q] :=
  (modEq_sub_five_iff_dvd_add_five_of_le (q := q) (m := m) hq).2 hm

/-- `Nat.ModEq` to residue `q-5` gives divisibility of `m+5`. -/
theorem dvd_add_five_of_modEq_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q)
    (hm : m ≡ q - 5 [MOD q]) :
    q ∣ m + 5 :=
  (modEq_sub_five_iff_dvd_add_five_of_le (q := q) (m := m) hq).1 hm

/-- Nondivisibility of `m+5` gives negated `Nat.ModEq` to residue `q-5`. -/
theorem not_modEq_sub_five_of_not_dvd_add_five_of_le {q m : ℕ} (hq : 5 ≤ q)
    (hm : ¬ (q ∣ m + 5)) :
    ¬ (m ≡ q - 5 [MOD q]) :=
  (not_modEq_sub_five_iff_not_dvd_add_five_of_le (q := q) (m := m) hq).2 hm

/-- Negated `Nat.ModEq` to residue `q-5` gives nondivisibility of `m+5`. -/
theorem not_dvd_add_five_of_not_modEq_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q)
    (hm : ¬ (m ≡ q - 5 [MOD q])) :
    ¬ (q ∣ m + 5) :=
  (not_modEq_sub_five_iff_not_dvd_add_five_of_le (q := q) (m := m) hq).1 hm

/-- Membership in the residue class `q-c` is equivalent to divisibility of
`m+c`. -/
theorem exists_mul_add_sub_iff_dvd_add_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    (∃ n, m = q * n + (q - c)) ↔ q ∣ m + c := by
  have hmod : q - c + c = q := Nat.sub_add_cancel hcq
  exact exists_mul_add_iff_dvd_add (q := q) (r := q - c) (c := c)
    (m := m) hc0 hmod

/-- Shifted divisibility is equivalent to membership in the residue class
`q-c`. -/
theorem dvd_add_iff_exists_mul_add_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    q ∣ m + c ↔ ∃ n, m = q * n + (q - c) :=
  (exists_mul_add_sub_iff_dvd_add_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).symm

/-- Nonmembership in the residue class `q-c` is equivalent to nondivisibility
of `m+c`. -/
theorem not_exists_mul_add_sub_iff_not_dvd_add_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    (¬ ∃ n, m = q * n + (q - c)) ↔ ¬ (q ∣ m + c) := by
  have hmod : q - c + c = q := Nat.sub_add_cancel hcq
  exact not_exists_mul_add_iff_not_dvd_add (q := q) (r := q - c) (c := c)
    (m := m) hc0 hmod

/-- Shifted nondivisibility is equivalent to nonmembership in the residue class
`q-c`. -/
theorem not_dvd_add_iff_not_exists_mul_add_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    ¬ (q ∣ m + c) ↔ ¬ ∃ n, m = q * n + (q - c) :=
  (not_exists_mul_add_sub_iff_not_dvd_add_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).symm

/-- Membership in the residue class `q-c` gives shifted divisibility. -/
theorem dvd_add_of_exists_mul_add_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : ∃ n, m = q * n + (q - c)) :
    q ∣ m + c :=
  (exists_mul_add_sub_iff_dvd_add_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).1 hm

/-- Shifted divisibility gives membership in the residue class `q-c`. -/
theorem exists_mul_add_sub_of_dvd_add_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : q ∣ m + c) :
    ∃ n, m = q * n + (q - c) :=
  (exists_mul_add_sub_iff_dvd_add_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).2 hm

/-- Nonmembership in the residue class `q-c` gives shifted nondivisibility. -/
theorem not_dvd_add_of_not_exists_mul_add_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q)
    (hm : ¬ ∃ n, m = q * n + (q - c)) :
    ¬ (q ∣ m + c) :=
  (not_exists_mul_add_sub_iff_not_dvd_add_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).1 hm

/-- Shifted nondivisibility gives nonmembership in the residue class `q-c`. -/
theorem not_exists_mul_add_sub_of_not_dvd_add_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : ¬ (q ∣ m + c)) :
    ¬ ∃ n, m = q * n + (q - c) :=
  (not_exists_mul_add_sub_iff_not_dvd_add_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).2 hm

/-- Membership in the predecessor residue class is equivalent to divisibility
of `m+1`. -/
theorem exists_mul_add_pred_iff_dvd_succ {q m : ℕ} (hq : 0 < q) :
    (∃ n, m = q * n + (q - 1)) ↔ q ∣ m + 1 :=
  exists_mul_add_sub_iff_dvd_add_of_pos_le (q := q) (c := 1) (m := m)
    (by decide) hq

/-- Divisibility of `m+1` is equivalent to membership in the predecessor
residue class. -/
theorem dvd_succ_iff_exists_mul_add_pred {q m : ℕ} (hq : 0 < q) :
    q ∣ m + 1 ↔ ∃ n, m = q * n + (q - 1) :=
  (exists_mul_add_pred_iff_dvd_succ (q := q) (m := m) hq).symm

/-- Nonmembership in the predecessor residue class is equivalent to
nondivisibility of `m+1`. -/
theorem not_exists_mul_add_pred_iff_not_dvd_succ {q m : ℕ} (hq : 0 < q) :
    (¬ ∃ n, m = q * n + (q - 1)) ↔ ¬ (q ∣ m + 1) :=
  not_exists_mul_add_sub_iff_not_dvd_add_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- Nondivisibility of `m+1` is equivalent to nonmembership in the predecessor
residue class. -/
theorem not_dvd_succ_iff_not_exists_mul_add_pred {q m : ℕ} (hq : 0 < q) :
    ¬ (q ∣ m + 1) ↔ ¬ ∃ n, m = q * n + (q - 1) :=
  (not_exists_mul_add_pred_iff_not_dvd_succ (q := q) (m := m) hq).symm

/-- Membership in the `q-2` residue class is equivalent to divisibility of
`m+2`. -/
theorem exists_mul_add_sub_two_iff_dvd_add_two_of_le {q m : ℕ} (hq : 2 ≤ q) :
    (∃ n, m = q * n + (q - 2)) ↔ q ∣ m + 2 :=
  exists_mul_add_sub_iff_dvd_add_of_pos_le (q := q) (c := 2) (m := m)
    (by decide) hq

/-- Divisibility of `m+2` is equivalent to membership in the `q-2` residue
class. -/
theorem dvd_add_two_iff_exists_mul_add_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q) :
    q ∣ m + 2 ↔ ∃ n, m = q * n + (q - 2) :=
  (exists_mul_add_sub_two_iff_dvd_add_two_of_le (q := q) (m := m) hq).symm

/-- Nonmembership in the `q-2` residue class is equivalent to nondivisibility
of `m+2`. -/
theorem not_exists_mul_add_sub_two_iff_not_dvd_add_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    (¬ ∃ n, m = q * n + (q - 2)) ↔ ¬ (q ∣ m + 2) :=
  not_exists_mul_add_sub_iff_not_dvd_add_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- Nondivisibility of `m+2` is equivalent to nonmembership in the `q-2`
residue class. -/
theorem not_dvd_add_two_iff_not_exists_mul_add_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    ¬ (q ∣ m + 2) ↔ ¬ ∃ n, m = q * n + (q - 2) :=
  (not_exists_mul_add_sub_two_iff_not_dvd_add_two_of_le (q := q) (m := m)
    hq).symm

/-- Membership in the `q-5` residue class is equivalent to divisibility of
`m+5`. -/
theorem exists_mul_add_sub_five_iff_dvd_add_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    (∃ n, m = q * n + (q - 5)) ↔ q ∣ m + 5 :=
  exists_mul_add_sub_iff_dvd_add_of_pos_le (q := q) (c := 5) (m := m)
    (by decide) hq

/-- Divisibility of `m+5` is equivalent to membership in the `q-5` residue
class. -/
theorem dvd_add_five_iff_exists_mul_add_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    q ∣ m + 5 ↔ ∃ n, m = q * n + (q - 5) :=
  (exists_mul_add_sub_five_iff_dvd_add_five_of_le (q := q) (m := m) hq).symm

/-- Nonmembership in the `q-5` residue class is equivalent to nondivisibility
of `m+5`. -/
theorem not_exists_mul_add_sub_five_iff_not_dvd_add_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    (¬ ∃ n, m = q * n + (q - 5)) ↔ ¬ (q ∣ m + 5) :=
  not_exists_mul_add_sub_iff_not_dvd_add_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- Nondivisibility of `m+5` is equivalent to nonmembership in the `q-5`
residue class. -/
theorem not_dvd_add_five_iff_not_exists_mul_add_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    ¬ (q ∣ m + 5) ↔ ¬ ∃ n, m = q * n + (q - 5) :=
  (not_exists_mul_add_sub_five_iff_not_dvd_add_five_of_le (q := q) (m := m)
    hq).symm

/-- Membership in the predecessor residue class gives divisibility of `m+1`. -/
theorem dvd_succ_of_exists_mul_add_pred {q m : ℕ} (hq : 0 < q)
    (hm : ∃ n, m = q * n + (q - 1)) :
    q ∣ m + 1 :=
  (exists_mul_add_pred_iff_dvd_succ (q := q) (m := m) hq).1 hm

/-- Divisibility of `m+1` gives membership in the predecessor residue class. -/
theorem exists_mul_add_pred_of_dvd_succ {q m : ℕ} (hq : 0 < q)
    (hm : q ∣ m + 1) :
    ∃ n, m = q * n + (q - 1) :=
  (exists_mul_add_pred_iff_dvd_succ (q := q) (m := m) hq).2 hm

/-- Nonmembership in the predecessor residue class gives nondivisibility of
`m+1`. -/
theorem not_dvd_succ_of_not_exists_mul_add_pred {q m : ℕ} (hq : 0 < q)
    (hm : ¬ ∃ n, m = q * n + (q - 1)) :
    ¬ (q ∣ m + 1) :=
  (not_exists_mul_add_pred_iff_not_dvd_succ (q := q) (m := m) hq).1 hm

/-- Nondivisibility of `m+1` gives nonmembership in the predecessor residue
class. -/
theorem not_exists_mul_add_pred_of_not_dvd_succ {q m : ℕ} (hq : 0 < q)
    (hm : ¬ (q ∣ m + 1)) :
    ¬ ∃ n, m = q * n + (q - 1) :=
  (not_exists_mul_add_pred_iff_not_dvd_succ (q := q) (m := m) hq).2 hm

/-- Membership in the `q-2` residue class gives divisibility of `m+2`. -/
theorem dvd_add_two_of_exists_mul_add_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : ∃ n, m = q * n + (q - 2)) :
    q ∣ m + 2 :=
  (exists_mul_add_sub_two_iff_dvd_add_two_of_le (q := q) (m := m) hq).1 hm

/-- Divisibility of `m+2` gives membership in the `q-2` residue class. -/
theorem exists_mul_add_sub_two_of_dvd_add_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : q ∣ m + 2) :
    ∃ n, m = q * n + (q - 2) :=
  (exists_mul_add_sub_two_iff_dvd_add_two_of_le (q := q) (m := m) hq).2 hm

/-- Nonmembership in the `q-2` residue class gives nondivisibility of `m+2`. -/
theorem not_dvd_add_two_of_not_exists_mul_add_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : ¬ ∃ n, m = q * n + (q - 2)) :
    ¬ (q ∣ m + 2) :=
  (not_exists_mul_add_sub_two_iff_not_dvd_add_two_of_le (q := q) (m := m)
    hq).1 hm

/-- Nondivisibility of `m+2` gives nonmembership in the `q-2` residue class. -/
theorem not_exists_mul_add_sub_two_of_not_dvd_add_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : ¬ (q ∣ m + 2)) :
    ¬ ∃ n, m = q * n + (q - 2) :=
  (not_exists_mul_add_sub_two_iff_not_dvd_add_two_of_le (q := q) (m := m)
    hq).2 hm

/-- Membership in the `q-5` residue class gives divisibility of `m+5`. -/
theorem dvd_add_five_of_exists_mul_add_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : ∃ n, m = q * n + (q - 5)) :
    q ∣ m + 5 :=
  (exists_mul_add_sub_five_iff_dvd_add_five_of_le (q := q) (m := m) hq).1 hm

/-- Divisibility of `m+5` gives membership in the `q-5` residue class. -/
theorem exists_mul_add_sub_five_of_dvd_add_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : q ∣ m + 5) :
    ∃ n, m = q * n + (q - 5) :=
  (exists_mul_add_sub_five_iff_dvd_add_five_of_le (q := q) (m := m) hq).2 hm

/-- Nonmembership in the `q-5` residue class gives nondivisibility of `m+5`. -/
theorem not_dvd_add_five_of_not_exists_mul_add_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : ¬ ∃ n, m = q * n + (q - 5)) :
    ¬ (q ∣ m + 5) :=
  (not_exists_mul_add_sub_five_iff_not_dvd_add_five_of_le (q := q) (m := m)
    hq).1 hm

/-- Nondivisibility of `m+5` gives nonmembership in the `q-5` residue class. -/
theorem not_exists_mul_add_sub_five_of_not_dvd_add_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : ¬ (q ∣ m + 5)) :
    ¬ ∃ n, m = q * n + (q - 5) :=
  (not_exists_mul_add_sub_five_iff_not_dvd_add_five_of_le (q := q) (m := m)
    hq).2 hm

/-- Membership in the residue class `q-c` is equivalent to direct residue
equality. -/
theorem exists_mul_add_sub_iff_mod_eq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    (∃ n, m = q * n + (q - c)) ↔ m % q = q - c := by
  exact Iff.trans
    (exists_mul_add_sub_iff_dvd_add_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq)
    (dvd_add_iff_mod_eq_sub_of_pos_le (q := q) (c := c) (m := m) hc0 hcq)

/-- Direct residue equality is equivalent to membership in the residue class
`q-c`. -/
theorem mod_eq_sub_iff_exists_mul_add_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    m % q = q - c ↔ ∃ n, m = q * n + (q - c) :=
  (exists_mul_add_sub_iff_mod_eq_sub_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).symm

/-- Nonmembership in the residue class `q-c` is equivalent to direct residue
inequality. -/
theorem not_exists_mul_add_sub_iff_mod_ne_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    (¬ ∃ n, m = q * n + (q - c)) ↔ m % q ≠ q - c := by
  exact Iff.trans
    (not_exists_mul_add_sub_iff_not_dvd_add_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq)
    (not_dvd_add_iff_mod_ne_sub_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq)

/-- Direct residue inequality is equivalent to nonmembership in the residue
class `q-c`. -/
theorem mod_ne_sub_iff_not_exists_mul_add_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    m % q ≠ q - c ↔ ¬ ∃ n, m = q * n + (q - c) :=
  (not_exists_mul_add_sub_iff_mod_ne_sub_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).symm

/-- Membership in the residue class `q-c` gives direct residue equality. -/
theorem mod_eq_sub_of_exists_mul_add_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : ∃ n, m = q * n + (q - c)) :
    m % q = q - c :=
  (exists_mul_add_sub_iff_mod_eq_sub_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).1 hm

/-- Direct residue equality gives membership in the residue class `q-c`. -/
theorem exists_mul_add_sub_of_mod_eq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : m % q = q - c) :
    ∃ n, m = q * n + (q - c) :=
  (exists_mul_add_sub_iff_mod_eq_sub_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).2 hm

/-- Nonmembership in the residue class `q-c` gives direct residue inequality. -/
theorem mod_ne_sub_of_not_exists_mul_add_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q)
    (hm : ¬ ∃ n, m = q * n + (q - c)) :
    m % q ≠ q - c :=
  (not_exists_mul_add_sub_iff_mod_ne_sub_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).1 hm

/-- Direct residue inequality gives nonmembership in the residue class `q-c`. -/
theorem not_exists_mul_add_sub_of_mod_ne_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : m % q ≠ q - c) :
    ¬ ∃ n, m = q * n + (q - c) :=
  (not_exists_mul_add_sub_iff_mod_ne_sub_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).2 hm

/-- Membership in the predecessor residue class is equivalent to the
predecessor residue. -/
theorem exists_mul_add_pred_iff_mod_eq_pred {q m : ℕ} (hq : 0 < q) :
    (∃ n, m = q * n + (q - 1)) ↔ m % q = q - 1 :=
  exists_mul_add_sub_iff_mod_eq_sub_of_pos_le (q := q) (c := 1) (m := m)
    (by decide) hq

/-- The predecessor residue is equivalent to membership in the predecessor
residue class. -/
theorem mod_eq_pred_iff_exists_mul_add_pred {q m : ℕ} (hq : 0 < q) :
    m % q = q - 1 ↔ ∃ n, m = q * n + (q - 1) :=
  (exists_mul_add_pred_iff_mod_eq_pred (q := q) (m := m) hq).symm

/-- Nonmembership in the predecessor residue class is equivalent to avoiding
the predecessor residue. -/
theorem not_exists_mul_add_pred_iff_mod_ne_pred {q m : ℕ} (hq : 0 < q) :
    (¬ ∃ n, m = q * n + (q - 1)) ↔ m % q ≠ q - 1 :=
  not_exists_mul_add_sub_iff_mod_ne_sub_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- Avoiding the predecessor residue is equivalent to nonmembership in the
predecessor residue class. -/
theorem mod_ne_pred_iff_not_exists_mul_add_pred {q m : ℕ} (hq : 0 < q) :
    m % q ≠ q - 1 ↔ ¬ ∃ n, m = q * n + (q - 1) :=
  (not_exists_mul_add_pred_iff_mod_ne_pred (q := q) (m := m) hq).symm

/-- Membership in the `q-2` residue class is equivalent to residue `q-2`. -/
theorem exists_mul_add_sub_two_iff_mod_eq_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    (∃ n, m = q * n + (q - 2)) ↔ m % q = q - 2 :=
  exists_mul_add_sub_iff_mod_eq_sub_of_pos_le (q := q) (c := 2) (m := m)
    (by decide) hq

/-- Residue `q-2` is equivalent to membership in the `q-2` residue class. -/
theorem mod_eq_sub_two_iff_exists_mul_add_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    m % q = q - 2 ↔ ∃ n, m = q * n + (q - 2) :=
  (exists_mul_add_sub_two_iff_mod_eq_sub_two_of_le (q := q) (m := m) hq).symm

/-- Nonmembership in the `q-2` residue class is equivalent to avoiding residue
`q-2`. -/
theorem not_exists_mul_add_sub_two_iff_mod_ne_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    (¬ ∃ n, m = q * n + (q - 2)) ↔ m % q ≠ q - 2 :=
  not_exists_mul_add_sub_iff_mod_ne_sub_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- Avoiding residue `q-2` is equivalent to nonmembership in the `q-2` residue
class. -/
theorem mod_ne_sub_two_iff_not_exists_mul_add_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    m % q ≠ q - 2 ↔ ¬ ∃ n, m = q * n + (q - 2) :=
  (not_exists_mul_add_sub_two_iff_mod_ne_sub_two_of_le (q := q) (m := m)
    hq).symm

/-- Membership in the `q-5` residue class is equivalent to residue `q-5`. -/
theorem exists_mul_add_sub_five_iff_mod_eq_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    (∃ n, m = q * n + (q - 5)) ↔ m % q = q - 5 :=
  exists_mul_add_sub_iff_mod_eq_sub_of_pos_le (q := q) (c := 5) (m := m)
    (by decide) hq

/-- Residue `q-5` is equivalent to membership in the `q-5` residue class. -/
theorem mod_eq_sub_five_iff_exists_mul_add_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    m % q = q - 5 ↔ ∃ n, m = q * n + (q - 5) :=
  (exists_mul_add_sub_five_iff_mod_eq_sub_five_of_le (q := q) (m := m)
    hq).symm

/-- Nonmembership in the `q-5` residue class is equivalent to avoiding residue
`q-5`. -/
theorem not_exists_mul_add_sub_five_iff_mod_ne_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    (¬ ∃ n, m = q * n + (q - 5)) ↔ m % q ≠ q - 5 :=
  not_exists_mul_add_sub_iff_mod_ne_sub_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- Avoiding residue `q-5` is equivalent to nonmembership in the `q-5` residue
class. -/
theorem mod_ne_sub_five_iff_not_exists_mul_add_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    m % q ≠ q - 5 ↔ ¬ ∃ n, m = q * n + (q - 5) :=
  (not_exists_mul_add_sub_five_iff_mod_ne_sub_five_of_le (q := q) (m := m)
    hq).symm

/-- Membership in the predecessor residue class gives the predecessor residue. -/
theorem mod_eq_pred_of_exists_mul_add_pred {q m : ℕ} (hq : 0 < q)
    (hm : ∃ n, m = q * n + (q - 1)) :
    m % q = q - 1 :=
  (exists_mul_add_pred_iff_mod_eq_pred (q := q) (m := m) hq).1 hm

/-- The predecessor residue gives membership in the predecessor residue class. -/
theorem exists_mul_add_pred_of_mod_eq_pred {q m : ℕ} (hq : 0 < q)
    (hm : m % q = q - 1) :
    ∃ n, m = q * n + (q - 1) :=
  (exists_mul_add_pred_iff_mod_eq_pred (q := q) (m := m) hq).2 hm

/-- Nonmembership in the predecessor residue class gives avoidance of the
predecessor residue. -/
theorem mod_ne_pred_of_not_exists_mul_add_pred {q m : ℕ} (hq : 0 < q)
    (hm : ¬ ∃ n, m = q * n + (q - 1)) :
    m % q ≠ q - 1 :=
  (not_exists_mul_add_pred_iff_mod_ne_pred (q := q) (m := m) hq).1 hm

/-- Avoiding the predecessor residue gives nonmembership in the predecessor
residue class. -/
theorem not_exists_mul_add_pred_of_mod_ne_pred {q m : ℕ} (hq : 0 < q)
    (hm : m % q ≠ q - 1) :
    ¬ ∃ n, m = q * n + (q - 1) :=
  (not_exists_mul_add_pred_iff_mod_ne_pred (q := q) (m := m) hq).2 hm

/-- Membership in the `q-2` residue class gives residue `q-2`. -/
theorem mod_eq_sub_two_of_exists_mul_add_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : ∃ n, m = q * n + (q - 2)) :
    m % q = q - 2 :=
  (exists_mul_add_sub_two_iff_mod_eq_sub_two_of_le (q := q) (m := m) hq).1 hm

/-- Residue `q-2` gives membership in the `q-2` residue class. -/
theorem exists_mul_add_sub_two_of_mod_eq_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : m % q = q - 2) :
    ∃ n, m = q * n + (q - 2) :=
  (exists_mul_add_sub_two_iff_mod_eq_sub_two_of_le (q := q) (m := m) hq).2 hm

/-- Nonmembership in the `q-2` residue class gives avoidance of residue
`q-2`. -/
theorem mod_ne_sub_two_of_not_exists_mul_add_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : ¬ ∃ n, m = q * n + (q - 2)) :
    m % q ≠ q - 2 :=
  (not_exists_mul_add_sub_two_iff_mod_ne_sub_two_of_le (q := q) (m := m)
    hq).1 hm

/-- Avoiding residue `q-2` gives nonmembership in the `q-2` residue class. -/
theorem not_exists_mul_add_sub_two_of_mod_ne_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : m % q ≠ q - 2) :
    ¬ ∃ n, m = q * n + (q - 2) :=
  (not_exists_mul_add_sub_two_iff_mod_ne_sub_two_of_le (q := q) (m := m)
    hq).2 hm

/-- Membership in the `q-5` residue class gives residue `q-5`. -/
theorem mod_eq_sub_five_of_exists_mul_add_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : ∃ n, m = q * n + (q - 5)) :
    m % q = q - 5 :=
  (exists_mul_add_sub_five_iff_mod_eq_sub_five_of_le (q := q) (m := m)
    hq).1 hm

/-- Residue `q-5` gives membership in the `q-5` residue class. -/
theorem exists_mul_add_sub_five_of_mod_eq_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : m % q = q - 5) :
    ∃ n, m = q * n + (q - 5) :=
  (exists_mul_add_sub_five_iff_mod_eq_sub_five_of_le (q := q) (m := m)
    hq).2 hm

/-- Nonmembership in the `q-5` residue class gives avoidance of residue
`q-5`. -/
theorem mod_ne_sub_five_of_not_exists_mul_add_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : ¬ ∃ n, m = q * n + (q - 5)) :
    m % q ≠ q - 5 :=
  (not_exists_mul_add_sub_five_iff_mod_ne_sub_five_of_le (q := q) (m := m)
    hq).1 hm

/-- Avoiding residue `q-5` gives nonmembership in the `q-5` residue class. -/
theorem not_exists_mul_add_sub_five_of_mod_ne_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : m % q ≠ q - 5) :
    ¬ ∃ n, m = q * n + (q - 5) :=
  (not_exists_mul_add_sub_five_iff_mod_ne_sub_five_of_le (q := q) (m := m)
    hq).2 hm

/-- Membership in the residue class `q-c` is equivalent to `Nat.ModEq` to
`q-c`. -/
theorem exists_mul_add_sub_iff_modEq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    (∃ n, m = q * n + (q - c)) ↔ m ≡ q - c [MOD q] := by
  exact Iff.trans
    (exists_mul_add_sub_iff_dvd_add_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq)
    (dvd_add_iff_modEq_sub_of_pos_le (q := q) (c := c) (m := m) hc0 hcq)

/-- `Nat.ModEq` to `q-c` is equivalent to membership in the residue class
`q-c`. -/
theorem modEq_sub_iff_exists_mul_add_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    m ≡ q - c [MOD q] ↔ ∃ n, m = q * n + (q - c) :=
  (exists_mul_add_sub_iff_modEq_sub_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).symm

/-- Nonmembership in the residue class `q-c` is equivalent to negated
`Nat.ModEq` to `q-c`. -/
theorem not_exists_mul_add_sub_iff_not_modEq_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    (¬ ∃ n, m = q * n + (q - c)) ↔ ¬ (m ≡ q - c [MOD q]) := by
  exact Iff.trans
    (not_exists_mul_add_sub_iff_not_dvd_add_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq)
    (not_dvd_add_iff_not_modEq_sub_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq)

/-- Negated `Nat.ModEq` to `q-c` is equivalent to nonmembership in the residue
class `q-c`. -/
theorem not_modEq_sub_iff_not_exists_mul_add_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    ¬ (m ≡ q - c [MOD q]) ↔ ¬ ∃ n, m = q * n + (q - c) :=
  (not_exists_mul_add_sub_iff_not_modEq_sub_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).symm

/-- Membership in the predecessor residue class is equivalent to `Nat.ModEq`
to the predecessor residue. -/
theorem exists_mul_add_pred_iff_modEq_pred {q m : ℕ} (hq : 0 < q) :
    (∃ n, m = q * n + (q - 1)) ↔ m ≡ q - 1 [MOD q] :=
  exists_mul_add_sub_iff_modEq_sub_of_pos_le (q := q) (c := 1) (m := m)
    (by decide) hq

/-- `Nat.ModEq` to the predecessor residue is equivalent to membership in the
predecessor residue class. -/
theorem modEq_pred_iff_exists_mul_add_pred {q m : ℕ} (hq : 0 < q) :
    m ≡ q - 1 [MOD q] ↔ ∃ n, m = q * n + (q - 1) :=
  (exists_mul_add_pred_iff_modEq_pred (q := q) (m := m) hq).symm

/-- Nonmembership in the predecessor residue class is equivalent to negated
`Nat.ModEq` to the predecessor residue. -/
theorem not_exists_mul_add_pred_iff_not_modEq_pred {q m : ℕ} (hq : 0 < q) :
    (¬ ∃ n, m = q * n + (q - 1)) ↔ ¬ (m ≡ q - 1 [MOD q]) :=
  not_exists_mul_add_sub_iff_not_modEq_sub_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- Negated `Nat.ModEq` to the predecessor residue is equivalent to
nonmembership in the predecessor residue class. -/
theorem not_modEq_pred_iff_not_exists_mul_add_pred {q m : ℕ} (hq : 0 < q) :
    ¬ (m ≡ q - 1 [MOD q]) ↔ ¬ ∃ n, m = q * n + (q - 1) :=
  (not_exists_mul_add_pred_iff_not_modEq_pred (q := q) (m := m) hq).symm

/-- Membership in the `q-2` residue class is equivalent to `Nat.ModEq` to
`q-2`. -/
theorem exists_mul_add_sub_two_iff_modEq_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    (∃ n, m = q * n + (q - 2)) ↔ m ≡ q - 2 [MOD q] :=
  exists_mul_add_sub_iff_modEq_sub_of_pos_le (q := q) (c := 2) (m := m)
    (by decide) hq

/-- `Nat.ModEq` to `q-2` is equivalent to membership in the `q-2` residue
class. -/
theorem modEq_sub_two_iff_exists_mul_add_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    m ≡ q - 2 [MOD q] ↔ ∃ n, m = q * n + (q - 2) :=
  (exists_mul_add_sub_two_iff_modEq_sub_two_of_le (q := q) (m := m) hq).symm

/-- Nonmembership in the `q-2` residue class is equivalent to negated
`Nat.ModEq` to `q-2`. -/
theorem not_exists_mul_add_sub_two_iff_not_modEq_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    (¬ ∃ n, m = q * n + (q - 2)) ↔ ¬ (m ≡ q - 2 [MOD q]) :=
  not_exists_mul_add_sub_iff_not_modEq_sub_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- Negated `Nat.ModEq` to `q-2` is equivalent to nonmembership in the `q-2`
residue class. -/
theorem not_modEq_sub_two_iff_not_exists_mul_add_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    ¬ (m ≡ q - 2 [MOD q]) ↔ ¬ ∃ n, m = q * n + (q - 2) :=
  (not_exists_mul_add_sub_two_iff_not_modEq_sub_two_of_le (q := q) (m := m)
    hq).symm

/-- Membership in the `q-5` residue class is equivalent to `Nat.ModEq` to
`q-5`. -/
theorem exists_mul_add_sub_five_iff_modEq_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    (∃ n, m = q * n + (q - 5)) ↔ m ≡ q - 5 [MOD q] :=
  exists_mul_add_sub_iff_modEq_sub_of_pos_le (q := q) (c := 5) (m := m)
    (by decide) hq

/-- `Nat.ModEq` to `q-5` is equivalent to membership in the `q-5` residue
class. -/
theorem modEq_sub_five_iff_exists_mul_add_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    m ≡ q - 5 [MOD q] ↔ ∃ n, m = q * n + (q - 5) :=
  (exists_mul_add_sub_five_iff_modEq_sub_five_of_le (q := q) (m := m)
    hq).symm

/-- Nonmembership in the `q-5` residue class is equivalent to negated
`Nat.ModEq` to `q-5`. -/
theorem not_exists_mul_add_sub_five_iff_not_modEq_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    (¬ ∃ n, m = q * n + (q - 5)) ↔ ¬ (m ≡ q - 5 [MOD q]) :=
  not_exists_mul_add_sub_iff_not_modEq_sub_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- Negated `Nat.ModEq` to `q-5` is equivalent to nonmembership in the `q-5`
residue class. -/
theorem not_modEq_sub_five_iff_not_exists_mul_add_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    ¬ (m ≡ q - 5 [MOD q]) ↔ ¬ ∃ n, m = q * n + (q - 5) :=
  (not_exists_mul_add_sub_five_iff_not_modEq_sub_five_of_le (q := q) (m := m)
    hq).symm

/-- Membership in the residue class `q-c` gives `Nat.ModEq` to `q-c`. -/
theorem modEq_sub_of_exists_mul_add_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : ∃ n, m = q * n + (q - c)) :
    m ≡ q - c [MOD q] :=
  (exists_mul_add_sub_iff_modEq_sub_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).1 hm

/-- `Nat.ModEq` to `q-c` gives membership in the residue class `q-c`. -/
theorem exists_mul_add_sub_of_modEq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : m ≡ q - c [MOD q]) :
    ∃ n, m = q * n + (q - c) :=
  (exists_mul_add_sub_iff_modEq_sub_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).2 hm

/-- Nonmembership in the residue class `q-c` gives negated `Nat.ModEq` to
`q-c`. -/
theorem not_modEq_sub_of_not_exists_mul_add_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q)
    (hm : ¬ ∃ n, m = q * n + (q - c)) :
    ¬ (m ≡ q - c [MOD q]) :=
  (not_exists_mul_add_sub_iff_not_modEq_sub_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).1 hm

/-- Negated `Nat.ModEq` to `q-c` gives nonmembership in the residue class
`q-c`. -/
theorem not_exists_mul_add_sub_of_not_modEq_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : ¬ (m ≡ q - c [MOD q])) :
    ¬ ∃ n, m = q * n + (q - c) :=
  (not_exists_mul_add_sub_iff_not_modEq_sub_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).2 hm

/-- Membership in the predecessor residue class gives `Nat.ModEq` to the
predecessor residue. -/
theorem modEq_pred_of_exists_mul_add_pred {q m : ℕ} (hq : 0 < q)
    (hm : ∃ n, m = q * n + (q - 1)) :
    m ≡ q - 1 [MOD q] :=
  (exists_mul_add_pred_iff_modEq_pred (q := q) (m := m) hq).1 hm

/-- `Nat.ModEq` to the predecessor residue gives membership in the predecessor
residue class. -/
theorem exists_mul_add_pred_of_modEq_pred {q m : ℕ} (hq : 0 < q)
    (hm : m ≡ q - 1 [MOD q]) :
    ∃ n, m = q * n + (q - 1) :=
  (exists_mul_add_pred_iff_modEq_pred (q := q) (m := m) hq).2 hm

/-- Nonmembership in the predecessor residue class gives negated `Nat.ModEq`
to the predecessor residue. -/
theorem not_modEq_pred_of_not_exists_mul_add_pred {q m : ℕ} (hq : 0 < q)
    (hm : ¬ ∃ n, m = q * n + (q - 1)) :
    ¬ (m ≡ q - 1 [MOD q]) :=
  (not_exists_mul_add_pred_iff_not_modEq_pred (q := q) (m := m) hq).1 hm

/-- Negated `Nat.ModEq` to the predecessor residue gives nonmembership in the
predecessor residue class. -/
theorem not_exists_mul_add_pred_of_not_modEq_pred {q m : ℕ} (hq : 0 < q)
    (hm : ¬ (m ≡ q - 1 [MOD q])) :
    ¬ ∃ n, m = q * n + (q - 1) :=
  (not_exists_mul_add_pred_iff_not_modEq_pred (q := q) (m := m) hq).2 hm

/-- Membership in the `q-2` residue class gives `Nat.ModEq` to `q-2`. -/
theorem modEq_sub_two_of_exists_mul_add_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : ∃ n, m = q * n + (q - 2)) :
    m ≡ q - 2 [MOD q] :=
  (exists_mul_add_sub_two_iff_modEq_sub_two_of_le (q := q) (m := m) hq).1 hm

/-- `Nat.ModEq` to `q-2` gives membership in the `q-2` residue class. -/
theorem exists_mul_add_sub_two_of_modEq_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : m ≡ q - 2 [MOD q]) :
    ∃ n, m = q * n + (q - 2) :=
  (exists_mul_add_sub_two_iff_modEq_sub_two_of_le (q := q) (m := m) hq).2 hm

/-- Nonmembership in the `q-2` residue class gives negated `Nat.ModEq` to
`q-2`. -/
theorem not_modEq_sub_two_of_not_exists_mul_add_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : ¬ ∃ n, m = q * n + (q - 2)) :
    ¬ (m ≡ q - 2 [MOD q]) :=
  (not_exists_mul_add_sub_two_iff_not_modEq_sub_two_of_le (q := q) (m := m)
    hq).1 hm

/-- Negated `Nat.ModEq` to `q-2` gives nonmembership in the `q-2` residue
class. -/
theorem not_exists_mul_add_sub_two_of_not_modEq_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : ¬ (m ≡ q - 2 [MOD q])) :
    ¬ ∃ n, m = q * n + (q - 2) :=
  (not_exists_mul_add_sub_two_iff_not_modEq_sub_two_of_le (q := q) (m := m)
    hq).2 hm

/-- Membership in the `q-5` residue class gives `Nat.ModEq` to `q-5`. -/
theorem modEq_sub_five_of_exists_mul_add_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : ∃ n, m = q * n + (q - 5)) :
    m ≡ q - 5 [MOD q] :=
  (exists_mul_add_sub_five_iff_modEq_sub_five_of_le (q := q) (m := m)
    hq).1 hm

/-- `Nat.ModEq` to `q-5` gives membership in the `q-5` residue class. -/
theorem exists_mul_add_sub_five_of_modEq_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : m ≡ q - 5 [MOD q]) :
    ∃ n, m = q * n + (q - 5) :=
  (exists_mul_add_sub_five_iff_modEq_sub_five_of_le (q := q) (m := m)
    hq).2 hm

/-- Nonmembership in the `q-5` residue class gives negated `Nat.ModEq` to
`q-5`. -/
theorem not_modEq_sub_five_of_not_exists_mul_add_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : ¬ ∃ n, m = q * n + (q - 5)) :
    ¬ (m ≡ q - 5 [MOD q]) :=
  (not_exists_mul_add_sub_five_iff_not_modEq_sub_five_of_le (q := q) (m := m)
    hq).1 hm

/-- Negated `Nat.ModEq` to `q-5` gives nonmembership in the `q-5` residue
class. -/
theorem not_exists_mul_add_sub_five_of_not_modEq_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : ¬ (m ≡ q - 5 [MOD q])) :
    ¬ ∃ n, m = q * n + (q - 5) :=
  (not_exists_mul_add_sub_five_iff_not_modEq_sub_five_of_le (q := q) (m := m)
    hq).2 hm

/-- Direct residue equality to `q-c` is equivalent to `Nat.ModEq` to `q-c`. -/
theorem mod_eq_sub_iff_modEq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    m % q = q - c ↔ m ≡ q - c [MOD q] := by
  have hred : q - c < q := by omega
  exact mod_eq_iff_modEq_of_lt (q := q) (r := q - c) (m := m) hred

/-- `Nat.ModEq` to `q-c` is equivalent to direct residue equality to `q-c`. -/
theorem modEq_sub_iff_mod_eq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    m ≡ q - c [MOD q] ↔ m % q = q - c :=
  (mod_eq_sub_iff_modEq_sub_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).symm

/-- Negated `Nat.ModEq` to `q-c` is equivalent to avoiding residue `q-c`. -/
theorem not_modEq_sub_iff_mod_ne_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    ¬ (m ≡ q - c [MOD q]) ↔ m % q ≠ q - c := by
  have hred : q - c < q := by omega
  exact not_modEq_iff_mod_ne_of_lt (q := q) (r := q - c) (m := m) hred

/-- Avoiding residue `q-c` is equivalent to negated `Nat.ModEq` to `q-c`. -/
theorem mod_ne_sub_iff_not_modEq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) :
    m % q ≠ q - c ↔ ¬ (m ≡ q - c [MOD q]) :=
  (not_modEq_sub_iff_mod_ne_sub_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).symm

/-- Direct residue equality to `q-c` gives `Nat.ModEq` to `q-c`. -/
theorem modEq_sub_of_mod_eq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : m % q = q - c) :
    m ≡ q - c [MOD q] :=
  (mod_eq_sub_iff_modEq_sub_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).1 hm

/-- `Nat.ModEq` to `q-c` gives direct residue equality to `q-c`. -/
theorem mod_eq_sub_of_modEq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : m ≡ q - c [MOD q]) :
    m % q = q - c :=
  (mod_eq_sub_iff_modEq_sub_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).2 hm

/-- Avoiding residue `q-c` gives negated `Nat.ModEq` to `q-c`. -/
theorem not_modEq_sub_of_mod_ne_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : m % q ≠ q - c) :
    ¬ (m ≡ q - c [MOD q]) :=
  (mod_ne_sub_iff_not_modEq_sub_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).1 hm

/-- Negated `Nat.ModEq` to `q-c` gives avoidance of residue `q-c`. -/
theorem mod_ne_sub_of_not_modEq_sub_of_pos_le {q c m : ℕ} (hc0 : 0 < c)
    (hcq : c ≤ q) (hm : ¬ (m ≡ q - c [MOD q])) :
    m % q ≠ q - c :=
  (mod_ne_sub_iff_not_modEq_sub_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).2 hm

/-- Direct predecessor residue is equivalent to `Nat.ModEq` to the predecessor
residue. -/
theorem mod_eq_pred_iff_modEq_pred {q m : ℕ} (hq : 0 < q) :
    m % q = q - 1 ↔ m ≡ q - 1 [MOD q] :=
  mod_eq_sub_iff_modEq_sub_of_pos_le (q := q) (c := 1) (m := m)
    (by decide) hq

/-- `Nat.ModEq` to the predecessor residue is equivalent to direct predecessor
residue. -/
theorem modEq_pred_iff_mod_eq_pred {q m : ℕ} (hq : 0 < q) :
    m ≡ q - 1 [MOD q] ↔ m % q = q - 1 :=
  (mod_eq_pred_iff_modEq_pred (q := q) (m := m) hq).symm

/-- Negated `Nat.ModEq` to the predecessor residue is equivalent to avoiding
the predecessor residue. -/
theorem not_modEq_pred_iff_mod_ne_pred {q m : ℕ} (hq : 0 < q) :
    ¬ (m ≡ q - 1 [MOD q]) ↔ m % q ≠ q - 1 :=
  not_modEq_sub_iff_mod_ne_sub_of_pos_le (q := q) (c := 1) (m := m)
    (by decide) hq

/-- Avoiding the predecessor residue is equivalent to negated `Nat.ModEq` to
the predecessor residue. -/
theorem mod_ne_pred_iff_not_modEq_pred {q m : ℕ} (hq : 0 < q) :
    m % q ≠ q - 1 ↔ ¬ (m ≡ q - 1 [MOD q]) :=
  (not_modEq_pred_iff_mod_ne_pred (q := q) (m := m) hq).symm

/-- Direct residue `q-2` is equivalent to `Nat.ModEq` to `q-2`. -/
theorem mod_eq_sub_two_iff_modEq_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q) :
    m % q = q - 2 ↔ m ≡ q - 2 [MOD q] :=
  mod_eq_sub_iff_modEq_sub_of_pos_le (q := q) (c := 2) (m := m)
    (by decide) hq

/-- `Nat.ModEq` to `q-2` is equivalent to direct residue `q-2`. -/
theorem modEq_sub_two_iff_mod_eq_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q) :
    m ≡ q - 2 [MOD q] ↔ m % q = q - 2 :=
  (mod_eq_sub_two_iff_modEq_sub_two_of_le (q := q) (m := m) hq).symm

/-- Negated `Nat.ModEq` to `q-2` is equivalent to avoiding residue `q-2`. -/
theorem not_modEq_sub_two_iff_mod_ne_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q) :
    ¬ (m ≡ q - 2 [MOD q]) ↔ m % q ≠ q - 2 :=
  not_modEq_sub_iff_mod_ne_sub_of_pos_le (q := q) (c := 2) (m := m)
    (by decide) hq

/-- Avoiding residue `q-2` is equivalent to negated `Nat.ModEq` to `q-2`. -/
theorem mod_ne_sub_two_iff_not_modEq_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q) :
    m % q ≠ q - 2 ↔ ¬ (m ≡ q - 2 [MOD q]) :=
  (not_modEq_sub_two_iff_mod_ne_sub_two_of_le (q := q) (m := m) hq).symm

/-- Direct residue `q-5` is equivalent to `Nat.ModEq` to `q-5`. -/
theorem mod_eq_sub_five_iff_modEq_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q) :
    m % q = q - 5 ↔ m ≡ q - 5 [MOD q] :=
  mod_eq_sub_iff_modEq_sub_of_pos_le (q := q) (c := 5) (m := m)
    (by decide) hq

/-- `Nat.ModEq` to `q-5` is equivalent to direct residue `q-5`. -/
theorem modEq_sub_five_iff_mod_eq_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q) :
    m ≡ q - 5 [MOD q] ↔ m % q = q - 5 :=
  (mod_eq_sub_five_iff_modEq_sub_five_of_le (q := q) (m := m) hq).symm

/-- Negated `Nat.ModEq` to `q-5` is equivalent to avoiding residue `q-5`. -/
theorem not_modEq_sub_five_iff_mod_ne_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q) :
    ¬ (m ≡ q - 5 [MOD q]) ↔ m % q ≠ q - 5 :=
  not_modEq_sub_iff_mod_ne_sub_of_pos_le (q := q) (c := 5) (m := m)
    (by decide) hq

/-- Avoiding residue `q-5` is equivalent to negated `Nat.ModEq` to `q-5`. -/
theorem mod_ne_sub_five_iff_not_modEq_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q) :
    m % q ≠ q - 5 ↔ ¬ (m ≡ q - 5 [MOD q]) :=
  (not_modEq_sub_five_iff_mod_ne_sub_five_of_le (q := q) (m := m) hq).symm

/-- Direct predecessor residue gives `Nat.ModEq` to the predecessor residue. -/
theorem modEq_pred_of_mod_eq_pred {q m : ℕ} (hq : 0 < q)
    (hm : m % q = q - 1) :
    m ≡ q - 1 [MOD q] :=
  (mod_eq_pred_iff_modEq_pred (q := q) (m := m) hq).1 hm

/-- `Nat.ModEq` to the predecessor residue gives direct predecessor residue. -/
theorem mod_eq_pred_of_modEq_pred {q m : ℕ} (hq : 0 < q)
    (hm : m ≡ q - 1 [MOD q]) :
    m % q = q - 1 :=
  (mod_eq_pred_iff_modEq_pred (q := q) (m := m) hq).2 hm

/-- Avoiding the predecessor residue gives negated `Nat.ModEq` to the
predecessor residue. -/
theorem not_modEq_pred_of_mod_ne_pred {q m : ℕ} (hq : 0 < q)
    (hm : m % q ≠ q - 1) :
    ¬ (m ≡ q - 1 [MOD q]) :=
  (mod_ne_pred_iff_not_modEq_pred (q := q) (m := m) hq).1 hm

/-- Negated `Nat.ModEq` to the predecessor residue gives avoidance of the
predecessor residue. -/
theorem mod_ne_pred_of_not_modEq_pred {q m : ℕ} (hq : 0 < q)
    (hm : ¬ (m ≡ q - 1 [MOD q])) :
    m % q ≠ q - 1 :=
  (mod_ne_pred_iff_not_modEq_pred (q := q) (m := m) hq).2 hm

/-- Direct residue `q-2` gives `Nat.ModEq` to `q-2`. -/
theorem modEq_sub_two_of_mod_eq_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : m % q = q - 2) :
    m ≡ q - 2 [MOD q] :=
  (mod_eq_sub_two_iff_modEq_sub_two_of_le (q := q) (m := m) hq).1 hm

/-- `Nat.ModEq` to `q-2` gives direct residue `q-2`. -/
theorem mod_eq_sub_two_of_modEq_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : m ≡ q - 2 [MOD q]) :
    m % q = q - 2 :=
  (mod_eq_sub_two_iff_modEq_sub_two_of_le (q := q) (m := m) hq).2 hm

/-- Avoiding residue `q-2` gives negated `Nat.ModEq` to `q-2`. -/
theorem not_modEq_sub_two_of_mod_ne_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : m % q ≠ q - 2) :
    ¬ (m ≡ q - 2 [MOD q]) :=
  (mod_ne_sub_two_iff_not_modEq_sub_two_of_le (q := q) (m := m) hq).1 hm

/-- Negated `Nat.ModEq` to `q-2` gives avoidance of residue `q-2`. -/
theorem mod_ne_sub_two_of_not_modEq_sub_two_of_le {q m : ℕ} (hq : 2 ≤ q)
    (hm : ¬ (m ≡ q - 2 [MOD q])) :
    m % q ≠ q - 2 :=
  (mod_ne_sub_two_iff_not_modEq_sub_two_of_le (q := q) (m := m) hq).2 hm

/-- Direct residue `q-5` gives `Nat.ModEq` to `q-5`. -/
theorem modEq_sub_five_of_mod_eq_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q)
    (hm : m % q = q - 5) :
    m ≡ q - 5 [MOD q] :=
  (mod_eq_sub_five_iff_modEq_sub_five_of_le (q := q) (m := m) hq).1 hm

/-- `Nat.ModEq` to `q-5` gives direct residue `q-5`. -/
theorem mod_eq_sub_five_of_modEq_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q)
    (hm : m ≡ q - 5 [MOD q]) :
    m % q = q - 5 :=
  (mod_eq_sub_five_iff_modEq_sub_five_of_le (q := q) (m := m) hq).2 hm

/-- Avoiding residue `q-5` gives negated `Nat.ModEq` to `q-5`. -/
theorem not_modEq_sub_five_of_mod_ne_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q)
    (hm : m % q ≠ q - 5) :
    ¬ (m ≡ q - 5 [MOD q]) :=
  (mod_ne_sub_five_iff_not_modEq_sub_five_of_le (q := q) (m := m) hq).1 hm

/-- Negated `Nat.ModEq` to `q-5` gives avoidance of residue `q-5`. -/
theorem mod_ne_sub_five_of_not_modEq_sub_five_of_le {q m : ℕ} (hq : 5 ≤ q)
    (hm : ¬ (m ≡ q - 5 [MOD q])) :
    m % q ≠ q - 5 :=
  (mod_ne_sub_five_iff_not_modEq_sub_five_of_le (q := q) (m := m) hq).2 hm

/-- The four standard positive descriptions of the residue class `q-c`. -/
theorem sub_residue_positive_equivalence_facts_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    ((∃ n, m = q * n + (q - c)) ↔ m % q = q - c) ∧
      ((∃ n, m = q * n + (q - c)) ↔ q ∣ m + c) ∧
      ((∃ n, m = q * n + (q - c)) ↔ m ≡ q - c [MOD q]) ∧
      (m % q = q - c ↔ q ∣ m + c) ∧
      (m % q = q - c ↔ m ≡ q - c [MOD q]) ∧
      (q ∣ m + c ↔ m ≡ q - c [MOD q]) := by
  exact ⟨exists_mul_add_sub_iff_mod_eq_sub_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq,
    exists_mul_add_sub_iff_dvd_add_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq,
    exists_mul_add_sub_iff_modEq_sub_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq,
    mod_eq_sub_iff_dvd_add_of_pos_le (q := q) (c := c) (m := m) hc0 hcq,
    mod_eq_sub_iff_modEq_sub_of_pos_le (q := q) (c := c) (m := m) hc0 hcq,
    dvd_add_iff_modEq_sub_of_pos_le (q := q) (c := c) (m := m) hc0 hcq⟩

/-- The four standard negative descriptions of avoiding the residue class
`q-c`. -/
theorem sub_residue_negative_equivalence_facts_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    ((¬ ∃ n, m = q * n + (q - c)) ↔ m % q ≠ q - c) ∧
      ((¬ ∃ n, m = q * n + (q - c)) ↔ ¬ (q ∣ m + c)) ∧
      ((¬ ∃ n, m = q * n + (q - c)) ↔ ¬ (m ≡ q - c [MOD q])) ∧
      (m % q ≠ q - c ↔ ¬ (q ∣ m + c)) ∧
      (m % q ≠ q - c ↔ ¬ (m ≡ q - c [MOD q])) ∧
      (¬ (q ∣ m + c) ↔ ¬ (m ≡ q - c [MOD q])) := by
  exact ⟨not_exists_mul_add_sub_iff_mod_ne_sub_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq,
    not_exists_mul_add_sub_iff_not_dvd_add_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq,
    not_exists_mul_add_sub_iff_not_modEq_sub_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq,
    mod_ne_sub_iff_not_dvd_add_of_pos_le (q := q) (c := c) (m := m) hc0 hcq,
    mod_ne_sub_iff_not_modEq_sub_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq,
    not_dvd_add_iff_not_modEq_sub_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq⟩

/-- Positive equivalence package for the predecessor residue class. -/
theorem pred_residue_positive_equivalence_facts {q m : ℕ} (hq : 0 < q) :
    ((∃ n, m = q * n + (q - 1)) ↔ m % q = q - 1) ∧
      ((∃ n, m = q * n + (q - 1)) ↔ q ∣ m + 1) ∧
      ((∃ n, m = q * n + (q - 1)) ↔ m ≡ q - 1 [MOD q]) ∧
      (m % q = q - 1 ↔ q ∣ m + 1) ∧
      (m % q = q - 1 ↔ m ≡ q - 1 [MOD q]) ∧
      (q ∣ m + 1 ↔ m ≡ q - 1 [MOD q]) :=
  sub_residue_positive_equivalence_facts_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- Negative equivalence package for avoiding the predecessor residue class. -/
theorem pred_residue_negative_equivalence_facts {q m : ℕ} (hq : 0 < q) :
    ((¬ ∃ n, m = q * n + (q - 1)) ↔ m % q ≠ q - 1) ∧
      ((¬ ∃ n, m = q * n + (q - 1)) ↔ ¬ (q ∣ m + 1)) ∧
      ((¬ ∃ n, m = q * n + (q - 1)) ↔ ¬ (m ≡ q - 1 [MOD q])) ∧
      (m % q ≠ q - 1 ↔ ¬ (q ∣ m + 1)) ∧
      (m % q ≠ q - 1 ↔ ¬ (m ≡ q - 1 [MOD q])) ∧
      (¬ (q ∣ m + 1) ↔ ¬ (m ≡ q - 1 [MOD q])) :=
  sub_residue_negative_equivalence_facts_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- Positive equivalence package for the `q-2` residue class. -/
theorem sub_two_residue_positive_equivalence_facts_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    ((∃ n, m = q * n + (q - 2)) ↔ m % q = q - 2) ∧
      ((∃ n, m = q * n + (q - 2)) ↔ q ∣ m + 2) ∧
      ((∃ n, m = q * n + (q - 2)) ↔ m ≡ q - 2 [MOD q]) ∧
      (m % q = q - 2 ↔ q ∣ m + 2) ∧
      (m % q = q - 2 ↔ m ≡ q - 2 [MOD q]) ∧
      (q ∣ m + 2 ↔ m ≡ q - 2 [MOD q]) :=
  sub_residue_positive_equivalence_facts_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- Negative equivalence package for avoiding the `q-2` residue class. -/
theorem sub_two_residue_negative_equivalence_facts_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    ((¬ ∃ n, m = q * n + (q - 2)) ↔ m % q ≠ q - 2) ∧
      ((¬ ∃ n, m = q * n + (q - 2)) ↔ ¬ (q ∣ m + 2)) ∧
      ((¬ ∃ n, m = q * n + (q - 2)) ↔ ¬ (m ≡ q - 2 [MOD q])) ∧
      (m % q ≠ q - 2 ↔ ¬ (q ∣ m + 2)) ∧
      (m % q ≠ q - 2 ↔ ¬ (m ≡ q - 2 [MOD q])) ∧
      (¬ (q ∣ m + 2) ↔ ¬ (m ≡ q - 2 [MOD q])) :=
  sub_residue_negative_equivalence_facts_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- Positive equivalence package for the `q-5` residue class. -/
theorem sub_five_residue_positive_equivalence_facts_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    ((∃ n, m = q * n + (q - 5)) ↔ m % q = q - 5) ∧
      ((∃ n, m = q * n + (q - 5)) ↔ q ∣ m + 5) ∧
      ((∃ n, m = q * n + (q - 5)) ↔ m ≡ q - 5 [MOD q]) ∧
      (m % q = q - 5 ↔ q ∣ m + 5) ∧
      (m % q = q - 5 ↔ m ≡ q - 5 [MOD q]) ∧
      (q ∣ m + 5 ↔ m ≡ q - 5 [MOD q]) :=
  sub_residue_positive_equivalence_facts_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- Negative equivalence package for avoiding the `q-5` residue class. -/
theorem sub_five_residue_negative_equivalence_facts_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    ((¬ ∃ n, m = q * n + (q - 5)) ↔ m % q ≠ q - 5) ∧
      ((¬ ∃ n, m = q * n + (q - 5)) ↔ ¬ (q ∣ m + 5)) ∧
      ((¬ ∃ n, m = q * n + (q - 5)) ↔ ¬ (m ≡ q - 5 [MOD q])) ∧
      (m % q ≠ q - 5 ↔ ¬ (q ∣ m + 5)) ∧
      (m % q ≠ q - 5 ↔ ¬ (m ≡ q - 5 [MOD q])) ∧
      (¬ (q ∣ m + 5) ↔ ¬ (m ≡ q - 5 [MOD q])) :=
  sub_residue_negative_equivalence_facts_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- Reverse-orientation positive equivalence package for the residue class
`q-c`. -/
theorem sub_residue_positive_symmetric_equivalence_facts_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    (m % q = q - c ↔ ∃ n, m = q * n + (q - c)) ∧
      (q ∣ m + c ↔ ∃ n, m = q * n + (q - c)) ∧
      (m ≡ q - c [MOD q] ↔ ∃ n, m = q * n + (q - c)) ∧
      (q ∣ m + c ↔ m % q = q - c) ∧
      (m ≡ q - c [MOD q] ↔ m % q = q - c) ∧
      (m ≡ q - c [MOD q] ↔ q ∣ m + c) := by
  exact ⟨mod_eq_sub_iff_exists_mul_add_sub_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq,
    dvd_add_iff_exists_mul_add_sub_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq,
    modEq_sub_iff_exists_mul_add_sub_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq,
    dvd_add_iff_mod_eq_sub_of_pos_le (q := q) (c := c) (m := m) hc0 hcq,
    modEq_sub_iff_mod_eq_sub_of_pos_le (q := q) (c := c) (m := m) hc0 hcq,
    modEq_sub_iff_dvd_add_of_pos_le (q := q) (c := c) (m := m) hc0 hcq⟩

/-- Reverse-orientation negative equivalence package for avoiding the residue
class `q-c`. -/
theorem sub_residue_negative_symmetric_equivalence_facts_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    (m % q ≠ q - c ↔ ¬ ∃ n, m = q * n + (q - c)) ∧
      (¬ (q ∣ m + c) ↔ ¬ ∃ n, m = q * n + (q - c)) ∧
      (¬ (m ≡ q - c [MOD q]) ↔ ¬ ∃ n, m = q * n + (q - c)) ∧
      (¬ (q ∣ m + c) ↔ m % q ≠ q - c) ∧
      (¬ (m ≡ q - c [MOD q]) ↔ m % q ≠ q - c) ∧
      (¬ (m ≡ q - c [MOD q]) ↔ ¬ (q ∣ m + c)) := by
  exact ⟨mod_ne_sub_iff_not_exists_mul_add_sub_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq,
    not_dvd_add_iff_not_exists_mul_add_sub_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq,
    not_modEq_sub_iff_not_exists_mul_add_sub_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq,
    not_dvd_add_iff_mod_ne_sub_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq,
    not_modEq_sub_iff_mod_ne_sub_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq,
    not_modEq_sub_iff_not_dvd_add_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq⟩

/-- Reverse-orientation positive equivalence package for the predecessor
residue class. -/
theorem pred_residue_positive_symmetric_equivalence_facts {q m : ℕ}
    (hq : 0 < q) :
    (m % q = q - 1 ↔ ∃ n, m = q * n + (q - 1)) ∧
      (q ∣ m + 1 ↔ ∃ n, m = q * n + (q - 1)) ∧
      (m ≡ q - 1 [MOD q] ↔ ∃ n, m = q * n + (q - 1)) ∧
      (q ∣ m + 1 ↔ m % q = q - 1) ∧
      (m ≡ q - 1 [MOD q] ↔ m % q = q - 1) ∧
      (m ≡ q - 1 [MOD q] ↔ q ∣ m + 1) :=
  sub_residue_positive_symmetric_equivalence_facts_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- Reverse-orientation negative equivalence package for avoiding the
predecessor residue class. -/
theorem pred_residue_negative_symmetric_equivalence_facts {q m : ℕ}
    (hq : 0 < q) :
    (m % q ≠ q - 1 ↔ ¬ ∃ n, m = q * n + (q - 1)) ∧
      (¬ (q ∣ m + 1) ↔ ¬ ∃ n, m = q * n + (q - 1)) ∧
      (¬ (m ≡ q - 1 [MOD q]) ↔ ¬ ∃ n, m = q * n + (q - 1)) ∧
      (¬ (q ∣ m + 1) ↔ m % q ≠ q - 1) ∧
      (¬ (m ≡ q - 1 [MOD q]) ↔ m % q ≠ q - 1) ∧
      (¬ (m ≡ q - 1 [MOD q]) ↔ ¬ (q ∣ m + 1)) :=
  sub_residue_negative_symmetric_equivalence_facts_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- Reverse-orientation positive equivalence package for the `q-2` residue
class. -/
theorem sub_two_residue_positive_symmetric_equivalence_facts_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    (m % q = q - 2 ↔ ∃ n, m = q * n + (q - 2)) ∧
      (q ∣ m + 2 ↔ ∃ n, m = q * n + (q - 2)) ∧
      (m ≡ q - 2 [MOD q] ↔ ∃ n, m = q * n + (q - 2)) ∧
      (q ∣ m + 2 ↔ m % q = q - 2) ∧
      (m ≡ q - 2 [MOD q] ↔ m % q = q - 2) ∧
      (m ≡ q - 2 [MOD q] ↔ q ∣ m + 2) :=
  sub_residue_positive_symmetric_equivalence_facts_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- Reverse-orientation negative equivalence package for avoiding the `q-2`
residue class. -/
theorem sub_two_residue_negative_symmetric_equivalence_facts_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    (m % q ≠ q - 2 ↔ ¬ ∃ n, m = q * n + (q - 2)) ∧
      (¬ (q ∣ m + 2) ↔ ¬ ∃ n, m = q * n + (q - 2)) ∧
      (¬ (m ≡ q - 2 [MOD q]) ↔ ¬ ∃ n, m = q * n + (q - 2)) ∧
      (¬ (q ∣ m + 2) ↔ m % q ≠ q - 2) ∧
      (¬ (m ≡ q - 2 [MOD q]) ↔ m % q ≠ q - 2) ∧
      (¬ (m ≡ q - 2 [MOD q]) ↔ ¬ (q ∣ m + 2)) :=
  sub_residue_negative_symmetric_equivalence_facts_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- Reverse-orientation positive equivalence package for the `q-5` residue
class. -/
theorem sub_five_residue_positive_symmetric_equivalence_facts_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    (m % q = q - 5 ↔ ∃ n, m = q * n + (q - 5)) ∧
      (q ∣ m + 5 ↔ ∃ n, m = q * n + (q - 5)) ∧
      (m ≡ q - 5 [MOD q] ↔ ∃ n, m = q * n + (q - 5)) ∧
      (q ∣ m + 5 ↔ m % q = q - 5) ∧
      (m ≡ q - 5 [MOD q] ↔ m % q = q - 5) ∧
      (m ≡ q - 5 [MOD q] ↔ q ∣ m + 5) :=
  sub_residue_positive_symmetric_equivalence_facts_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- Reverse-orientation negative equivalence package for avoiding the `q-5`
residue class. -/
theorem sub_five_residue_negative_symmetric_equivalence_facts_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    (m % q ≠ q - 5 ↔ ¬ ∃ n, m = q * n + (q - 5)) ∧
      (¬ (q ∣ m + 5) ↔ ¬ ∃ n, m = q * n + (q - 5)) ∧
      (¬ (m ≡ q - 5 [MOD q]) ↔ ¬ ∃ n, m = q * n + (q - 5)) ∧
      (¬ (q ∣ m + 5) ↔ m % q ≠ q - 5) ∧
      (¬ (m ≡ q - 5 [MOD q]) ↔ m % q ≠ q - 5) ∧
      (¬ (m ≡ q - 5 [MOD q]) ↔ ¬ (q ∣ m + 5)) :=
  sub_residue_negative_symmetric_equivalence_facts_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- Membership in `q-c` is equivalent to all three standard positive forms. -/
theorem sub_residue_positive_all_forms_iff_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    (∃ n, m = q * n + (q - c)) ↔
      m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q] := by
  constructor
  · intro hm
    exact ⟨mod_eq_sub_of_exists_mul_add_sub_of_pos_le (q := q) (c := c)
        (m := m) hc0 hcq hm,
      dvd_add_of_exists_mul_add_sub_of_pos_le (q := q) (c := c) (m := m)
        hc0 hcq hm,
      modEq_sub_of_exists_mul_add_sub_of_pos_le (q := q) (c := c) (m := m)
        hc0 hcq hm⟩
  · intro hm
    exact exists_mul_add_sub_of_mod_eq_sub_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq hm.1

/-- Avoiding `q-c` is equivalent to all three standard negative forms. -/
theorem sub_residue_negative_all_forms_iff_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    (¬ ∃ n, m = q * n + (q - c)) ↔
      m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]) := by
  constructor
  · intro hm
    exact ⟨mod_ne_sub_of_not_exists_mul_add_sub_of_pos_le (q := q) (c := c)
        (m := m) hc0 hcq hm,
      not_dvd_add_of_not_exists_mul_add_sub_of_pos_le (q := q) (c := c)
        (m := m) hc0 hcq hm,
      not_modEq_sub_of_not_exists_mul_add_sub_of_pos_le (q := q) (c := c)
        (m := m) hc0 hcq hm⟩
  · intro hm
    exact not_exists_mul_add_sub_of_mod_ne_sub_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq hm.1

/-- Predecessor membership is equivalent to all three standard positive forms. -/
theorem pred_residue_positive_all_forms_iff {q m : ℕ} (hq : 0 < q) :
    (∃ n, m = q * n + (q - 1)) ↔
      m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q] :=
  sub_residue_positive_all_forms_iff_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- Avoiding the predecessor residue is equivalent to all three standard
negative forms. -/
theorem pred_residue_negative_all_forms_iff {q m : ℕ} (hq : 0 < q) :
    (¬ ∃ n, m = q * n + (q - 1)) ↔
      m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]) :=
  sub_residue_negative_all_forms_iff_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- `q-2` membership is equivalent to all three standard positive forms. -/
theorem sub_two_residue_positive_all_forms_iff_of_le {q m : ℕ} (hq : 2 ≤ q) :
    (∃ n, m = q * n + (q - 2)) ↔
      m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q] :=
  sub_residue_positive_all_forms_iff_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- Avoiding `q-2` is equivalent to all three standard negative forms. -/
theorem sub_two_residue_negative_all_forms_iff_of_le {q m : ℕ} (hq : 2 ≤ q) :
    (¬ ∃ n, m = q * n + (q - 2)) ↔
      m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]) :=
  sub_residue_negative_all_forms_iff_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- `q-5` membership is equivalent to all three standard positive forms. -/
theorem sub_five_residue_positive_all_forms_iff_of_le {q m : ℕ} (hq : 5 ≤ q) :
    (∃ n, m = q * n + (q - 5)) ↔
      m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q] :=
  sub_residue_positive_all_forms_iff_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- Avoiding `q-5` is equivalent to all three standard negative forms. -/
theorem sub_five_residue_negative_all_forms_iff_of_le {q m : ℕ} (hq : 5 ≤ q) :
    (¬ ∃ n, m = q * n + (q - 5)) ↔
      m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]) :=
  sub_residue_negative_all_forms_iff_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- Membership in `q-c` gives all three standard positive forms. -/
theorem sub_residue_positive_all_forms_of_exists_mul_add_sub_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q)
    (hm : ∃ n, m = q * n + (q - c)) :
    m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q] :=
  (sub_residue_positive_all_forms_iff_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).1 hm

/-- All three standard positive forms give membership in `q-c`. -/
theorem exists_mul_add_sub_of_sub_residue_positive_all_forms_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q)
    (hm : m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) :
    ∃ n, m = q * n + (q - c) :=
  (sub_residue_positive_all_forms_iff_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).2 hm

/-- Avoiding `q-c` gives all three standard negative forms. -/
theorem sub_residue_negative_all_forms_of_not_exists_mul_add_sub_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q)
    (hm : ¬ ∃ n, m = q * n + (q - c)) :
    m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]) :=
  (sub_residue_negative_all_forms_iff_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).1 hm

/-- All three standard negative forms give avoidance of `q-c`. -/
theorem not_exists_mul_add_sub_of_sub_residue_negative_all_forms_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q)
    (hm : m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) :
    ¬ ∃ n, m = q * n + (q - c) :=
  (sub_residue_negative_all_forms_iff_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).2 hm

/-- Predecessor membership gives all three standard positive forms. -/
theorem pred_residue_positive_all_forms_of_exists_mul_add_pred {q m : ℕ}
    (hq : 0 < q) (hm : ∃ n, m = q * n + (q - 1)) :
    m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q] :=
  (pred_residue_positive_all_forms_iff (q := q) (m := m) hq).1 hm

/-- All three standard positive predecessor forms give predecessor membership. -/
theorem exists_mul_add_pred_of_pred_residue_positive_all_forms {q m : ℕ}
    (hq : 0 < q)
    (hm : m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) :
    ∃ n, m = q * n + (q - 1) :=
  (pred_residue_positive_all_forms_iff (q := q) (m := m) hq).2 hm

/-- Avoiding the predecessor residue gives all three standard negative forms. -/
theorem pred_residue_negative_all_forms_of_not_exists_mul_add_pred {q m : ℕ}
    (hq : 0 < q) (hm : ¬ ∃ n, m = q * n + (q - 1)) :
    m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]) :=
  (pred_residue_negative_all_forms_iff (q := q) (m := m) hq).1 hm

/-- All three standard negative predecessor forms give avoidance of the
predecessor residue. -/
theorem not_exists_mul_add_pred_of_pred_residue_negative_all_forms {q m : ℕ}
    (hq : 0 < q)
    (hm : m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) :
    ¬ ∃ n, m = q * n + (q - 1) :=
  (pred_residue_negative_all_forms_iff (q := q) (m := m) hq).2 hm

/-- `q-2` membership gives all three standard positive forms. -/
theorem sub_two_residue_positive_all_forms_of_exists_mul_add_sub_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) (hm : ∃ n, m = q * n + (q - 2)) :
    m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q] :=
  (sub_two_residue_positive_all_forms_iff_of_le (q := q) (m := m) hq).1 hm

/-- All three standard positive `q-2` forms give `q-2` membership. -/
theorem exists_mul_add_sub_two_of_sub_two_residue_positive_all_forms_of_le
    {q m : ℕ} (hq : 2 ≤ q)
    (hm : m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) :
    ∃ n, m = q * n + (q - 2) :=
  (sub_two_residue_positive_all_forms_iff_of_le (q := q) (m := m) hq).2 hm

/-- Avoiding `q-2` gives all three standard negative forms. -/
theorem sub_two_residue_negative_all_forms_of_not_exists_mul_add_sub_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) (hm : ¬ ∃ n, m = q * n + (q - 2)) :
    m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]) :=
  (sub_two_residue_negative_all_forms_iff_of_le (q := q) (m := m) hq).1 hm

/-- All three standard negative `q-2` forms give avoidance of `q-2`. -/
theorem not_exists_mul_add_sub_two_of_sub_two_residue_negative_all_forms_of_le
    {q m : ℕ} (hq : 2 ≤ q)
    (hm : m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) :
    ¬ ∃ n, m = q * n + (q - 2) :=
  (sub_two_residue_negative_all_forms_iff_of_le (q := q) (m := m) hq).2 hm

/-- `q-5` membership gives all three standard positive forms. -/
theorem sub_five_residue_positive_all_forms_of_exists_mul_add_sub_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) (hm : ∃ n, m = q * n + (q - 5)) :
    m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q] :=
  (sub_five_residue_positive_all_forms_iff_of_le (q := q) (m := m) hq).1 hm

/-- All three standard positive `q-5` forms give `q-5` membership. -/
theorem exists_mul_add_sub_five_of_sub_five_residue_positive_all_forms_of_le
    {q m : ℕ} (hq : 5 ≤ q)
    (hm : m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) :
    ∃ n, m = q * n + (q - 5) :=
  (sub_five_residue_positive_all_forms_iff_of_le (q := q) (m := m) hq).2 hm

/-- Avoiding `q-5` gives all three standard negative forms. -/
theorem sub_five_residue_negative_all_forms_of_not_exists_mul_add_sub_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) (hm : ¬ ∃ n, m = q * n + (q - 5)) :
    m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]) :=
  (sub_five_residue_negative_all_forms_iff_of_le (q := q) (m := m) hq).1 hm

/-- All three standard negative `q-5` forms give avoidance of `q-5`. -/
theorem not_exists_mul_add_sub_five_of_sub_five_residue_negative_all_forms_of_le
    {q m : ℕ} (hq : 5 ≤ q)
    (hm : m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) :
    ¬ ∃ n, m = q * n + (q - 5) :=
  (sub_five_residue_negative_all_forms_iff_of_le (q := q) (m := m) hq).2 hm

/-- All three standard positive forms are equivalent to membership in `q-c`. -/
theorem sub_residue_positive_all_forms_iff_exists_mul_add_sub_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q) :
    (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) ↔
      ∃ n, m = q * n + (q - c) :=
  (sub_residue_positive_all_forms_iff_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).symm

/-- All three standard negative forms are equivalent to avoiding `q-c`. -/
theorem sub_residue_negative_all_forms_iff_not_exists_mul_add_sub_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q) :
    (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) ↔
      ¬ ∃ n, m = q * n + (q - c) :=
  (sub_residue_negative_all_forms_iff_of_pos_le (q := q) (c := c) (m := m)
    hc0 hcq).symm

/-- All three standard positive predecessor forms are equivalent to predecessor
membership. -/
theorem pred_residue_positive_all_forms_iff_exists_mul_add_pred {q m : ℕ}
    (hq : 0 < q) :
    (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) ↔
      ∃ n, m = q * n + (q - 1) :=
  (pred_residue_positive_all_forms_iff (q := q) (m := m) hq).symm

/-- All three standard negative predecessor forms are equivalent to avoiding
the predecessor residue. -/
theorem pred_residue_negative_all_forms_iff_not_exists_mul_add_pred {q m : ℕ}
    (hq : 0 < q) :
    (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) ↔
      ¬ ∃ n, m = q * n + (q - 1) :=
  (pred_residue_negative_all_forms_iff (q := q) (m := m) hq).symm

/-- All three standard positive `q-2` forms are equivalent to `q-2`
membership. -/
theorem sub_two_residue_positive_all_forms_iff_exists_mul_add_sub_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) ↔
      ∃ n, m = q * n + (q - 2) :=
  (sub_two_residue_positive_all_forms_iff_of_le (q := q) (m := m) hq).symm

/-- All three standard negative `q-2` forms are equivalent to avoiding `q-2`. -/
theorem sub_two_residue_negative_all_forms_iff_not_exists_mul_add_sub_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) ↔
      ¬ ∃ n, m = q * n + (q - 2) :=
  (sub_two_residue_negative_all_forms_iff_of_le (q := q) (m := m) hq).symm

/-- All three standard positive `q-5` forms are equivalent to `q-5`
membership. -/
theorem sub_five_residue_positive_all_forms_iff_exists_mul_add_sub_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) ↔
      ∃ n, m = q * n + (q - 5) :=
  (sub_five_residue_positive_all_forms_iff_of_le (q := q) (m := m) hq).symm

/-- All three standard negative `q-5` forms are equivalent to avoiding `q-5`. -/
theorem sub_five_residue_negative_all_forms_iff_not_exists_mul_add_sub_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) ↔
      ¬ ∃ n, m = q * n + (q - 5) :=
  (sub_five_residue_negative_all_forms_iff_of_le (q := q) (m := m) hq).symm

/-- Project the direct residue equality from the positive all-forms package. -/
theorem mod_eq_sub_of_sub_residue_positive_all_forms {q c m : ℕ}
    (hm : m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) :
    m % q = q - c :=
  hm.1

/-- Project shifted divisibility from the positive all-forms package. -/
theorem dvd_add_of_sub_residue_positive_all_forms {q c m : ℕ}
    (hm : m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) :
    q ∣ m + c :=
  hm.2.1

/-- Project `Nat.ModEq` from the positive all-forms package. -/
theorem modEq_sub_of_sub_residue_positive_all_forms {q c m : ℕ}
    (hm : m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) :
    m ≡ q - c [MOD q] :=
  hm.2.2

/-- Project direct residue inequality from the negative all-forms package. -/
theorem mod_ne_sub_of_sub_residue_negative_all_forms {q c m : ℕ}
    (hm : m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) :
    m % q ≠ q - c :=
  hm.1

/-- Project shifted nondivisibility from the negative all-forms package. -/
theorem not_dvd_add_of_sub_residue_negative_all_forms {q c m : ℕ}
    (hm : m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) :
    ¬ (q ∣ m + c) :=
  hm.2.1

/-- Project negated `Nat.ModEq` from the negative all-forms package. -/
theorem not_modEq_sub_of_sub_residue_negative_all_forms {q c m : ℕ}
    (hm : m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) :
    ¬ (m ≡ q - c [MOD q]) :=
  hm.2.2

/-- Project predecessor residue equality from the positive predecessor package. -/
theorem mod_eq_pred_of_pred_residue_positive_all_forms {q m : ℕ}
    (hm : m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) :
    m % q = q - 1 :=
  hm.1

/-- Project divisibility of `m+1` from the positive predecessor package. -/
theorem dvd_succ_of_pred_residue_positive_all_forms {q m : ℕ}
    (hm : m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) :
    q ∣ m + 1 :=
  hm.2.1

/-- Project predecessor `Nat.ModEq` from the positive predecessor package. -/
theorem modEq_pred_of_pred_residue_positive_all_forms {q m : ℕ}
    (hm : m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) :
    m ≡ q - 1 [MOD q] :=
  hm.2.2

/-- Project predecessor residue inequality from the negative predecessor
package. -/
theorem mod_ne_pred_of_pred_residue_negative_all_forms {q m : ℕ}
    (hm : m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) :
    m % q ≠ q - 1 :=
  hm.1

/-- Project nondivisibility of `m+1` from the negative predecessor package. -/
theorem not_dvd_succ_of_pred_residue_negative_all_forms {q m : ℕ}
    (hm : m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) :
    ¬ (q ∣ m + 1) :=
  hm.2.1

/-- Project negated predecessor `Nat.ModEq` from the negative predecessor
package. -/
theorem not_modEq_pred_of_pred_residue_negative_all_forms {q m : ℕ}
    (hm : m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) :
    ¬ (m ≡ q - 1 [MOD q]) :=
  hm.2.2

/-- Project residue `q-2` equality from the positive `q-2` package. -/
theorem mod_eq_sub_two_of_sub_two_residue_positive_all_forms {q m : ℕ}
    (hm : m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) :
    m % q = q - 2 :=
  hm.1

/-- Project divisibility of `m+2` from the positive `q-2` package. -/
theorem dvd_add_two_of_sub_two_residue_positive_all_forms {q m : ℕ}
    (hm : m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) :
    q ∣ m + 2 :=
  hm.2.1

/-- Project `Nat.ModEq` to `q-2` from the positive `q-2` package. -/
theorem modEq_sub_two_of_sub_two_residue_positive_all_forms {q m : ℕ}
    (hm : m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) :
    m ≡ q - 2 [MOD q] :=
  hm.2.2

/-- Project residue `q-2` inequality from the negative `q-2` package. -/
theorem mod_ne_sub_two_of_sub_two_residue_negative_all_forms {q m : ℕ}
    (hm : m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) :
    m % q ≠ q - 2 :=
  hm.1

/-- Project nondivisibility of `m+2` from the negative `q-2` package. -/
theorem not_dvd_add_two_of_sub_two_residue_negative_all_forms {q m : ℕ}
    (hm : m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) :
    ¬ (q ∣ m + 2) :=
  hm.2.1

/-- Project negated `Nat.ModEq` to `q-2` from the negative `q-2` package. -/
theorem not_modEq_sub_two_of_sub_two_residue_negative_all_forms {q m : ℕ}
    (hm : m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) :
    ¬ (m ≡ q - 2 [MOD q]) :=
  hm.2.2

/-- Project residue `q-5` equality from the positive `q-5` package. -/
theorem mod_eq_sub_five_of_sub_five_residue_positive_all_forms {q m : ℕ}
    (hm : m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) :
    m % q = q - 5 :=
  hm.1

/-- Project divisibility of `m+5` from the positive `q-5` package. -/
theorem dvd_add_five_of_sub_five_residue_positive_all_forms {q m : ℕ}
    (hm : m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) :
    q ∣ m + 5 :=
  hm.2.1

/-- Project `Nat.ModEq` to `q-5` from the positive `q-5` package. -/
theorem modEq_sub_five_of_sub_five_residue_positive_all_forms {q m : ℕ}
    (hm : m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) :
    m ≡ q - 5 [MOD q] :=
  hm.2.2

/-- Project residue `q-5` inequality from the negative `q-5` package. -/
theorem mod_ne_sub_five_of_sub_five_residue_negative_all_forms {q m : ℕ}
    (hm : m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) :
    m % q ≠ q - 5 :=
  hm.1

/-- Project nondivisibility of `m+5` from the negative `q-5` package. -/
theorem not_dvd_add_five_of_sub_five_residue_negative_all_forms {q m : ℕ}
    (hm : m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) :
    ¬ (q ∣ m + 5) :=
  hm.2.1

/-- Project negated `Nat.ModEq` to `q-5` from the negative `q-5` package. -/
theorem not_modEq_sub_five_of_sub_five_residue_negative_all_forms {q m : ℕ}
    (hm : m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) :
    ¬ (m ≡ q - 5 [MOD q]) :=
  hm.2.2

/-- Direct residue equality generates the positive all-forms package. -/
theorem sub_residue_positive_all_forms_of_mod_eq_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : m % q = q - c) :
    m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q] :=
  sub_residue_positive_all_forms_of_exists_mul_add_sub_of_pos_le (q := q)
    (c := c) (m := m) hc0 hcq
    (exists_mul_add_sub_of_mod_eq_sub_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq hm)

/-- Shifted divisibility generates the positive all-forms package. -/
theorem sub_residue_positive_all_forms_of_dvd_add_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : q ∣ m + c) :
    m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q] :=
  sub_residue_positive_all_forms_of_exists_mul_add_sub_of_pos_le (q := q)
    (c := c) (m := m) hc0 hcq
    (exists_mul_add_sub_of_dvd_add_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq hm)

/-- `Nat.ModEq` to `q-c` generates the positive all-forms package. -/
theorem sub_residue_positive_all_forms_of_modEq_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : m ≡ q - c [MOD q]) :
    m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q] :=
  sub_residue_positive_all_forms_of_exists_mul_add_sub_of_pos_le (q := q)
    (c := c) (m := m) hc0 hcq
    (exists_mul_add_sub_of_modEq_sub_of_pos_le (q := q) (c := c) (m := m)
      hc0 hcq hm)

/-- Direct residue inequality generates the negative all-forms package. -/
theorem sub_residue_negative_all_forms_of_mod_ne_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : m % q ≠ q - c) :
    m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]) :=
  sub_residue_negative_all_forms_of_not_exists_mul_add_sub_of_pos_le (q := q)
    (c := c) (m := m) hc0 hcq
    (not_exists_mul_add_sub_of_mod_ne_sub_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq hm)

/-- Shifted nondivisibility generates the negative all-forms package. -/
theorem sub_residue_negative_all_forms_of_not_dvd_add_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : ¬ (q ∣ m + c)) :
    m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]) :=
  sub_residue_negative_all_forms_of_not_exists_mul_add_sub_of_pos_le (q := q)
    (c := c) (m := m) hc0 hcq
    (not_exists_mul_add_sub_of_not_dvd_add_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq hm)

/-- Negated `Nat.ModEq` to `q-c` generates the negative all-forms package. -/
theorem sub_residue_negative_all_forms_of_not_modEq_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : ¬ (m ≡ q - c [MOD q])) :
    m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]) :=
  sub_residue_negative_all_forms_of_not_exists_mul_add_sub_of_pos_le (q := q)
    (c := c) (m := m) hc0 hcq
    (not_exists_mul_add_sub_of_not_modEq_sub_of_pos_le (q := q) (c := c)
      (m := m) hc0 hcq hm)

/-- Predecessor residue equality generates the predecessor positive package. -/
theorem pred_residue_positive_all_forms_of_mod_eq_pred {q m : ℕ} (hq : 0 < q)
    (hm : m % q = q - 1) :
    m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q] :=
  sub_residue_positive_all_forms_of_mod_eq_sub_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq hm

/-- Divisibility of `m+1` generates the predecessor positive package. -/
theorem pred_residue_positive_all_forms_of_dvd_succ {q m : ℕ} (hq : 0 < q)
    (hm : q ∣ m + 1) :
    m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q] :=
  sub_residue_positive_all_forms_of_dvd_add_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq hm

/-- Predecessor `Nat.ModEq` generates the predecessor positive package. -/
theorem pred_residue_positive_all_forms_of_modEq_pred {q m : ℕ} (hq : 0 < q)
    (hm : m ≡ q - 1 [MOD q]) :
    m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q] :=
  sub_residue_positive_all_forms_of_modEq_sub_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq hm

/-- Predecessor residue inequality generates the predecessor negative package. -/
theorem pred_residue_negative_all_forms_of_mod_ne_pred {q m : ℕ} (hq : 0 < q)
    (hm : m % q ≠ q - 1) :
    m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]) :=
  sub_residue_negative_all_forms_of_mod_ne_sub_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq hm

/-- Nondivisibility of `m+1` generates the predecessor negative package. -/
theorem pred_residue_negative_all_forms_of_not_dvd_succ {q m : ℕ} (hq : 0 < q)
    (hm : ¬ (q ∣ m + 1)) :
    m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]) :=
  sub_residue_negative_all_forms_of_not_dvd_add_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq hm

/-- Negated predecessor `Nat.ModEq` generates the predecessor negative package. -/
theorem pred_residue_negative_all_forms_of_not_modEq_pred {q m : ℕ}
    (hq : 0 < q) (hm : ¬ (m ≡ q - 1 [MOD q])) :
    m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]) :=
  sub_residue_negative_all_forms_of_not_modEq_sub_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq hm

/-- Residue `q-2` equality generates the `q-2` positive package. -/
theorem sub_two_residue_positive_all_forms_of_mod_eq_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : m % q = q - 2) :
    m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q] :=
  sub_residue_positive_all_forms_of_mod_eq_sub_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq hm

/-- Divisibility of `m+2` generates the `q-2` positive package. -/
theorem sub_two_residue_positive_all_forms_of_dvd_add_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : q ∣ m + 2) :
    m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q] :=
  sub_residue_positive_all_forms_of_dvd_add_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq hm

/-- `Nat.ModEq` to `q-2` generates the `q-2` positive package. -/
theorem sub_two_residue_positive_all_forms_of_modEq_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : m ≡ q - 2 [MOD q]) :
    m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q] :=
  sub_residue_positive_all_forms_of_modEq_sub_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq hm

/-- Residue `q-2` inequality generates the `q-2` negative package. -/
theorem sub_two_residue_negative_all_forms_of_mod_ne_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : m % q ≠ q - 2) :
    m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]) :=
  sub_residue_negative_all_forms_of_mod_ne_sub_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq hm

/-- Nondivisibility of `m+2` generates the `q-2` negative package. -/
theorem sub_two_residue_negative_all_forms_of_not_dvd_add_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : ¬ (q ∣ m + 2)) :
    m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]) :=
  sub_residue_negative_all_forms_of_not_dvd_add_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq hm

/-- Negated `Nat.ModEq` to `q-2` generates the `q-2` negative package. -/
theorem sub_two_residue_negative_all_forms_of_not_modEq_sub_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) (hm : ¬ (m ≡ q - 2 [MOD q])) :
    m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]) :=
  sub_residue_negative_all_forms_of_not_modEq_sub_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq hm

/-- Residue `q-5` equality generates the `q-5` positive package. -/
theorem sub_five_residue_positive_all_forms_of_mod_eq_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : m % q = q - 5) :
    m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q] :=
  sub_residue_positive_all_forms_of_mod_eq_sub_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq hm

/-- Divisibility of `m+5` generates the `q-5` positive package. -/
theorem sub_five_residue_positive_all_forms_of_dvd_add_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : q ∣ m + 5) :
    m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q] :=
  sub_residue_positive_all_forms_of_dvd_add_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq hm

/-- `Nat.ModEq` to `q-5` generates the `q-5` positive package. -/
theorem sub_five_residue_positive_all_forms_of_modEq_sub_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) (hm : m ≡ q - 5 [MOD q]) :
    m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q] :=
  sub_residue_positive_all_forms_of_modEq_sub_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq hm

/-- Residue `q-5` inequality generates the `q-5` negative package. -/
theorem sub_five_residue_negative_all_forms_of_mod_ne_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : m % q ≠ q - 5) :
    m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]) :=
  sub_residue_negative_all_forms_of_mod_ne_sub_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq hm

/-- Nondivisibility of `m+5` generates the `q-5` negative package. -/
theorem sub_five_residue_negative_all_forms_of_not_dvd_add_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) (hm : ¬ (q ∣ m + 5)) :
    m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]) :=
  sub_residue_negative_all_forms_of_not_dvd_add_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq hm

/-- Negated `Nat.ModEq` to `q-5` generates the `q-5` negative package. -/
theorem sub_five_residue_negative_all_forms_of_not_modEq_sub_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) (hm : ¬ (m ≡ q - 5 [MOD q])) :
    m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]) :=
  sub_residue_negative_all_forms_of_not_modEq_sub_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq hm

/-- Direct residue equality is equivalent to the positive all-forms package. -/
theorem mod_eq_sub_iff_sub_residue_positive_all_forms_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    m % q = q - c ↔
      m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q] := by
  constructor
  · exact sub_residue_positive_all_forms_of_mod_eq_sub_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq
  · exact fun hm => hm.1

/-- Shifted divisibility is equivalent to the positive all-forms package. -/
theorem dvd_add_iff_sub_residue_positive_all_forms_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    q ∣ m + c ↔
      m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q] := by
  constructor
  · exact sub_residue_positive_all_forms_of_dvd_add_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq
  · exact fun hm => hm.2.1

/-- `Nat.ModEq` to `q-c` is equivalent to the positive all-forms package. -/
theorem modEq_sub_iff_sub_residue_positive_all_forms_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    m ≡ q - c [MOD q] ↔
      m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q] := by
  constructor
  · exact sub_residue_positive_all_forms_of_modEq_sub_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq
  · exact fun hm => hm.2.2

/-- Direct residue inequality is equivalent to the negative all-forms package. -/
theorem mod_ne_sub_iff_sub_residue_negative_all_forms_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    m % q ≠ q - c ↔
      m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]) := by
  constructor
  · exact sub_residue_negative_all_forms_of_mod_ne_sub_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq
  · exact fun hm => hm.1

/-- Shifted nondivisibility is equivalent to the negative all-forms package. -/
theorem not_dvd_add_iff_sub_residue_negative_all_forms_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    ¬ (q ∣ m + c) ↔
      m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]) := by
  constructor
  · exact sub_residue_negative_all_forms_of_not_dvd_add_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq
  · exact fun hm => hm.2.1

/-- Negated `Nat.ModEq` to `q-c` is equivalent to the negative all-forms
package. -/
theorem not_modEq_sub_iff_sub_residue_negative_all_forms_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q) :
    ¬ (m ≡ q - c [MOD q]) ↔
      m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]) := by
  constructor
  · exact sub_residue_negative_all_forms_of_not_modEq_sub_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq
  · exact fun hm => hm.2.2

/-- Predecessor residue equality is equivalent to the predecessor positive
package. -/
theorem mod_eq_pred_iff_pred_residue_positive_all_forms {q m : ℕ}
    (hq : 0 < q) :
    m % q = q - 1 ↔
      m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q] :=
  mod_eq_sub_iff_sub_residue_positive_all_forms_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- Divisibility of `m+1` is equivalent to the predecessor positive package. -/
theorem dvd_succ_iff_pred_residue_positive_all_forms {q m : ℕ} (hq : 0 < q) :
    q ∣ m + 1 ↔
      m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q] :=
  dvd_add_iff_sub_residue_positive_all_forms_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- Predecessor `Nat.ModEq` is equivalent to the predecessor positive package. -/
theorem modEq_pred_iff_pred_residue_positive_all_forms {q m : ℕ}
    (hq : 0 < q) :
    m ≡ q - 1 [MOD q] ↔
      m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q] :=
  modEq_sub_iff_sub_residue_positive_all_forms_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- Predecessor residue inequality is equivalent to the predecessor negative
package. -/
theorem mod_ne_pred_iff_pred_residue_negative_all_forms {q m : ℕ}
    (hq : 0 < q) :
    m % q ≠ q - 1 ↔
      m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]) :=
  mod_ne_sub_iff_sub_residue_negative_all_forms_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- Nondivisibility of `m+1` is equivalent to the predecessor negative
package. -/
theorem not_dvd_succ_iff_pred_residue_negative_all_forms {q m : ℕ}
    (hq : 0 < q) :
    ¬ (q ∣ m + 1) ↔
      m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]) :=
  not_dvd_add_iff_sub_residue_negative_all_forms_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- Negated predecessor `Nat.ModEq` is equivalent to the predecessor negative
package. -/
theorem not_modEq_pred_iff_pred_residue_negative_all_forms {q m : ℕ}
    (hq : 0 < q) :
    ¬ (m ≡ q - 1 [MOD q]) ↔
      m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]) :=
  not_modEq_sub_iff_sub_residue_negative_all_forms_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- Residue `q-2` equality is equivalent to the `q-2` positive package. -/
theorem mod_eq_sub_two_iff_sub_two_residue_positive_all_forms_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    m % q = q - 2 ↔
      m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q] :=
  mod_eq_sub_iff_sub_residue_positive_all_forms_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- Divisibility of `m+2` is equivalent to the `q-2` positive package. -/
theorem dvd_add_two_iff_sub_two_residue_positive_all_forms_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    q ∣ m + 2 ↔
      m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q] :=
  dvd_add_iff_sub_residue_positive_all_forms_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- `Nat.ModEq` to `q-2` is equivalent to the `q-2` positive package. -/
theorem modEq_sub_two_iff_sub_two_residue_positive_all_forms_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    m ≡ q - 2 [MOD q] ↔
      m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q] :=
  modEq_sub_iff_sub_residue_positive_all_forms_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- Residue `q-2` inequality is equivalent to the `q-2` negative package. -/
theorem mod_ne_sub_two_iff_sub_two_residue_negative_all_forms_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    m % q ≠ q - 2 ↔
      m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]) :=
  mod_ne_sub_iff_sub_residue_negative_all_forms_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- Nondivisibility of `m+2` is equivalent to the `q-2` negative package. -/
theorem not_dvd_add_two_iff_sub_two_residue_negative_all_forms_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    ¬ (q ∣ m + 2) ↔
      m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]) :=
  not_dvd_add_iff_sub_residue_negative_all_forms_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- Negated `Nat.ModEq` to `q-2` is equivalent to the `q-2` negative package. -/
theorem not_modEq_sub_two_iff_sub_two_residue_negative_all_forms_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    ¬ (m ≡ q - 2 [MOD q]) ↔
      m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]) :=
  not_modEq_sub_iff_sub_residue_negative_all_forms_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- Residue `q-5` equality is equivalent to the `q-5` positive package. -/
theorem mod_eq_sub_five_iff_sub_five_residue_positive_all_forms_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    m % q = q - 5 ↔
      m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q] :=
  mod_eq_sub_iff_sub_residue_positive_all_forms_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- Divisibility of `m+5` is equivalent to the `q-5` positive package. -/
theorem dvd_add_five_iff_sub_five_residue_positive_all_forms_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    q ∣ m + 5 ↔
      m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q] :=
  dvd_add_iff_sub_residue_positive_all_forms_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- `Nat.ModEq` to `q-5` is equivalent to the `q-5` positive package. -/
theorem modEq_sub_five_iff_sub_five_residue_positive_all_forms_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    m ≡ q - 5 [MOD q] ↔
      m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q] :=
  modEq_sub_iff_sub_residue_positive_all_forms_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- Residue `q-5` inequality is equivalent to the `q-5` negative package. -/
theorem mod_ne_sub_five_iff_sub_five_residue_negative_all_forms_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    m % q ≠ q - 5 ↔
      m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]) :=
  mod_ne_sub_iff_sub_residue_negative_all_forms_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- Nondivisibility of `m+5` is equivalent to the `q-5` negative package. -/
theorem not_dvd_add_five_iff_sub_five_residue_negative_all_forms_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    ¬ (q ∣ m + 5) ↔
      m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]) :=
  not_dvd_add_iff_sub_residue_negative_all_forms_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- Negated `Nat.ModEq` to `q-5` is equivalent to the `q-5` negative package. -/
theorem not_modEq_sub_five_iff_sub_five_residue_negative_all_forms_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    ¬ (m ≡ q - 5 [MOD q]) ↔
      m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]) :=
  not_modEq_sub_iff_sub_residue_negative_all_forms_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- The positive all-forms package is equivalent to direct residue equality. -/
theorem sub_residue_positive_all_forms_iff_mod_eq_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) ↔
      m % q = q - c :=
  (mod_eq_sub_iff_sub_residue_positive_all_forms_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).symm

/-- The positive all-forms package is equivalent to shifted divisibility. -/
theorem sub_residue_positive_all_forms_iff_dvd_add_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) ↔
      q ∣ m + c :=
  (dvd_add_iff_sub_residue_positive_all_forms_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).symm

/-- The positive all-forms package is equivalent to `Nat.ModEq` to `q-c`. -/
theorem sub_residue_positive_all_forms_iff_modEq_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) ↔
      m ≡ q - c [MOD q] :=
  (modEq_sub_iff_sub_residue_positive_all_forms_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).symm

/-- The negative all-forms package is equivalent to direct residue inequality. -/
theorem sub_residue_negative_all_forms_iff_mod_ne_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) ↔
      m % q ≠ q - c :=
  (mod_ne_sub_iff_sub_residue_negative_all_forms_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).symm

/-- The negative all-forms package is equivalent to shifted nondivisibility. -/
theorem sub_residue_negative_all_forms_iff_not_dvd_add_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) ↔
      ¬ (q ∣ m + c) :=
  (not_dvd_add_iff_sub_residue_negative_all_forms_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).symm

/-- The negative all-forms package is equivalent to negated `Nat.ModEq` to
`q-c`. -/
theorem sub_residue_negative_all_forms_iff_not_modEq_sub_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q) :
    (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) ↔
      ¬ (m ≡ q - c [MOD q]) :=
  (not_modEq_sub_iff_sub_residue_negative_all_forms_of_pos_le (q := q) (c := c)
    (m := m) hc0 hcq).symm

/-- The predecessor positive package is equivalent to predecessor residue
equality. -/
theorem pred_residue_positive_all_forms_iff_mod_eq_pred {q m : ℕ}
    (hq : 0 < q) :
    (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) ↔
      m % q = q - 1 :=
  (mod_eq_pred_iff_pred_residue_positive_all_forms (q := q) (m := m)
    hq).symm

/-- The predecessor positive package is equivalent to divisibility of `m+1`. -/
theorem pred_residue_positive_all_forms_iff_dvd_succ {q m : ℕ} (hq : 0 < q) :
    (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) ↔
      q ∣ m + 1 :=
  (dvd_succ_iff_pred_residue_positive_all_forms (q := q) (m := m) hq).symm

/-- The predecessor positive package is equivalent to predecessor `Nat.ModEq`. -/
theorem pred_residue_positive_all_forms_iff_modEq_pred {q m : ℕ}
    (hq : 0 < q) :
    (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) ↔
      m ≡ q - 1 [MOD q] :=
  (modEq_pred_iff_pred_residue_positive_all_forms (q := q) (m := m) hq).symm

/-- The predecessor negative package is equivalent to predecessor residue
inequality. -/
theorem pred_residue_negative_all_forms_iff_mod_ne_pred {q m : ℕ}
    (hq : 0 < q) :
    (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) ↔
      m % q ≠ q - 1 :=
  (mod_ne_pred_iff_pred_residue_negative_all_forms (q := q) (m := m)
    hq).symm

/-- The predecessor negative package is equivalent to nondivisibility of `m+1`. -/
theorem pred_residue_negative_all_forms_iff_not_dvd_succ {q m : ℕ}
    (hq : 0 < q) :
    (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) ↔
      ¬ (q ∣ m + 1) :=
  (not_dvd_succ_iff_pred_residue_negative_all_forms (q := q) (m := m)
    hq).symm

/-- The predecessor negative package is equivalent to negated predecessor
`Nat.ModEq`. -/
theorem pred_residue_negative_all_forms_iff_not_modEq_pred {q m : ℕ}
    (hq : 0 < q) :
    (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) ↔
      ¬ (m ≡ q - 1 [MOD q]) :=
  (not_modEq_pred_iff_pred_residue_negative_all_forms (q := q) (m := m)
    hq).symm

/-- The `q-2` positive package is equivalent to residue `q-2` equality. -/
theorem sub_two_residue_positive_all_forms_iff_mod_eq_sub_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) ↔
      m % q = q - 2 :=
  (mod_eq_sub_two_iff_sub_two_residue_positive_all_forms_of_le (q := q)
    (m := m) hq).symm

/-- The `q-2` positive package is equivalent to divisibility of `m+2`. -/
theorem sub_two_residue_positive_all_forms_iff_dvd_add_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) ↔
      q ∣ m + 2 :=
  (dvd_add_two_iff_sub_two_residue_positive_all_forms_of_le (q := q)
    (m := m) hq).symm

/-- The `q-2` positive package is equivalent to `Nat.ModEq` to `q-2`. -/
theorem sub_two_residue_positive_all_forms_iff_modEq_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) ↔
      m ≡ q - 2 [MOD q] :=
  (modEq_sub_two_iff_sub_two_residue_positive_all_forms_of_le (q := q)
    (m := m) hq).symm

/-- The `q-2` negative package is equivalent to residue `q-2` inequality. -/
theorem sub_two_residue_negative_all_forms_iff_mod_ne_sub_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) ↔
      m % q ≠ q - 2 :=
  (mod_ne_sub_two_iff_sub_two_residue_negative_all_forms_of_le (q := q)
    (m := m) hq).symm

/-- The `q-2` negative package is equivalent to nondivisibility of `m+2`. -/
theorem sub_two_residue_negative_all_forms_iff_not_dvd_add_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) ↔
      ¬ (q ∣ m + 2) :=
  (not_dvd_add_two_iff_sub_two_residue_negative_all_forms_of_le (q := q)
    (m := m) hq).symm

/-- The `q-2` negative package is equivalent to negated `Nat.ModEq` to `q-2`. -/
theorem sub_two_residue_negative_all_forms_iff_not_modEq_sub_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) ↔
      ¬ (m ≡ q - 2 [MOD q]) :=
  (not_modEq_sub_two_iff_sub_two_residue_negative_all_forms_of_le (q := q)
    (m := m) hq).symm

/-- The `q-5` positive package is equivalent to residue `q-5` equality. -/
theorem sub_five_residue_positive_all_forms_iff_mod_eq_sub_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) ↔
      m % q = q - 5 :=
  (mod_eq_sub_five_iff_sub_five_residue_positive_all_forms_of_le (q := q)
    (m := m) hq).symm

/-- The `q-5` positive package is equivalent to divisibility of `m+5`. -/
theorem sub_five_residue_positive_all_forms_iff_dvd_add_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) ↔
      q ∣ m + 5 :=
  (dvd_add_five_iff_sub_five_residue_positive_all_forms_of_le (q := q)
    (m := m) hq).symm

/-- The `q-5` positive package is equivalent to `Nat.ModEq` to `q-5`. -/
theorem sub_five_residue_positive_all_forms_iff_modEq_sub_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) ↔
      m ≡ q - 5 [MOD q] :=
  (modEq_sub_five_iff_sub_five_residue_positive_all_forms_of_le (q := q)
    (m := m) hq).symm

/-- The `q-5` negative package is equivalent to residue `q-5` inequality. -/
theorem sub_five_residue_negative_all_forms_iff_mod_ne_sub_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) ↔
      m % q ≠ q - 5 :=
  (mod_ne_sub_five_iff_sub_five_residue_negative_all_forms_of_le (q := q)
    (m := m) hq).symm

/-- The `q-5` negative package is equivalent to nondivisibility of `m+5`. -/
theorem sub_five_residue_negative_all_forms_iff_not_dvd_add_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) ↔
      ¬ (q ∣ m + 5) :=
  (not_dvd_add_five_iff_sub_five_residue_negative_all_forms_of_le (q := q)
    (m := m) hq).symm

/-- The `q-5` negative package is equivalent to negated `Nat.ModEq` to `q-5`. -/
theorem sub_five_residue_negative_all_forms_iff_not_modEq_sub_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) ↔
      ¬ (m ≡ q - 5 [MOD q]) :=
  (not_modEq_sub_five_iff_sub_five_residue_negative_all_forms_of_le (q := q)
    (m := m) hq).symm

/-- The positive and negative `q-c` all-forms packages are mutually exclusive. -/
theorem sub_residue_positive_all_forms_not_negative_all_forms {q c m : ℕ}
    (hp : m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) :
    ¬ (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) := by
  intro hn
  exact hn.1 hp.1

/-- The negative and positive `q-c` all-forms packages are mutually exclusive. -/
theorem sub_residue_negative_all_forms_not_positive_all_forms {q c m : ℕ}
    (hn : m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) :
    ¬ (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) := by
  intro hp
  exact hn.1 hp.1

/-- The predecessor positive and negative all-forms packages are mutually
exclusive. -/
theorem pred_residue_positive_all_forms_not_negative_all_forms {q m : ℕ}
    (hp : m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) :
    ¬ (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) := by
  intro hn
  exact hn.1 hp.1

/-- The predecessor negative and positive all-forms packages are mutually
exclusive. -/
theorem pred_residue_negative_all_forms_not_positive_all_forms {q m : ℕ}
    (hn : m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) :
    ¬ (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) := by
  intro hp
  exact hn.1 hp.1

/-- The `q-2` positive and negative all-forms packages are mutually exclusive. -/
theorem sub_two_residue_positive_all_forms_not_negative_all_forms {q m : ℕ}
    (hp : m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) :
    ¬ (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) := by
  intro hn
  exact hn.1 hp.1

/-- The `q-2` negative and positive all-forms packages are mutually exclusive. -/
theorem sub_two_residue_negative_all_forms_not_positive_all_forms {q m : ℕ}
    (hn : m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) :
    ¬ (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) := by
  intro hp
  exact hn.1 hp.1

/-- The `q-5` positive and negative all-forms packages are mutually exclusive. -/
theorem sub_five_residue_positive_all_forms_not_negative_all_forms {q m : ℕ}
    (hp : m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) :
    ¬ (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) := by
  intro hn
  exact hn.1 hp.1

/-- The `q-5` negative and positive all-forms packages are mutually exclusive. -/
theorem sub_five_residue_negative_all_forms_not_positive_all_forms {q m : ℕ}
    (hn : m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) :
    ¬ (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) := by
  intro hp
  exact hn.1 hp.1

/-- The negative `q-c` all-forms package is equivalent to not having the
positive package. -/
theorem sub_residue_negative_all_forms_iff_not_positive_all_forms_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q) :
    (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) ↔
      ¬ (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) := by
  constructor
  · exact sub_residue_negative_all_forms_not_positive_all_forms
  · intro hnot
    by_cases hm : m % q = q - c
    · exact False.elim (hnot
        (sub_residue_positive_all_forms_of_mod_eq_sub_of_pos_le (q := q)
          (c := c) (m := m) hc0 hcq hm))
    · exact sub_residue_negative_all_forms_of_mod_ne_sub_of_pos_le (q := q)
        (c := c) (m := m) hc0 hcq hm

/-- Not having the positive `q-c` all-forms package is equivalent to the
negative package. -/
theorem sub_residue_not_positive_all_forms_iff_negative_all_forms_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q) :
    (¬ (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q])) ↔
      m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]) :=
  (sub_residue_negative_all_forms_iff_not_positive_all_forms_of_pos_le
    (q := q) (c := c) (m := m) hc0 hcq).symm

/-- The positive `q-c` all-forms package is equivalent to not having the
negative package. -/
theorem sub_residue_positive_all_forms_iff_not_negative_all_forms_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q) :
    (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) ↔
      ¬ (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) := by
  constructor
  · exact sub_residue_positive_all_forms_not_negative_all_forms
  · intro hnot
    by_cases hm : m % q = q - c
    · exact sub_residue_positive_all_forms_of_mod_eq_sub_of_pos_le (q := q)
        (c := c) (m := m) hc0 hcq hm
    · exact False.elim (hnot
        (sub_residue_negative_all_forms_of_mod_ne_sub_of_pos_le (q := q)
          (c := c) (m := m) hc0 hcq hm))

/-- Not having the negative `q-c` all-forms package is equivalent to the
positive package. -/
theorem sub_residue_not_negative_all_forms_iff_positive_all_forms_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q) :
    (¬ (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]))) ↔
      m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q] :=
  (sub_residue_positive_all_forms_iff_not_negative_all_forms_of_pos_le
    (q := q) (c := c) (m := m) hc0 hcq).symm

/-- The predecessor negative package is equivalent to not having the
predecessor positive package. -/
theorem pred_residue_negative_all_forms_iff_not_positive_all_forms {q m : ℕ}
    (hq : 0 < q) :
    (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) ↔
      ¬ (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) :=
  sub_residue_negative_all_forms_iff_not_positive_all_forms_of_pos_le (q := q)
    (c := 1) (m := m) (by decide) hq

/-- Not having the predecessor positive package is equivalent to the
predecessor negative package. -/
theorem pred_residue_not_positive_all_forms_iff_negative_all_forms {q m : ℕ}
    (hq : 0 < q) :
    (¬ (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q])) ↔
      m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]) :=
  sub_residue_not_positive_all_forms_iff_negative_all_forms_of_pos_le (q := q)
    (c := 1) (m := m) (by decide) hq

/-- The predecessor positive package is equivalent to not having the
predecessor negative package. -/
theorem pred_residue_positive_all_forms_iff_not_negative_all_forms {q m : ℕ}
    (hq : 0 < q) :
    (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) ↔
      ¬ (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) :=
  sub_residue_positive_all_forms_iff_not_negative_all_forms_of_pos_le (q := q)
    (c := 1) (m := m) (by decide) hq

/-- Not having the predecessor negative package is equivalent to the
predecessor positive package. -/
theorem pred_residue_not_negative_all_forms_iff_positive_all_forms {q m : ℕ}
    (hq : 0 < q) :
    (¬ (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]))) ↔
      m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q] :=
  sub_residue_not_negative_all_forms_iff_positive_all_forms_of_pos_le (q := q)
    (c := 1) (m := m) (by decide) hq

/-- The `q-2` negative package is equivalent to not having the `q-2` positive
package. -/
theorem sub_two_residue_negative_all_forms_iff_not_positive_all_forms_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) ↔
      ¬ (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) :=
  sub_residue_negative_all_forms_iff_not_positive_all_forms_of_pos_le (q := q)
    (c := 2) (m := m) (by decide) hq

/-- Not having the `q-2` positive package is equivalent to the `q-2` negative
package. -/
theorem sub_two_residue_not_positive_all_forms_iff_negative_all_forms_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (¬ (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q])) ↔
      m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]) :=
  sub_residue_not_positive_all_forms_iff_negative_all_forms_of_pos_le (q := q)
    (c := 2) (m := m) (by decide) hq

/-- The `q-2` positive package is equivalent to not having the `q-2` negative
package. -/
theorem sub_two_residue_positive_all_forms_iff_not_negative_all_forms_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) ↔
      ¬ (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) :=
  sub_residue_positive_all_forms_iff_not_negative_all_forms_of_pos_le (q := q)
    (c := 2) (m := m) (by decide) hq

/-- Not having the `q-2` negative package is equivalent to the `q-2` positive
package. -/
theorem sub_two_residue_not_negative_all_forms_iff_positive_all_forms_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (¬ (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]))) ↔
      m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q] :=
  sub_residue_not_negative_all_forms_iff_positive_all_forms_of_pos_le (q := q)
    (c := 2) (m := m) (by decide) hq

/-- The `q-5` negative package is equivalent to not having the `q-5` positive
package. -/
theorem sub_five_residue_negative_all_forms_iff_not_positive_all_forms_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) ↔
      ¬ (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) :=
  sub_residue_negative_all_forms_iff_not_positive_all_forms_of_pos_le (q := q)
    (c := 5) (m := m) (by decide) hq

/-- Not having the `q-5` positive package is equivalent to the `q-5` negative
package. -/
theorem sub_five_residue_not_positive_all_forms_iff_negative_all_forms_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (¬ (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q])) ↔
      m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]) :=
  sub_residue_not_positive_all_forms_iff_negative_all_forms_of_pos_le (q := q)
    (c := 5) (m := m) (by decide) hq

/-- The `q-5` positive package is equivalent to not having the `q-5` negative
package. -/
theorem sub_five_residue_positive_all_forms_iff_not_negative_all_forms_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) ↔
      ¬ (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) :=
  sub_residue_positive_all_forms_iff_not_negative_all_forms_of_pos_le (q := q)
    (c := 5) (m := m) (by decide) hq

/-- Not having the `q-5` negative package is equivalent to the `q-5` positive
package. -/
theorem sub_five_residue_not_negative_all_forms_iff_positive_all_forms_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (¬ (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]))) ↔
      m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q] :=
  sub_residue_not_negative_all_forms_iff_positive_all_forms_of_pos_le (q := q)
    (c := 5) (m := m) (by decide) hq

/-- Not having the positive `q-c` package gives the negative package. -/
theorem sub_residue_negative_all_forms_of_not_positive_all_forms_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q)
    (h : ¬ (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q])) :
    m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]) :=
  (sub_residue_not_positive_all_forms_iff_negative_all_forms_of_pos_le
    (q := q) (c := c) (m := m) hc0 hcq).1 h

/-- The negative `q-c` package gives nonexistence of the positive package. -/
theorem not_positive_all_forms_of_sub_residue_negative_all_forms {q c m : ℕ}
    (h : m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) :
    ¬ (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) :=
  sub_residue_negative_all_forms_not_positive_all_forms h

/-- Not having the negative `q-c` package gives the positive package. -/
theorem sub_residue_positive_all_forms_of_not_negative_all_forms_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q)
    (h : ¬ (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]))) :
    m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q] :=
  (sub_residue_not_negative_all_forms_iff_positive_all_forms_of_pos_le
    (q := q) (c := c) (m := m) hc0 hcq).1 h

/-- The positive `q-c` package gives nonexistence of the negative package. -/
theorem not_negative_all_forms_of_sub_residue_positive_all_forms {q c m : ℕ}
    (h : m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) :
    ¬ (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) :=
  sub_residue_positive_all_forms_not_negative_all_forms h

/-- Not having the predecessor positive package gives the predecessor negative
package. -/
theorem pred_residue_negative_all_forms_of_not_positive_all_forms {q m : ℕ}
    (hq : 0 < q)
    (h : ¬ (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q])) :
    m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]) :=
  (pred_residue_not_positive_all_forms_iff_negative_all_forms (q := q)
    (m := m) hq).1 h

/-- The predecessor negative package gives nonexistence of the predecessor
positive package. -/
theorem pred_residue_not_positive_all_forms_of_negative_all_forms {q m : ℕ}
    (h : m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) :
    ¬ (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) :=
  pred_residue_negative_all_forms_not_positive_all_forms h

/-- Not having the predecessor negative package gives the predecessor positive
package. -/
theorem pred_residue_positive_all_forms_of_not_negative_all_forms {q m : ℕ}
    (hq : 0 < q)
    (h : ¬ (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]))) :
    m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q] :=
  (pred_residue_not_negative_all_forms_iff_positive_all_forms (q := q)
    (m := m) hq).1 h

/-- The predecessor positive package gives nonexistence of the predecessor
negative package. -/
theorem pred_residue_not_negative_all_forms_of_positive_all_forms {q m : ℕ}
    (h : m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) :
    ¬ (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) :=
  pred_residue_positive_all_forms_not_negative_all_forms h

/-- Not having the `q-2` positive package gives the `q-2` negative package. -/
theorem sub_two_residue_negative_all_forms_of_not_positive_all_forms_of_le
    {q m : ℕ} (hq : 2 ≤ q)
    (h : ¬ (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q])) :
    m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]) :=
  (sub_two_residue_not_positive_all_forms_iff_negative_all_forms_of_le
    (q := q) (m := m) hq).1 h

/-- The `q-2` negative package gives nonexistence of the `q-2` positive
package. -/
theorem sub_two_residue_not_positive_all_forms_of_negative_all_forms
    {q m : ℕ}
    (h : m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) :
    ¬ (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) :=
  sub_two_residue_negative_all_forms_not_positive_all_forms h

/-- Not having the `q-2` negative package gives the `q-2` positive package. -/
theorem sub_two_residue_positive_all_forms_of_not_negative_all_forms_of_le
    {q m : ℕ} (hq : 2 ≤ q)
    (h : ¬ (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]))) :
    m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q] :=
  (sub_two_residue_not_negative_all_forms_iff_positive_all_forms_of_le
    (q := q) (m := m) hq).1 h

/-- The `q-2` positive package gives nonexistence of the `q-2` negative
package. -/
theorem sub_two_residue_not_negative_all_forms_of_positive_all_forms
    {q m : ℕ}
    (h : m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) :
    ¬ (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) :=
  sub_two_residue_positive_all_forms_not_negative_all_forms h

/-- Not having the `q-5` positive package gives the `q-5` negative package. -/
theorem sub_five_residue_negative_all_forms_of_not_positive_all_forms_of_le
    {q m : ℕ} (hq : 5 ≤ q)
    (h : ¬ (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q])) :
    m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]) :=
  (sub_five_residue_not_positive_all_forms_iff_negative_all_forms_of_le
    (q := q) (m := m) hq).1 h

/-- The `q-5` negative package gives nonexistence of the `q-5` positive
package. -/
theorem sub_five_residue_not_positive_all_forms_of_negative_all_forms
    {q m : ℕ}
    (h : m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) :
    ¬ (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) :=
  sub_five_residue_negative_all_forms_not_positive_all_forms h

/-- Not having the `q-5` negative package gives the `q-5` positive package. -/
theorem sub_five_residue_positive_all_forms_of_not_negative_all_forms_of_le
    {q m : ℕ} (hq : 5 ≤ q)
    (h : ¬ (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]))) :
    m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q] :=
  (sub_five_residue_not_negative_all_forms_iff_positive_all_forms_of_le
    (q := q) (m := m) hq).1 h

/-- The `q-5` positive package gives nonexistence of the `q-5` negative
package. -/
theorem sub_five_residue_not_negative_all_forms_of_positive_all_forms
    {q m : ℕ}
    (h : m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) :
    ¬ (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) :=
  sub_five_residue_positive_all_forms_not_negative_all_forms h

/-- The `q-c` all-forms packages satisfy excluded middle. -/
theorem sub_residue_positive_or_negative_all_forms_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) ∨
      (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) := by
  by_cases hm : m % q = q - c
  · exact Or.inl (sub_residue_positive_all_forms_of_mod_eq_sub_of_pos_le
      (q := q) (c := c) (m := m) hc0 hcq hm)
  · exact Or.inr (sub_residue_negative_all_forms_of_mod_ne_sub_of_pos_le
      (q := q) (c := c) (m := m) hc0 hcq hm)

/-- The `q-c` all-forms packages satisfy excluded middle, negative first. -/
theorem sub_residue_negative_or_positive_all_forms_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) :
    (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) ∨
      (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) := by
  rcases sub_residue_positive_or_negative_all_forms_of_pos_le (q := q)
    (c := c) (m := m) hc0 hcq with hp | hn
  · exact Or.inr hp
  · exact Or.inl hn

/-- The predecessor all-forms packages satisfy excluded middle. -/
theorem pred_residue_positive_or_negative_all_forms {q m : ℕ} (hq : 0 < q) :
    (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) ∨
      (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) :=
  sub_residue_positive_or_negative_all_forms_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- The predecessor all-forms packages satisfy excluded middle, negative first. -/
theorem pred_residue_negative_or_positive_all_forms {q m : ℕ} (hq : 0 < q) :
    (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) ∨
      (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) :=
  sub_residue_negative_or_positive_all_forms_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq

/-- The `q-2` all-forms packages satisfy excluded middle. -/
theorem sub_two_residue_positive_or_negative_all_forms_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) ∨
      (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) :=
  sub_residue_positive_or_negative_all_forms_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- The `q-2` all-forms packages satisfy excluded middle, negative first. -/
theorem sub_two_residue_negative_or_positive_all_forms_of_le {q m : ℕ}
    (hq : 2 ≤ q) :
    (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) ∨
      (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) :=
  sub_residue_negative_or_positive_all_forms_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq

/-- The `q-5` all-forms packages satisfy excluded middle. -/
theorem sub_five_residue_positive_or_negative_all_forms_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) ∨
      (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) :=
  sub_residue_positive_or_negative_all_forms_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- The `q-5` all-forms packages satisfy excluded middle, negative first. -/
theorem sub_five_residue_negative_or_positive_all_forms_of_le {q m : ℕ}
    (hq : 5 ≤ q) :
    (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) ∨
      (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) :=
  sub_residue_negative_or_positive_all_forms_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq

/-- Case eliminator for the positive/negative `q-c` all-forms split. -/
theorem sub_residue_all_forms_cases_of_pos_le {q c m : ℕ} {P : Prop}
    (hc0 : 0 < c) (hcq : c ≤ q)
    (hp : (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) → P)
    (hn : (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) → P) :
    P := by
  rcases sub_residue_positive_or_negative_all_forms_of_pos_le (q := q)
    (c := c) (m := m) hc0 hcq with hpos | hneg
  · exact hp hpos
  · exact hn hneg

/-- Case eliminator for the negative/positive `q-c` all-forms split. -/
theorem sub_residue_all_forms_cases_neg_first_of_pos_le {q c m : ℕ} {P : Prop}
    (hc0 : 0 < c) (hcq : c ≤ q)
    (hn : (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) → P)
    (hp : (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) → P) :
    P := by
  rcases sub_residue_negative_or_positive_all_forms_of_pos_le (q := q)
    (c := c) (m := m) hc0 hcq with hneg | hpos
  · exact hn hneg
  · exact hp hpos

/-- Case eliminator for the predecessor all-forms split. -/
theorem pred_residue_all_forms_cases {q m : ℕ} {P : Prop} (hq : 0 < q)
    (hp : (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) → P)
    (hn : (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) → P) :
    P :=
  sub_residue_all_forms_cases_of_pos_le (q := q) (c := 1) (m := m)
    (P := P) (by decide) hq hp hn

/-- Case eliminator for the predecessor all-forms split, negative first. -/
theorem pred_residue_all_forms_cases_neg_first {q m : ℕ} {P : Prop}
    (hq : 0 < q)
    (hn : (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) → P)
    (hp : (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) → P) :
    P :=
  sub_residue_all_forms_cases_neg_first_of_pos_le (q := q) (c := 1)
    (m := m) (P := P) (by decide) hq hn hp

/-- Case eliminator for the `q-2` all-forms split. -/
theorem sub_two_residue_all_forms_cases_of_le {q m : ℕ} {P : Prop}
    (hq : 2 ≤ q)
    (hp : (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) → P)
    (hn : (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) → P) :
    P :=
  sub_residue_all_forms_cases_of_pos_le (q := q) (c := 2) (m := m)
    (P := P) (by decide) hq hp hn

/-- Case eliminator for the `q-2` all-forms split, negative first. -/
theorem sub_two_residue_all_forms_cases_neg_first_of_le {q m : ℕ} {P : Prop}
    (hq : 2 ≤ q)
    (hn : (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) → P)
    (hp : (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) → P) :
    P :=
  sub_residue_all_forms_cases_neg_first_of_pos_le (q := q) (c := 2)
    (m := m) (P := P) (by decide) hq hn hp

/-- Case eliminator for the `q-5` all-forms split. -/
theorem sub_five_residue_all_forms_cases_of_le {q m : ℕ} {P : Prop}
    (hq : 5 ≤ q)
    (hp : (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) → P)
    (hn : (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) → P) :
    P :=
  sub_residue_all_forms_cases_of_pos_le (q := q) (c := 5) (m := m)
    (P := P) (by decide) hq hp hn

/-- Case eliminator for the `q-5` all-forms split, negative first. -/
theorem sub_five_residue_all_forms_cases_neg_first_of_le {q m : ℕ} {P : Prop}
    (hq : 5 ≤ q)
    (hn : (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) → P)
    (hp : (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) → P) :
    P :=
  sub_residue_all_forms_cases_neg_first_of_pos_le (q := q) (c := 5)
    (m := m) (P := P) (by decide) hq hn hp

/-- Not having the positive package gives direct residue inequality. -/
theorem mod_ne_sub_of_not_positive_all_forms_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q)
    (h : ¬ (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q])) :
    m % q ≠ q - c :=
  mod_ne_sub_of_sub_residue_negative_all_forms
    (sub_residue_negative_all_forms_of_not_positive_all_forms_of_pos_le
      (q := q) (c := c) (m := m) hc0 hcq h)

/-- Not having the positive package gives shifted nondivisibility. -/
theorem not_dvd_add_of_not_positive_all_forms_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q)
    (h : ¬ (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q])) :
    ¬ (q ∣ m + c) :=
  not_dvd_add_of_sub_residue_negative_all_forms
    (sub_residue_negative_all_forms_of_not_positive_all_forms_of_pos_le
      (q := q) (c := c) (m := m) hc0 hcq h)

/-- Not having the positive package gives negated `Nat.ModEq`. -/
theorem not_modEq_sub_of_not_positive_all_forms_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q)
    (h : ¬ (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q])) :
    ¬ (m ≡ q - c [MOD q]) :=
  not_modEq_sub_of_sub_residue_negative_all_forms
    (sub_residue_negative_all_forms_of_not_positive_all_forms_of_pos_le
      (q := q) (c := c) (m := m) hc0 hcq h)

/-- Not having the negative package gives direct residue equality. -/
theorem mod_eq_sub_of_not_negative_all_forms_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q)
    (h : ¬ (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]))) :
    m % q = q - c :=
  mod_eq_sub_of_sub_residue_positive_all_forms
    (sub_residue_positive_all_forms_of_not_negative_all_forms_of_pos_le
      (q := q) (c := c) (m := m) hc0 hcq h)

/-- Not having the negative package gives shifted divisibility. -/
theorem dvd_add_of_not_negative_all_forms_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q)
    (h : ¬ (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]))) :
    q ∣ m + c :=
  dvd_add_of_sub_residue_positive_all_forms
    (sub_residue_positive_all_forms_of_not_negative_all_forms_of_pos_le
      (q := q) (c := c) (m := m) hc0 hcq h)

/-- Not having the negative package gives `Nat.ModEq`. -/
theorem modEq_sub_of_not_negative_all_forms_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q)
    (h : ¬ (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]))) :
    m ≡ q - c [MOD q] :=
  modEq_sub_of_sub_residue_positive_all_forms
    (sub_residue_positive_all_forms_of_not_negative_all_forms_of_pos_le
      (q := q) (c := c) (m := m) hc0 hcq h)

/-- Not having the predecessor positive package gives predecessor residue
inequality. -/
theorem mod_ne_pred_of_not_positive_all_forms {q m : ℕ} (hq : 0 < q)
    (h : ¬ (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q])) :
    m % q ≠ q - 1 :=
  mod_ne_sub_of_not_positive_all_forms_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq h

/-- Not having the predecessor positive package gives nondivisibility of `m+1`. -/
theorem not_dvd_succ_of_not_positive_all_forms {q m : ℕ} (hq : 0 < q)
    (h : ¬ (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q])) :
    ¬ (q ∣ m + 1) :=
  not_dvd_add_of_not_positive_all_forms_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq h

/-- Not having the predecessor positive package gives negated predecessor
`Nat.ModEq`. -/
theorem not_modEq_pred_of_not_positive_all_forms {q m : ℕ} (hq : 0 < q)
    (h : ¬ (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q])) :
    ¬ (m ≡ q - 1 [MOD q]) :=
  not_modEq_sub_of_not_positive_all_forms_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq h

/-- Not having the predecessor negative package gives predecessor residue
equality. -/
theorem mod_eq_pred_of_not_negative_all_forms {q m : ℕ} (hq : 0 < q)
    (h : ¬ (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]))) :
    m % q = q - 1 :=
  mod_eq_sub_of_not_negative_all_forms_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq h

/-- Not having the predecessor negative package gives divisibility of `m+1`. -/
theorem dvd_succ_of_not_negative_all_forms {q m : ℕ} (hq : 0 < q)
    (h : ¬ (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]))) :
    q ∣ m + 1 :=
  dvd_add_of_not_negative_all_forms_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq h

/-- Not having the predecessor negative package gives predecessor `Nat.ModEq`. -/
theorem modEq_pred_of_not_negative_all_forms {q m : ℕ} (hq : 0 < q)
    (h : ¬ (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]))) :
    m ≡ q - 1 [MOD q] :=
  modEq_sub_of_not_negative_all_forms_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq h

/-- Not having the `q-2` positive package gives residue `q-2` inequality. -/
theorem mod_ne_sub_two_of_not_positive_all_forms_of_le {q m : ℕ}
    (hq : 2 ≤ q)
    (h : ¬ (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q])) :
    m % q ≠ q - 2 :=
  mod_ne_sub_of_not_positive_all_forms_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq h

/-- Not having the `q-2` positive package gives nondivisibility of `m+2`. -/
theorem not_dvd_add_two_of_not_positive_all_forms_of_le {q m : ℕ}
    (hq : 2 ≤ q)
    (h : ¬ (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q])) :
    ¬ (q ∣ m + 2) :=
  not_dvd_add_of_not_positive_all_forms_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq h

/-- Not having the `q-2` positive package gives negated `Nat.ModEq` to `q-2`. -/
theorem not_modEq_sub_two_of_not_positive_all_forms_of_le {q m : ℕ}
    (hq : 2 ≤ q)
    (h : ¬ (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q])) :
    ¬ (m ≡ q - 2 [MOD q]) :=
  not_modEq_sub_of_not_positive_all_forms_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq h

/-- Not having the `q-2` negative package gives residue `q-2` equality. -/
theorem mod_eq_sub_two_of_not_negative_all_forms_of_le {q m : ℕ}
    (hq : 2 ≤ q)
    (h : ¬ (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]))) :
    m % q = q - 2 :=
  mod_eq_sub_of_not_negative_all_forms_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq h

/-- Not having the `q-2` negative package gives divisibility of `m+2`. -/
theorem dvd_add_two_of_not_negative_all_forms_of_le {q m : ℕ} (hq : 2 ≤ q)
    (h : ¬ (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]))) :
    q ∣ m + 2 :=
  dvd_add_of_not_negative_all_forms_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq h

/-- Not having the `q-2` negative package gives `Nat.ModEq` to `q-2`. -/
theorem modEq_sub_two_of_not_negative_all_forms_of_le {q m : ℕ}
    (hq : 2 ≤ q)
    (h : ¬ (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]))) :
    m ≡ q - 2 [MOD q] :=
  modEq_sub_of_not_negative_all_forms_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq h

/-- Not having the `q-5` positive package gives residue `q-5` inequality. -/
theorem mod_ne_sub_five_of_not_positive_all_forms_of_le {q m : ℕ}
    (hq : 5 ≤ q)
    (h : ¬ (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q])) :
    m % q ≠ q - 5 :=
  mod_ne_sub_of_not_positive_all_forms_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq h

/-- Not having the `q-5` positive package gives nondivisibility of `m+5`. -/
theorem not_dvd_add_five_of_not_positive_all_forms_of_le {q m : ℕ}
    (hq : 5 ≤ q)
    (h : ¬ (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q])) :
    ¬ (q ∣ m + 5) :=
  not_dvd_add_of_not_positive_all_forms_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq h

/-- Not having the `q-5` positive package gives negated `Nat.ModEq` to `q-5`. -/
theorem not_modEq_sub_five_of_not_positive_all_forms_of_le {q m : ℕ}
    (hq : 5 ≤ q)
    (h : ¬ (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q])) :
    ¬ (m ≡ q - 5 [MOD q]) :=
  not_modEq_sub_of_not_positive_all_forms_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq h

/-- Not having the `q-5` negative package gives residue `q-5` equality. -/
theorem mod_eq_sub_five_of_not_negative_all_forms_of_le {q m : ℕ}
    (hq : 5 ≤ q)
    (h : ¬ (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]))) :
    m % q = q - 5 :=
  mod_eq_sub_of_not_negative_all_forms_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq h

/-- Not having the `q-5` negative package gives divisibility of `m+5`. -/
theorem dvd_add_five_of_not_negative_all_forms_of_le {q m : ℕ} (hq : 5 ≤ q)
    (h : ¬ (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]))) :
    q ∣ m + 5 :=
  dvd_add_of_not_negative_all_forms_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq h

/-- Not having the `q-5` negative package gives `Nat.ModEq` to `q-5`. -/
theorem modEq_sub_five_of_not_negative_all_forms_of_le {q m : ℕ}
    (hq : 5 ≤ q)
    (h : ¬ (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]))) :
    m ≡ q - 5 [MOD q] :=
  modEq_sub_of_not_negative_all_forms_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq h

/-- Direct residue equality rules out the negative `q-c` all-forms package. -/
theorem not_negative_all_forms_of_mod_eq_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : m % q = q - c) :
    ¬ (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) :=
  not_negative_all_forms_of_sub_residue_positive_all_forms
    (sub_residue_positive_all_forms_of_mod_eq_sub_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq hm)

/-- Shifted divisibility rules out the negative `q-c` all-forms package. -/
theorem not_negative_all_forms_of_dvd_add_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : q ∣ m + c) :
    ¬ (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) :=
  not_negative_all_forms_of_sub_residue_positive_all_forms
    (sub_residue_positive_all_forms_of_dvd_add_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq hm)

/-- `Nat.ModEq` to `q-c` rules out the negative `q-c` all-forms package. -/
theorem not_negative_all_forms_of_modEq_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : m ≡ q - c [MOD q]) :
    ¬ (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q])) :=
  not_negative_all_forms_of_sub_residue_positive_all_forms
    (sub_residue_positive_all_forms_of_modEq_sub_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq hm)

/-- Direct residue inequality rules out the positive `q-c` all-forms package. -/
theorem not_positive_all_forms_of_mod_ne_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : m % q ≠ q - c) :
    ¬ (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) :=
  not_positive_all_forms_of_sub_residue_negative_all_forms
    (sub_residue_negative_all_forms_of_mod_ne_sub_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq hm)

/-- Shifted nondivisibility rules out the positive `q-c` all-forms package. -/
theorem not_positive_all_forms_of_not_dvd_add_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : ¬ (q ∣ m + c)) :
    ¬ (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) :=
  not_positive_all_forms_of_sub_residue_negative_all_forms
    (sub_residue_negative_all_forms_of_not_dvd_add_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq hm)

/-- Negated `Nat.ModEq` to `q-c` rules out the positive all-forms package. -/
theorem not_positive_all_forms_of_not_modEq_sub_of_pos_le {q c m : ℕ}
    (hc0 : 0 < c) (hcq : c ≤ q) (hm : ¬ (m ≡ q - c [MOD q])) :
    ¬ (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q]) :=
  not_positive_all_forms_of_sub_residue_negative_all_forms
    (sub_residue_negative_all_forms_of_not_modEq_sub_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq hm)

/-- Predecessor residue equality rules out the predecessor negative package. -/
theorem not_negative_all_forms_of_mod_eq_pred {q m : ℕ} (hq : 0 < q)
    (hm : m % q = q - 1) :
    ¬ (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) :=
  not_negative_all_forms_of_mod_eq_sub_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq hm

/-- Divisibility of `m+1` rules out the predecessor negative package. -/
theorem not_negative_all_forms_of_dvd_succ {q m : ℕ} (hq : 0 < q)
    (hm : q ∣ m + 1) :
    ¬ (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) :=
  not_negative_all_forms_of_dvd_add_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq hm

/-- Predecessor `Nat.ModEq` rules out the predecessor negative package. -/
theorem not_negative_all_forms_of_modEq_pred {q m : ℕ} (hq : 0 < q)
    (hm : m ≡ q - 1 [MOD q]) :
    ¬ (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q])) :=
  not_negative_all_forms_of_modEq_sub_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq hm

/-- Predecessor residue inequality rules out the predecessor positive package. -/
theorem not_positive_all_forms_of_mod_ne_pred {q m : ℕ} (hq : 0 < q)
    (hm : m % q ≠ q - 1) :
    ¬ (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) :=
  not_positive_all_forms_of_mod_ne_sub_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq hm

/-- Nondivisibility of `m+1` rules out the predecessor positive package. -/
theorem not_positive_all_forms_of_not_dvd_succ {q m : ℕ} (hq : 0 < q)
    (hm : ¬ (q ∣ m + 1)) :
    ¬ (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) :=
  not_positive_all_forms_of_not_dvd_add_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq hm

/-- Negated predecessor `Nat.ModEq` rules out the predecessor positive package. -/
theorem not_positive_all_forms_of_not_modEq_pred {q m : ℕ} (hq : 0 < q)
    (hm : ¬ (m ≡ q - 1 [MOD q])) :
    ¬ (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q]) :=
  not_positive_all_forms_of_not_modEq_sub_of_pos_le (q := q) (c := 1)
    (m := m) (by decide) hq hm

/-- Residue `q-2` equality rules out the `q-2` negative package. -/
theorem not_negative_all_forms_of_mod_eq_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : m % q = q - 2) :
    ¬ (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) :=
  not_negative_all_forms_of_mod_eq_sub_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq hm

/-- Divisibility of `m+2` rules out the `q-2` negative package. -/
theorem not_negative_all_forms_of_dvd_add_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : q ∣ m + 2) :
    ¬ (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) :=
  not_negative_all_forms_of_dvd_add_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq hm

/-- `Nat.ModEq` to `q-2` rules out the `q-2` negative package. -/
theorem not_negative_all_forms_of_modEq_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : m ≡ q - 2 [MOD q]) :
    ¬ (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q])) :=
  not_negative_all_forms_of_modEq_sub_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq hm

/-- Residue `q-2` inequality rules out the `q-2` positive package. -/
theorem not_positive_all_forms_of_mod_ne_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : m % q ≠ q - 2) :
    ¬ (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) :=
  not_positive_all_forms_of_mod_ne_sub_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq hm

/-- Nondivisibility of `m+2` rules out the `q-2` positive package. -/
theorem not_positive_all_forms_of_not_dvd_add_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : ¬ (q ∣ m + 2)) :
    ¬ (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) :=
  not_positive_all_forms_of_not_dvd_add_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq hm

/-- Negated `Nat.ModEq` to `q-2` rules out the `q-2` positive package. -/
theorem not_positive_all_forms_of_not_modEq_sub_two_of_le {q m : ℕ}
    (hq : 2 ≤ q) (hm : ¬ (m ≡ q - 2 [MOD q])) :
    ¬ (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q]) :=
  not_positive_all_forms_of_not_modEq_sub_of_pos_le (q := q) (c := 2)
    (m := m) (by decide) hq hm

/-- Residue `q-5` equality rules out the `q-5` negative package. -/
theorem not_negative_all_forms_of_mod_eq_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : m % q = q - 5) :
    ¬ (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) :=
  not_negative_all_forms_of_mod_eq_sub_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq hm

/-- Divisibility of `m+5` rules out the `q-5` negative package. -/
theorem not_negative_all_forms_of_dvd_add_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : q ∣ m + 5) :
    ¬ (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) :=
  not_negative_all_forms_of_dvd_add_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq hm

/-- `Nat.ModEq` to `q-5` rules out the `q-5` negative package. -/
theorem not_negative_all_forms_of_modEq_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : m ≡ q - 5 [MOD q]) :
    ¬ (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q])) :=
  not_negative_all_forms_of_modEq_sub_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq hm

/-- Residue `q-5` inequality rules out the `q-5` positive package. -/
theorem not_positive_all_forms_of_mod_ne_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : m % q ≠ q - 5) :
    ¬ (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) :=
  not_positive_all_forms_of_mod_ne_sub_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq hm

/-- Nondivisibility of `m+5` rules out the `q-5` positive package. -/
theorem not_positive_all_forms_of_not_dvd_add_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : ¬ (q ∣ m + 5)) :
    ¬ (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) :=
  not_positive_all_forms_of_not_dvd_add_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq hm

/-- Negated `Nat.ModEq` to `q-5` rules out the `q-5` positive package. -/
theorem not_positive_all_forms_of_not_modEq_sub_five_of_le {q m : ℕ}
    (hq : 5 ≤ q) (hm : ¬ (m ≡ q - 5 [MOD q])) :
    ¬ (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q]) :=
  not_positive_all_forms_of_not_modEq_sub_of_pos_le (q := q) (c := 5)
    (m := m) (by decide) hq hm

/-- Not having the positive `q-c` package is equivalent to avoiding residue
`q-c`. -/
theorem sub_residue_not_positive_all_forms_iff_mod_ne_sub_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q) :
    (¬ (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q])) ↔
      m % q ≠ q - c :=
  Iff.trans
    (sub_residue_not_positive_all_forms_iff_negative_all_forms_of_pos_le
      (q := q) (c := c) (m := m) hc0 hcq)
    (sub_residue_negative_all_forms_iff_mod_ne_sub_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq)

/-- Not having the positive `q-c` package is equivalent to shifted
nondivisibility. -/
theorem sub_residue_not_positive_all_forms_iff_not_dvd_add_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q) :
    (¬ (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q])) ↔
      ¬ (q ∣ m + c) :=
  Iff.trans
    (sub_residue_not_positive_all_forms_iff_negative_all_forms_of_pos_le
      (q := q) (c := c) (m := m) hc0 hcq)
    (sub_residue_negative_all_forms_iff_not_dvd_add_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq)

/-- Not having the positive `q-c` package is equivalent to negated
`Nat.ModEq`. -/
theorem sub_residue_not_positive_all_forms_iff_not_modEq_sub_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q) :
    (¬ (m % q = q - c ∧ q ∣ m + c ∧ m ≡ q - c [MOD q])) ↔
      ¬ (m ≡ q - c [MOD q]) :=
  Iff.trans
    (sub_residue_not_positive_all_forms_iff_negative_all_forms_of_pos_le
      (q := q) (c := c) (m := m) hc0 hcq)
    (sub_residue_negative_all_forms_iff_not_modEq_sub_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq)

/-- Not having the negative `q-c` package is equivalent to direct residue
equality. -/
theorem sub_residue_not_negative_all_forms_iff_mod_eq_sub_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q) :
    (¬ (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]))) ↔
      m % q = q - c :=
  Iff.trans
    (sub_residue_not_negative_all_forms_iff_positive_all_forms_of_pos_le
      (q := q) (c := c) (m := m) hc0 hcq)
    (sub_residue_positive_all_forms_iff_mod_eq_sub_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq)

/-- Not having the negative `q-c` package is equivalent to shifted
divisibility. -/
theorem sub_residue_not_negative_all_forms_iff_dvd_add_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q) :
    (¬ (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]))) ↔
      q ∣ m + c :=
  Iff.trans
    (sub_residue_not_negative_all_forms_iff_positive_all_forms_of_pos_le
      (q := q) (c := c) (m := m) hc0 hcq)
    (sub_residue_positive_all_forms_iff_dvd_add_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq)

/-- Not having the negative `q-c` package is equivalent to `Nat.ModEq` to
`q-c`. -/
theorem sub_residue_not_negative_all_forms_iff_modEq_sub_of_pos_le
    {q c m : ℕ} (hc0 : 0 < c) (hcq : c ≤ q) :
    (¬ (m % q ≠ q - c ∧ ¬ (q ∣ m + c) ∧ ¬ (m ≡ q - c [MOD q]))) ↔
      m ≡ q - c [MOD q] :=
  Iff.trans
    (sub_residue_not_negative_all_forms_iff_positive_all_forms_of_pos_le
      (q := q) (c := c) (m := m) hc0 hcq)
    (sub_residue_positive_all_forms_iff_modEq_sub_of_pos_le (q := q)
      (c := c) (m := m) hc0 hcq)

/-- Not having the predecessor positive package is equivalent to predecessor
residue inequality. -/
theorem pred_residue_not_positive_all_forms_iff_mod_ne_pred {q m : ℕ}
    (hq : 0 < q) :
    (¬ (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q])) ↔
      m % q ≠ q - 1 :=
  sub_residue_not_positive_all_forms_iff_mod_ne_sub_of_pos_le (q := q)
    (c := 1) (m := m) (by decide) hq

/-- Not having the predecessor positive package is equivalent to
nondivisibility of `m+1`. -/
theorem pred_residue_not_positive_all_forms_iff_not_dvd_succ {q m : ℕ}
    (hq : 0 < q) :
    (¬ (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q])) ↔
      ¬ (q ∣ m + 1) :=
  sub_residue_not_positive_all_forms_iff_not_dvd_add_of_pos_le (q := q)
    (c := 1) (m := m) (by decide) hq

/-- Not having the predecessor positive package is equivalent to negated
predecessor `Nat.ModEq`. -/
theorem pred_residue_not_positive_all_forms_iff_not_modEq_pred {q m : ℕ}
    (hq : 0 < q) :
    (¬ (m % q = q - 1 ∧ q ∣ m + 1 ∧ m ≡ q - 1 [MOD q])) ↔
      ¬ (m ≡ q - 1 [MOD q]) :=
  sub_residue_not_positive_all_forms_iff_not_modEq_sub_of_pos_le (q := q)
    (c := 1) (m := m) (by decide) hq

/-- Not having the predecessor negative package is equivalent to predecessor
residue equality. -/
theorem pred_residue_not_negative_all_forms_iff_mod_eq_pred {q m : ℕ}
    (hq : 0 < q) :
    (¬ (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]))) ↔
      m % q = q - 1 :=
  sub_residue_not_negative_all_forms_iff_mod_eq_sub_of_pos_le (q := q)
    (c := 1) (m := m) (by decide) hq

/-- Not having the predecessor negative package is equivalent to divisibility
of `m+1`. -/
theorem pred_residue_not_negative_all_forms_iff_dvd_succ {q m : ℕ}
    (hq : 0 < q) :
    (¬ (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]))) ↔
      q ∣ m + 1 :=
  sub_residue_not_negative_all_forms_iff_dvd_add_of_pos_le (q := q)
    (c := 1) (m := m) (by decide) hq

/-- Not having the predecessor negative package is equivalent to predecessor
`Nat.ModEq`. -/
theorem pred_residue_not_negative_all_forms_iff_modEq_pred {q m : ℕ}
    (hq : 0 < q) :
    (¬ (m % q ≠ q - 1 ∧ ¬ (q ∣ m + 1) ∧ ¬ (m ≡ q - 1 [MOD q]))) ↔
      m ≡ q - 1 [MOD q] :=
  sub_residue_not_negative_all_forms_iff_modEq_sub_of_pos_le (q := q)
    (c := 1) (m := m) (by decide) hq

/-- Not having the `q-2` positive package is equivalent to residue `q-2`
inequality. -/
theorem sub_two_residue_not_positive_all_forms_iff_mod_ne_sub_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (¬ (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q])) ↔
      m % q ≠ q - 2 :=
  sub_residue_not_positive_all_forms_iff_mod_ne_sub_of_pos_le (q := q)
    (c := 2) (m := m) (by decide) hq

/-- Not having the `q-2` positive package is equivalent to nondivisibility of
`m+2`. -/
theorem sub_two_residue_not_positive_all_forms_iff_not_dvd_add_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (¬ (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q])) ↔
      ¬ (q ∣ m + 2) :=
  sub_residue_not_positive_all_forms_iff_not_dvd_add_of_pos_le (q := q)
    (c := 2) (m := m) (by decide) hq

/-- Not having the `q-2` positive package is equivalent to negated
`Nat.ModEq` to `q-2`. -/
theorem sub_two_residue_not_positive_all_forms_iff_not_modEq_sub_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (¬ (m % q = q - 2 ∧ q ∣ m + 2 ∧ m ≡ q - 2 [MOD q])) ↔
      ¬ (m ≡ q - 2 [MOD q]) :=
  sub_residue_not_positive_all_forms_iff_not_modEq_sub_of_pos_le (q := q)
    (c := 2) (m := m) (by decide) hq

/-- Not having the `q-2` negative package is equivalent to residue `q-2`
equality. -/
theorem sub_two_residue_not_negative_all_forms_iff_mod_eq_sub_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (¬ (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]))) ↔
      m % q = q - 2 :=
  sub_residue_not_negative_all_forms_iff_mod_eq_sub_of_pos_le (q := q)
    (c := 2) (m := m) (by decide) hq

/-- Not having the `q-2` negative package is equivalent to divisibility of
`m+2`. -/
theorem sub_two_residue_not_negative_all_forms_iff_dvd_add_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (¬ (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]))) ↔
      q ∣ m + 2 :=
  sub_residue_not_negative_all_forms_iff_dvd_add_of_pos_le (q := q)
    (c := 2) (m := m) (by decide) hq

/-- Not having the `q-2` negative package is equivalent to `Nat.ModEq` to
`q-2`. -/
theorem sub_two_residue_not_negative_all_forms_iff_modEq_sub_two_of_le
    {q m : ℕ} (hq : 2 ≤ q) :
    (¬ (m % q ≠ q - 2 ∧ ¬ (q ∣ m + 2) ∧ ¬ (m ≡ q - 2 [MOD q]))) ↔
      m ≡ q - 2 [MOD q] :=
  sub_residue_not_negative_all_forms_iff_modEq_sub_of_pos_le (q := q)
    (c := 2) (m := m) (by decide) hq

/-- Not having the `q-5` positive package is equivalent to residue `q-5`
inequality. -/
theorem sub_five_residue_not_positive_all_forms_iff_mod_ne_sub_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (¬ (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q])) ↔
      m % q ≠ q - 5 :=
  sub_residue_not_positive_all_forms_iff_mod_ne_sub_of_pos_le (q := q)
    (c := 5) (m := m) (by decide) hq

/-- Not having the `q-5` positive package is equivalent to nondivisibility of
`m+5`. -/
theorem sub_five_residue_not_positive_all_forms_iff_not_dvd_add_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (¬ (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q])) ↔
      ¬ (q ∣ m + 5) :=
  sub_residue_not_positive_all_forms_iff_not_dvd_add_of_pos_le (q := q)
    (c := 5) (m := m) (by decide) hq

/-- Not having the `q-5` positive package is equivalent to negated
`Nat.ModEq` to `q-5`. -/
theorem sub_five_residue_not_positive_all_forms_iff_not_modEq_sub_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (¬ (m % q = q - 5 ∧ q ∣ m + 5 ∧ m ≡ q - 5 [MOD q])) ↔
      ¬ (m ≡ q - 5 [MOD q]) :=
  sub_residue_not_positive_all_forms_iff_not_modEq_sub_of_pos_le (q := q)
    (c := 5) (m := m) (by decide) hq

/-- Not having the `q-5` negative package is equivalent to residue `q-5`
equality. -/
theorem sub_five_residue_not_negative_all_forms_iff_mod_eq_sub_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (¬ (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]))) ↔
      m % q = q - 5 :=
  sub_residue_not_negative_all_forms_iff_mod_eq_sub_of_pos_le (q := q)
    (c := 5) (m := m) (by decide) hq

/-- Not having the `q-5` negative package is equivalent to divisibility of
`m+5`. -/
theorem sub_five_residue_not_negative_all_forms_iff_dvd_add_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (¬ (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]))) ↔
      q ∣ m + 5 :=
  sub_residue_not_negative_all_forms_iff_dvd_add_of_pos_le (q := q)
    (c := 5) (m := m) (by decide) hq

/-- Not having the `q-5` negative package is equivalent to `Nat.ModEq` to
`q-5`. -/
theorem sub_five_residue_not_negative_all_forms_iff_modEq_sub_five_of_le
    {q m : ℕ} (hq : 5 ≤ q) :
    (¬ (m % q ≠ q - 5 ∧ ¬ (q ∣ m + 5) ∧ ¬ (m ≡ q - 5 [MOD q]))) ↔
      m ≡ q - 5 [MOD q] :=
  sub_residue_not_negative_all_forms_iff_modEq_sub_of_pos_le (q := q)
    (c := 5) (m := m) (by decide) hq

/-- Not having the `q-10` positive package is equivalent to residue `q-10`
inequality. -/
theorem sub_ten_residue_not_positive_all_forms_iff_mod_ne_sub_ten_of_le
    {q m : ℕ} (hq : 10 ≤ q) :
    (¬ (m % q = q - 10 ∧ q ∣ m + 10 ∧ m ≡ q - 10 [MOD q])) ↔
      m % q ≠ q - 10 :=
  sub_residue_not_positive_all_forms_iff_mod_ne_sub_of_pos_le (q := q)
    (c := 10) (m := m) (by decide) hq

/-- Not having the `q-10` positive package is equivalent to nondivisibility of
`m+10`. -/
theorem sub_ten_residue_not_positive_all_forms_iff_not_dvd_add_ten_of_le
    {q m : ℕ} (hq : 10 ≤ q) :
    (¬ (m % q = q - 10 ∧ q ∣ m + 10 ∧ m ≡ q - 10 [MOD q])) ↔
      ¬ (q ∣ m + 10) :=
  sub_residue_not_positive_all_forms_iff_not_dvd_add_of_pos_le (q := q)
    (c := 10) (m := m) (by decide) hq

/-- Not having the `q-10` positive package is equivalent to negated
`Nat.ModEq` to `q-10`. -/
theorem sub_ten_residue_not_positive_all_forms_iff_not_modEq_sub_ten_of_le
    {q m : ℕ} (hq : 10 ≤ q) :
    (¬ (m % q = q - 10 ∧ q ∣ m + 10 ∧ m ≡ q - 10 [MOD q])) ↔
      ¬ (m ≡ q - 10 [MOD q]) :=
  sub_residue_not_positive_all_forms_iff_not_modEq_sub_of_pos_le (q := q)
    (c := 10) (m := m) (by decide) hq

/-- Not having the `q-10` negative package is equivalent to residue `q-10`
equality. -/
theorem sub_ten_residue_not_negative_all_forms_iff_mod_eq_sub_ten_of_le
    {q m : ℕ} (hq : 10 ≤ q) :
    (¬ (m % q ≠ q - 10 ∧ ¬ (q ∣ m + 10) ∧ ¬ (m ≡ q - 10 [MOD q]))) ↔
      m % q = q - 10 :=
  sub_residue_not_negative_all_forms_iff_mod_eq_sub_of_pos_le (q := q)
    (c := 10) (m := m) (by decide) hq

/-- Not having the `q-10` negative package is equivalent to divisibility of
`m+10`. -/
theorem sub_ten_residue_not_negative_all_forms_iff_dvd_add_ten_of_le
    {q m : ℕ} (hq : 10 ≤ q) :
    (¬ (m % q ≠ q - 10 ∧ ¬ (q ∣ m + 10) ∧ ¬ (m ≡ q - 10 [MOD q]))) ↔
      q ∣ m + 10 :=
  sub_residue_not_negative_all_forms_iff_dvd_add_of_pos_le (q := q)
    (c := 10) (m := m) (by decide) hq

/-- Not having the `q-10` negative package is equivalent to `Nat.ModEq` to
`q-10`. -/
theorem sub_ten_residue_not_negative_all_forms_iff_modEq_sub_ten_of_le
    {q m : ℕ} (hq : 10 ≤ q) :
    (¬ (m % q ≠ q - 10 ∧ ¬ (q ∣ m + 10) ∧ ¬ (m ≡ q - 10 [MOD q]))) ↔
      m ≡ q - 10 [MOD q] :=
  sub_residue_not_negative_all_forms_iff_modEq_sub_of_pos_le (q := q)
    (c := 10) (m := m) (by decide) hq

/-- Residue `q-10` is equivalent to divisibility of `m+10`. -/
theorem mod_eq_sub_ten_iff_dvd_add_ten_of_le {q m : ℕ} (hq : 10 ≤ q) :
    m % q = q - 10 ↔ q ∣ m + 10 :=
  mod_eq_sub_iff_dvd_add_of_pos_le (q := q) (c := 10) (m := m)
    (by decide) hq

/-- Divisibility of `m+10` is equivalent to residue `q-10`. -/
theorem dvd_add_ten_iff_mod_eq_sub_ten_of_le {q m : ℕ} (hq : 10 ≤ q) :
    q ∣ m + 10 ↔ m % q = q - 10 :=
  (mod_eq_sub_ten_iff_dvd_add_ten_of_le (q := q) (m := m) hq).symm

/-- Avoiding residue `q-10` is equivalent to nondivisibility of `m+10`. -/
theorem mod_ne_sub_ten_iff_not_dvd_add_ten_of_le {q m : ℕ}
    (hq : 10 ≤ q) :
    m % q ≠ q - 10 ↔ ¬ (q ∣ m + 10) :=
  mod_ne_sub_iff_not_dvd_add_of_pos_le (q := q) (c := 10) (m := m)
    (by decide) hq

/-- Nondivisibility of `m+10` is equivalent to avoiding residue `q-10`. -/
theorem not_dvd_add_ten_iff_mod_ne_sub_ten_of_le {q m : ℕ}
    (hq : 10 ≤ q) :
    ¬ (q ∣ m + 10) ↔ m % q ≠ q - 10 :=
  (mod_ne_sub_ten_iff_not_dvd_add_ten_of_le (q := q) (m := m) hq).symm

/-- Residue `q-10` gives divisibility of `m+10`. -/
theorem dvd_add_ten_of_mod_eq_sub_ten_of_le {q m : ℕ} (hq : 10 ≤ q)
    (hm : m % q = q - 10) :
    q ∣ m + 10 :=
  (mod_eq_sub_ten_iff_dvd_add_ten_of_le (q := q) (m := m) hq).1 hm

/-- Divisibility of `m+10` gives residue `q-10`. -/
theorem mod_eq_sub_ten_of_dvd_add_ten_of_le {q m : ℕ} (hq : 10 ≤ q)
    (hm : q ∣ m + 10) :
    m % q = q - 10 :=
  (mod_eq_sub_ten_iff_dvd_add_ten_of_le (q := q) (m := m) hq).2 hm

/-- Avoiding residue `q-10` gives nondivisibility of `m+10`. -/
theorem not_dvd_add_ten_of_mod_ne_sub_ten_of_le {q m : ℕ}
    (hq : 10 ≤ q) (hm : m % q ≠ q - 10) :
    ¬ (q ∣ m + 10) :=
  (mod_ne_sub_ten_iff_not_dvd_add_ten_of_le (q := q) (m := m) hq).1 hm

/-- Nondivisibility of `m+10` gives avoidance of residue `q-10`. -/
theorem mod_ne_sub_ten_of_not_dvd_add_ten_of_le {q m : ℕ}
    (hq : 10 ≤ q) (hm : ¬ (q ∣ m + 10)) :
    m % q ≠ q - 10 :=
  (mod_ne_sub_ten_iff_not_dvd_add_ten_of_le (q := q) (m := m) hq).2 hm

/-- `Nat.ModEq` to `q-10` is equivalent to divisibility of `m+10`. -/
theorem modEq_sub_ten_iff_dvd_add_ten_of_le {q m : ℕ} (hq : 10 ≤ q) :
    m ≡ q - 10 [MOD q] ↔ q ∣ m + 10 :=
  modEq_sub_iff_dvd_add_of_pos_le (q := q) (c := 10) (m := m)
    (by decide) hq

/-- Divisibility of `m+10` is equivalent to `Nat.ModEq` to `q-10`. -/
theorem dvd_add_ten_iff_modEq_sub_ten_of_le {q m : ℕ} (hq : 10 ≤ q) :
    q ∣ m + 10 ↔ m ≡ q - 10 [MOD q] :=
  (modEq_sub_ten_iff_dvd_add_ten_of_le (q := q) (m := m) hq).symm

/-- Negated `Nat.ModEq` to `q-10` is equivalent to nondivisibility of
`m+10`. -/
theorem not_modEq_sub_ten_iff_not_dvd_add_ten_of_le {q m : ℕ}
    (hq : 10 ≤ q) :
    ¬ (m ≡ q - 10 [MOD q]) ↔ ¬ (q ∣ m + 10) :=
  not_modEq_sub_iff_not_dvd_add_of_pos_le (q := q) (c := 10) (m := m)
    (by decide) hq

/-- Nondivisibility of `m+10` is equivalent to negated `Nat.ModEq` to
`q-10`. -/
theorem not_dvd_add_ten_iff_not_modEq_sub_ten_of_le {q m : ℕ}
    (hq : 10 ≤ q) :
    ¬ (q ∣ m + 10) ↔ ¬ (m ≡ q - 10 [MOD q]) :=
  (not_modEq_sub_ten_iff_not_dvd_add_ten_of_le (q := q) (m := m) hq).symm

/-- Divisibility of `m+10` gives `Nat.ModEq` to `q-10`. -/
theorem modEq_sub_ten_of_dvd_add_ten_of_le {q m : ℕ} (hq : 10 ≤ q)
    (hm : q ∣ m + 10) :
    m ≡ q - 10 [MOD q] :=
  (modEq_sub_ten_iff_dvd_add_ten_of_le (q := q) (m := m) hq).2 hm

/-- `Nat.ModEq` to `q-10` gives divisibility of `m+10`. -/
theorem dvd_add_ten_of_modEq_sub_ten_of_le {q m : ℕ} (hq : 10 ≤ q)
    (hm : m ≡ q - 10 [MOD q]) :
    q ∣ m + 10 :=
  (modEq_sub_ten_iff_dvd_add_ten_of_le (q := q) (m := m) hq).1 hm

/-- Nondivisibility of `m+10` gives negated `Nat.ModEq` to `q-10`. -/
theorem not_modEq_sub_ten_of_not_dvd_add_ten_of_le {q m : ℕ}
    (hq : 10 ≤ q) (hm : ¬ (q ∣ m + 10)) :
    ¬ (m ≡ q - 10 [MOD q]) :=
  (not_modEq_sub_ten_iff_not_dvd_add_ten_of_le (q := q) (m := m) hq).2 hm

/-- Negated `Nat.ModEq` to `q-10` gives nondivisibility of `m+10`. -/
theorem not_dvd_add_ten_of_not_modEq_sub_ten_of_le {q m : ℕ}
    (hq : 10 ≤ q) (hm : ¬ (m ≡ q - 10 [MOD q])) :
    ¬ (q ∣ m + 10) :=
  (not_modEq_sub_ten_iff_not_dvd_add_ten_of_le (q := q) (m := m) hq).1 hm

/-- Direct residue `q-10` is equivalent to `Nat.ModEq` to `q-10`. -/
theorem mod_eq_sub_ten_iff_modEq_sub_ten_of_le {q m : ℕ} (hq : 10 ≤ q) :
    m % q = q - 10 ↔ m ≡ q - 10 [MOD q] :=
  mod_eq_sub_iff_modEq_sub_of_pos_le (q := q) (c := 10) (m := m)
    (by decide) hq

/-- `Nat.ModEq` to `q-10` is equivalent to direct residue `q-10`. -/
theorem modEq_sub_ten_iff_mod_eq_sub_ten_of_le {q m : ℕ} (hq : 10 ≤ q) :
    m ≡ q - 10 [MOD q] ↔ m % q = q - 10 :=
  (mod_eq_sub_ten_iff_modEq_sub_ten_of_le (q := q) (m := m) hq).symm

/-- Negated `Nat.ModEq` to `q-10` is equivalent to avoiding residue `q-10`. -/
theorem not_modEq_sub_ten_iff_mod_ne_sub_ten_of_le {q m : ℕ}
    (hq : 10 ≤ q) :
    ¬ (m ≡ q - 10 [MOD q]) ↔ m % q ≠ q - 10 :=
  not_modEq_sub_iff_mod_ne_sub_of_pos_le (q := q) (c := 10) (m := m)
    (by decide) hq

/-- Avoiding residue `q-10` is equivalent to negated `Nat.ModEq` to `q-10`. -/
theorem mod_ne_sub_ten_iff_not_modEq_sub_ten_of_le {q m : ℕ}
    (hq : 10 ≤ q) :
    m % q ≠ q - 10 ↔ ¬ (m ≡ q - 10 [MOD q]) :=
  (not_modEq_sub_ten_iff_mod_ne_sub_ten_of_le (q := q) (m := m) hq).symm

/-- Direct residue `q-10` gives `Nat.ModEq` to `q-10`. -/
theorem modEq_sub_ten_of_mod_eq_sub_ten_of_le {q m : ℕ} (hq : 10 ≤ q)
    (hm : m % q = q - 10) :
    m ≡ q - 10 [MOD q] :=
  (mod_eq_sub_ten_iff_modEq_sub_ten_of_le (q := q) (m := m) hq).1 hm

/-- `Nat.ModEq` to `q-10` gives direct residue `q-10`. -/
theorem mod_eq_sub_ten_of_modEq_sub_ten_of_le {q m : ℕ} (hq : 10 ≤ q)
    (hm : m ≡ q - 10 [MOD q]) :
    m % q = q - 10 :=
  (mod_eq_sub_ten_iff_modEq_sub_ten_of_le (q := q) (m := m) hq).2 hm

/-- Avoiding residue `q-10` gives negated `Nat.ModEq` to `q-10`. -/
theorem not_modEq_sub_ten_of_mod_ne_sub_ten_of_le {q m : ℕ}
    (hq : 10 ≤ q) (hm : m % q ≠ q - 10) :
    ¬ (m ≡ q - 10 [MOD q]) :=
  (mod_ne_sub_ten_iff_not_modEq_sub_ten_of_le (q := q) (m := m) hq).1 hm

/-- Negated `Nat.ModEq` to `q-10` gives avoidance of residue `q-10`. -/
theorem mod_ne_sub_ten_of_not_modEq_sub_ten_of_le {q m : ℕ}
    (hq : 10 ≤ q) (hm : ¬ (m ≡ q - 10 [MOD q])) :
    m % q ≠ q - 10 :=
  (mod_ne_sub_ten_iff_not_modEq_sub_ten_of_le (q := q) (m := m) hq).2 hm

end Ch17NestedModArithmetic
end Pending
end QseriesFormalization
