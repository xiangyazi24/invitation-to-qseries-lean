import QseriesFormalization.Chapter14

/-!
# Chapter 14 - Crank hits all 5 residues mod 5 for partitions of 19

The `n = 3` case of the Dyson-Garvan crank theorem for `p = 5`
(`19 = 5*3 + 4`), companion to `Chapter14_CrankN4.lean`,
`Chapter14_CrankN9.lean`, and `Chapter14_CrankN14.lean`. We exhibit five
partitions of 19 whose cranks cover all residues mod 5:

  `[19]`       crank = 19 ≡ 4
  `[18,1]`     crank = 0
  `[17,2]`     crank = 17 ≡ 2
  `[16,3]`     crank = 16 ≡ 1
  `[13,3,3]`   crank = 13 ≡ 3

For the parts with `1 ∉ parts` the crank is the largest part; for `[18,1]`,
`omega = 1` one and `mu = 1` (just `[18] > 1`), so crank `= 1 - 1 = 0`.

The full Dyson-Garvan equidistribution theorem is still OPEN; this adds the
`n = 3`, `p = 5` surjectivity case to the `n = 0`, `n = 1`, and `n = 2` cases
already in `Chapter14_CrankN4.lean`, `Chapter14_CrankN9.lean`, and
`Chapter14_CrankN14.lean`.
-/

namespace QseriesFormalization
namespace PartIII
namespace Ch14

open Multiset

/-- Partition `[19]` of 19. -/
def partitionNineteenNineteen : Nat.Partition 19 where
  parts := {19}
  parts_pos := by intro a ha; rw [Multiset.mem_singleton] at ha; omega
  parts_sum := by rw [Multiset.sum_singleton]

/-- Partition `[18, 1]` of 19. -/
def partitionNineteenEighteenOne : Nat.Partition 19 where
  parts := {18, 1}
  parts_pos := by intro a ha; fin_cases ha <;> omega
  parts_sum := by decide

/-- Partition `[17, 2]` of 19. -/
def partitionNineteenSeventeenTwo : Nat.Partition 19 where
  parts := {17, 2}
  parts_pos := by intro a ha; fin_cases ha <;> omega
  parts_sum := by decide

/-- Partition `[16, 3]` of 19. -/
def partitionNineteenSixteenThree : Nat.Partition 19 where
  parts := {16, 3}
  parts_pos := by intro a ha; fin_cases ha <;> omega
  parts_sum := by decide

/-- Partition `[13, 3, 3]` of 19. -/
def partitionNineteenThirteenThreeThree : Nat.Partition 19 where
  parts := {13, 3, 3}
  parts_pos := by intro a ha; fin_cases ha <;> omega
  parts_sum := by decide

/-- `crank([19]) = 19`: `1 ∉ parts`, largest = 19. -/
theorem crank_partitionNineteenNineteen : crank partitionNineteenNineteen = 19 := by
  show (if (1 : ℕ) ∈ ({19} : Multiset ℕ) then
          ((crankMu partitionNineteenNineteen : Int) - (crankOnes partitionNineteenNineteen : Int))
        else (crankLargest partitionNineteenNineteen : Int)) = 19
  rw [if_neg (by decide : (1 : ℕ) ∉ ({19} : Multiset ℕ))]
  show ((({19} : Multiset ℕ).fold max 0 : Nat) : Int) = 19
  decide

/-- `crank([18,1]) = 0`: `1 ∈ parts`, `omega = 1`, `mu = 1` (only `[18] > 1`). -/
theorem crank_partitionNineteenEighteenOne : crank partitionNineteenEighteenOne = 0 := by
  show (if (1 : ℕ) ∈ ({18, 1} : Multiset ℕ) then
          ((crankMu partitionNineteenEighteenOne : Int) -
            (crankOnes partitionNineteenEighteenOne : Int))
        else (crankLargest partitionNineteenEighteenOne : Int)) = 0
  rw [if_pos (by decide : (1 : ℕ) ∈ ({18, 1} : Multiset ℕ))]
  have h_ones : crankOnes partitionNineteenEighteenOne = 1 := by
    show ({18, 1} : Multiset ℕ).count 1 = 1
    decide
  have h_mu : crankMu partitionNineteenEighteenOne = 1 := by
    show (({18, 1} : Multiset ℕ).filter
      (fun x => x > crankOnes partitionNineteenEighteenOne)).card = 1
    rw [h_ones]; decide
  rw [h_ones, h_mu]; rfl

/-- `crank([17,2]) = 17`: `1 ∉ parts`, largest = 17. -/
theorem crank_partitionNineteenSeventeenTwo : crank partitionNineteenSeventeenTwo = 17 := by
  show (if (1 : ℕ) ∈ ({17, 2} : Multiset ℕ) then
          ((crankMu partitionNineteenSeventeenTwo : Int) - (crankOnes partitionNineteenSeventeenTwo : Int))
        else (crankLargest partitionNineteenSeventeenTwo : Int)) = 17
  rw [if_neg (by decide : (1 : ℕ) ∉ ({17, 2} : Multiset ℕ))]
  show ((({17, 2} : Multiset ℕ).fold max 0 : Nat) : Int) = 17
  decide

/-- `crank([16,3]) = 16`: `1 ∉ parts`, largest = 16. -/
theorem crank_partitionNineteenSixteenThree : crank partitionNineteenSixteenThree = 16 := by
  show (if (1 : ℕ) ∈ ({16, 3} : Multiset ℕ) then
          ((crankMu partitionNineteenSixteenThree : Int) -
            (crankOnes partitionNineteenSixteenThree : Int))
        else (crankLargest partitionNineteenSixteenThree : Int)) = 16
  rw [if_neg (by decide : (1 : ℕ) ∉ ({16, 3} : Multiset ℕ))]
  show ((({16, 3} : Multiset ℕ).fold max 0 : Nat) : Int) = 16
  decide

/-- `crank([13,3,3]) = 13`: `1 ∉ parts`, largest = 13. -/
theorem crank_partitionNineteenThirteenThreeThree :
    crank partitionNineteenThirteenThreeThree = 13 := by
  show (if (1 : ℕ) ∈ ({13, 3, 3} : Multiset ℕ) then
          ((crankMu partitionNineteenThirteenThreeThree : Int) -
            (crankOnes partitionNineteenThirteenThreeThree : Int))
        else (crankLargest partitionNineteenThirteenThreeThree : Int)) = 13
  rw [if_neg (by decide : (1 : ℕ) ∉ ({13, 3, 3} : Multiset ℕ))]
  show ((({13, 3, 3} : Multiset ℕ).fold max 0 : Nat) : Int) = 13
  decide

/-- **Chan §14 (Dyson-Garvan), `n = 3`, `p = 5` case.**

For every `r : ZMod 5`, there is a partition `p` of `19` with `crank p ≡ r (mod 5)`.
Witnesses: `[18,1]→0, [16,3]→1, [17,2]→2, [13,3,3]→3, [19]→4`. -/
theorem crank_n19_surjective_mod_five :
    ∀ r : ZMod 5, ∃ p : Nat.Partition 19, ((crank p : Int) : ZMod 5) = r := by
  intro r
  fin_cases r
  · exact ⟨partitionNineteenEighteenOne, by rw [crank_partitionNineteenEighteenOne]; rfl⟩
  · exact ⟨partitionNineteenSixteenThree, by rw [crank_partitionNineteenSixteenThree]; rfl⟩
  · exact ⟨partitionNineteenSeventeenTwo, by rw [crank_partitionNineteenSeventeenTwo]; rfl⟩
  · exact ⟨partitionNineteenThirteenThreeThree, by rw [crank_partitionNineteenThirteenThreeThree]; rfl⟩
  · exact ⟨partitionNineteenNineteen, by rw [crank_partitionNineteenNineteen]; rfl⟩

end Ch14
end PartIII
end QseriesFormalization
