import QseriesFormalization.Chapter14

/-!
# Chapter 14 - Crank hits all 5 residues mod 5 for partitions of 29

The `n = 5` case of the Dyson-Garvan crank theorem for `p = 5`
(`29 = 5*5 + 4`), companion to `Chapter14_CrankN4.lean`,
`Chapter14_CrankN9.lean`, `Chapter14_CrankN14.lean`,
`Chapter14_CrankN19.lean`, and `Chapter14_CrankN24.lean`. We exhibit five
partitions of 29 whose cranks cover all residues mod 5:

  `[29]`       crank = 29 == 4
  `[28,1]`     crank = 0
  `[27,2]`     crank = 27 == 2
  `[26,3]`     crank = 26 == 1
  `[23,3,3]`   crank = 23 == 3

For the parts with `1` absent the crank is the largest part; for `[28,1]`,
`omega = 1` one and `mu = 1` (just `[28] > 1`), so crank `= 1 - 1 = 0`.

The full Dyson-Garvan equidistribution theorem is still OPEN; this adds the
`n = 5`, `p = 5` surjectivity case to the `n = 0`, `n = 1`, `n = 2`,
`n = 3`, and `n = 4` cases already in `Chapter14_CrankN4.lean`,
`Chapter14_CrankN9.lean`, `Chapter14_CrankN14.lean`,
`Chapter14_CrankN19.lean`, and `Chapter14_CrankN24.lean`.
-/

namespace QseriesFormalization
namespace PartIII
namespace Ch14

open Multiset

/-- Partition `[29]` of 29. -/
def partitionTwentyNineTwentyNine : Nat.Partition 29 where
  parts := {29}
  parts_pos := by intro a ha; rw [Multiset.mem_singleton] at ha; omega
  parts_sum := by rw [Multiset.sum_singleton]

/-- Partition `[28, 1]` of 29. -/
def partitionTwentyNineTwentyEightOne : Nat.Partition 29 where
  parts := {28, 1}
  parts_pos := by intro a ha; fin_cases ha <;> omega
  parts_sum := by decide

/-- Partition `[27, 2]` of 29. -/
def partitionTwentyNineTwentySevenTwo : Nat.Partition 29 where
  parts := {27, 2}
  parts_pos := by intro a ha; fin_cases ha <;> omega
  parts_sum := by decide

/-- Partition `[26, 3]` of 29. -/
def partitionTwentyNineTwentySixThree : Nat.Partition 29 where
  parts := {26, 3}
  parts_pos := by intro a ha; fin_cases ha <;> omega
  parts_sum := by decide

/-- Partition `[23, 3, 3]` of 29. -/
def partitionTwentyNineTwentyThreeThreeThree : Nat.Partition 29 where
  parts := {23, 3, 3}
  parts_pos := by intro a ha; fin_cases ha <;> omega
  parts_sum := by decide

/-- `crank([29]) = 29`: `1` absent, largest = 29. -/
theorem crank_partitionTwentyNineTwentyNine : crank partitionTwentyNineTwentyNine = 29 := by
  show (if (1 : Nat) ∈ ({29} : Multiset Nat) then
          ((crankMu partitionTwentyNineTwentyNine : Int) -
            (crankOnes partitionTwentyNineTwentyNine : Int))
        else (crankLargest partitionTwentyNineTwentyNine : Int)) = 29
  rw [if_neg (by decide : (1 : Nat) ∉ ({29} : Multiset Nat))]
  show ((({29} : Multiset Nat).fold max 0 : Nat) : Int) = 29
  decide

/-- `crank([28,1]) = 0`: `1` present, `omega = 1`, `mu = 1` (only `[28] > 1`). -/
theorem crank_partitionTwentyNineTwentyEightOne :
    crank partitionTwentyNineTwentyEightOne = 0 := by
  show (if (1 : Nat) ∈ ({28, 1} : Multiset Nat) then
          ((crankMu partitionTwentyNineTwentyEightOne : Int) -
            (crankOnes partitionTwentyNineTwentyEightOne : Int))
        else (crankLargest partitionTwentyNineTwentyEightOne : Int)) = 0
  rw [if_pos (by decide : (1 : Nat) ∈ ({28, 1} : Multiset Nat))]
  have h_ones : crankOnes partitionTwentyNineTwentyEightOne = 1 := by
    show ({28, 1} : Multiset Nat).count 1 = 1
    decide
  have h_mu : crankMu partitionTwentyNineTwentyEightOne = 1 := by
    show (({28, 1} : Multiset Nat).filter
      (fun x => x > crankOnes partitionTwentyNineTwentyEightOne)).card = 1
    rw [h_ones]; decide
  rw [h_ones, h_mu]; rfl

/-- `crank([27,2]) = 27`: `1` absent, largest = 27. -/
theorem crank_partitionTwentyNineTwentySevenTwo :
    crank partitionTwentyNineTwentySevenTwo = 27 := by
  show (if (1 : Nat) ∈ ({27, 2} : Multiset Nat) then
          ((crankMu partitionTwentyNineTwentySevenTwo : Int) -
            (crankOnes partitionTwentyNineTwentySevenTwo : Int))
        else (crankLargest partitionTwentyNineTwentySevenTwo : Int)) = 27
  rw [if_neg (by decide : (1 : Nat) ∉ ({27, 2} : Multiset Nat))]
  show ((({27, 2} : Multiset Nat).fold max 0 : Nat) : Int) = 27
  decide

/-- `crank([26,3]) = 26`: `1` absent, largest = 26. -/
theorem crank_partitionTwentyNineTwentySixThree :
    crank partitionTwentyNineTwentySixThree = 26 := by
  show (if (1 : Nat) ∈ ({26, 3} : Multiset Nat) then
          ((crankMu partitionTwentyNineTwentySixThree : Int) -
            (crankOnes partitionTwentyNineTwentySixThree : Int))
        else (crankLargest partitionTwentyNineTwentySixThree : Int)) = 26
  rw [if_neg (by decide : (1 : Nat) ∉ ({26, 3} : Multiset Nat))]
  show ((({26, 3} : Multiset Nat).fold max 0 : Nat) : Int) = 26
  decide

/-- `crank([23,3,3]) = 23`: `1` absent, largest = 23. -/
theorem crank_partitionTwentyNineTwentyThreeThreeThree :
    crank partitionTwentyNineTwentyThreeThreeThree = 23 := by
  show (if (1 : Nat) ∈ ({23, 3, 3} : Multiset Nat) then
          ((crankMu partitionTwentyNineTwentyThreeThreeThree : Int) -
            (crankOnes partitionTwentyNineTwentyThreeThreeThree : Int))
        else (crankLargest partitionTwentyNineTwentyThreeThreeThree : Int)) = 23
  rw [if_neg (by decide : (1 : Nat) ∉ ({23, 3, 3} : Multiset Nat))]
  show ((({23, 3, 3} : Multiset Nat).fold max 0 : Nat) : Int) = 23
  decide

/-- **Chan Section 14 (Dyson-Garvan), `n = 5`, `p = 5` case.**

For every `r : ZMod 5`, there is a partition `p` of `29` with
`crank p == r (mod 5)`.
Witnesses: `[28,1] -> 0`, `[26,3] -> 1`, `[27,2] -> 2`,
`[23,3,3] -> 3`, `[29] -> 4`. -/
theorem crank_n29_surjective_mod_five :
    ∀ r : ZMod 5, ∃ p : Nat.Partition 29, ((crank p : Int) : ZMod 5) = r := by
  intro r
  fin_cases r
  · exact ⟨partitionTwentyNineTwentyEightOne,
      by rw [crank_partitionTwentyNineTwentyEightOne]; rfl⟩
  · exact ⟨partitionTwentyNineTwentySixThree,
      by rw [crank_partitionTwentyNineTwentySixThree]; rfl⟩
  · exact ⟨partitionTwentyNineTwentySevenTwo,
      by rw [crank_partitionTwentyNineTwentySevenTwo]; rfl⟩
  · exact ⟨partitionTwentyNineTwentyThreeThreeThree,
      by rw [crank_partitionTwentyNineTwentyThreeThreeThree]; rfl⟩
  · exact ⟨partitionTwentyNineTwentyNine,
      by rw [crank_partitionTwentyNineTwentyNine]; rfl⟩

end Ch14
end PartIII
end QseriesFormalization
