import QseriesFormalization.Chapter14

/-!
# Chapter 14 - Crank hits all 5 residues mod 5 for partitions of 34

The `n = 6` case of the Dyson-Garvan crank theorem for `p = 5`
(`34 = 5*6 + 4`), companion to `Chapter14_CrankN4.lean`,
`Chapter14_CrankN9.lean`, `Chapter14_CrankN14.lean`,
`Chapter14_CrankN19.lean`, `Chapter14_CrankN24.lean`, and
`Chapter14_CrankN29.lean`. We exhibit five partitions of 34 whose cranks
cover all residues mod 5:

  `[34]`       crank = 34 == 4
  `[33,1]`     crank = 0
  `[32,2]`     crank = 32 == 2
  `[31,3]`     crank = 31 == 1
  `[28,3,3]`   crank = 28 == 3

For the parts with `1` absent the crank is the largest part; for `[33,1]`,
`omega = 1` one and `mu = 1` (just `[33] > 1`), so crank `= 1 - 1 = 0`.

The full Dyson-Garvan equidistribution theorem is still OPEN; this adds the
`n = 6`, `p = 5` surjectivity case to the `n = 0`, `n = 1`, `n = 2`,
`n = 3`, `n = 4`, and `n = 5` cases already in
`Chapter14_CrankN4.lean`, `Chapter14_CrankN9.lean`,
`Chapter14_CrankN14.lean`, `Chapter14_CrankN19.lean`,
`Chapter14_CrankN24.lean`, and `Chapter14_CrankN29.lean`.
-/

namespace QseriesFormalization
namespace PartIII
namespace Ch14

open Multiset

/-- Partition `[34]` of 34. -/
def partitionThirtyFourThirtyFour : Nat.Partition 34 where
  parts := {34}
  parts_pos := by intro a ha; rw [Multiset.mem_singleton] at ha; omega
  parts_sum := by rw [Multiset.sum_singleton]

/-- Partition `[33, 1]` of 34. -/
def partitionThirtyFourThirtyThreeOne : Nat.Partition 34 where
  parts := {33, 1}
  parts_pos := by intro a ha; fin_cases ha <;> omega
  parts_sum := by decide

/-- Partition `[32, 2]` of 34. -/
def partitionThirtyFourThirtyTwoTwo : Nat.Partition 34 where
  parts := {32, 2}
  parts_pos := by intro a ha; fin_cases ha <;> omega
  parts_sum := by decide

/-- Partition `[31, 3]` of 34. -/
def partitionThirtyFourThirtyOneThree : Nat.Partition 34 where
  parts := {31, 3}
  parts_pos := by intro a ha; fin_cases ha <;> omega
  parts_sum := by decide

/-- Partition `[28, 3, 3]` of 34. -/
def partitionThirtyFourTwentyEightThreeThree : Nat.Partition 34 where
  parts := {28, 3, 3}
  parts_pos := by intro a ha; fin_cases ha <;> omega
  parts_sum := by decide

/-- `crank([34]) = 34`: `1` absent, largest = 34. -/
theorem crank_partitionThirtyFourThirtyFour :
    crank partitionThirtyFourThirtyFour = 34 := by
  show (if (1 : Nat) ∈ ({34} : Multiset Nat) then
          ((crankMu partitionThirtyFourThirtyFour : Int) -
            (crankOnes partitionThirtyFourThirtyFour : Int))
        else (crankLargest partitionThirtyFourThirtyFour : Int)) = 34
  rw [if_neg (by decide : (1 : Nat) ∉ ({34} : Multiset Nat))]
  show ((({34} : Multiset Nat).fold max 0 : Nat) : Int) = 34
  decide

/-- `crank([33,1]) = 0`: `1` present, `omega = 1`, `mu = 1` (only `[33] > 1`). -/
theorem crank_partitionThirtyFourThirtyThreeOne :
    crank partitionThirtyFourThirtyThreeOne = 0 := by
  show (if (1 : Nat) ∈ ({33, 1} : Multiset Nat) then
          ((crankMu partitionThirtyFourThirtyThreeOne : Int) -
            (crankOnes partitionThirtyFourThirtyThreeOne : Int))
        else (crankLargest partitionThirtyFourThirtyThreeOne : Int)) = 0
  rw [if_pos (by decide : (1 : Nat) ∈ ({33, 1} : Multiset Nat))]
  have h_ones : crankOnes partitionThirtyFourThirtyThreeOne = 1 := by
    show ({33, 1} : Multiset Nat).count 1 = 1
    decide
  have h_mu : crankMu partitionThirtyFourThirtyThreeOne = 1 := by
    show (({33, 1} : Multiset Nat).filter
      (fun x => x > crankOnes partitionThirtyFourThirtyThreeOne)).card = 1
    rw [h_ones]; decide
  rw [h_ones, h_mu]; rfl

/-- `crank([32,2]) = 32`: `1` absent, largest = 32. -/
theorem crank_partitionThirtyFourThirtyTwoTwo :
    crank partitionThirtyFourThirtyTwoTwo = 32 := by
  show (if (1 : Nat) ∈ ({32, 2} : Multiset Nat) then
          ((crankMu partitionThirtyFourThirtyTwoTwo : Int) -
            (crankOnes partitionThirtyFourThirtyTwoTwo : Int))
        else (crankLargest partitionThirtyFourThirtyTwoTwo : Int)) = 32
  rw [if_neg (by decide : (1 : Nat) ∉ ({32, 2} : Multiset Nat))]
  show ((({32, 2} : Multiset Nat).fold max 0 : Nat) : Int) = 32
  decide

/-- `crank([31,3]) = 31`: `1` absent, largest = 31. -/
theorem crank_partitionThirtyFourThirtyOneThree :
    crank partitionThirtyFourThirtyOneThree = 31 := by
  show (if (1 : Nat) ∈ ({31, 3} : Multiset Nat) then
          ((crankMu partitionThirtyFourThirtyOneThree : Int) -
            (crankOnes partitionThirtyFourThirtyOneThree : Int))
        else (crankLargest partitionThirtyFourThirtyOneThree : Int)) = 31
  rw [if_neg (by decide : (1 : Nat) ∉ ({31, 3} : Multiset Nat))]
  show ((({31, 3} : Multiset Nat).fold max 0 : Nat) : Int) = 31
  decide

/-- `crank([28,3,3]) = 28`: `1` absent, largest = 28. -/
theorem crank_partitionThirtyFourTwentyEightThreeThree :
    crank partitionThirtyFourTwentyEightThreeThree = 28 := by
  show (if (1 : Nat) ∈ ({28, 3, 3} : Multiset Nat) then
          ((crankMu partitionThirtyFourTwentyEightThreeThree : Int) -
            (crankOnes partitionThirtyFourTwentyEightThreeThree : Int))
        else (crankLargest partitionThirtyFourTwentyEightThreeThree : Int)) = 28
  rw [if_neg (by decide : (1 : Nat) ∉ ({28, 3, 3} : Multiset Nat))]
  show ((({28, 3, 3} : Multiset Nat).fold max 0 : Nat) : Int) = 28
  decide

/-- **Chan Section 14 (Dyson-Garvan), `n = 6`, `p = 5` case.**

For every `r : ZMod 5`, there is a partition `p` of `34` with
`crank p == r (mod 5)`.
Witnesses: `[33,1] -> 0`, `[31,3] -> 1`, `[32,2] -> 2`,
`[28,3,3] -> 3`, `[34] -> 4`. -/
theorem crank_n34_surjective_mod_five :
    ∀ r : ZMod 5, ∃ p : Nat.Partition 34, ((crank p : Int) : ZMod 5) = r := by
  intro r
  fin_cases r
  · exact ⟨partitionThirtyFourThirtyThreeOne,
      by rw [crank_partitionThirtyFourThirtyThreeOne]; rfl⟩
  · exact ⟨partitionThirtyFourThirtyOneThree,
      by rw [crank_partitionThirtyFourThirtyOneThree]; rfl⟩
  · exact ⟨partitionThirtyFourThirtyTwoTwo,
      by rw [crank_partitionThirtyFourThirtyTwoTwo]; rfl⟩
  · exact ⟨partitionThirtyFourTwentyEightThreeThree,
      by rw [crank_partitionThirtyFourTwentyEightThreeThree]; rfl⟩
  · exact ⟨partitionThirtyFourThirtyFour,
      by rw [crank_partitionThirtyFourThirtyFour]; rfl⟩

end Ch14
end PartIII
end QseriesFormalization
