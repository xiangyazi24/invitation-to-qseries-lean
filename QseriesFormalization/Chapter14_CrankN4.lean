import QseriesFormalization.Chapter14

/-!
# Chapter 14 — Crank hits all 5 residues mod 5 for partitions of 4

Companion file to `Chapter14.lean`.  Concretely verifies the n=4 case
of the Dyson-Garvan crank theorem: the 5 partitions of 4 have cranks

  [4]       crank = 4
  [3,1]     crank = 0
  [2,2]     crank = 2
  [2,1,1]   crank = -2
  [1,1,1,1] crank = -4

which mod 5 are `{4, 0, 2, 3, 1}`, i.e. all 5 residues mod 5 are hit
exactly once.  This is the combinatorial witness for `p(4) ≡ 0 (mod 5)`.

The full Dyson-Garvan theorem (`crank distributes evenly mod p over
partitions of `5n+4`/`7n+5`/`11n+6` for `p ∈ {5,7,11}`) is OPEN; this file
covers only the `n = 0`, `p = 5` case.
-/

namespace QseriesFormalization
namespace PartIII
namespace Ch14

open Multiset

/-! ## Construct the three mid-crank partitions explicitly -/

/-- Partition `[3, 1]` of 4. -/
def partitionFourThreeOne : Nat.Partition 4 where
  parts := {3, 1}
  parts_pos := by
    intro a ha
    fin_cases ha <;> omega
  parts_sum := by decide

/-- Partition `[2, 2]` of 4. -/
def partitionFourTwoTwo : Nat.Partition 4 where
  parts := {2, 2}
  parts_pos := by
    intro a ha
    fin_cases ha <;> omega
  parts_sum := by decide

/-- Partition `[2, 1, 1]` of 4. -/
def partitionFourTwoOneOne : Nat.Partition 4 where
  parts := {2, 1, 1}
  parts_pos := by
    intro a ha
    fin_cases ha <;> omega
  parts_sum := by decide

/-! ## Compute cranks of the three mid partitions -/

/-- `crank([3, 1]) = 0`: `1 ∈ parts`, `ω = 1`, `μ = 1` (just [3] > 1). -/
theorem crank_partitionFourThreeOne :
    crank partitionFourThreeOne = 0 := by
  show (if (1 : ℕ) ∈ ({3, 1} : Multiset ℕ) then
          ((crankMu partitionFourThreeOne : Int) -
           (crankOnes partitionFourThreeOne : Int))
        else (crankLargest partitionFourThreeOne : Int)) = 0
  have h_mem : (1 : ℕ) ∈ ({3, 1} : Multiset ℕ) := by decide
  rw [if_pos h_mem]
  have h_ones : crankOnes partitionFourThreeOne = 1 := by
    show ({3, 1} : Multiset ℕ).count 1 = 1
    decide
  have h_mu : crankMu partitionFourThreeOne = 1 := by
    show (({3, 1} : Multiset ℕ).filter
           (fun x => x > crankOnes partitionFourThreeOne)).card = 1
    rw [h_ones]; decide
  rw [h_ones, h_mu]; rfl

/-- `crank([2, 2]) = 2`: `1 ∉ parts`, largest = 2. -/
theorem crank_partitionFourTwoTwo :
    crank partitionFourTwoTwo = 2 := by
  show (if (1 : ℕ) ∈ ({2, 2} : Multiset ℕ) then
          ((crankMu partitionFourTwoTwo : Int) -
           (crankOnes partitionFourTwoTwo : Int))
        else (crankLargest partitionFourTwoTwo : Int)) = 2
  have h_not_mem : (1 : ℕ) ∉ ({2, 2} : Multiset ℕ) := by decide
  rw [if_neg h_not_mem]
  show ((({2, 2} : Multiset ℕ).fold max 0 : Nat) : Int) = 2
  decide

/-- `crank([2, 1, 1]) = -2`: `1 ∈ parts`, `ω = 2`, `μ = 0`. -/
theorem crank_partitionFourTwoOneOne :
    crank partitionFourTwoOneOne = -2 := by
  show (if (1 : ℕ) ∈ ({2, 1, 1} : Multiset ℕ) then
          ((crankMu partitionFourTwoOneOne : Int) -
           (crankOnes partitionFourTwoOneOne : Int))
        else (crankLargest partitionFourTwoOneOne : Int)) = -2
  have h_mem : (1 : ℕ) ∈ ({2, 1, 1} : Multiset ℕ) := by decide
  rw [if_pos h_mem]
  have h_ones : crankOnes partitionFourTwoOneOne = 2 := by
    show ({2, 1, 1} : Multiset ℕ).count 1 = 2
    decide
  have h_mu : crankMu partitionFourTwoOneOne = 0 := by
    show (({2, 1, 1} : Multiset ℕ).filter
           (fun x => x > crankOnes partitionFourTwoOneOne)).card = 0
    rw [h_ones]; decide
  rw [h_ones, h_mu]; rfl

/-! ## Surjectivity onto ZMod 5 -/

/-- **Chan §14 (Dyson-Garvan), n = 0 case.**

For every `r : ZMod 5`, there exists a partition `p` of 4 whose crank
maps to `r` mod 5.  Concretely, the cranks `4, 0, 2, -2, -4` of the
five partitions of 4 cover residues `4, 0, 2, 3, 1` respectively, hence
all of `ZMod 5`. -/
theorem crank_n4_surjective_mod_five :
    ∀ r : ZMod 5, ∃ p : Nat.Partition 4, ((crank p : Int) : ZMod 5) = r := by
  intro r
  -- Use the explicit five partitions:
  --   crank [1,1,1,1] = -4 ≡ 1 (mod 5)
  --   crank [3,1]     =  0
  --   crank [2,2]     =  2
  --   crank [2,1,1]   = -2 ≡ 3 (mod 5)
  --   crank [4]       =  4
  fin_cases r
  · -- r = 0: use [3, 1]
    refine ⟨partitionFourThreeOne, ?_⟩
    rw [crank_partitionFourThreeOne]; rfl
  · -- r = 1: use [1, 1, 1, 1] with crank = -4
    refine ⟨{
      parts := Multiset.replicate 4 1
      parts_pos := by intro a ha; rw [Multiset.mem_replicate] at ha; omega
      parts_sum := by rw [Multiset.sum_replicate]; simp }, ?_⟩
    rw [crank_allOnes 4 (by omega)]; rfl
  · -- r = 2: use [2, 2]
    refine ⟨partitionFourTwoTwo, ?_⟩
    rw [crank_partitionFourTwoTwo]; rfl
  · -- r = 3: use [2, 1, 1] with crank = -2
    refine ⟨partitionFourTwoOneOne, ?_⟩
    rw [crank_partitionFourTwoOneOne]; rfl
  · -- r = 4: use [4]
    refine ⟨{
      parts := {4}
      parts_pos := by intro a ha; rw [Multiset.mem_singleton] at ha; omega
      parts_sum := by rw [Multiset.sum_singleton] }, ?_⟩
    rw [crank_singleton 4 (by omega)]; rfl

end Ch14
end PartIII
end QseriesFormalization
