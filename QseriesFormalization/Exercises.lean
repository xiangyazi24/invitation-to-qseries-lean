import QseriesFormalization.Basic
import QseriesFormalization.Chapter01
import QseriesFormalization.Chapter02
import QseriesFormalization.Chapter03
import QseriesFormalization.Chapter04
import QseriesFormalization.Chapter04_T43
import QseriesFormalization.Chapter05
import QseriesFormalization.Chapter06
import QseriesFormalization.Chapter07
import QseriesFormalization.Chapter08
import QseriesFormalization.Chapter09
import QseriesFormalization.Chapter10
import QseriesFormalization.Chapter11
import QseriesFormalization.Chapter12
import QseriesFormalization.Chapter13
import QseriesFormalization.Chapter14
import QseriesFormalization.Chapter15
import QseriesFormalization.Chapter16
import QseriesFormalization.Chapter17
import QseriesFormalization.Chapter18
import QseriesFormalization.Chapter19
import QseriesFormalization.Chapter20
import QseriesFormalization.Chapter07_RRStep5
import QseriesFormalization.Chapter07_RRStep5H

/-!
# Exercises

Exercise-facing wrappers for theorem statements proved in the chapter files.
-/

namespace QseriesFormalization

section Chapter1Exercises

/-- Exercise (Chapter 1 style): weight is additive under list concatenation. -/
theorem exercise1_partitionWeight_append (l1 l2 : List Nat) :
    partitionWeight (l1 ++ l2) = partitionWeight l1 + partitionWeight l2 :=
  partitionWeight_append l1 l2

end Chapter1Exercises

section Chapter2Exercises

variable {R : Type*} [Field R]

/-- Exercise (Chapter 2 style): the zero function satisfies the functional equation. -/
theorem exercise2_zero_function (q : R) :
    PartI.Ch02.SatisfiesFunctionalEquation (R := R) (fun _ => 0) q := by
  intro z
  simp

end Chapter2Exercises

section Chapter3Exercises

variable {R : Type*} [CommSemiring R]

/-- Exercise (Chapter 3 style): the finite q-binomial theorem at `n = 0`. -/
theorem exercise3_qbinomial_n0 (q x : R) :
    PartI.Ch03.qBinomialLHS q x 0 = PartI.Ch03.qBinomialRHS q x 0 :=
  PartI.Ch03.finiteQBinomialTheorem (R := R) q x 0

/-- Exercise (Chapter 3 style): the finite q-binomial theorem at `n = 1`. -/
theorem exercise3_qbinomial_n1 (q x : R) :
    PartI.Ch03.qBinomialLHS q x 1 = PartI.Ch03.qBinomialRHS q x 1 :=
  PartI.Ch03.finiteQBinomialTheorem (R := R) q x 1

end Chapter3Exercises

section Chapter4Exercises

variable {R : Type*} [Field R]

/-- Exercise (Chapter 4 style): low-value check of pentagonal numbers. -/
theorem exercise4_pentagonal_two : pentagonalNumber 2 = 5 := by
  norm_num [pentagonalNumber]

/-- Exercise (Chapter 4 style): low-value check of pentagonal numbers. -/
theorem exercise4_pentagonal_three : pentagonalNumber 3 = 12 := by
  norm_num [pentagonalNumber]

/-- Exercise (Chapter 4 style): finite Euler product vanishes at `q = 1` for positive length. -/
theorem exercise4_eulerProduct_one_succ (n : Nat) :
    PartI.Ch04.eulerProductTrunc (R := R) 1 (Nat.succ n) = 0 := by
  simp [PartI.Ch04.eulerProductTrunc]

theorem exercise4_quintupleProductFactor_partial_eq_trunc (q z : ℂ) (N : Nat) :
    (∏ n ∈ Finset.range N, PartI.Ch04.quintupleProductFactor q z n) =
      PartI.Ch04.quintupleProductLHSTrunc q z N :=
  PartI.Ch04.quintupleProductFactor_partial_eq_trunc q z N

theorem exercise4_tendsto_quintupleProductLHSTrunc (q z : ℂ) (hq : ‖q‖ < 1) :
    Filter.Tendsto (fun N : ℕ => PartI.Ch04.quintupleProductLHSTrunc q z N) Filter.atTop
      (nhds (PartI.Ch04.quintupleProductLHS q z)) :=
  PartI.Ch04.tendsto_quintupleProductLHSTrunc q z hq

theorem exercise4_theorem44ProductFactor_substitution_eq_quintuple
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (n : Nat) :
    PartI.Ch04.theorem44ProductFactor (q ^ 2) (z / q) n =
      PartI.Ch04.quintupleProductFactor q z n :=
  PartI.Ch04.theorem44ProductFactor_substitution_eq_quintuple q z hq hz n

theorem exercise4_theorem44ProductLHS_substitution_eq_quintuple
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) :
    PartI.Ch04.theorem44ProductLHS (q ^ 2) (z / q) =
      PartI.Ch04.quintupleProductLHS q z :=
  PartI.Ch04.theorem44ProductLHS_substitution_eq_quintuple q z hq hz

theorem exercise4_theorem44ProductPartial_eq_qPoch (q z : ℂ) (N : Nat) :
    PartI.Ch04.theorem44ProductPartial q z N =
      qPoch q q N * qPoch (z * q) q N * qPoch z⁻¹ q N *
        qPoch (z ^ 2 * q) (q ^ 2) N * qPoch (z⁻¹ ^ 2 * q) (q ^ 2) N :=
  PartI.Ch04.theorem44ProductPartial_eq_qPoch q z N

theorem exercise4_theorem44DoubleSumZIndex_reindex (k n : Int) :
    PartI.Ch04.theorem44DoubleSumZIndex (2 * n - k) n = k :=
  PartI.Ch04.theorem44DoubleSumZIndex_reindex k n

theorem exercise4_theorem44DoubleSumSignIndex_reindex (k n : Int) :
    PartI.Ch04.theorem44DoubleSumSignIndex (2 * n - k) n = 3 * n - k :=
  PartI.Ch04.theorem44DoubleSumSignIndex_reindex k n

theorem exercise4_theorem44DoubleSumSixExponent_reindex (k n : Int) :
    PartI.Ch04.theorem44DoubleSumSixExponent (2 * n - k) n =
      PartI.Ch04.theorem44CoeffSixExponent k (3 * n - k) :=
  PartI.Ch04.theorem44DoubleSumSixExponent_reindex k n

theorem exercise4_theorem44CoeffResidueCondition_reindex (k n : Int) :
    (3 : Int) ∣ (3 * n - k) + k :=
  PartI.Ch04.theorem44CoeffResidueCondition_reindex k n

theorem exercise4_theorem44CoeffSixExponent_nonneg (k l : Int) :
    0 ≤ PartI.Ch04.theorem44CoeffSixExponent k l :=
  PartI.Ch04.theorem44CoeffSixExponent_nonneg k l

theorem exercise4_two_dvd_theorem44CoeffSixExponent (k l : Int) :
    (2 : Int) ∣ PartI.Ch04.theorem44CoeffSixExponent k l :=
  PartI.Ch04.two_dvd_theorem44CoeffSixExponent k l

theorem exercise4_six_dvd_theorem44CoeffSixExponent_of_residue
    (k l : Int) (h : (3 : Int) ∣ l + k) :
    (6 : Int) ∣ PartI.Ch04.theorem44CoeffSixExponent k l :=
  PartI.Ch04.six_dvd_theorem44CoeffSixExponent_of_residue k l h

theorem exercise4_theorem44CoeffExponentIndex_spec
    (k l : Int) (h : (3 : Int) ∣ l + k) :
    6 * ((PartI.Ch04.theorem44CoeffExponentIndex k l : Nat) : Int) =
      PartI.Ch04.theorem44CoeffSixExponent k l :=
  PartI.Ch04.theorem44CoeffExponentIndex_spec k l h

theorem exercise4_theorem44_zpow_reindex (z : ℂ) (hz : z ≠ 0) (k n : Int) :
    z ^ (-(2 * n - k)) * z ^ (2 * n) = z ^ k :=
  PartI.Ch04.theorem44_zpow_reindex z hz k n

theorem exercise4_theorem44_sign_reindex (k n : Int) :
    (-1 : ℂ) ^ (2 * n - k) * (-1 : ℂ) ^ n = (-1 : ℂ) ^ (3 * n - k) :=
  PartI.Ch04.theorem44_sign_reindex k n

theorem exercise4_theorem44CoeffSixExponent_residue_zero (r j : Int) :
    PartI.Ch04.theorem44CoeffSixExponent (3 * r) (3 * j) =
      3 * r * (3 * r + 1) + 6 * j * (3 * j - 1) :=
  PartI.Ch04.theorem44CoeffSixExponent_residue_zero r j

theorem exercise4_theorem44CoeffSixExponent_residue_one (r j : Int) :
    PartI.Ch04.theorem44CoeffSixExponent (-(3 * r) - 1) (3 * j + 1) =
      3 * r * (3 * r + 1) + 6 * j * (3 * j + 1) :=
  PartI.Ch04.theorem44CoeffSixExponent_residue_one r j

theorem exercise4_theorem44CoeffSixExponent_residue_two (r j : Int) :
    PartI.Ch04.theorem44CoeffSixExponent (3 * r - 2) (3 * j + 2) =
      (3 * r - 2) * (3 * r - 1) + 2 * (3 * j + 2) * (3 * j + 1) :=
  PartI.Ch04.theorem44CoeffSixExponent_residue_two r j

theorem exercise4_theorem44CoeffResidueCondition_zero (r j : Int) :
    (3 : Int) ∣ (3 * j) + (3 * r) :=
  PartI.Ch04.theorem44CoeffResidueCondition_zero r j

theorem exercise4_theorem44CoeffResidueCondition_one (r j : Int) :
    (3 : Int) ∣ (3 * j + 1) + (-(3 * r) - 1) :=
  PartI.Ch04.theorem44CoeffResidueCondition_one r j

theorem exercise4_theorem44CoeffResidueCondition_two (r j : Int) :
    (3 : Int) ∣ (3 * j + 2) + (3 * r - 2) :=
  PartI.Ch04.theorem44CoeffResidueCondition_two r j

theorem exercise4_theorem44CoeffResidueCondition_zero_iff (r l : Int) :
    ((3 : Int) ∣ l + 3 * r) ↔ ∃ j : Int, l = 3 * j :=
  PartI.Ch04.theorem44CoeffResidueCondition_zero_iff r l

theorem exercise4_theorem44CoeffResidueCondition_one_iff (r l : Int) :
    ((3 : Int) ∣ l + (-(3 * r) - 1)) ↔ ∃ j : Int, l = 3 * j + 1 :=
  PartI.Ch04.theorem44CoeffResidueCondition_one_iff r l

theorem exercise4_theorem44CoeffResidueCondition_two_iff (r l : Int) :
    ((3 : Int) ∣ l + (3 * r - 2)) ↔ ∃ j : Int, l = 3 * j + 2 :=
  PartI.Ch04.theorem44CoeffResidueCondition_two_iff r l

theorem exercise4_theorem44CoeffExponentIndex_residue_zero_spec (r j : Int) :
    6 * ((PartI.Ch04.theorem44CoeffExponentIndex (3 * r) (3 * j) : Nat) : Int) =
      3 * r * (3 * r + 1) + 6 * j * (3 * j - 1) :=
  PartI.Ch04.theorem44CoeffExponentIndex_residue_zero_spec r j

theorem exercise4_theorem44CoeffExponentIndex_residue_one_spec (r j : Int) :
    6 * ((PartI.Ch04.theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1) : Nat) : Int) =
      3 * r * (3 * r + 1) + 6 * j * (3 * j + 1) :=
  PartI.Ch04.theorem44CoeffExponentIndex_residue_one_spec r j

theorem exercise4_theorem44CoeffExponentIndex_residue_two_spec (r j : Int) :
    6 * ((PartI.Ch04.theorem44CoeffExponentIndex (3 * r - 2) (3 * j + 2) : Nat) : Int) =
      (3 * r - 2) * (3 * r - 1) + 2 * (3 * j + 2) * (3 * j + 1) :=
  PartI.Ch04.theorem44CoeffExponentIndex_residue_two_spec r j

theorem exercise4_theorem44CoeffExponentIndex_residue_zero_eq (r j : Int) :
    ((PartI.Ch04.theorem44CoeffExponentIndex (3 * r) (3 * j) : Nat) : Int) =
      r * (3 * r + 1) / 2 + j * (3 * j - 1) :=
  PartI.Ch04.theorem44CoeffExponentIndex_residue_zero_eq r j

theorem exercise4_theorem44CoeffExponentIndex_residue_one_eq (r j : Int) :
    ((PartI.Ch04.theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1) : Nat) : Int) =
      r * (3 * r + 1) / 2 + j * (3 * j + 1) :=
  PartI.Ch04.theorem44CoeffExponentIndex_residue_one_eq r j

theorem exercise4_theorem44Coeff_qpow_residue_zero (q : ℂ) (r j : Int) :
    q ^ PartI.Ch04.theorem44CoeffExponentIndex (3 * r) (3 * j) =
      q ^ Int.toNat (r * (3 * r + 1) / 2) *
        q ^ Int.toNat (j * (3 * j - 1)) :=
  PartI.Ch04.theorem44Coeff_qpow_residue_zero q r j

theorem exercise4_theorem44Coeff_qpow_residue_one (q : ℂ) (r j : Int) :
    q ^ PartI.Ch04.theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1) =
      q ^ Int.toNat (r * (3 * r + 1) / 2) *
        q ^ Int.toNat (j * (3 * j + 1)) :=
  PartI.Ch04.theorem44Coeff_qpow_residue_one q r j

theorem exercise4_theorem44_sign_residue_zero (j : Int) :
    (-1 : ℂ) ^ (3 * j) = (-1 : ℂ) ^ j :=
  PartI.Ch04.theorem44_sign_residue_zero j

theorem exercise4_theorem44_sign_residue_one (j : Int) :
    (-1 : ℂ) ^ (3 * j + 1) = -((-1 : ℂ) ^ j) :=
  PartI.Ch04.theorem44_sign_residue_one j

theorem exercise4_theorem44_sign_residue_two (j : Int) :
    (-1 : ℂ) ^ (3 * j + 2) = (-1 : ℂ) ^ j :=
  PartI.Ch04.theorem44_sign_residue_two j

theorem exercise4_theorem44Coeff_signed_qpow_residue_zero (q : ℂ) (r j : Int) :
    (-1 : ℂ) ^ (3 * j) *
        q ^ PartI.Ch04.theorem44CoeffExponentIndex (3 * r) (3 * j) =
      q ^ Int.toNat (r * (3 * r + 1) / 2) *
        ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))) :=
  PartI.Ch04.theorem44Coeff_signed_qpow_residue_zero q r j

theorem exercise4_theorem44Coeff_signed_qpow_residue_one (q : ℂ) (r j : Int) :
    (-1 : ℂ) ^ (3 * j + 1) *
        q ^ PartI.Ch04.theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1) =
      -(q ^ Int.toNat (r * (3 * r + 1) / 2) *
          ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1)))) :=
  PartI.Ch04.theorem44Coeff_signed_qpow_residue_one q r j

theorem exercise4_theorem44Coeff_monomial_residue_zero (q z : ℂ) (r j : Int) :
    z ^ (3 * r) *
        ((-1 : ℂ) ^ (3 * j) *
          q ^ PartI.Ch04.theorem44CoeffExponentIndex (3 * r) (3 * j)) =
      (z ^ (3 * r) * q ^ Int.toNat (r * (3 * r + 1) / 2)) *
        ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))) :=
  PartI.Ch04.theorem44Coeff_monomial_residue_zero q z r j

theorem exercise4_theorem44Coeff_monomial_residue_one (q z : ℂ) (r j : Int) :
    z ^ (-(3 * r) - 1) *
        ((-1 : ℂ) ^ (3 * j + 1) *
          q ^ PartI.Ch04.theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1)) =
      -((z ^ (-(3 * r) - 1) * q ^ Int.toNat (r * (3 * r + 1) / 2)) *
          ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1)))) :=
  PartI.Ch04.theorem44Coeff_monomial_residue_one q z r j

theorem exercise4_theorem44Coeff_monomial_residue_zero_add_one (q z : ℂ) (r j : Int) :
    z ^ (3 * r) *
        ((-1 : ℂ) ^ (3 * j) *
          q ^ PartI.Ch04.theorem44CoeffExponentIndex (3 * r) (3 * j)) +
      z ^ (-(3 * r) - 1) *
        ((-1 : ℂ) ^ (3 * j + 1) *
          q ^ PartI.Ch04.theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1)) =
      q ^ Int.toNat (r * (3 * r + 1) / 2) *
        (z ^ (3 * r) * ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))) -
          z ^ (-(3 * r) - 1) *
            ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1)))) :=
  PartI.Ch04.theorem44Coeff_monomial_residue_zero_add_one q z r j

theorem exercise4_theorem44Coeff_monomial_residue_zero_add_one_eq_pairedTerm
    (q z : ℂ) (r j : Int) :
    z ^ (3 * r) *
        ((-1 : ℂ) ^ (3 * j) *
          q ^ PartI.Ch04.theorem44CoeffExponentIndex (3 * r) (3 * j)) +
      z ^ (-(3 * r) - 1) *
        ((-1 : ℂ) ^ (3 * j + 1) *
          q ^ PartI.Ch04.theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1)) =
      PartI.Ch04.theorem44CoeffPairedBranchTerm q z r j :=
  PartI.Ch04.theorem44Coeff_monomial_residue_zero_add_one_eq_pairedTerm q z r j

theorem exercise4_theorem44CoeffPairedBranchOuter_eq (q : ℂ) (r : Int) :
    PartI.Ch04.theorem44CoeffPairedBranchOuter q r =
      q ^ Int.toNat (r * (3 * r + 1) / 2) :=
  PartI.Ch04.theorem44CoeffPairedBranchOuter_eq q r

theorem exercise4_theorem44CoeffPairedBranchInner_eq (q z : ℂ) (r j : Int) :
    PartI.Ch04.theorem44CoeffPairedBranchInner q z r j =
      z ^ (3 * r) * ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))) -
        z ^ (-(3 * r) - 1) *
          ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1))) :=
  PartI.Ch04.theorem44CoeffPairedBranchInner_eq q z r j

theorem exercise4_theorem44CoeffPairedBranchTerm_eq (q z : ℂ) (r j : Int) :
    PartI.Ch04.theorem44CoeffPairedBranchTerm q z r j =
      PartI.Ch04.theorem44CoeffPairedBranchOuter q r *
        PartI.Ch04.theorem44CoeffPairedBranchInner q z r j :=
  PartI.Ch04.theorem44CoeffPairedBranchTerm_eq q z r j

theorem exercise4_theorem44CoeffPairedBranchTerm_eq_explicit (q z : ℂ) (r j : Int) :
    PartI.Ch04.theorem44CoeffPairedBranchTerm q z r j =
      q ^ Int.toNat (r * (3 * r + 1) / 2) *
        (z ^ (3 * r) * ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))) -
          z ^ (-(3 * r) - 1) *
            ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1)))) :=
  PartI.Ch04.theorem44CoeffPairedBranchTerm_eq_explicit q z r j

theorem exercise4_theorem44CoeffPairedBranchTermPartial_eq_outer_mul_innerPartial
    (q z : ℂ) (r : Int) (N : Nat) :
    PartI.Ch04.theorem44CoeffPairedBranchTermPartial q z r N =
      PartI.Ch04.theorem44CoeffPairedBranchOuter q r *
        PartI.Ch04.theorem44CoeffPairedBranchInnerPartial q z r N :=
  PartI.Ch04.theorem44CoeffPairedBranchTermPartial_eq_outer_mul_innerPartial q z r N

theorem exercise4_theorem44CoeffPairedBranchInnerPartial_eq_left_sub_right
    (q z : ℂ) (r : Int) (N : Nat) :
    PartI.Ch04.theorem44CoeffPairedBranchInnerPartial q z r N =
      PartI.Ch04.theorem44CoeffPairedBranchInnerLeftPartial q z r N -
        PartI.Ch04.theorem44CoeffPairedBranchInnerRightPartial q z r N :=
  PartI.Ch04.theorem44CoeffPairedBranchInnerPartial_eq_left_sub_right q z r N

theorem exercise4_theorem44CoeffPairedBranchTermPartial_eq_outer_mul_left_sub_right
    (q z : ℂ) (r : Int) (N : Nat) :
    PartI.Ch04.theorem44CoeffPairedBranchTermPartial q z r N =
      PartI.Ch04.theorem44CoeffPairedBranchOuter q r *
        (PartI.Ch04.theorem44CoeffPairedBranchInnerLeftPartial q z r N -
          PartI.Ch04.theorem44CoeffPairedBranchInnerRightPartial q z r N) :=
  PartI.Ch04.theorem44CoeffPairedBranchTermPartial_eq_outer_mul_left_sub_right q z r N

theorem exercise4_theorem44CoeffPairedBranchInnerLeftPartial_eq_zpow_mul_theta
    (q z : ℂ) (r : Int) (N : Nat) :
    PartI.Ch04.theorem44CoeffPairedBranchInnerLeftPartial q z r N =
      z ^ (3 * r) * PartI.Ch04.theorem44CoeffPairedBranchLeftThetaPartial q N :=
  PartI.Ch04.theorem44CoeffPairedBranchInnerLeftPartial_eq_zpow_mul_theta q z r N

theorem exercise4_theorem44CoeffPairedBranchInnerRightPartial_eq_zpow_mul_theta
    (q z : ℂ) (r : Int) (N : Nat) :
    PartI.Ch04.theorem44CoeffPairedBranchInnerRightPartial q z r N =
      z ^ (-(3 * r) - 1) * PartI.Ch04.theorem44CoeffPairedBranchRightThetaPartial q N :=
  PartI.Ch04.theorem44CoeffPairedBranchInnerRightPartial_eq_zpow_mul_theta q z r N

theorem exercise4_theorem44CoeffPairedBranchInnerPartial_eq_zpow_mul_theta_sub_zpow_mul_theta
    (q z : ℂ) (r : Int) (N : Nat) :
    PartI.Ch04.theorem44CoeffPairedBranchInnerPartial q z r N =
      z ^ (3 * r) * PartI.Ch04.theorem44CoeffPairedBranchLeftThetaPartial q N -
        z ^ (-(3 * r) - 1) *
          PartI.Ch04.theorem44CoeffPairedBranchRightThetaPartial q N :=
  PartI.Ch04.theorem44CoeffPairedBranchInnerPartial_eq_zpow_mul_theta_sub_zpow_mul_theta
    q z r N

theorem exercise4_theorem44CoeffPairedBranchTermPartial_eq_outer_mul_zpow_theta_sub_zpow_theta
    (q z : ℂ) (r : Int) (N : Nat) :
    PartI.Ch04.theorem44CoeffPairedBranchTermPartial q z r N =
      PartI.Ch04.theorem44CoeffPairedBranchOuter q r *
        (z ^ (3 * r) * PartI.Ch04.theorem44CoeffPairedBranchLeftThetaPartial q N -
          z ^ (-(3 * r) - 1) *
            PartI.Ch04.theorem44CoeffPairedBranchRightThetaPartial q N) :=
  PartI.Ch04.theorem44CoeffPairedBranchTermPartial_eq_outer_mul_zpow_theta_sub_zpow_theta
    q z r N

theorem exercise4_theorem44CoeffPairedBranchRightThetaPartial_eq_leftThetaPartial
    (q : ℂ) (N : Nat) :
    PartI.Ch04.theorem44CoeffPairedBranchRightThetaPartial q N =
      PartI.Ch04.theorem44CoeffPairedBranchLeftThetaPartial q N :=
  PartI.Ch04.theorem44CoeffPairedBranchRightThetaPartial_eq_leftThetaPartial q N

theorem exercise4_theorem44CoeffPairedBranchInnerPartial_eq_zpow_sub_zpow_mul_theta
    (q z : ℂ) (r : Int) (N : Nat) :
    PartI.Ch04.theorem44CoeffPairedBranchInnerPartial q z r N =
      (z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
        PartI.Ch04.theorem44CoeffPairedBranchLeftThetaPartial q N :=
  PartI.Ch04.theorem44CoeffPairedBranchInnerPartial_eq_zpow_sub_zpow_mul_theta q z r N

theorem exercise4_theorem44CoeffPairedBranchTermPartial_eq_outer_mul_zpow_sub_zpow_mul_theta
    (q z : ℂ) (r : Int) (N : Nat) :
    PartI.Ch04.theorem44CoeffPairedBranchTermPartial q z r N =
      PartI.Ch04.theorem44CoeffPairedBranchOuter q r *
        ((z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
          PartI.Ch04.theorem44CoeffPairedBranchLeftThetaPartial q N) :=
  PartI.Ch04.theorem44CoeffPairedBranchTermPartial_eq_outer_mul_zpow_sub_zpow_mul_theta
    q z r N

theorem exercise4_theorem44CoeffMonomialPairPartial_eq_pairedBranchTermPartial
    (q z : ℂ) (r : Int) (N : Nat) :
    PartI.Ch04.theorem44CoeffMonomialPairPartial q z r N =
      PartI.Ch04.theorem44CoeffPairedBranchTermPartial q z r N :=
  PartI.Ch04.theorem44CoeffMonomialPairPartial_eq_pairedBranchTermPartial q z r N

theorem exercise4_theorem44CoeffMonomialPairPartial_eq_outer_mul_innerPartial
    (q z : ℂ) (r : Int) (N : Nat) :
    PartI.Ch04.theorem44CoeffMonomialPairPartial q z r N =
      PartI.Ch04.theorem44CoeffPairedBranchOuter q r *
        PartI.Ch04.theorem44CoeffPairedBranchInnerPartial q z r N :=
  PartI.Ch04.theorem44CoeffMonomialPairPartial_eq_outer_mul_innerPartial q z r N

theorem exercise4_theorem44CoeffMonomialPairPartial_eq_outer_mul_zpow_sub_zpow_mul_theta
    (q z : ℂ) (r : Int) (N : Nat) :
    PartI.Ch04.theorem44CoeffMonomialPairPartial q z r N =
      PartI.Ch04.theorem44CoeffPairedBranchOuter q r *
        ((z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
          PartI.Ch04.theorem44CoeffPairedBranchLeftThetaPartial q N) :=
  PartI.Ch04.theorem44CoeffMonomialPairPartial_eq_outer_mul_zpow_sub_zpow_mul_theta
    q z r N

theorem exercise4_theorem44CoeffPairedBranchLeftThetaPartial_eq_sum_thetaTerm
    (q : ℂ) (N : Nat) :
    PartI.Ch04.theorem44CoeffPairedBranchLeftThetaPartial q N =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        PartI.Ch04.theorem44CoeffPairedBranchThetaTerm q j :=
  PartI.Ch04.theorem44CoeffPairedBranchLeftThetaPartial_eq_sum_thetaTerm q N

theorem exercise4_theorem44CoeffPairedBranchThetaTerm_eq_jacobiSeriesTerm
    (q : ℂ) (hq : q ≠ 0) (j : Int) :
    PartI.Ch04.theorem44CoeffPairedBranchThetaTerm q j =
      (-q⁻¹) ^ j * (q ^ 3) ^ (j ^ 2) :=
  PartI.Ch04.theorem44CoeffPairedBranchThetaTerm_eq_jacobiSeriesTerm q hq j

theorem exercise4_theorem44CoeffPairedBranchThetaSeries_eq_jacobiInfiniteSeries
    (q : ℂ) (hq : q ≠ 0) :
    PartI.Ch04.theorem44CoeffPairedBranchThetaSeries q =
      PartI.Ch02.jacobiInfiniteSeries (q ^ 3) (-q⁻¹) :=
  PartI.Ch04.theorem44CoeffPairedBranchThetaSeries_eq_jacobiInfiniteSeries q hq

theorem exercise4_theorem44CoeffPairedBranchLeftThetaPartial_eq_jacobiSeriesSymmetricPartial
    (q : ℂ) (hq : q ≠ 0) (N : Nat) :
    PartI.Ch04.theorem44CoeffPairedBranchLeftThetaPartial q N =
      PartI.Ch02.jacobiSeriesSymmetricPartial (q ^ 3) (-q⁻¹) N :=
  PartI.Ch04.theorem44CoeffPairedBranchLeftThetaPartial_eq_jacobiSeriesSymmetricPartial
    q hq N

theorem exercise4_summable_theorem44CoeffPairedBranchThetaTerm
    (q : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) :
    Summable fun j : ℤ => PartI.Ch04.theorem44CoeffPairedBranchThetaTerm q j :=
  PartI.Ch04.summable_theorem44CoeffPairedBranchThetaTerm q hqnorm hq

theorem exercise4_hasSum_theorem44CoeffPairedBranchThetaTerm
    (q : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) :
    HasSum (fun j : ℤ => PartI.Ch04.theorem44CoeffPairedBranchThetaTerm q j)
      (PartI.Ch04.theorem44CoeffPairedBranchThetaSeries q) :=
  PartI.Ch04.hasSum_theorem44CoeffPairedBranchThetaTerm q hqnorm hq

theorem exercise4_tendsto_theorem44CoeffPairedBranchLeftThetaPartial
    (q : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => PartI.Ch04.theorem44CoeffPairedBranchLeftThetaPartial q N)
      Filter.atTop (nhds (PartI.Ch04.theorem44CoeffPairedBranchThetaSeries q)) :=
  PartI.Ch04.tendsto_theorem44CoeffPairedBranchLeftThetaPartial q hqnorm hq

theorem exercise4_tendsto_theorem44CoeffPairedBranchInnerPartial
    (q z : ℂ) (r : Int) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => PartI.Ch04.theorem44CoeffPairedBranchInnerPartial q z r N)
      Filter.atTop
      (nhds ((z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
        PartI.Ch04.theorem44CoeffPairedBranchThetaSeries q)) :=
  PartI.Ch04.tendsto_theorem44CoeffPairedBranchInnerPartial q z r hqnorm hq

theorem exercise4_tendsto_theorem44CoeffPairedBranchTermPartial
    (q z : ℂ) (r : Int) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => PartI.Ch04.theorem44CoeffPairedBranchTermPartial q z r N)
      Filter.atTop
      (nhds (PartI.Ch04.theorem44CoeffPairedBranchOuter q r *
        ((z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
          PartI.Ch04.theorem44CoeffPairedBranchThetaSeries q))) :=
  PartI.Ch04.tendsto_theorem44CoeffPairedBranchTermPartial q z r hqnorm hq

theorem exercise4_tendsto_theorem44CoeffMonomialPairPartial
    (q z : ℂ) (r : Int) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => PartI.Ch04.theorem44CoeffMonomialPairPartial q z r N)
      Filter.atTop
      (nhds (PartI.Ch04.theorem44CoeffPairedBranchOuter q r *
        ((z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
          PartI.Ch04.theorem44CoeffPairedBranchThetaSeries q))) :=
  PartI.Ch04.tendsto_theorem44CoeffMonomialPairPartial q z r hqnorm hq

theorem exercise4_qPoch_one_succ_eq_zero (q : R) (n : Nat) :
    qPoch (1 : R) q (n + 1) = 0 :=
  PartI.Ch04.qPoch_one_succ_eq_zero q n

theorem exercise4_theorem44ResidueTwo_qPoch_one_qsix_zero (q : ℂ) (n : Nat) :
    qPoch (1 : ℂ) (q ^ 6) (n + 1) = 0 :=
  PartI.Ch04.theorem44ResidueTwo_qPoch_one_qsix_zero q n

theorem exercise4_theorem44ResidueTwo_qPoch_zero_factor (q A B : ℂ) (n : Nat) :
    A * qPoch (1 : ℂ) (q ^ 6) (n + 1) * B = 0 :=
  PartI.Ch04.theorem44ResidueTwo_qPoch_zero_factor q A B n

theorem exercise4_theorem44ProductPartial_substitution_eq_quintuple
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch04.theorem44ProductPartial (q ^ 2) (z / q) N =
      PartI.Ch04.quintupleProductLHSTrunc q z N :=
  PartI.Ch04.theorem44ProductPartial_substitution_eq_quintuple q z hq hz N

theorem exercise4_quintupleProductLHSTrunc_eq_qPoch
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch04.quintupleProductLHSTrunc q z N =
      qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
        qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
          qPoch (q ^ 4 / z ^ 2) (q ^ 4) N :=
  PartI.Ch04.quintupleProductLHSTrunc_eq_qPoch q z hq hz N

theorem exercise4_tendsto_theorem44ProductPartial (q z : ℂ) (hq : ‖q‖ < 1) :
    Filter.Tendsto (fun N : ℕ => PartI.Ch04.theorem44ProductPartial q z N) Filter.atTop
      (nhds (PartI.Ch04.theorem44ProductLHS q z)) :=
  PartI.Ch04.tendsto_theorem44ProductPartial q z hq

theorem exercise4_theorem44SeriesTerm_substitution_eq_substituted
    (q z : ℂ) (n : ℤ) :
    PartI.Ch04.theorem44SeriesTerm (q ^ 2) (z / q) n =
      PartI.Ch04.theorem44SubstitutedSeriesTerm q z n :=
  PartI.Ch04.theorem44SeriesTerm_substitution_eq_substituted q z n

theorem exercise4_theorem44SeriesRHS_substitution_eq_substituted (q z : ℂ) :
    PartI.Ch04.theorem44SeriesRHS (q ^ 2) (z / q) =
      PartI.Ch04.theorem44SubstitutedSeriesRHS q z :=
  PartI.Ch04.theorem44SeriesRHS_substitution_eq_substituted q z

theorem exercise4_theorem44SubstitutedSeriesTerm_eq_quintupleProductSeriesTerm
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (n : ℤ) :
    PartI.Ch04.theorem44SubstitutedSeriesTerm q z n =
      PartI.Ch04.quintupleProductSeriesTerm q z n :=
  PartI.Ch04.theorem44SubstitutedSeriesTerm_eq_quintupleProductSeriesTerm q z hq hz n

theorem exercise4_theorem44SubstitutedSeriesRHS_eq_quintupleProductRHS
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) :
    PartI.Ch04.theorem44SubstitutedSeriesRHS q z =
      PartI.Ch04.quintupleProductRHS q z :=
  PartI.Ch04.theorem44SubstitutedSeriesRHS_eq_quintupleProductRHS q z hq hz

theorem exercise4_summable_theorem44SubstitutedSeriesTerm
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    Summable fun n : ℤ => PartI.Ch04.theorem44SubstitutedSeriesTerm q z n :=
  PartI.Ch04.summable_theorem44SubstitutedSeriesTerm q z hqnorm hq hz

theorem exercise4_hasSum_theorem44SubstitutedSeriesTerm
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    HasSum (fun n : ℤ => PartI.Ch04.theorem44SubstitutedSeriesTerm q z n)
      (PartI.Ch04.theorem44SubstitutedSeriesRHS q z) :=
  PartI.Ch04.hasSum_theorem44SubstitutedSeriesTerm q z hqnorm hq hz

theorem exercise4_summable_theorem44SeriesTerm_substitution
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    Summable fun n : ℤ => PartI.Ch04.theorem44SeriesTerm (q ^ 2) (z / q) n :=
  PartI.Ch04.summable_theorem44SeriesTerm_substitution q z hqnorm hq hz

theorem exercise4_hasSum_theorem44SeriesTerm_substitution
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    HasSum (fun n : ℤ => PartI.Ch04.theorem44SeriesTerm (q ^ 2) (z / q) n)
      (PartI.Ch04.theorem44SeriesRHS (q ^ 2) (z / q)) :=
  PartI.Ch04.hasSum_theorem44SeriesTerm_substitution q z hqnorm hq hz

theorem exercise4_theorem44_substitution_identity_iff_quintupleProduct
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) :
    PartI.Ch04.theorem44ProductLHS (q ^ 2) (z / q) =
        PartI.Ch04.theorem44SeriesRHS (q ^ 2) (z / q) ↔
      PartI.Ch04.quintupleProductLHS q z = PartI.Ch04.quintupleProductRHS q z :=
  PartI.Ch04.theorem44_substitution_identity_iff_quintupleProduct q z hq hz

theorem exercise4_theorem44_substitution_identity_of_quintupleProduct
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0)
    (h : PartI.Ch04.quintupleProductLHS q z = PartI.Ch04.quintupleProductRHS q z) :
    PartI.Ch04.theorem44ProductLHS (q ^ 2) (z / q) =
      PartI.Ch04.theorem44SeriesRHS (q ^ 2) (z / q) :=
  PartI.Ch04.theorem44_substitution_identity_of_quintupleProduct q z hq hz h

theorem exercise4_quintupleProduct_of_theorem44_substitution_identity
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0)
    (h : PartI.Ch04.theorem44ProductLHS (q ^ 2) (z / q) =
      PartI.Ch04.theorem44SeriesRHS (q ^ 2) (z / q)) :
    PartI.Ch04.quintupleProductLHS q z = PartI.Ch04.quintupleProductRHS q z :=
  PartI.Ch04.quintupleProduct_of_theorem44_substitution_identity q z hq hz h

theorem exercise4_summable_quintupleProductSeriesTerm (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℤ => PartI.Ch04.quintupleProductSeriesTerm q z n :=
  PartI.Ch04.summable_quintupleProductSeriesTerm q z hq

theorem exercise4_hasSum_quintupleProductSeriesTerm (q z : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℤ => PartI.Ch04.quintupleProductSeriesTerm q z n)
      (PartI.Ch04.quintupleProductRHS q z) :=
  PartI.Ch04.hasSum_quintupleProductSeriesTerm q z hq

theorem exercise4_quintupleProductRHS_eq_jacobiSeries_sub
    (q z : ℂ) (hq : ‖q‖ < 1) :
    PartI.Ch04.quintupleProductRHS q z =
      PartI.Ch02.jacobiInfiniteSeries (q ^ 3) (z ^ 3 / q ^ 2) -
        (q / z) * PartI.Ch02.jacobiInfiniteSeries (q ^ 3) (q ^ 4 / z ^ 3) :=
  PartI.Ch04.quintupleProductRHS_eq_jacobiSeries_sub q z hq

theorem exercise4_quintupleProductRHS_eq_jacobiProduct_sub
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    PartI.Ch04.quintupleProductRHS q z =
      PartI.Ch02.jacobiInfiniteProduct (q ^ 3) (z ^ 3 / q ^ 2) -
        (q / z) * PartI.Ch02.jacobiInfiniteProduct (q ^ 3) (q ^ 4 / z ^ 3) :=
  PartI.Ch04.quintupleProductRHS_eq_jacobiProduct_sub q z hqnorm hq hz

theorem exercise4_quintupleProductRHS_eq_explicitProduct_sub
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    PartI.Ch04.quintupleProductRHS q z =
      PartI.Ch04.quintupleProductExplicitRHS q z :=
  PartI.Ch04.quintupleProductRHS_eq_explicitProduct_sub q z hqnorm hq hz

theorem exercise4_quintupleProduct_identity_iff_explicitProduct
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    PartI.Ch04.quintupleProductLHS q z = PartI.Ch04.quintupleProductRHS q z ↔
      PartI.Ch04.quintupleProductLHS q z =
        PartI.Ch04.quintupleProductExplicitRHS q z :=
  PartI.Ch04.quintupleProduct_identity_iff_explicitProduct q z hqnorm hq hz

theorem exercise4_quintupleProduct_identity_of_explicitProduct
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h : PartI.Ch04.quintupleProductLHS q z =
      PartI.Ch04.quintupleProductExplicitRHS q z) :
    PartI.Ch04.quintupleProductLHS q z = PartI.Ch04.quintupleProductRHS q z :=
  PartI.Ch04.quintupleProduct_identity_of_explicitProduct q z hqnorm hq hz h

theorem exercise4_quintupleProduct_explicitProduct_of_identity
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h : PartI.Ch04.quintupleProductLHS q z =
      PartI.Ch04.quintupleProductRHS q z) :
    PartI.Ch04.quintupleProductLHS q z =
      PartI.Ch04.quintupleProductExplicitRHS q z :=
  PartI.Ch04.quintupleProduct_explicitProduct_of_identity q z hqnorm hq hz h

/-- **Chan's Theorem 4.4 / equation (2.12)** in exercise form: the
quintuple product identity `LHS = RHS`, for any `q` with `‖q‖ < 1`
and `z ≠ 0`. -/
theorem exercise4_quintupleProduct_identity (q z : ℂ)
    (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    PartI.Ch04.quintupleProductLHS q z = PartI.Ch04.quintupleProductRHS q z :=
  PartI.Ch04.quintupleProduct_identity q z hqnorm hq hz

/-- Bridge through the explicit JTP product form: the bilateral series
product equals `(q⁴; q⁴)_∞` times `quintupleProductRHS`. -/
theorem exercise4_jacobiSeries_mul_eq_qPoch_mul_quintupleRHS
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    PartI.Ch02.jacobiInfiniteSeries q (-z) *
        PartI.Ch02.jacobiInfiniteSeries (q ^ 2) (-(z ^ 2 / q ^ 2)) =
      (∏' n : ℕ, (1 - q ^ (4 * n + 4))) * PartI.Ch04.quintupleProductRHS q z :=
  PartI.Ch04.jacobiSeries_mul_eq_qPoch_mul_quintupleRHS q z hqnorm hq hz

theorem exercise4_jacobiProductPartial_quintuple_left_substitution
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch02.jacobiProductPartial (q ^ 3) (z ^ 3 / q ^ 2) N =
      PartI.Ch04.quintupleJacobiLeftPartial q z N :=
  PartI.Ch04.jacobiProductPartial_quintuple_left_substitution q z hq hz N

theorem exercise4_jacobiProductPartial_quintuple_right_substitution
    (q z : ℂ) (N : Nat) :
    PartI.Ch02.jacobiProductPartial (q ^ 3) (q ^ 4 / z ^ 3) N =
      PartI.Ch04.quintupleJacobiRightPartial q z N :=
  PartI.Ch04.jacobiProductPartial_quintuple_right_substitution q z N

theorem exercise4_quintupleProductExplicitRHSPartial_eq_jacobiProductPartial_sub
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch04.quintupleProductExplicitRHSPartial q z N =
      PartI.Ch02.jacobiProductPartial (q ^ 3) (z ^ 3 / q ^ 2) N -
        (q / z) * PartI.Ch02.jacobiProductPartial (q ^ 3) (q ^ 4 / z ^ 3) N :=
  PartI.Ch04.quintupleProductExplicitRHSPartial_eq_jacobiProductPartial_sub
    q z hq hz N

theorem exercise4_quintupleProduct_trunc_sub_explicitPartial_eq_jacobiProductPartial_sub
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch04.quintupleProductLHSTrunc q z N -
        PartI.Ch04.quintupleProductExplicitRHSPartial q z N =
      PartI.Ch04.quintupleProductLHSTrunc q z N -
        (PartI.Ch02.jacobiProductPartial (q ^ 3) (z ^ 3 / q ^ 2) N -
          (q / z) * PartI.Ch02.jacobiProductPartial (q ^ 3) (q ^ 4 / z ^ 3) N) :=
  PartI.Ch04.quintupleProduct_trunc_sub_explicitPartial_eq_jacobiProductPartial_sub
    q z hq hz N

theorem exercise4_quintupleProductExplicitRHSPartial_eq_qPoch_mul_finiteJTPRHS_sub
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch04.quintupleProductExplicitRHSPartial q z N =
      qPoch (q ^ 6) (q ^ 6) N *
          PartI.Ch03.finiteJTPRHS (q ^ 6) (-(z ^ 3 * q)) N -
        (q / z) * (qPoch (q ^ 6) (q ^ 6) N *
          PartI.Ch03.finiteJTPRHS (q ^ 6) (-(q ^ 7 / z ^ 3)) N) :=
  PartI.Ch04.quintupleProductExplicitRHSPartial_eq_qPoch_mul_finiteJTPRHS_sub
    q z hq hz N

theorem exercise4_quintupleFiniteJTPLeftMonomial_eq_zpow_qpow
    (q z : ℂ) (hq : q ≠ 0) (l : Int) :
    (z ^ 3 / q ^ 2) ^ l * (q ^ 3) ^ (l ^ 2) =
      z ^ (3 * l) * q ^ (3 * l ^ 2 - 2 * l) :=
  PartI.Ch04.quintupleFiniteJTPLeftMonomial_eq_zpow_qpow q z hq l

theorem exercise4_quintupleFiniteJTPRightScaledMonomial_eq_zpow_qpow
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (l : Int) :
    (q / z) * ((q ^ 4 / z ^ 3) ^ l * (q ^ 3) ^ (l ^ 2)) =
      z ^ (-(3 * l) - 1) * q ^ (3 * l ^ 2 + 4 * l + 1) :=
  PartI.Ch04.quintupleFiniteJTPRightScaledMonomial_eq_zpow_qpow q z hq hz l

theorem exercise4_quintupleProductSeriesTerm_eq_combinedMonomialBracket
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (l : Int) :
    PartI.Ch04.quintupleProductSeriesTerm q z l =
      z ^ (3 * l) * q ^ (3 * l ^ 2 - 2 * l) -
        z ^ (-(3 * l) - 1) * q ^ (3 * l ^ 2 + 4 * l + 1) :=
  PartI.Ch04.quintupleProductSeriesTerm_eq_combinedMonomialBracket q z hq hz l

theorem exercise4_quintupleFiniteJTPCombinedMonomialSummand_eq_gaussian_mul_seriesTerm
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N k : Nat) :
    PartI.Ch04.quintupleFiniteJTPCombinedMonomialSummand q z N k =
      gaussianBinom (q ^ 6) (2 * N) k *
        PartI.Ch04.quintupleProductSeriesTerm q z ((k : Int) - (N : Int)) :=
  PartI.Ch04.quintupleFiniteJTPCombinedMonomialSummand_eq_gaussian_mul_seriesTerm
    q z hq hz N k

theorem exercise4_tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSummand_center_add
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) (r : Nat) :
    Filter.Tendsto
      (fun N : ℕ =>
        qPoch (q ^ 6) (q ^ 6) N *
          PartI.Ch04.quintupleFiniteJTPCombinedMonomialSummand q z N (N + r))
      Filter.atTop (nhds (PartI.Ch04.quintupleProductSeriesTerm q z (r : Int))) :=
  PartI.Ch04.tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSummand_center_add
    q z hqnorm hq hz r

theorem exercise4_tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSummand_center_sub
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) (r : Nat) :
    Filter.Tendsto
      (fun N : ℕ =>
        qPoch (q ^ 6) (q ^ 6) N *
          PartI.Ch04.quintupleFiniteJTPCombinedMonomialSummand q z N (N - r))
      Filter.atTop (nhds (PartI.Ch04.quintupleProductSeriesTerm q z (-(r : Int)))) :=
  PartI.Ch04.tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSummand_center_sub
    q z hqnorm hq hz r

theorem exercise4_tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialPairTerm
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) (r : Nat) :
    Filter.Tendsto
      (fun N : ℕ =>
        qPoch (q ^ 6) (q ^ 6) N *
          PartI.Ch04.quintupleFiniteJTPCombinedMonomialPairTerm q z N r)
      Filter.atTop
        (nhds (PartI.Ch04.quintupleProductSeriesSymmetricPairTerm q z r)) :=
  PartI.Ch04.tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialPairTerm
    q z hqnorm hq hz r

theorem exercise4_tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialPairPartial
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) (M : Nat) :
    Filter.Tendsto
      (fun N : ℕ =>
        qPoch (q ^ 6) (q ^ 6) N *
          PartI.Ch04.quintupleFiniteJTPCombinedMonomialPairPartial q z N M)
      Filter.atTop
        (nhds (PartI.Ch04.quintupleProductSeriesSymmetricPairPartial q z M)) :=
  PartI.Ch04.tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialPairPartial
    q z hqnorm hq hz M

theorem exercise4_tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSymmetricPartial
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) (M : Nat) :
    Filter.Tendsto
      (fun N : ℕ =>
        qPoch (q ^ 6) (q ^ 6) N *
          PartI.Ch04.quintupleFiniteJTPCombinedMonomialSymmetricPartial q z N M)
      Filter.atTop
        (nhds (PartI.Ch04.quintupleProductSeriesSymmetricPartial q z M)) :=
  PartI.Ch04.tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSymmetricPartial
    q z hqnorm hq hz M

theorem exercise4_finiteJTPRHS_quintuple_left_eq_weightedSum
    (q z : ℂ) (hq : q ≠ 0) (N : Nat) :
    PartI.Ch03.finiteJTPRHS (q ^ 6) (-(z ^ 3 * q)) N =
      PartI.Ch04.quintupleFiniteJTPLeftWeightedSum q z N :=
  PartI.Ch04.finiteJTPRHS_quintuple_left_eq_weightedSum q z hq N

theorem exercise4_finiteJTPRHS_quintuple_right_eq_weightedSum
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch03.finiteJTPRHS (q ^ 6) (-(q ^ 7 / z ^ 3)) N =
      PartI.Ch04.quintupleFiniteJTPRightWeightedSum q z N :=
  PartI.Ch04.finiteJTPRHS_quintuple_right_eq_weightedSum q z hq hz N

theorem exercise4_quintupleProductExplicitRHSPartial_eq_qPoch_mul_weightedSums_sub
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch04.quintupleProductExplicitRHSPartial q z N =
      qPoch (q ^ 6) (q ^ 6) N *
          PartI.Ch04.quintupleFiniteJTPLeftWeightedSum q z N -
        (q / z) * (qPoch (q ^ 6) (q ^ 6) N *
          PartI.Ch04.quintupleFiniteJTPRightWeightedSum q z N) :=
  PartI.Ch04.quintupleProductExplicitRHSPartial_eq_qPoch_mul_weightedSums_sub
    q z hq hz N

theorem exercise4_quintupleFiniteJTPWeightedSum_sub_eq_combined
    (q z : ℂ) (N : Nat) :
    PartI.Ch04.quintupleFiniteJTPLeftWeightedSum q z N -
        (q / z) * PartI.Ch04.quintupleFiniteJTPRightWeightedSum q z N =
      PartI.Ch04.quintupleFiniteJTPCombinedWeightedSum q z N :=
  PartI.Ch04.quintupleFiniteJTPWeightedSum_sub_eq_combined q z N

theorem exercise4_quintupleFiniteJTPCombinedWeightedSummand_eq_monomialSummand
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N k : Nat) :
    PartI.Ch04.quintupleFiniteJTPCombinedWeightedSummand q z N k =
      PartI.Ch04.quintupleFiniteJTPCombinedMonomialSummand q z N k :=
  PartI.Ch04.quintupleFiniteJTPCombinedWeightedSummand_eq_monomialSummand q z hq hz N k

theorem exercise4_quintupleFiniteJTPCombinedWeightedSum_eq_monomialSum
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch04.quintupleFiniteJTPCombinedWeightedSum q z N =
      PartI.Ch04.quintupleFiniteJTPCombinedMonomialSum q z N :=
  PartI.Ch04.quintupleFiniteJTPCombinedWeightedSum_eq_monomialSum q z hq hz N

theorem exercise4_quintupleProductExplicitRHSPartial_eq_qPoch_mul_combinedWeightedSum
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch04.quintupleProductExplicitRHSPartial q z N =
      qPoch (q ^ 6) (q ^ 6) N *
        PartI.Ch04.quintupleFiniteJTPCombinedWeightedSum q z N :=
  PartI.Ch04.quintupleProductExplicitRHSPartial_eq_qPoch_mul_combinedWeightedSum
    q z hq hz N

theorem exercise4_quintupleProductExplicitRHSPartial_eq_qPoch_mul_combinedMonomialSum
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch04.quintupleProductExplicitRHSPartial q z N =
      qPoch (q ^ 6) (q ^ 6) N *
        PartI.Ch04.quintupleFiniteJTPCombinedMonomialSum q z N :=
  PartI.Ch04.quintupleProductExplicitRHSPartial_eq_qPoch_mul_combinedMonomialSum
    q z hq hz N

theorem exercise4_quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_finiteJTPRHS
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch04.quintupleProductLHSTrunc q z N -
        PartI.Ch04.quintupleProductExplicitRHSPartial q z N =
      (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
          qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
            qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
        (qPoch (q ^ 6) (q ^ 6) N *
            PartI.Ch03.finiteJTPRHS (q ^ 6) (-(z ^ 3 * q)) N -
          (q / z) * (qPoch (q ^ 6) (q ^ 6) N *
            PartI.Ch03.finiteJTPRHS (q ^ 6) (-(q ^ 7 / z ^ 3)) N)) :=
  PartI.Ch04.quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_finiteJTPRHS
    q z hq hz N

theorem exercise4_quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_weightedSums
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch04.quintupleProductLHSTrunc q z N -
        PartI.Ch04.quintupleProductExplicitRHSPartial q z N =
      (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
          qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
            qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
        (qPoch (q ^ 6) (q ^ 6) N *
            PartI.Ch04.quintupleFiniteJTPLeftWeightedSum q z N -
          (q / z) * (qPoch (q ^ 6) (q ^ 6) N *
            PartI.Ch04.quintupleFiniteJTPRightWeightedSum q z N)) :=
  PartI.Ch04.quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_weightedSums
    q z hq hz N

theorem exercise4_quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_combinedWeightedSum
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch04.quintupleProductLHSTrunc q z N -
        PartI.Ch04.quintupleProductExplicitRHSPartial q z N =
      (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
          qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
            qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
        qPoch (q ^ 6) (q ^ 6) N *
          PartI.Ch04.quintupleFiniteJTPCombinedWeightedSum q z N :=
  PartI.Ch04.quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_combinedWeightedSum
    q z hq hz N

theorem exercise4_quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_combinedMonomialSum
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    PartI.Ch04.quintupleProductLHSTrunc q z N -
        PartI.Ch04.quintupleProductExplicitRHSPartial q z N =
      (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
          qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
            qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
        qPoch (q ^ 6) (q ^ 6) N *
          PartI.Ch04.quintupleFiniteJTPCombinedMonomialSum q z N :=
  PartI.Ch04.quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_combinedMonomialSum
    q z hq hz N

theorem exercise4_tendsto_quintupleProductExplicitRHSPartial
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => PartI.Ch04.quintupleProductExplicitRHSPartial q z N)
      Filter.atTop (nhds (PartI.Ch04.quintupleProductExplicitRHS q z)) :=
  PartI.Ch04.tendsto_quintupleProductExplicitRHSPartial q z hqnorm hq hz

theorem exercise4_quintupleProduct_explicitProduct_of_tendsto_trunc_sub_explicit
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h :
      Filter.Tendsto
        (fun N : ℕ =>
          PartI.Ch04.quintupleProductLHSTrunc q z N -
            PartI.Ch04.quintupleProductExplicitRHSPartial q z N)
        Filter.atTop (nhds 0)) :
    PartI.Ch04.quintupleProductLHS q z =
      PartI.Ch04.quintupleProductExplicitRHS q z :=
  PartI.Ch04.quintupleProduct_explicitProduct_of_tendsto_trunc_sub_explicit
    q z hqnorm hq hz h

theorem exercise4_quintupleProduct_explicitProduct_of_tendsto_trunc_sub_jacobiPartials
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h :
      Filter.Tendsto
        (fun N : ℕ =>
          PartI.Ch04.quintupleProductLHSTrunc q z N -
            (PartI.Ch02.jacobiProductPartial (q ^ 3) (z ^ 3 / q ^ 2) N -
              (q / z) *
                PartI.Ch02.jacobiProductPartial (q ^ 3) (q ^ 4 / z ^ 3) N))
        Filter.atTop (nhds 0)) :
    PartI.Ch04.quintupleProductLHS q z =
      PartI.Ch04.quintupleProductExplicitRHS q z :=
  PartI.Ch04.quintupleProduct_explicitProduct_of_tendsto_trunc_sub_jacobiPartials
    q z hqnorm hq hz h

theorem exercise4_quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_finiteJTPRHS
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h :
      Filter.Tendsto
        (fun N : ℕ =>
          (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
              qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
                qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
            (qPoch (q ^ 6) (q ^ 6) N *
                PartI.Ch03.finiteJTPRHS (q ^ 6) (-(z ^ 3 * q)) N -
              (q / z) * (qPoch (q ^ 6) (q ^ 6) N *
                PartI.Ch03.finiteJTPRHS (q ^ 6) (-(q ^ 7 / z ^ 3)) N)))
        Filter.atTop (nhds 0)) :
    PartI.Ch04.quintupleProductLHS q z =
      PartI.Ch04.quintupleProductExplicitRHS q z :=
  PartI.Ch04.quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_finiteJTPRHS
    q z hqnorm hq hz h

theorem exercise4_quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_weightedSums
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h :
      Filter.Tendsto
        (fun N : ℕ =>
          (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
              qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
                qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
            (qPoch (q ^ 6) (q ^ 6) N *
                PartI.Ch04.quintupleFiniteJTPLeftWeightedSum q z N -
              (q / z) * (qPoch (q ^ 6) (q ^ 6) N *
                PartI.Ch04.quintupleFiniteJTPRightWeightedSum q z N)))
        Filter.atTop (nhds 0)) :
    PartI.Ch04.quintupleProductLHS q z =
      PartI.Ch04.quintupleProductExplicitRHS q z :=
  PartI.Ch04.quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_weightedSums
    q z hqnorm hq hz h

theorem exercise4_quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_combinedWeightedSum
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h :
      Filter.Tendsto
        (fun N : ℕ =>
          (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
              qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
                qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
            qPoch (q ^ 6) (q ^ 6) N *
              PartI.Ch04.quintupleFiniteJTPCombinedWeightedSum q z N)
        Filter.atTop (nhds 0)) :
    PartI.Ch04.quintupleProductLHS q z =
      PartI.Ch04.quintupleProductExplicitRHS q z :=
  PartI.Ch04.quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_combinedWeightedSum
    q z hqnorm hq hz h

theorem exercise4_quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_combinedMonomialSum
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h :
      Filter.Tendsto
        (fun N : ℕ =>
          (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
              qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
                qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
            qPoch (q ^ 6) (q ^ 6) N *
              PartI.Ch04.quintupleFiniteJTPCombinedMonomialSum q z N)
        Filter.atTop (nhds 0)) :
    PartI.Ch04.quintupleProductLHS q z =
      PartI.Ch04.quintupleProductExplicitRHS q z :=
  PartI.Ch04.quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_combinedMonomialSum
    q z hqnorm hq hz h

theorem exercise4_tendsto_quintupleJacobiLeftPartial
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    Filter.Tendsto (fun N : ℕ => PartI.Ch04.quintupleJacobiLeftPartial q z N) Filter.atTop
      (nhds (∏' n : ℕ, PartI.Ch04.quintupleJacobiLeftFactor q z n)) :=
  PartI.Ch04.tendsto_quintupleJacobiLeftPartial q z hqnorm hq hz

theorem exercise4_tendsto_quintupleJacobiRightPartial
    (q z : ℂ) (hqnorm : ‖q‖ < 1) :
    Filter.Tendsto (fun N : ℕ => PartI.Ch04.quintupleJacobiRightPartial q z N) Filter.atTop
      (nhds (∏' n : ℕ, PartI.Ch04.quintupleJacobiRightFactor q z n)) :=
  PartI.Ch04.tendsto_quintupleJacobiRightPartial q z hqnorm

/-- **Theorem 4.3 (Jacobi's identity)** in q-parameter form.
For `‖q‖ < 1`: `(∏' k, 1 - q^(k+1))^3 = ∑' n, (-1)^n · (2n+1) · q^(n(n+1)/2)`. -/
theorem exercise4_jacobiIdentity (q : ℂ) (hq : ‖q‖ < 1) :
    (∏' k : ℕ, (1 - q ^ (k + 1))) ^ 3 =
      ∑' n : ℕ, ((-1) ^ n * (2 * (n : ℂ) + 1) * q ^ (n * (n + 1) / 2)) :=
  PartI.Ch04.jacobiIdentity q hq

end Chapter4Exercises

section Chapter5Exercises

/-- Exercise (Chapter 5 style): the top-left Ferrers cell exists in `[3,2,1]`. -/
theorem exercise5_ferrers_three_two_one_zero_zero :
    PartI.Ch05.FerrersCell [3, 2, 1] 0 0 :=
  PartI.Ch05.FerrersCell_three_two_one_zero_zero

/-- Exercise (Chapter 5 style): row 2 of `[3,2,1]` has no column-1 cell. -/
theorem exercise5_not_ferrers_three_two_one_two_one :
    ¬ PartI.Ch05.FerrersCell [3, 2, 1] 2 1 :=
  PartI.Ch05.not_FerrersCell_three_two_one_two_one

/-- Exercise (Chapter 5 style): full Ferrers diagram membership is the cell predicate. -/
theorem exercise5_mem_FerrersDiagramCells_iff (lam : List Nat) (r c : Nat) :
    (r, c) ∈ PartI.Ch05.FerrersDiagramCells lam ↔ PartI.Ch05.FerrersCell lam r c :=
  PartI.Ch05.mem_FerrersDiagramCells_iff

/-- Exercise (Chapter 5 style): indexed row lengths sum to the partition weight. -/
theorem exercise5_partitionWeight_eq_sum_getD (lam : List Nat) :
    (Finset.range lam.length).sum (fun r => lam.getD r 0) = partitionWeight lam :=
  PartI.Ch05.partitionWeight_eq_sum_getD lam

/-- Exercise (Chapter 5 style): the Ferrers diagram has as many cells as the partition weight. -/
theorem exercise5_FerrersDiagramCells_card (lam : List Nat) :
    (PartI.Ch05.FerrersDiagramCells lam).card = partitionWeight lam :=
  PartI.Ch05.FerrersDiagramCells_card lam

theorem exercise5_IsStrictPartition_tail {n : Nat} {lam : List Nat}
    (h : PartI.Ch05.IsStrictPartition (n :: lam)) :
    PartI.Ch05.IsStrictPartition lam :=
  PartI.Ch05.IsStrictPartition.tail h

theorem exercise5_IsStrictPartition_cons_of_forall_lt {n : Nat} {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam) (hn : 0 < n)
    (hgt : ∀ m, m ∈ lam → m < n) :
    PartI.Ch05.IsStrictPartition (n :: lam) :=
  PartI.Ch05.IsStrictPartition.cons_of_forall_lt hstrict hn hgt

theorem exercise5_IsStrictPartition_tail_lt_head {n : Nat} {lam : List Nat}
    (h : PartI.Ch05.IsStrictPartition (n :: lam)) {m : Nat} (hm : m ∈ lam) :
    m < n :=
  PartI.Ch05.IsStrictPartition.tail_lt_head h hm

theorem exercise5_IsStrictPartition_head_pos {n : Nat} {lam : List Nat}
    (h : PartI.Ch05.IsStrictPartition (n :: lam)) :
    0 < n :=
  PartI.Ch05.IsStrictPartition.head_pos h

theorem exercise5_IsStrictPartition_head_not_mem_tail {n : Nat} {lam : List Nat}
    (h : PartI.Ch05.IsStrictPartition (n :: lam)) :
    n ∉ lam :=
  PartI.Ch05.IsStrictPartition.head_not_mem_tail h

theorem exercise5_IsStrictPartition_cons_iff {n : Nat} {lam : List Nat} :
    PartI.Ch05.IsStrictPartition (n :: lam) ↔
      PartI.Ch05.IsStrictPartition lam ∧ 0 < n ∧ ∀ m, m ∈ lam → m < n :=
  PartI.Ch05.IsStrictPartition_cons_iff

theorem exercise5_IsStrictPartition_append_of_forall_gt {lam mu : List Nat}
    (hlam : PartI.Ch05.IsStrictPartition lam) (hmu : PartI.Ch05.IsStrictPartition mu)
    (hgt : ∀ a, a ∈ lam → ∀ b, b ∈ mu → b < a) :
    PartI.Ch05.IsStrictPartition (lam ++ mu) :=
  PartI.Ch05.IsStrictPartition_append_of_forall_gt hlam hmu hgt

theorem exercise5_IsStrictPartition_left_of_append {lam mu : List Nat}
    (h : PartI.Ch05.IsStrictPartition (lam ++ mu)) :
    PartI.Ch05.IsStrictPartition lam :=
  PartI.Ch05.IsStrictPartition_left_of_append h

theorem exercise5_IsStrictPartition_right_of_append {lam mu : List Nat}
    (h : PartI.Ch05.IsStrictPartition (lam ++ mu)) :
    PartI.Ch05.IsStrictPartition mu :=
  PartI.Ch05.IsStrictPartition_right_of_append h

theorem exercise5_IsStrictPartition_append_forall_gt {lam mu : List Nat}
    (h : PartI.Ch05.IsStrictPartition (lam ++ mu)) :
    ∀ a, a ∈ lam → ∀ b, b ∈ mu → b < a :=
  PartI.Ch05.IsStrictPartition_append_forall_gt h

theorem exercise5_IsStrictPartition_append_iff {lam mu : List Nat} :
    PartI.Ch05.IsStrictPartition (lam ++ mu) ↔
      PartI.Ch05.IsStrictPartition lam ∧ PartI.Ch05.IsStrictPartition mu ∧
        ∀ a, a ∈ lam → ∀ b, b ∈ mu → b < a :=
  PartI.Ch05.IsStrictPartition_append_iff

theorem exercise5_IsStrictPartition_dropLast {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam) :
    PartI.Ch05.IsStrictPartition lam.dropLast :=
  PartI.Ch05.IsStrictPartition_dropLast hstrict

theorem exercise5_partitionWeight_cons_part (n : Nat) (lam : List Nat) :
    partitionWeight (n :: lam) = n + partitionWeight lam :=
  PartI.Ch05.partitionWeight_cons_part n lam

theorem exercise5_partitionWeight_cons_sub_head (n : Nat) (lam : List Nat) :
    partitionWeight (n :: lam) - n = partitionWeight lam :=
  PartI.Ch05.partitionWeight_cons_sub_head n lam

theorem exercise5_partitionWeight_tail_add_head (n : Nat) (lam : List Nat) :
    partitionWeight lam + n = partitionWeight (n :: lam) :=
  PartI.Ch05.partitionWeight_tail_add_head n lam

theorem exercise5_partitionWeight_append_parts (lam mu : List Nat) :
    partitionWeight (lam ++ mu) = partitionWeight lam + partitionWeight mu :=
  PartI.Ch05.partitionWeight_append_parts lam mu

theorem exercise5_numberOfParts_nil :
    PartI.Ch05.numberOfParts [] = 0 :=
  PartI.Ch05.numberOfParts_nil

theorem exercise5_numberOfParts_cons (n : Nat) (lam : List Nat) :
    PartI.Ch05.numberOfParts (n :: lam) = PartI.Ch05.numberOfParts lam + 1 :=
  PartI.Ch05.numberOfParts_cons n lam

theorem exercise5_numberOfParts_append (lam mu : List Nat) :
    PartI.Ch05.numberOfParts (lam ++ mu) =
      PartI.Ch05.numberOfParts lam + PartI.Ch05.numberOfParts mu :=
  PartI.Ch05.numberOfParts_append lam mu

theorem exercise5_numberOfParts_dropLast_of_ne_nil {lam : List Nat}
    (hne : lam ≠ []) :
    PartI.Ch05.numberOfParts lam.dropLast =
      PartI.Ch05.numberOfParts lam - 1 :=
  PartI.Ch05.numberOfParts_dropLast_of_ne_nil hne

theorem exercise5_numberOfParts_dropLast_add_one_of_ne_nil {lam : List Nat}
    (hne : lam ≠ []) :
    PartI.Ch05.numberOfParts lam.dropLast + 1 =
      PartI.Ch05.numberOfParts lam :=
  PartI.Ch05.numberOfParts_dropLast_add_one_of_ne_nil hne

theorem exercise5_lastPart_eq_getLast {lam : List Nat} (hne : lam ≠ []) :
    lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 = lam.getLast hne :=
  PartI.Ch05.lastPart_eq_getLast hne

theorem exercise5_dropLast_getD_of_lt {lam : List Nat} {r : Nat}
    (hr : r < lam.dropLast.length) :
    lam.dropLast.getD r 0 = lam.getD r 0 :=
  PartI.Ch05.dropLast_getD_of_lt hr

theorem exercise5_numberOfParts_cons_sub_one (n : Nat) (lam : List Nat) :
    PartI.Ch05.numberOfParts (n :: lam) - 1 = PartI.Ch05.numberOfParts lam :=
  PartI.Ch05.numberOfParts_cons_sub_one n lam

theorem exercise5_numberOfParts_tail_add_one (n : Nat) (lam : List Nat) :
    PartI.Ch05.numberOfParts lam + 1 = PartI.Ch05.numberOfParts (n :: lam) :=
  PartI.Ch05.numberOfParts_tail_add_one n lam

theorem exercise5_partParity_nil :
    PartI.Ch05.partParity [] = 0 :=
  PartI.Ch05.partParity_nil

theorem exercise5_partParity_cons (n : Nat) (lam : List Nat) :
    PartI.Ch05.partParity (n :: lam) = (PartI.Ch05.partParity lam + 1) % 2 :=
  PartI.Ch05.partParity_cons n lam

theorem exercise5_partParity_tail_cons (n : Nat) (lam : List Nat) :
    PartI.Ch05.partParity lam = (PartI.Ch05.partParity (n :: lam) + 1) % 2 :=
  PartI.Ch05.partParity_tail_cons n lam

theorem exercise5_partParity_cons_cons (m n : Nat) (lam : List Nat) :
    PartI.Ch05.partParity (m :: n :: lam) = PartI.Ch05.partParity lam :=
  PartI.Ch05.partParity_cons_cons m n lam

theorem exercise5_partParity_append (lam mu : List Nat) :
    PartI.Ch05.partParity (lam ++ mu) =
      (PartI.Ch05.partParity lam + PartI.Ch05.partParity mu) % 2 :=
  PartI.Ch05.partParity_append lam mu

theorem exercise5_partParity_cons_of_zero {n : Nat} {lam : List Nat}
    (h : PartI.Ch05.partParity lam = 0) :
    PartI.Ch05.partParity (n :: lam) = 1 :=
  PartI.Ch05.partParity_cons_of_zero h

theorem exercise5_partParity_cons_of_one {n : Nat} {lam : List Nat}
    (h : PartI.Ch05.partParity lam = 1) :
    PartI.Ch05.partParity (n :: lam) = 0 :=
  PartI.Ch05.partParity_cons_of_one h

theorem exercise5_partParity_tail_of_cons_zero {n : Nat} {lam : List Nat}
    (h : PartI.Ch05.partParity (n :: lam) = 0) :
    PartI.Ch05.partParity lam = 1 :=
  PartI.Ch05.partParity_tail_of_cons_zero h

theorem exercise5_partParity_tail_of_cons_one {n : Nat} {lam : List Nat}
    (h : PartI.Ch05.partParity (n :: lam) = 1) :
    PartI.Ch05.partParity lam = 0 :=
  PartI.Ch05.partParity_tail_of_cons_one h

theorem exercise5_partParity_eq_zero_or_one (lam : List Nat) :
    PartI.Ch05.partParity lam = 0 ∨ PartI.Ch05.partParity lam = 1 :=
  PartI.Ch05.partParity_eq_zero_or_one lam

theorem exercise5_partSign_nil :
    PartI.Ch05.partSign [] = 1 :=
  PartI.Ch05.partSign_nil

theorem exercise5_partSign_of_partParity_zero {lam : List Nat}
    (h : PartI.Ch05.partParity lam = 0) :
    PartI.Ch05.partSign lam = 1 :=
  PartI.Ch05.partSign_of_partParity_zero h

theorem exercise5_partSign_of_partParity_one {lam : List Nat}
    (h : PartI.Ch05.partParity lam = 1) :
    PartI.Ch05.partSign lam = -1 :=
  PartI.Ch05.partSign_of_partParity_one h

theorem exercise5_partSign_eq_one_or_neg_one (lam : List Nat) :
    PartI.Ch05.partSign lam = 1 ∨ PartI.Ch05.partSign lam = -1 :=
  PartI.Ch05.partSign_eq_one_or_neg_one lam

theorem exercise5_partSign_ne_zero (lam : List Nat) :
    PartI.Ch05.partSign lam ≠ 0 :=
  PartI.Ch05.partSign_ne_zero lam

theorem exercise5_partSign_mul_self (lam : List Nat) :
    PartI.Ch05.partSign lam * PartI.Ch05.partSign lam = 1 :=
  PartI.Ch05.partSign_mul_self lam

theorem exercise5_partSign_cons (n : Nat) (lam : List Nat) :
    PartI.Ch05.partSign (n :: lam) = - PartI.Ch05.partSign lam :=
  PartI.Ch05.partSign_cons n lam

theorem exercise5_partSign_tail_cons (n : Nat) (lam : List Nat) :
    PartI.Ch05.partSign lam = - PartI.Ch05.partSign (n :: lam) :=
  PartI.Ch05.partSign_tail_cons n lam

theorem exercise5_tail_weight_sign_of_cons (n : Nat) (lam : List Nat) :
    partitionWeight (n :: lam) - n = partitionWeight lam ∧
      PartI.Ch05.partSign lam = - PartI.Ch05.partSign (n :: lam) :=
  PartI.Ch05.tail_weight_sign_of_cons n lam

theorem exercise5_removeFirstPart_nil :
    PartI.Ch05.removeFirstPart [] = [] :=
  PartI.Ch05.removeFirstPart_nil

theorem exercise5_removeFirstPart_cons (n : Nat) (lam : List Nat) :
    PartI.Ch05.removeFirstPart (n :: lam) = lam :=
  PartI.Ch05.removeFirstPart_cons n lam

theorem exercise5_firstPart_nil :
    PartI.Ch05.firstPart [] = 0 :=
  PartI.Ch05.firstPart_nil

theorem exercise5_firstPart_cons (n : Nat) (lam : List Nat) :
    PartI.Ch05.firstPart (n :: lam) = n :=
  PartI.Ch05.firstPart_cons n lam

theorem exercise5_IsStrictPartition_removeFirstPart_cons {n : Nat} {lam : List Nat}
    (h : PartI.Ch05.IsStrictPartition (n :: lam)) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.removeFirstPart (n :: lam)) :=
  PartI.Ch05.IsStrictPartition_removeFirstPart_cons h

theorem exercise5_firstPart_pos_of_IsStrictPartition_cons {n : Nat} {lam : List Nat}
    (h : PartI.Ch05.IsStrictPartition (n :: lam)) :
    0 < PartI.Ch05.firstPart (n :: lam) :=
  PartI.Ch05.firstPart_pos_of_IsStrictPartition_cons h

theorem exercise5_firstPart_pos_of_IsStrictPartition_of_ne_nil {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam) (hne : lam ≠ []) :
    0 < PartI.Ch05.firstPart lam :=
  PartI.Ch05.firstPart_pos_of_IsStrictPartition_of_ne_nil hstrict hne

theorem exercise5_IsStrictPartition_removeFirstPart {lam : List Nat}
    (h : PartI.Ch05.IsStrictPartition lam) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.removeFirstPart lam) :=
  PartI.Ch05.IsStrictPartition_removeFirstPart h

theorem exercise5_numberOfParts_removeFirstPart_cons (n : Nat) (lam : List Nat) :
    PartI.Ch05.numberOfParts (PartI.Ch05.removeFirstPart (n :: lam)) + 1 =
      PartI.Ch05.numberOfParts (n :: lam) :=
  PartI.Ch05.numberOfParts_removeFirstPart_cons n lam

theorem exercise5_partParity_removeFirstPart_cons (n : Nat) (lam : List Nat) :
    PartI.Ch05.partParity (PartI.Ch05.removeFirstPart (n :: lam)) =
      (PartI.Ch05.partParity (n :: lam) + 1) % 2 :=
  PartI.Ch05.partParity_removeFirstPart_cons n lam

theorem exercise5_partSign_removeFirstPart_cons (n : Nat) (lam : List Nat) :
    PartI.Ch05.partSign (PartI.Ch05.removeFirstPart (n :: lam)) =
      - PartI.Ch05.partSign (n :: lam) :=
  PartI.Ch05.partSign_removeFirstPart_cons n lam

theorem exercise5_removeFirstPart_weight_sign_cons (n : Nat) (lam : List Nat) :
    partitionWeight (n :: lam) - n =
        partitionWeight (PartI.Ch05.removeFirstPart (n :: lam)) ∧
      PartI.Ch05.partSign (PartI.Ch05.removeFirstPart (n :: lam)) =
        - PartI.Ch05.partSign (n :: lam) :=
  PartI.Ch05.removeFirstPart_weight_sign_cons n lam

theorem exercise5_prependPart_eq_cons (n : Nat) (lam : List Nat) :
    PartI.Ch05.prependPart n lam = n :: lam :=
  PartI.Ch05.prependPart_eq_cons n lam

theorem exercise5_firstPart_prependPart (n : Nat) (lam : List Nat) :
    PartI.Ch05.firstPart (PartI.Ch05.prependPart n lam) = n :=
  PartI.Ch05.firstPart_prependPart n lam

theorem exercise5_removeFirstPart_prependPart (n : Nat) (lam : List Nat) :
    PartI.Ch05.removeFirstPart (PartI.Ch05.prependPart n lam) = lam :=
  PartI.Ch05.removeFirstPart_prependPart n lam

theorem exercise5_prependPart_removeFirstPart_cons (n : Nat) (lam : List Nat) :
    PartI.Ch05.prependPart n (PartI.Ch05.removeFirstPart (n :: lam)) = n :: lam :=
  PartI.Ch05.prependPart_removeFirstPart_cons n lam

theorem exercise5_prependPart_firstPart_removeFirstPart_cons (n : Nat) (lam : List Nat) :
    PartI.Ch05.prependPart (PartI.Ch05.firstPart (n :: lam))
      (PartI.Ch05.removeFirstPart (n :: lam)) = n :: lam :=
  PartI.Ch05.prependPart_firstPart_removeFirstPart_cons n lam

theorem exercise5_prependPart_firstPart_removeFirstPart_of_ne_nil (lam : List Nat)
    (hne : lam ≠ []) :
    PartI.Ch05.prependPart (PartI.Ch05.firstPart lam)
      (PartI.Ch05.removeFirstPart lam) = lam :=
  PartI.Ch05.prependPart_firstPart_removeFirstPart_of_ne_nil lam hne

theorem exercise5_removeFirstPart_lt_firstPart_of_IsStrictPartition_cons
    {n : Nat} {lam : List Nat} (h : PartI.Ch05.IsStrictPartition (n :: lam))
    {m : Nat} (hm : m ∈ PartI.Ch05.removeFirstPart (n :: lam)) :
    m < PartI.Ch05.firstPart (n :: lam) :=
  PartI.Ch05.removeFirstPart_lt_firstPart_of_IsStrictPartition_cons h hm

theorem exercise5_removeFirstPart_lt_firstPart_of_IsStrictPartition {lam : List Nat}
    (h : PartI.Ch05.IsStrictPartition lam) {m : Nat}
    (hm : m ∈ PartI.Ch05.removeFirstPart lam) :
    m < PartI.Ch05.firstPart lam :=
  PartI.Ch05.removeFirstPart_lt_firstPart_of_IsStrictPartition h hm

theorem exercise5_partitionWeight_firstPart_add_removeFirstPart_cons (n : Nat) (lam : List Nat) :
    partitionWeight (n :: lam) =
      PartI.Ch05.firstPart (n :: lam) +
        partitionWeight (PartI.Ch05.removeFirstPart (n :: lam)) :=
  PartI.Ch05.partitionWeight_firstPart_add_removeFirstPart_cons n lam

theorem exercise5_numberOfParts_removeFirstPart_add_one_cons (n : Nat) (lam : List Nat) :
    PartI.Ch05.numberOfParts (n :: lam) =
      PartI.Ch05.numberOfParts (PartI.Ch05.removeFirstPart (n :: lam)) + 1 :=
  PartI.Ch05.numberOfParts_removeFirstPart_add_one_cons n lam

theorem exercise5_partSign_cons_eq_neg_removeFirstPart (n : Nat) (lam : List Nat) :
    PartI.Ch05.partSign (n :: lam) =
      - PartI.Ch05.partSign (PartI.Ch05.removeFirstPart (n :: lam)) :=
  PartI.Ch05.partSign_cons_eq_neg_removeFirstPart n lam

theorem exercise5_IsStrictPartition_prependPart_of_forall_lt {n : Nat} {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam) (hn : 0 < n)
    (hgt : ∀ m, m ∈ lam → m < n) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.prependPart n lam) :=
  PartI.Ch05.IsStrictPartition_prependPart_of_forall_lt hstrict hn hgt

theorem exercise5_numberOfParts_prependPart (n : Nat) (lam : List Nat) :
    PartI.Ch05.numberOfParts (PartI.Ch05.prependPart n lam) =
      PartI.Ch05.numberOfParts lam + 1 :=
  PartI.Ch05.numberOfParts_prependPart n lam

theorem exercise5_partParity_prependPart (n : Nat) (lam : List Nat) :
    PartI.Ch05.partParity (PartI.Ch05.prependPart n lam) =
      (PartI.Ch05.partParity lam + 1) % 2 :=
  PartI.Ch05.partParity_prependPart n lam

theorem exercise5_partSign_prependPart (n : Nat) (lam : List Nat) :
    PartI.Ch05.partSign (PartI.Ch05.prependPart n lam) =
      - PartI.Ch05.partSign lam :=
  PartI.Ch05.partSign_prependPart n lam

theorem exercise5_prependPart_weight_sign (n : Nat) (lam : List Nat) :
    partitionWeight (PartI.Ch05.prependPart n lam) = n + partitionWeight lam ∧
      PartI.Ch05.partSign (PartI.Ch05.prependPart n lam) = - PartI.Ch05.partSign lam :=
  PartI.Ch05.prependPart_weight_sign n lam

theorem exercise5_cons_strict_weight_sign_of_forall_lt {n : Nat} {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam) (hn : 0 < n)
    (hgt : ∀ m, m ∈ lam → m < n) :
    PartI.Ch05.IsStrictPartition (n :: lam) ∧
      partitionWeight (n :: lam) = n + partitionWeight lam ∧
      PartI.Ch05.partSign (n :: lam) = - PartI.Ch05.partSign lam :=
  PartI.Ch05.cons_strict_weight_sign_of_forall_lt hstrict hn hgt

theorem exercise5_prependPart_strict_weight_sign_of_forall_lt {n : Nat} {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam) (hn : 0 < n)
    (hgt : ∀ m, m ∈ lam → m < n) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.prependPart n lam) ∧
      partitionWeight (PartI.Ch05.prependPart n lam) = n + partitionWeight lam ∧
      PartI.Ch05.partSign (PartI.Ch05.prependPart n lam) = - PartI.Ch05.partSign lam :=
  PartI.Ch05.prependPart_strict_weight_sign_of_forall_lt hstrict hn hgt

theorem exercise5_partSign_cons_cons (m n : Nat) (lam : List Nat) :
    PartI.Ch05.partSign (m :: n :: lam) = PartI.Ch05.partSign lam :=
  PartI.Ch05.partSign_cons_cons m n lam

theorem exercise5_partSign_append (lam mu : List Nat) :
    PartI.Ch05.partSign (lam ++ mu) =
      PartI.Ch05.partSign lam * PartI.Ch05.partSign mu :=
  PartI.Ch05.partSign_append lam mu

/-- Exercise (Chapter 5 style): `[3,2,1]` is a strict partition. -/
theorem exercise5_IsStrictPartition_three_two_one :
    PartI.Ch05.IsStrictPartition [3, 2, 1] :=
  PartI.Ch05.IsStrictPartition_three_two_one

/-- Exercise (Chapter 5 style): `[2,2]` is not a strict partition. -/
theorem exercise5_not_IsStrictPartition_two_two :
    ¬ PartI.Ch05.IsStrictPartition [2, 2] :=
  PartI.Ch05.not_IsStrictPartition_two_two

/-- Exercise (Chapter 5 style): the staircase partition of height 3 is `[3,2,1]`. -/
theorem exercise5_staircasePartition_three :
    PartI.Ch05.staircasePartition 3 = [3, 2, 1] :=
  PartI.Ch05.staircasePartition_three

/-- Exercise (Chapter 5 style): staircase partitions have triangular weight. -/
theorem exercise5_partitionWeight_staircasePartition (n : Nat) :
    partitionWeight (PartI.Ch05.staircasePartition n) = triangular n :=
  PartI.Ch05.partitionWeight_staircasePartition n

theorem exercise5_staircasePartition_length (n : Nat) :
    (PartI.Ch05.staircasePartition n).length = n :=
  PartI.Ch05.staircasePartition_length n

theorem exercise5_staircasePartition_getD_of_lt {n r : Nat} (hr : r < n) :
    (PartI.Ch05.staircasePartition n).getD r 0 = n - r :=
  PartI.Ch05.staircasePartition_getD_of_lt hr

theorem exercise5_partParity_staircasePartition (n : Nat) :
    PartI.Ch05.partParity (PartI.Ch05.staircasePartition n) = n % 2 :=
  PartI.Ch05.partParity_staircasePartition n

theorem exercise5_partSign_staircasePartition (n : Nat) :
    PartI.Ch05.partSign (PartI.Ch05.staircasePartition n) =
      if n % 2 = 0 then 1 else -1 :=
  PartI.Ch05.partSign_staircasePartition n

/-- Exercise (Chapter 5 style): every staircase partition is strict. -/
theorem exercise5_IsStrictPartition_staircasePartition (n : Nat) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.staircasePartition n) :=
  PartI.Ch05.IsStrictPartition_staircasePartition n

/-- Exercise (Chapter 5 style): shifting all parts preserves strict partitions. -/
theorem exercise5_IsStrictPartition_shiftParts {d : Nat} {lam : List Nat}
    (h : PartI.Ch05.IsStrictPartition lam) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.shiftParts d lam) :=
  PartI.Ch05.IsStrictPartition_shiftParts h

/-- Exercise (Chapter 5 style): shifting `[3,2,1]` by one gives `[4,3,2]`. -/
theorem exercise5_shiftParts_three_two_one_one :
    PartI.Ch05.shiftParts 1 [3, 2, 1] = [4, 3, 2] :=
  PartI.Ch05.shiftParts_three_two_one_one

/-- Exercise (Chapter 5 style): shifting all parts changes weight predictably. -/
theorem exercise5_partitionWeight_shiftParts (d : Nat) (lam : List Nat) :
    partitionWeight (PartI.Ch05.shiftParts d lam) =
      partitionWeight lam + d * PartI.Ch05.numberOfParts lam :=
  PartI.Ch05.partitionWeight_shiftParts d lam

theorem exercise5_partParity_shiftParts (d : Nat) (lam : List Nat) :
    PartI.Ch05.partParity (PartI.Ch05.shiftParts d lam) = PartI.Ch05.partParity lam :=
  PartI.Ch05.partParity_shiftParts d lam

theorem exercise5_partSign_shiftParts (d : Nat) (lam : List Nat) :
    PartI.Ch05.partSign (PartI.Ch05.shiftParts d lam) = PartI.Ch05.partSign lam :=
  PartI.Ch05.partSign_shiftParts d lam

theorem exercise5_shiftParts_getD_of_lt {d : Nat} {lam : List Nat} {r : Nat}
    (hr : r < lam.length) :
    (PartI.Ch05.shiftParts d lam).getD r 0 = lam.getD r 0 + d :=
  PartI.Ch05.shiftParts_getD_of_lt hr

theorem exercise5_shiftParts_shiftParts (a b : Nat) (lam : List Nat) :
    PartI.Ch05.shiftParts a (PartI.Ch05.shiftParts b lam) =
      PartI.Ch05.shiftParts (b + a) lam :=
  PartI.Ch05.shiftParts_shiftParts a b lam

/-- Exercise (Chapter 5 style): row-shortening preserves the number of displayed parts. -/
theorem exercise5_numberOfParts_decrementParts (lam : List Nat) :
    PartI.Ch05.numberOfParts (PartI.Ch05.decrementParts lam) = PartI.Ch05.numberOfParts lam :=
  PartI.Ch05.numberOfParts_decrementParts lam

/-- Exercise (Chapter 5 style): row-shortening preserves Franklin's parity sign. -/
theorem exercise5_partSign_decrementParts (lam : List Nat) :
    PartI.Ch05.partSign (PartI.Ch05.decrementParts lam) = PartI.Ch05.partSign lam :=
  PartI.Ch05.partSign_decrementParts lam

/-- Exercise (Chapter 5 style): weight loss from row-shortening positive parts. -/
theorem exercise5_partitionWeight_decrementParts_add_numberOfParts {lam : List Nat}
    (hpos : PartI.Ch05.PositiveParts lam) :
    partitionWeight (PartI.Ch05.decrementParts lam) + PartI.Ch05.numberOfParts lam =
      partitionWeight lam :=
  PartI.Ch05.partitionWeight_decrementParts_add_numberOfParts hpos

/-- Exercise (Chapter 5 style): row-shortening preserves weakly decreasing order. -/
theorem exercise5_IsPartition_decrementParts {lam : List Nat}
    (hpart : IsPartition lam) :
    IsPartition (PartI.Ch05.decrementParts lam) :=
  PartI.Ch05.IsPartition_decrementParts hpart

/-- Exercise (Chapter 5 style): positivity survives shortening when parts are > 1. -/
theorem exercise5_PositiveParts_decrementParts_of_one_lt {lam : List Nat}
    (hgt : ∀ n, n ∈ lam → 1 < n) :
    PartI.Ch05.PositiveParts (PartI.Ch05.decrementParts lam) :=
  PartI.Ch05.PositiveParts_decrementParts_of_one_lt hgt

/-- Exercise (Chapter 5 style): distinctness survives row-shortening on positive parts. -/
theorem exercise5_HasDistinctParts_decrementParts {lam : List Nat}
    (hpos : PartI.Ch05.PositiveParts lam) (hnodup : PartI.Ch05.HasDistinctParts lam) :
    PartI.Ch05.HasDistinctParts (PartI.Ch05.decrementParts lam) :=
  PartI.Ch05.HasDistinctParts_decrementParts hpos hnodup

/-- Exercise (Chapter 5 style): row-shortening preserves strictness. -/
theorem exercise5_IsStrictPartition_decrementParts_of_one_lt {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam) (hgt : ∀ n, n ∈ lam → 1 < n) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.decrementParts lam) :=
  PartI.Ch05.IsStrictPartition_decrementParts_of_one_lt hstrict hgt

/-- Exercise (Chapter 5 style): the down move adds one displayed part. -/
theorem exercise5_numberOfParts_franklinDownMove (lam : List Nat) :
    PartI.Ch05.numberOfParts (PartI.Ch05.franklinDownMove lam) =
      PartI.Ch05.numberOfParts lam + 1 :=
  PartI.Ch05.numberOfParts_franklinDownMove lam

theorem exercise5_IsFranklinDownBranchInput (lam : List Nat) :
    PartI.Ch05.IsFranklinDownBranchInput lam ↔
      0 < PartI.Ch05.numberOfParts lam ∧
        ∀ n, n ∈ lam → PartI.Ch05.numberOfParts lam + 1 < n := by
  rfl

theorem exercise5_IsFranklinUpBranchInput (lam : List Nat) :
    PartI.Ch05.IsFranklinUpBranchInput lam ↔
      ∃ mu : List Nat,
        PartI.Ch05.IsStrictPartition mu ∧
          lam = mu ++ [PartI.Ch05.numberOfParts mu] := by
  rfl

/-- Exercise (Chapter 5 style): the down move reverses Franklin's sign. -/
theorem exercise5_partSign_franklinDownMove (lam : List Nat) :
    PartI.Ch05.partSign (PartI.Ch05.franklinDownMove lam) = - PartI.Ch05.partSign lam :=
  PartI.Ch05.partSign_franklinDownMove lam

/-- Exercise (Chapter 5 style): the down move preserves weight on positive-parts lists. -/
theorem exercise5_partitionWeight_franklinDownMove {lam : List Nat}
    (hpos : PartI.Ch05.PositiveParts lam) :
    partitionWeight (PartI.Ch05.franklinDownMove lam) = partitionWeight lam :=
  PartI.Ch05.partitionWeight_franklinDownMove hpos

/-- Exercise (Chapter 5 style): the down move preserves strictness under Franklin inequality. -/
theorem exercise5_IsStrictPartition_franklinDownMove {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam) (hlen : 0 < PartI.Ch05.numberOfParts lam)
    (hgt : ∀ n, n ∈ lam → PartI.Ch05.numberOfParts lam + 1 < n) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.franklinDownMove lam) :=
  PartI.Ch05.IsStrictPartition_franklinDownMove hstrict hlen hgt

/-- Exercise (Chapter 5 style): weight, sign, and strictness package for the down branch. -/
theorem exercise5_franklinDownMove_strict_weight_sign {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam) (hlen : 0 < PartI.Ch05.numberOfParts lam)
    (hgt : ∀ n, n ∈ lam → PartI.Ch05.numberOfParts lam + 1 < n) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.franklinDownMove lam) ∧
      partitionWeight (PartI.Ch05.franklinDownMove lam) = partitionWeight lam ∧
      PartI.Ch05.partSign (PartI.Ch05.franklinDownMove lam) = - PartI.Ch05.partSign lam :=
  PartI.Ch05.franklinDownMove_strict_weight_sign hstrict hlen hgt

theorem exercise5_IsStrictPartition_decrementParts_of_franklinDownMove_hgt {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hgt : ∀ n, n ∈ lam → PartI.Ch05.numberOfParts lam + 1 < n) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.decrementParts lam) :=
  PartI.Ch05.IsStrictPartition_decrementParts_of_franklinDownMove_hgt hstrict hgt

theorem exercise5_franklinDownMove_eq_append_numberOfParts_decrementParts (lam : List Nat) :
    PartI.Ch05.franklinDownMove lam =
      PartI.Ch05.decrementParts lam ++
        [PartI.Ch05.numberOfParts (PartI.Ch05.decrementParts lam)] :=
  PartI.Ch05.franklinDownMove_eq_append_numberOfParts_decrementParts lam

theorem exercise5_franklinDownMove_eq_append_numberOfParts_exists (lam : List Nat) :
    ∃ mu : List Nat,
      PartI.Ch05.franklinDownMove lam =
        mu ++ [PartI.Ch05.numberOfParts mu] :=
  PartI.Ch05.franklinDownMove_eq_append_numberOfParts_exists lam

theorem exercise5_franklinDownMove_eq_append_numberOfParts_strict_exists {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hgt : ∀ n, n ∈ lam → PartI.Ch05.numberOfParts lam + 1 < n) :
    ∃ mu : List Nat,
      PartI.Ch05.IsStrictPartition mu ∧
        PartI.Ch05.franklinDownMove lam =
          mu ++ [PartI.Ch05.numberOfParts mu] :=
  PartI.Ch05.franklinDownMove_eq_append_numberOfParts_strict_exists hstrict hgt

theorem exercise5_IsFranklinUpBranchInput_franklinDownMove {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hdown : PartI.Ch05.IsFranklinDownBranchInput lam) :
    PartI.Ch05.IsFranklinUpBranchInput (PartI.Ch05.franklinDownMove lam) :=
  PartI.Ch05.IsFranklinUpBranchInput_franklinDownMove hstrict hdown

theorem exercise5_franklinDownMove_strict_weight_sign_of_branch_input {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hdown : PartI.Ch05.IsFranklinDownBranchInput lam) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.franklinDownMove lam) ∧
      partitionWeight (PartI.Ch05.franklinDownMove lam) = partitionWeight lam ∧
      PartI.Ch05.partSign (PartI.Ch05.franklinDownMove lam) = - PartI.Ch05.partSign lam :=
  PartI.Ch05.franklinDownMove_strict_weight_sign_of_branch_input hstrict hdown

theorem exercise5_franklinDownMove_branch_transition_and_inverse {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hdown : PartI.Ch05.IsFranklinDownBranchInput lam) :
    PartI.Ch05.IsFranklinUpBranchInput (PartI.Ch05.franklinDownMove lam) ∧
      PartI.Ch05.franklinUpMove (PartI.Ch05.franklinDownMove lam) = lam :=
  PartI.Ch05.franklinDownMove_branch_transition_and_inverse hstrict hdown

theorem exercise5_shiftParts_one_decrementParts_eq_of_positive {lam : List Nat}
    (hpos : PartI.Ch05.PositiveParts lam) :
    PartI.Ch05.shiftParts 1 (PartI.Ch05.decrementParts lam) = lam :=
  PartI.Ch05.shiftParts_one_decrementParts_eq_of_positive hpos

theorem exercise5_decrementParts_shiftParts_one_eq (lam : List Nat) :
    PartI.Ch05.decrementParts (PartI.Ch05.shiftParts 1 lam) = lam :=
  PartI.Ch05.decrementParts_shiftParts_one_eq lam

theorem exercise5_decrementParts_shiftParts_succ (d : Nat) (lam : List Nat) :
    PartI.Ch05.decrementParts (PartI.Ch05.shiftParts (d + 1) lam) =
      PartI.Ch05.shiftParts d lam :=
  PartI.Ch05.decrementParts_shiftParts_succ d lam

theorem exercise5_franklinUpMove_franklinDownMove_of_positive {lam : List Nat}
    (hpos : PartI.Ch05.PositiveParts lam) :
    PartI.Ch05.franklinUpMove (PartI.Ch05.franklinDownMove lam) = lam :=
  PartI.Ch05.franklinUpMove_franklinDownMove_of_positive hpos

theorem exercise5_franklinUpMove_append_singleton (mu : List Nat) (n : Nat) :
    PartI.Ch05.franklinUpMove (mu ++ [n]) = PartI.Ch05.shiftParts 1 mu :=
  PartI.Ch05.franklinUpMove_append_singleton mu n

theorem exercise5_franklinDownMove_franklinUpMove_append_numberOfParts (mu : List Nat) :
    PartI.Ch05.franklinDownMove
        (PartI.Ch05.franklinUpMove (mu ++ [PartI.Ch05.numberOfParts mu])) =
      mu ++ [PartI.Ch05.numberOfParts mu] :=
  PartI.Ch05.franklinDownMove_franklinUpMove_append_numberOfParts mu

theorem exercise5_numberOfParts_franklinUpMove_append_singleton
    (mu : List Nat) (n : Nat) :
    PartI.Ch05.numberOfParts (PartI.Ch05.franklinUpMove (mu ++ [n])) =
      PartI.Ch05.numberOfParts mu :=
  PartI.Ch05.numberOfParts_franklinUpMove_append_singleton mu n

theorem exercise5_IsFranklinDownBranchInput_franklinUpMove {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hup : PartI.Ch05.IsFranklinUpBranchInput lam) :
    PartI.Ch05.IsFranklinDownBranchInput (PartI.Ch05.franklinUpMove lam) :=
  PartI.Ch05.IsFranklinDownBranchInput_franklinUpMove hstrict hup

theorem exercise5_partSign_franklinUpMove_append_singleton (mu : List Nat) (n : Nat) :
    PartI.Ch05.partSign (PartI.Ch05.franklinUpMove (mu ++ [n])) =
      - PartI.Ch05.partSign (mu ++ [n]) :=
  PartI.Ch05.partSign_franklinUpMove_append_singleton mu n

theorem exercise5_partitionWeight_franklinUpMove_append_numberOfParts (mu : List Nat) :
    partitionWeight (PartI.Ch05.franklinUpMove (mu ++ [PartI.Ch05.numberOfParts mu])) =
      partitionWeight (mu ++ [PartI.Ch05.numberOfParts mu]) :=
  PartI.Ch05.partitionWeight_franklinUpMove_append_numberOfParts mu

theorem exercise5_IsStrictPartition_franklinUpMove_append_singleton
    {mu : List Nat} {n : Nat} (hstrict : PartI.Ch05.IsStrictPartition mu) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.franklinUpMove (mu ++ [n])) :=
  PartI.Ch05.IsStrictPartition_franklinUpMove_append_singleton hstrict

theorem exercise5_franklinUpMove_append_numberOfParts_strict_weight_sign {mu : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition mu) :
    PartI.Ch05.IsStrictPartition
        (PartI.Ch05.franklinUpMove (mu ++ [PartI.Ch05.numberOfParts mu])) ∧
      partitionWeight
          (PartI.Ch05.franklinUpMove (mu ++ [PartI.Ch05.numberOfParts mu])) =
        partitionWeight (mu ++ [PartI.Ch05.numberOfParts mu]) ∧
  PartI.Ch05.partSign
      (PartI.Ch05.franklinUpMove (mu ++ [PartI.Ch05.numberOfParts mu])) =
        - PartI.Ch05.partSign (mu ++ [PartI.Ch05.numberOfParts mu]) :=
  PartI.Ch05.franklinUpMove_append_numberOfParts_strict_weight_sign hstrict

theorem exercise5_franklinUpMove_strict_weight_sign_of_branch_input {lam : List Nat}
    (hup : PartI.Ch05.IsFranklinUpBranchInput lam) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.franklinUpMove lam) ∧
      partitionWeight (PartI.Ch05.franklinUpMove lam) = partitionWeight lam ∧
      PartI.Ch05.partSign (PartI.Ch05.franklinUpMove lam) = - PartI.Ch05.partSign lam :=
  PartI.Ch05.franklinUpMove_strict_weight_sign_of_branch_input hup

theorem exercise5_franklinUpMove_branch_transition_and_inverse {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hup : PartI.Ch05.IsFranklinUpBranchInput lam) :
    PartI.Ch05.IsFranklinDownBranchInput (PartI.Ch05.franklinUpMove lam) ∧
      PartI.Ch05.franklinDownMove (PartI.Ch05.franklinUpMove lam) = lam :=
  PartI.Ch05.franklinUpMove_branch_transition_and_inverse hstrict hup

theorem exercise5_numberOfParts_franklinUpMove_of_ne_nil {lam : List Nat}
    (hne : lam ≠ []) :
    PartI.Ch05.numberOfParts (PartI.Ch05.franklinUpMove lam) =
      PartI.Ch05.numberOfParts lam - 1 :=
  PartI.Ch05.numberOfParts_franklinUpMove_of_ne_nil hne

theorem exercise5_successive_getD_franklinUpMove_of_successive {lam : List Nat}
    (hsucc : ∀ r, r + 1 < PartI.Ch05.numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    ∀ r, r + 1 < PartI.Ch05.numberOfParts (PartI.Ch05.franklinUpMove lam) →
      (PartI.Ch05.franklinUpMove lam).getD (r + 1) 0 + 1 =
        (PartI.Ch05.franklinUpMove lam).getD r 0 :=
  PartI.Ch05.successive_getD_franklinUpMove_of_successive hsucc

theorem exercise5_not_IsFranklinDownBranchInput_of_IsFranklinUpBranchInput
    {lam : List Nat} (hup : PartI.Ch05.IsFranklinUpBranchInput lam) :
    ¬ PartI.Ch05.IsFranklinDownBranchInput lam :=
  PartI.Ch05.not_IsFranklinDownBranchInput_of_IsFranklinUpBranchInput hup

theorem exercise5_not_IsFranklinUpBranchInput_of_IsFranklinDownBranchInput
    {lam : List Nat} (hdown : PartI.Ch05.IsFranklinDownBranchInput lam) :
    ¬ PartI.Ch05.IsFranklinUpBranchInput lam :=
  PartI.Ch05.not_IsFranklinUpBranchInput_of_IsFranklinDownBranchInput hdown

theorem exercise5_IsFranklinUpBranchInput_lastPart_eq_pred {lam : List Nat}
    (hup : PartI.Ch05.IsFranklinUpBranchInput lam) :
    lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
      PartI.Ch05.numberOfParts lam - 1 :=
  PartI.Ch05.IsFranklinUpBranchInput.lastPart_eq_pred hup

theorem exercise5_IsFranklinUpBranchInput_of_strict_lastPart_eq_pred
    {lam : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hne : lam ≠ [])
    (hlast : lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
      PartI.Ch05.numberOfParts lam - 1) :
    PartI.Ch05.IsFranklinUpBranchInput lam :=
  PartI.Ch05.IsFranklinUpBranchInput_of_strict_lastPart_eq_pred hstrict hne hlast

theorem exercise5_IsFranklinUpBranchInput_iff_lastPart_eq_pred_of_strict
    {lam : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hne : lam ≠ []) :
    PartI.Ch05.IsFranklinUpBranchInput lam ↔
      lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
        PartI.Ch05.numberOfParts lam - 1 :=
  PartI.Ch05.IsFranklinUpBranchInput_iff_lastPart_eq_pred_of_strict hstrict hne

theorem exercise5_IsFranklinDownBranchInput_lastPart_gt_numberOfParts_add_one
    {lam : List Nat} (hdown : PartI.Ch05.IsFranklinDownBranchInput lam) :
    PartI.Ch05.numberOfParts lam + 1 <
      lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 :=
  PartI.Ch05.IsFranklinDownBranchInput.lastPart_gt_numberOfParts_add_one hdown

theorem exercise5_IsFranklinDownBranchInput_of_strict_lastPart_gt_numberOfParts_add_one
    {lam : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hne : lam ≠ [])
    (hlast : PartI.Ch05.numberOfParts lam + 1 <
      lam.getD (PartI.Ch05.numberOfParts lam - 1) 0) :
    PartI.Ch05.IsFranklinDownBranchInput lam :=
  PartI.Ch05.IsFranklinDownBranchInput_of_strict_lastPart_gt_numberOfParts_add_one
    hstrict hne hlast

theorem exercise5_IsFranklinDownBranchInput_iff_lastPart_gt_numberOfParts_add_one_of_strict
    {lam : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hne : lam ≠ []) :
    PartI.Ch05.IsFranklinDownBranchInput lam ↔
      PartI.Ch05.numberOfParts lam + 1 <
        lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 :=
  PartI.Ch05.IsFranklinDownBranchInput_iff_lastPart_gt_numberOfParts_add_one_of_strict
    hstrict hne

theorem exercise5_IsFranklinMovePair_franklinDownMove {lam : List Nat}
    (hdown : PartI.Ch05.IsFranklinDownBranchInput lam) :
    PartI.Ch05.IsFranklinMovePair lam (PartI.Ch05.franklinDownMove lam) :=
  PartI.Ch05.IsFranklinMovePair_franklinDownMove hdown

theorem exercise5_IsFranklinMovePair_franklinUpMove {lam : List Nat}
    (hup : PartI.Ch05.IsFranklinUpBranchInput lam) :
    PartI.Ch05.IsFranklinMovePair lam (PartI.Ch05.franklinUpMove lam) :=
  PartI.Ch05.IsFranklinMovePair_franklinUpMove hup

theorem exercise5_exists_IsFranklinMovePair_iff (lam : List Nat) :
    (∃ mu : List Nat, PartI.Ch05.IsFranklinMovePair lam mu) ↔
      PartI.Ch05.IsFranklinDownBranchInput lam ∨
        PartI.Ch05.IsFranklinUpBranchInput lam :=
  PartI.Ch05.exists_IsFranklinMovePair_iff lam

theorem exercise5_exists_IsFranklinMovePair_iff_lastPart_boundary_of_strict
    {lam : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hne : lam ≠ []) :
    (∃ mu : List Nat, PartI.Ch05.IsFranklinMovePair lam mu) ↔
      PartI.Ch05.numberOfParts lam + 1 <
          lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 ∨
        lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
          PartI.Ch05.numberOfParts lam - 1 :=
  PartI.Ch05.exists_IsFranklinMovePair_iff_lastPart_boundary_of_strict hstrict hne

theorem exercise5_not_exists_IsFranklinMovePair_iff_not_lastPart_boundary_of_strict
    {lam : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hne : lam ≠ []) :
    (¬ ∃ mu : List Nat, PartI.Ch05.IsFranklinMovePair lam mu) ↔
      ¬ PartI.Ch05.numberOfParts lam + 1 <
          lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 ∧
        lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 ≠
          PartI.Ch05.numberOfParts lam - 1 :=
  PartI.Ch05.not_exists_IsFranklinMovePair_iff_not_lastPart_boundary_of_strict
    hstrict hne

theorem exercise5_IsFranklinMovePair_iff_lastPart_boundary_of_strict
    {lam mu : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hne : lam ≠ []) :
    PartI.Ch05.IsFranklinMovePair lam mu ↔
      (PartI.Ch05.numberOfParts lam + 1 <
          lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 ∧
        mu = PartI.Ch05.franklinDownMove lam) ∨
      (lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
          PartI.Ch05.numberOfParts lam - 1 ∧
        mu = PartI.Ch05.franklinUpMove lam) :=
  PartI.Ch05.IsFranklinMovePair_iff_lastPart_boundary_of_strict hstrict hne

theorem exercise5_IsFranklinMovePair_lastPart_cases_of_strict
    {lam : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hne : lam ≠ []) :
    (lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 <
        PartI.Ch05.numberOfParts lam - 1 ∧
        ¬ ∃ mu : List Nat, PartI.Ch05.IsFranklinMovePair lam mu) ∨
      (lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
          PartI.Ch05.numberOfParts lam - 1 ∧
        PartI.Ch05.IsFranklinMovePair lam (PartI.Ch05.franklinUpMove lam)) ∨
      (((lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
            PartI.Ch05.numberOfParts lam) ∨
          lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
            PartI.Ch05.numberOfParts lam + 1) ∧
        ¬ ∃ mu : List Nat, PartI.Ch05.IsFranklinMovePair lam mu) ∨
      (PartI.Ch05.numberOfParts lam + 1 <
          lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 ∧
        PartI.Ch05.IsFranklinMovePair lam (PartI.Ch05.franklinDownMove lam)) :=
  PartI.Ch05.IsFranklinMovePair_lastPart_cases_of_strict hstrict hne

theorem exercise5_IsFranklinMovePair_eq_of_left {lam mu nu : List Nat}
    (hmu : PartI.Ch05.IsFranklinMovePair lam mu)
    (hnu : PartI.Ch05.IsFranklinMovePair lam nu) :
    mu = nu :=
  PartI.Ch05.IsFranklinMovePair.eq_of_left hmu hnu

theorem exercise5_IsFranklinMovePair_symm_of_strict {lam mu : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hpair : PartI.Ch05.IsFranklinMovePair lam mu) :
    PartI.Ch05.IsFranklinMovePair mu lam :=
  PartI.Ch05.IsFranklinMovePair.symm_of_strict hstrict hpair

theorem exercise5_IsFranklinMovePair_comm_iff_of_strict {lam mu : List Nat}
    (hlam : PartI.Ch05.IsStrictPartition lam)
    (hmu : PartI.Ch05.IsStrictPartition mu) :
    PartI.Ch05.IsFranklinMovePair lam mu ↔
      PartI.Ch05.IsFranklinMovePair mu lam :=
  PartI.Ch05.IsFranklinMovePair_comm_iff_of_strict hlam hmu

theorem exercise5_IsFranklinMovePair_eq_of_right_of_strict {lam mu nu : List Nat}
    (hlam : PartI.Ch05.IsStrictPartition lam)
    (hmu : PartI.Ch05.IsStrictPartition mu)
    (hpair_lam : PartI.Ch05.IsFranklinMovePair lam nu)
    (hpair_mu : PartI.Ch05.IsFranklinMovePair mu nu) :
    lam = mu :=
  PartI.Ch05.IsFranklinMovePair.eq_of_right_of_strict hlam hmu hpair_lam hpair_mu

theorem exercise5_IsFranklinMovePair_strict_weight_sign {lam mu : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hpair : PartI.Ch05.IsFranklinMovePair lam mu) :
    PartI.Ch05.IsStrictPartition mu ∧
      partitionWeight mu = partitionWeight lam ∧
      PartI.Ch05.partSign mu = - PartI.Ch05.partSign lam :=
  PartI.Ch05.IsFranklinMovePair.strict_weight_sign hstrict hpair

theorem exercise5_IsFranklinMovePair_not_self_of_strict {lam : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam) :
    ¬ PartI.Ch05.IsFranklinMovePair lam lam :=
  PartI.Ch05.IsFranklinMovePair.not_self_of_strict hstrict

theorem exercise5_IsFranklinMovePair_ne_of_strict {lam mu : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hpair : PartI.Ch05.IsFranklinMovePair lam mu) :
    mu ≠ lam :=
  PartI.Ch05.IsFranklinMovePair.ne_of_strict hstrict hpair

theorem exercise5_IsFranklinMovePair_involution_package {lam mu : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hpair : PartI.Ch05.IsFranklinMovePair lam mu) :
    PartI.Ch05.IsStrictPartition mu ∧
      PartI.Ch05.IsFranklinMovePair mu lam ∧
      partitionWeight mu = partitionWeight lam ∧
      PartI.Ch05.partSign mu = - PartI.Ch05.partSign lam ∧
      mu ≠ lam :=
  PartI.Ch05.IsFranklinMovePair.involution_package hstrict hpair

theorem exercise5_IsFranklinMovePair_partSign_add_eq_zero {lam mu : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hpair : PartI.Ch05.IsFranklinMovePair lam mu) :
    PartI.Ch05.partSign lam + PartI.Ch05.partSign mu = 0 :=
  PartI.Ch05.IsFranklinMovePair.partSign_add_eq_zero hstrict hpair

theorem exercise5_IsFranklinMovePair_partSign_add_eq_zero' {lam mu : List Nat}
    (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hpair : PartI.Ch05.IsFranklinMovePair lam mu) :
    PartI.Ch05.partSign mu + PartI.Ch05.partSign lam = 0 :=
  PartI.Ch05.IsFranklinMovePair.partSign_add_eq_zero' hstrict hpair

theorem exercise5_not_IsFranklinMovePair_of_IsPentagonalFixedShape_left
    {lam mu : List Nat} (hfixed : PartI.Ch05.IsPentagonalFixedShape lam) :
    ¬ PartI.Ch05.IsFranklinMovePair lam mu :=
  PartI.Ch05.not_IsFranklinMovePair_of_IsPentagonalFixedShape_left hfixed

theorem exercise5_not_exists_IsFranklinMovePair_of_IsPentagonalFixedShape_left
    {lam : List Nat} (hfixed : PartI.Ch05.IsPentagonalFixedShape lam) :
    ¬ ∃ mu : List Nat, PartI.Ch05.IsFranklinMovePair lam mu :=
  PartI.Ch05.not_exists_IsFranklinMovePair_of_IsPentagonalFixedShape_left hfixed

theorem exercise5_not_IsFranklinMovePair_of_middle_lastPart_and_successive
    {lam mu : List Nat} (hlen : 0 < PartI.Ch05.numberOfParts lam)
    (hlast :
      lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
          PartI.Ch05.numberOfParts lam ∨
        lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
          PartI.Ch05.numberOfParts lam + 1)
    (hsucc : ∀ r, r + 1 < PartI.Ch05.numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    ¬ PartI.Ch05.IsFranklinMovePair lam mu :=
  PartI.Ch05.not_IsFranklinMovePair_of_middle_lastPart_and_successive
    hlen hlast hsucc

theorem exercise5_not_exists_IsFranklinMovePair_of_middle_lastPart_and_successive
    {lam : List Nat} (hlen : 0 < PartI.Ch05.numberOfParts lam)
    (hlast :
      lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
          PartI.Ch05.numberOfParts lam ∨
        lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
          PartI.Ch05.numberOfParts lam + 1)
    (hsucc : ∀ r, r + 1 < PartI.Ch05.numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    ¬ ∃ mu : List Nat, PartI.Ch05.IsFranklinMovePair lam mu :=
  PartI.Ch05.not_exists_IsFranklinMovePair_of_middle_lastPart_and_successive
    hlen hlast hsucc

theorem exercise5_IsFranklinMovePair_successive_lastPart_cases_of_strict
    {lam : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hne : lam ≠ [])
    (hsucc : ∀ r, r + 1 < PartI.Ch05.numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    (lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 <
        PartI.Ch05.numberOfParts lam - 1 ∧
        ¬ ∃ mu : List Nat, PartI.Ch05.IsFranklinMovePair lam mu) ∨
      (lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
          PartI.Ch05.numberOfParts lam - 1 ∧
        PartI.Ch05.IsFranklinMovePair lam (PartI.Ch05.franklinUpMove lam)) ∨
      (PartI.Ch05.IsPentagonalFixedShape lam ∧
        ¬ ∃ mu : List Nat, PartI.Ch05.IsFranklinMovePair lam mu) ∨
      (PartI.Ch05.numberOfParts lam + 1 <
          lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 ∧
        PartI.Ch05.IsFranklinMovePair lam (PartI.Ch05.franklinDownMove lam)) :=
  PartI.Ch05.IsFranklinMovePair_successive_lastPart_cases_of_strict
    hstrict hne hsucc

theorem exercise5_not_exists_IsFranklinMovePair_iff_low_or_fixed_of_successive_of_strict
    {lam : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hne : lam ≠ [])
    (hsucc : ∀ r, r + 1 < PartI.Ch05.numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    (¬ ∃ mu : List Nat, PartI.Ch05.IsFranklinMovePair lam mu) ↔
      lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 <
          PartI.Ch05.numberOfParts lam - 1 ∨
        PartI.Ch05.IsPentagonalFixedShape lam :=
  PartI.Ch05.not_exists_IsFranklinMovePair_iff_low_or_fixed_of_successive_of_strict
    hstrict hne hsucc

theorem exercise5_exists_IsFranklinMovePair_iff_not_low_not_fixed_of_successive_of_strict
    {lam : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hne : lam ≠ [])
    (hsucc : ∀ r, r + 1 < PartI.Ch05.numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    (∃ mu : List Nat, PartI.Ch05.IsFranklinMovePair lam mu) ↔
      ¬ lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 <
          PartI.Ch05.numberOfParts lam - 1 ∧
        ¬ PartI.Ch05.IsPentagonalFixedShape lam :=
  PartI.Ch05.exists_IsFranklinMovePair_iff_not_low_not_fixed_of_successive_of_strict
    hstrict hne hsucc

theorem exercise5_exists_unique_IsFranklinMovePair_of_not_low_not_fixed_of_successive_of_strict
    {lam : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hne : lam ≠ [])
    (hsucc : ∀ r, r + 1 < PartI.Ch05.numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0)
    (hnotLow : ¬ lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 <
      PartI.Ch05.numberOfParts lam - 1)
    (hnotFixed : ¬ PartI.Ch05.IsPentagonalFixedShape lam) :
    ∃! mu : List Nat, PartI.Ch05.IsFranklinMovePair lam mu :=
  PartI.Ch05.exists_unique_IsFranklinMovePair_of_not_low_not_fixed_of_successive_of_strict
    hstrict hne hsucc hnotLow hnotFixed

theorem exercise5_exists_IsFranklinMovePair_involution_package_of_not_low_not_fixed_of_successive_of_strict
    {lam : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hne : lam ≠ [])
    (hsucc : ∀ r, r + 1 < PartI.Ch05.numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0)
    (hnotLow : ¬ lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 <
      PartI.Ch05.numberOfParts lam - 1)
    (hnotFixed : ¬ PartI.Ch05.IsPentagonalFixedShape lam) :
    ∃ mu : List Nat,
      PartI.Ch05.IsFranklinMovePair lam mu ∧
        PartI.Ch05.IsStrictPartition mu ∧
        PartI.Ch05.IsFranklinMovePair mu lam ∧
        partitionWeight mu = partitionWeight lam ∧
        PartI.Ch05.partSign mu = - PartI.Ch05.partSign lam ∧
        mu ≠ lam :=
  PartI.Ch05.exists_IsFranklinMovePair_involution_package_of_not_low_not_fixed_of_successive_of_strict
    hstrict hne hsucc hnotLow hnotFixed

theorem exercise5_IsFranklinMovePair_active_target_cases_of_not_low_not_fixed_of_successive_of_strict
    {lam mu : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hne : lam ≠ [])
    (hsucc : ∀ r, r + 1 < PartI.Ch05.numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0)
    (hnotLow : ¬ lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 <
      PartI.Ch05.numberOfParts lam - 1)
    (hnotFixed : ¬ PartI.Ch05.IsPentagonalFixedShape lam)
    (hpair : PartI.Ch05.IsFranklinMovePair lam mu) :
    (lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
        PartI.Ch05.numberOfParts lam - 1 ∧
        mu = PartI.Ch05.franklinUpMove lam) ∨
      (PartI.Ch05.numberOfParts lam + 1 <
        lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 ∧
        mu = PartI.Ch05.franklinDownMove lam) :=
  PartI.Ch05.IsFranklinMovePair_active_target_cases_of_not_low_not_fixed_of_successive_of_strict
    hstrict hne hsucc hnotLow hnotFixed hpair

theorem exercise5_not_IsPentagonalFixedShape_right_of_IsFranklinMovePair
    {lam mu : List Nat} (hstrict : PartI.Ch05.IsStrictPartition lam)
    (hpair : PartI.Ch05.IsFranklinMovePair lam mu) :
    ¬ PartI.Ch05.IsPentagonalFixedShape mu :=
  PartI.Ch05.not_IsPentagonalFixedShape_right_of_IsFranklinMovePair hstrict hpair

theorem exercise5_append_numberOfParts_lastPart (mu : List Nat) :
    (mu ++ [PartI.Ch05.numberOfParts mu]).getD
        (PartI.Ch05.numberOfParts (mu ++ [PartI.Ch05.numberOfParts mu]) - 1) 0 =
      PartI.Ch05.numberOfParts (mu ++ [PartI.Ch05.numberOfParts mu]) - 1 :=
  PartI.Ch05.append_numberOfParts_lastPart mu

/-- Exercise (Chapter 5 style): the staircase of height 3 shifted by 1 is [4,3,2]. -/
theorem exercise5_shiftedStaircasePartition_three_one :
    PartI.Ch05.shiftedStaircasePartition 1 3 = [4, 3, 2] :=
  PartI.Ch05.shiftedStaircasePartition_three_one

/-- Exercise (Chapter 5 style): shifted staircase partitions have `n` parts. -/
theorem exercise5_numberOfParts_shiftedStaircasePartition (d n : Nat) :
    PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d n) = n :=
  PartI.Ch05.numberOfParts_shiftedStaircasePartition d n

theorem exercise5_shiftedStaircasePartition_getD_of_lt {d n r : Nat} (hr : r < n) :
    (PartI.Ch05.shiftedStaircasePartition d n).getD r 0 = n - r + d :=
  PartI.Ch05.shiftedStaircasePartition_getD_of_lt hr

theorem exercise5_shiftedStaircasePartition_lastPart (d n : Nat) (hn : 0 < n) :
    (PartI.Ch05.shiftedStaircasePartition d n).getD (n - 1) 0 = 1 + d :=
  PartI.Ch05.shiftedStaircasePartition_lastPart d n hn

theorem exercise5_shiftedStaircasePartition_succ_append (d n : Nat) :
    PartI.Ch05.shiftedStaircasePartition d (n + 1) =
      PartI.Ch05.shiftedStaircasePartition (d + 1) n ++ [1 + d] :=
  PartI.Ch05.shiftedStaircasePartition_succ_append d n

theorem exercise5_shiftParts_shiftedStaircasePartition (a d n : Nat) :
    PartI.Ch05.shiftParts a (PartI.Ch05.shiftedStaircasePartition d n) =
      PartI.Ch05.shiftedStaircasePartition (d + a) n :=
  PartI.Ch05.shiftParts_shiftedStaircasePartition a d n

theorem exercise5_decrementParts_shiftedStaircasePartition_succ_offset (d n : Nat) :
    PartI.Ch05.decrementParts (PartI.Ch05.shiftedStaircasePartition (d + 1) n) =
      PartI.Ch05.shiftedStaircasePartition d n :=
  PartI.Ch05.decrementParts_shiftedStaircasePartition_succ_offset d n

theorem exercise5_franklinUpMove_shiftedStaircasePartition_succ (d n : Nat) :
    PartI.Ch05.franklinUpMove (PartI.Ch05.shiftedStaircasePartition d (n + 1)) =
      PartI.Ch05.shiftedStaircasePartition (d + 2) n :=
  PartI.Ch05.franklinUpMove_shiftedStaircasePartition_succ d n

theorem exercise5_franklinUpMove_shiftedStaircasePartition_of_pos_height
    {d k : Nat} (hk : 0 < k) :
    PartI.Ch05.franklinUpMove (PartI.Ch05.shiftedStaircasePartition d k) =
      PartI.Ch05.shiftedStaircasePartition (d + 2) (k - 1) :=
  PartI.Ch05.franklinUpMove_shiftedStaircasePartition_of_pos_height hk

theorem exercise5_franklinDownMove_shiftedStaircasePartition_succ_offset
    (d n : Nat) :
    PartI.Ch05.franklinDownMove (PartI.Ch05.shiftedStaircasePartition (d + 1) n) =
      PartI.Ch05.shiftedStaircasePartition d n ++ [n] :=
  PartI.Ch05.franklinDownMove_shiftedStaircasePartition_succ_offset d n

theorem exercise5_franklinDownMove_shiftedStaircasePartition_of_pos_offset
    {d k : Nat} (hd : 0 < d) :
    PartI.Ch05.franklinDownMove (PartI.Ch05.shiftedStaircasePartition d k) =
      PartI.Ch05.shiftedStaircasePartition (d - 1) k ++ [k] :=
  PartI.Ch05.franklinDownMove_shiftedStaircasePartition_of_pos_offset hd

theorem exercise5_franklinDownMove_hgt_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    (∀ n, n ∈ PartI.Ch05.shiftedStaircasePartition d k →
      PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) + 1 < n) ↔
      k < d :=
  PartI.Ch05.franklinDownMove_hgt_shiftedStaircasePartition_iff hk

theorem exercise5_not_franklinDownMove_hgt_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    ¬ (∀ n, n ∈ PartI.Ch05.shiftedStaircasePartition d k →
      PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) + 1 < n) ↔
      d ≤ k :=
  PartI.Ch05.not_franklinDownMove_hgt_shiftedStaircasePartition_iff hk

theorem exercise5_eq_shiftedStaircasePartition_of_getD {lam : List Nat} {d n : Nat}
    (hlen : PartI.Ch05.numberOfParts lam = n)
    (hget : ∀ r, r < n → lam.getD r 0 = n - r + d) :
    lam = PartI.Ch05.shiftedStaircasePartition d n :=
  PartI.Ch05.eq_shiftedStaircasePartition_of_getD hlen hget

theorem exercise5_partParity_shiftedStaircasePartition (d n : Nat) :
    PartI.Ch05.partParity (PartI.Ch05.shiftedStaircasePartition d n) = n % 2 :=
  PartI.Ch05.partParity_shiftedStaircasePartition d n

theorem exercise5_partSign_shiftedStaircasePartition (d n : Nat) :
    PartI.Ch05.partSign (PartI.Ch05.shiftedStaircasePartition d n) =
      if n % 2 = 0 then 1 else -1 :=
  PartI.Ch05.partSign_shiftedStaircasePartition d n

/-- Exercise (Chapter 5 style): weight of a shifted staircase is triangular + d*n. -/
theorem exercise5_partitionWeight_shiftedStaircasePartition (d n : Nat) :
    partitionWeight (PartI.Ch05.shiftedStaircasePartition d n) = triangular n + d * n :=
  PartI.Ch05.partitionWeight_shiftedStaircasePartition d n

/-- Exercise (Chapter 5 style): every shifted staircase partition is strict. -/
theorem exercise5_IsStrictPartition_shiftedStaircasePartition (d n : Nat) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.shiftedStaircasePartition d n) :=
  PartI.Ch05.IsStrictPartition_shiftedStaircasePartition d n

/-- Exercise (Chapter 5 style): the lower pentagonal partition of height 3 is [5,4,3]. -/
theorem exercise5_lowerPentagonalPartition_three :
    PartI.Ch05.lowerPentagonalPartition 3 = [5, 4, 3] :=
  PartI.Ch05.lowerPentagonalPartition_three

/-- Exercise (Chapter 5 style): the upper pentagonal partition of height 3 is [6,5,4]. -/
theorem exercise5_upperPentagonalPartition_three :
    PartI.Ch05.upperPentagonalPartition 3 = [6, 5, 4] :=
  PartI.Ch05.upperPentagonalPartition_three

theorem exercise5_eq_lowerPentagonalPartition_of_getD {lam : List Nat} {k : Nat}
    (hlen : PartI.Ch05.numberOfParts lam = k)
    (hget : ∀ r, r < k → lam.getD r 0 = k - r + (k - 1)) :
    lam = PartI.Ch05.lowerPentagonalPartition k :=
  PartI.Ch05.eq_lowerPentagonalPartition_of_getD hlen hget

theorem exercise5_eq_upperPentagonalPartition_of_getD {lam : List Nat} {k : Nat}
    (hlen : PartI.Ch05.numberOfParts lam = k)
    (hget : ∀ r, r < k → lam.getD r 0 = k - r + k) :
    lam = PartI.Ch05.upperPentagonalPartition k :=
  PartI.Ch05.eq_upperPentagonalPartition_of_getD hlen hget

theorem exercise5_eq_lowerPentagonalPartition_of_firstPart_and_successive
    {lam : List Nat} {k : Nat}
    (hlen : PartI.Ch05.numberOfParts lam = k)
    (hfirst : lam.getD 0 0 = 2 * k - 1)
    (hsucc : ∀ r, r + 1 < k → lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    lam = PartI.Ch05.lowerPentagonalPartition k :=
  PartI.Ch05.eq_lowerPentagonalPartition_of_firstPart_and_successive hlen hfirst hsucc

theorem exercise5_eq_upperPentagonalPartition_of_firstPart_and_successive
    {lam : List Nat} {k : Nat}
    (hlen : PartI.Ch05.numberOfParts lam = k)
    (hfirst : lam.getD 0 0 = 2 * k)
    (hsucc : ∀ r, r + 1 < k → lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    lam = PartI.Ch05.upperPentagonalPartition k :=
  PartI.Ch05.eq_upperPentagonalPartition_of_firstPart_and_successive hlen hfirst hsucc

theorem exercise5_getD_zero_eq_last_add_of_successive {lam : List Nat} {k : Nat}
    (hk : 0 < k)
    (hsucc : ∀ r, r + 1 < k → lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    lam.getD 0 0 = lam.getD (k - 1) 0 + (k - 1) :=
  PartI.Ch05.getD_zero_eq_last_add_of_successive hk hsucc

theorem exercise5_eq_lowerPentagonalPartition_of_lastPart_and_successive
    {lam : List Nat} {k : Nat}
    (hk : 0 < k) (hlen : PartI.Ch05.numberOfParts lam = k)
    (hlast : lam.getD (k - 1) 0 = k)
    (hsucc : ∀ r, r + 1 < k → lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    lam = PartI.Ch05.lowerPentagonalPartition k :=
  PartI.Ch05.eq_lowerPentagonalPartition_of_lastPart_and_successive
    hk hlen hlast hsucc

theorem exercise5_eq_upperPentagonalPartition_of_lastPart_and_successive
    {lam : List Nat} {k : Nat}
    (hk : 0 < k) (hlen : PartI.Ch05.numberOfParts lam = k)
    (hlast : lam.getD (k - 1) 0 = k + 1)
    (hsucc : ∀ r, r + 1 < k → lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    lam = PartI.Ch05.upperPentagonalPartition k :=
  PartI.Ch05.eq_upperPentagonalPartition_of_lastPart_and_successive
    hk hlen hlast hsucc

theorem exercise5_IsPentagonalFixedShape_of_lastPart_eq_numberOfParts_or_add_one
    {lam : List Nat} (hlen : 0 < PartI.Ch05.numberOfParts lam)
    (hlast :
      lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 = PartI.Ch05.numberOfParts lam ∨
        lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
          PartI.Ch05.numberOfParts lam + 1)
    (hsucc : ∀ r, r + 1 < PartI.Ch05.numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    PartI.Ch05.IsPentagonalFixedShape lam :=
  PartI.Ch05.IsPentagonalFixedShape_of_lastPart_eq_numberOfParts_or_add_one
    hlen hlast hsucc

theorem exercise5_lowerPentagonalPartition_getD_of_lt {k r : Nat} (hr : r < k) :
    (PartI.Ch05.lowerPentagonalPartition k).getD r 0 = k - r + (k - 1) :=
  PartI.Ch05.lowerPentagonalPartition_getD_of_lt hr

theorem exercise5_upperPentagonalPartition_getD_of_lt {k r : Nat} (hr : r < k) :
    (PartI.Ch05.upperPentagonalPartition k).getD r 0 = k - r + k :=
  PartI.Ch05.upperPentagonalPartition_getD_of_lt hr

theorem exercise5_lowerPentagonalPartition_lastPart (k : Nat) (hk : 0 < k) :
    (PartI.Ch05.lowerPentagonalPartition k).getD (k - 1) 0 = k :=
  PartI.Ch05.lowerPentagonalPartition_lastPart k hk

theorem exercise5_upperPentagonalPartition_lastPart (k : Nat) (hk : 0 < k) :
    (PartI.Ch05.upperPentagonalPartition k).getD (k - 1) 0 = k + 1 :=
  PartI.Ch05.upperPentagonalPartition_lastPart k hk

theorem exercise5_lowerPentagonalPartition_firstPart (k : Nat) (hk : 0 < k) :
    (PartI.Ch05.lowerPentagonalPartition k).getD 0 0 = 2 * k - 1 :=
  PartI.Ch05.lowerPentagonalPartition_firstPart k hk

theorem exercise5_upperPentagonalPartition_firstPart (k : Nat) (hk : 0 < k) :
    (PartI.Ch05.upperPentagonalPartition k).getD 0 0 = 2 * k :=
  PartI.Ch05.upperPentagonalPartition_firstPart k hk

theorem exercise5_lowerPentagonalPartition_successive_getD
    (k r : Nat) (hr : r + 1 < k) :
    (PartI.Ch05.lowerPentagonalPartition k).getD (r + 1) 0 + 1 =
      (PartI.Ch05.lowerPentagonalPartition k).getD r 0 :=
  PartI.Ch05.lowerPentagonalPartition_successive_getD k r hr

theorem exercise5_upperPentagonalPartition_successive_getD
    (k r : Nat) (hr : r + 1 < k) :
    (PartI.Ch05.upperPentagonalPartition k).getD (r + 1) 0 + 1 =
      (PartI.Ch05.upperPentagonalPartition k).getD r 0 :=
  PartI.Ch05.upperPentagonalPartition_successive_getD k r hr

/-- Exercise (Chapter 5 style): lower pentagonal partitions have pentagonal weight. -/
theorem exercise5_partitionWeight_lowerPentagonalPartition (k : Nat) :
    partitionWeight (PartI.Ch05.lowerPentagonalPartition k) = pentagonalNumber k :=
  PartI.Ch05.partitionWeight_lowerPentagonalPartition k

/-- Exercise (Chapter 5 style): upper pentagonal partitions have upper pentagonal weight. -/
theorem exercise5_partitionWeight_upperPentagonalPartition (k : Nat) :
    partitionWeight (PartI.Ch05.upperPentagonalPartition k) = PartI.Ch05.upperPentagonalNumber k :=
  PartI.Ch05.partitionWeight_upperPentagonalPartition k

/-- Exercise (Chapter 5 style): formula for the upper pentagonal number. -/
theorem exercise5_two_mul_upperPentagonalNumber (k : Nat) :
    2 * PartI.Ch05.upperPentagonalNumber k = k * (3 * k + 1) :=
  PartI.Ch05.two_mul_upperPentagonalNumber k

/-- Exercise (Chapter 5 style): lower pentagonal partitions are strict. -/
theorem exercise5_IsStrictPartition_lowerPentagonalPartition (k : Nat) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.lowerPentagonalPartition k) :=
  PartI.Ch05.IsStrictPartition_lowerPentagonalPartition k

/-- Exercise (Chapter 5 style): upper pentagonal partitions are strict. -/
theorem exercise5_IsStrictPartition_upperPentagonalPartition (k : Nat) :
    PartI.Ch05.IsStrictPartition (PartI.Ch05.upperPentagonalPartition k) :=
  PartI.Ch05.IsStrictPartition_upperPentagonalPartition k

theorem exercise5_IsPentagonalFixedShape_lower (k : Nat) (hk : 0 < k) :
    PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.lowerPentagonalPartition k) :=
  PartI.Ch05.IsPentagonalFixedShape_lower k hk

theorem exercise5_IsPentagonalFixedShape_upper (k : Nat) (hk : 0 < k) :
    PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.upperPentagonalPartition k) :=
  PartI.Ch05.IsPentagonalFixedShape_upper k hk

theorem exercise5_IsStrictPartition_of_IsPentagonalFixedShape {lam : List Nat}
    (hfixed : PartI.Ch05.IsPentagonalFixedShape lam) :
    PartI.Ch05.IsStrictPartition lam :=
  PartI.Ch05.IsStrictPartition_of_IsPentagonalFixedShape hfixed

theorem exercise5_numberOfParts_pos_of_IsPentagonalFixedShape {lam : List Nat}
    (hfixed : PartI.Ch05.IsPentagonalFixedShape lam) :
    0 < PartI.Ch05.numberOfParts lam :=
  PartI.Ch05.numberOfParts_pos_of_IsPentagonalFixedShape hfixed

/-- Exercise (Chapter 5 style): lower pentagonal partitions have k parts. -/
theorem exercise5_numberOfParts_lowerPentagonalPartition (k : Nat) :
    PartI.Ch05.numberOfParts (PartI.Ch05.lowerPentagonalPartition k) = k :=
  PartI.Ch05.numberOfParts_lowerPentagonalPartition k

/-- Exercise (Chapter 5 style): upper pentagonal partitions have k parts. -/
theorem exercise5_numberOfParts_upperPentagonalPartition (k : Nat) :
    PartI.Ch05.numberOfParts (PartI.Ch05.upperPentagonalPartition k) = k :=
  PartI.Ch05.numberOfParts_upperPentagonalPartition k

theorem exercise5_lowerPentagonalPartition_lastPart_mem (k : Nat) (hk : 0 < k) :
    k ∈ PartI.Ch05.lowerPentagonalPartition k :=
  PartI.Ch05.lowerPentagonalPartition_lastPart_mem k hk

theorem exercise5_upperPentagonalPartition_lastPart_mem (k : Nat) (hk : 0 < k) :
    k + 1 ∈ PartI.Ch05.upperPentagonalPartition k :=
  PartI.Ch05.upperPentagonalPartition_lastPart_mem k hk

theorem exercise5_lowerPentagonalPartition_lastPart_eq_numberOfParts
    (k : Nat) (hk : 0 < k) :
    (PartI.Ch05.lowerPentagonalPartition k).getD
      (PartI.Ch05.numberOfParts (PartI.Ch05.lowerPentagonalPartition k) - 1) 0 =
        PartI.Ch05.numberOfParts (PartI.Ch05.lowerPentagonalPartition k) :=
  PartI.Ch05.lowerPentagonalPartition_lastPart_eq_numberOfParts k hk

theorem exercise5_upperPentagonalPartition_lastPart_eq_numberOfParts_add_one
    (k : Nat) (hk : 0 < k) :
    (PartI.Ch05.upperPentagonalPartition k).getD
      (PartI.Ch05.numberOfParts (PartI.Ch05.upperPentagonalPartition k) - 1) 0 =
        PartI.Ch05.numberOfParts (PartI.Ch05.upperPentagonalPartition k) + 1 :=
  PartI.Ch05.upperPentagonalPartition_lastPart_eq_numberOfParts_add_one k hk

theorem exercise5_not_franklinDownMove_hgt_lowerPentagonalPartition
    (k : Nat) (hk : 0 < k) :
    ¬ (∀ n, n ∈ PartI.Ch05.lowerPentagonalPartition k →
      PartI.Ch05.numberOfParts (PartI.Ch05.lowerPentagonalPartition k) + 1 < n) :=
  PartI.Ch05.not_franklinDownMove_hgt_lowerPentagonalPartition k hk

theorem exercise5_not_franklinDownMove_hgt_upperPentagonalPartition
    (k : Nat) (hk : 0 < k) :
    ¬ (∀ n, n ∈ PartI.Ch05.upperPentagonalPartition k →
      PartI.Ch05.numberOfParts (PartI.Ch05.upperPentagonalPartition k) + 1 < n) :=
  PartI.Ch05.not_franklinDownMove_hgt_upperPentagonalPartition k hk

theorem exercise5_not_lowerPentagonalPartition_eq_append_numberOfParts
    (k : Nat) (hk : 0 < k) :
    ¬ ∃ mu : List Nat,
      PartI.Ch05.lowerPentagonalPartition k = mu ++ [PartI.Ch05.numberOfParts mu] :=
  PartI.Ch05.not_lowerPentagonalPartition_eq_append_numberOfParts k hk

theorem exercise5_not_upperPentagonalPartition_eq_append_numberOfParts
    (k : Nat) (hk : 0 < k) :
    ¬ ∃ mu : List Nat,
      PartI.Ch05.upperPentagonalPartition k = mu ++ [PartI.Ch05.numberOfParts mu] :=
  PartI.Ch05.not_upperPentagonalPartition_eq_append_numberOfParts k hk

theorem exercise5_not_franklinDownMove_hgt_of_IsPentagonalFixedShape {lam : List Nat}
    (hfixed : PartI.Ch05.IsPentagonalFixedShape lam) :
    ¬ (∀ n, n ∈ lam → PartI.Ch05.numberOfParts lam + 1 < n) :=
  PartI.Ch05.not_franklinDownMove_hgt_of_IsPentagonalFixedShape hfixed

theorem exercise5_not_eq_append_numberOfParts_of_IsPentagonalFixedShape {lam : List Nat}
    (hfixed : PartI.Ch05.IsPentagonalFixedShape lam) :
    ¬ ∃ mu : List Nat, lam = mu ++ [PartI.Ch05.numberOfParts mu] :=
  PartI.Ch05.not_eq_append_numberOfParts_of_IsPentagonalFixedShape hfixed

theorem exercise5_not_IsFranklinDownBranchInput_of_IsPentagonalFixedShape
    {lam : List Nat} (hfixed : PartI.Ch05.IsPentagonalFixedShape lam) :
    ¬ PartI.Ch05.IsFranklinDownBranchInput lam :=
  PartI.Ch05.not_IsFranklinDownBranchInput_of_IsPentagonalFixedShape hfixed

theorem exercise5_not_IsFranklinUpBranchInput_of_IsPentagonalFixedShape
    {lam : List Nat} (hfixed : PartI.Ch05.IsPentagonalFixedShape lam) :
    ¬ PartI.Ch05.IsFranklinUpBranchInput lam :=
  PartI.Ch05.not_IsFranklinUpBranchInput_of_IsPentagonalFixedShape hfixed

theorem exercise5_lastPart_eq_numberOfParts_or_add_one_of_IsPentagonalFixedShape
    {lam : List Nat} (hfixed : PartI.Ch05.IsPentagonalFixedShape lam) :
    lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 = PartI.Ch05.numberOfParts lam ∨
      lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
        PartI.Ch05.numberOfParts lam + 1 :=
  PartI.Ch05.lastPart_eq_numberOfParts_or_add_one_of_IsPentagonalFixedShape hfixed

theorem exercise5_successive_getD_of_IsPentagonalFixedShape {lam : List Nat}
    (hfixed : PartI.Ch05.IsPentagonalFixedShape lam) :
    ∀ r, r + 1 < PartI.Ch05.numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0 :=
  PartI.Ch05.successive_getD_of_IsPentagonalFixedShape hfixed

theorem exercise5_IsPentagonalFixedShape_iff_lastPart_boundary_and_successive
    {lam : List Nat} (hlen : 0 < PartI.Ch05.numberOfParts lam) :
    PartI.Ch05.IsPentagonalFixedShape lam ↔
      (lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
          PartI.Ch05.numberOfParts lam ∨
        lam.getD (PartI.Ch05.numberOfParts lam - 1) 0 =
          PartI.Ch05.numberOfParts lam + 1) ∧
        ∀ r, r + 1 < PartI.Ch05.numberOfParts lam →
          lam.getD (r + 1) 0 + 1 = lam.getD r 0 :=
  PartI.Ch05.IsPentagonalFixedShape_iff_lastPart_boundary_and_successive hlen

theorem exercise5_IsPentagonalFixedShape_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.shiftedStaircasePartition d k) ↔
      d = k - 1 ∨ d = k :=
  PartI.Ch05.IsPentagonalFixedShape_shiftedStaircasePartition_iff hk

theorem exercise5_not_IsPentagonalFixedShape_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    ¬ PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.shiftedStaircasePartition d k) ↔
      d ≠ k - 1 ∧ d ≠ k :=
  PartI.Ch05.not_IsPentagonalFixedShape_shiftedStaircasePartition_iff hk

theorem exercise5_shiftedStaircasePartition_eq_append_numberOfParts_iff
    {d k : Nat} (hk : 0 < k) :
    (∃ mu : List Nat,
      PartI.Ch05.shiftedStaircasePartition d k =
        mu ++ [PartI.Ch05.numberOfParts mu]) ↔
      d + 2 = k :=
  PartI.Ch05.shiftedStaircasePartition_eq_append_numberOfParts_iff hk

theorem exercise5_IsFranklinUpBranchInput_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    PartI.Ch05.IsFranklinUpBranchInput (PartI.Ch05.shiftedStaircasePartition d k) ↔
      d + 2 = k :=
  PartI.Ch05.IsFranklinUpBranchInput_shiftedStaircasePartition_iff hk

theorem exercise5_IsFranklinDownBranchInput_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    PartI.Ch05.IsFranklinDownBranchInput (PartI.Ch05.shiftedStaircasePartition d k) ↔
      k < d :=
  PartI.Ch05.IsFranklinDownBranchInput_shiftedStaircasePartition_iff hk

theorem exercise5_exists_IsFranklinMovePair_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    (∃ mu : List Nat,
      PartI.Ch05.IsFranklinMovePair (PartI.Ch05.shiftedStaircasePartition d k) mu) ↔
      d + 2 = k ∨ k < d :=
  PartI.Ch05.exists_IsFranklinMovePair_shiftedStaircasePartition_iff hk

theorem exercise5_not_exists_IsFranklinMovePair_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    (¬ ∃ mu : List Nat,
      PartI.Ch05.IsFranklinMovePair (PartI.Ch05.shiftedStaircasePartition d k) mu) ↔
      PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.shiftedStaircasePartition d k) ∨
        d + 2 < k :=
  PartI.Ch05.not_exists_IsFranklinMovePair_shiftedStaircasePartition_iff hk

theorem exercise5_IsFranklinMovePair_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) {mu : List Nat} :
    PartI.Ch05.IsFranklinMovePair (PartI.Ch05.shiftedStaircasePartition d k) mu ↔
      (d + 2 = k ∧
        mu = PartI.Ch05.franklinUpMove (PartI.Ch05.shiftedStaircasePartition d k)) ∨
        (k < d ∧
          mu = PartI.Ch05.franklinDownMove
            (PartI.Ch05.shiftedStaircasePartition d k)) :=
  PartI.Ch05.IsFranklinMovePair_shiftedStaircasePartition_iff hk

theorem exercise5_shiftedStaircasePartition_lastPart_low_residual_iff
    {d k : Nat} (hk : 0 < k) :
    (PartI.Ch05.shiftedStaircasePartition d k).getD
        (PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) - 1) 0 <
      PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) - 1 ↔
      d + 2 < k :=
  PartI.Ch05.shiftedStaircasePartition_lastPart_low_residual_iff hk

theorem exercise5_shiftedStaircasePartition_lastPart_up_boundary_iff
    {d k : Nat} (hk : 0 < k) :
    (PartI.Ch05.shiftedStaircasePartition d k).getD
        (PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) - 1) 0 =
      PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) - 1 ↔
      PartI.Ch05.IsFranklinUpBranchInput (PartI.Ch05.shiftedStaircasePartition d k) :=
  PartI.Ch05.shiftedStaircasePartition_lastPart_up_boundary_iff hk

theorem exercise5_shiftedStaircasePartition_lastPart_fixed_boundary_iff
    {d k : Nat} (hk : 0 < k) :
    ((PartI.Ch05.shiftedStaircasePartition d k).getD
          (PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) - 1) 0 =
        PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) ∨
      (PartI.Ch05.shiftedStaircasePartition d k).getD
          (PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) - 1) 0 =
        PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) + 1) ↔
      PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.shiftedStaircasePartition d k) :=
  PartI.Ch05.shiftedStaircasePartition_lastPart_fixed_boundary_iff hk

theorem exercise5_shiftedStaircasePartition_lastPart_down_boundary_iff
    {d k : Nat} (hk : 0 < k) :
    PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) + 1 <
        (PartI.Ch05.shiftedStaircasePartition d k).getD
          (PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) - 1) 0 ↔
      PartI.Ch05.IsFranklinDownBranchInput (PartI.Ch05.shiftedStaircasePartition d k) :=
  PartI.Ch05.shiftedStaircasePartition_lastPart_down_boundary_iff hk

theorem exercise5_IsFranklinDownBranchInput_franklinUpMove_shiftedStaircasePartition
    {d k : Nat} (hk : 0 < k) (hup : d + 2 = k) :
    PartI.Ch05.IsFranklinDownBranchInput
      (PartI.Ch05.franklinUpMove (PartI.Ch05.shiftedStaircasePartition d k)) :=
  PartI.Ch05.IsFranklinDownBranchInput_franklinUpMove_shiftedStaircasePartition hk hup

theorem exercise5_IsFranklinUpBranchInput_franklinDownMove_shiftedStaircasePartition
    {d k : Nat} (hk : 0 < k) (hdown : k < d) :
    PartI.Ch05.IsFranklinUpBranchInput
      (PartI.Ch05.franklinDownMove (PartI.Ch05.shiftedStaircasePartition d k)) :=
  PartI.Ch05.IsFranklinUpBranchInput_franklinDownMove_shiftedStaircasePartition hk hdown

theorem exercise5_franklinDownMove_franklinUpMove_shiftedStaircasePartition
    {d k : Nat} (hk : 0 < k) (hup : d + 2 = k) :
    PartI.Ch05.franklinDownMove
        (PartI.Ch05.franklinUpMove (PartI.Ch05.shiftedStaircasePartition d k)) =
      PartI.Ch05.shiftedStaircasePartition d k :=
  PartI.Ch05.franklinDownMove_franklinUpMove_shiftedStaircasePartition hk hup

theorem exercise5_franklinUpMove_franklinDownMove_shiftedStaircasePartition
    {d k : Nat} (hk : 0 < k) (hdown : k < d) :
    PartI.Ch05.franklinUpMove
        (PartI.Ch05.franklinDownMove (PartI.Ch05.shiftedStaircasePartition d k)) =
      PartI.Ch05.shiftedStaircasePartition d k :=
  PartI.Ch05.franklinUpMove_franklinDownMove_shiftedStaircasePartition hk hdown

theorem exercise5_franklinUpMove_shiftedStaircasePartition_strict_weight_sign
    {d k : Nat} (hk : 0 < k) (hup : d + 2 = k) :
    PartI.Ch05.IsStrictPartition
        (PartI.Ch05.franklinUpMove (PartI.Ch05.shiftedStaircasePartition d k)) ∧
      partitionWeight
          (PartI.Ch05.franklinUpMove (PartI.Ch05.shiftedStaircasePartition d k)) =
        partitionWeight (PartI.Ch05.shiftedStaircasePartition d k) ∧
      PartI.Ch05.partSign
          (PartI.Ch05.franklinUpMove (PartI.Ch05.shiftedStaircasePartition d k)) =
        - PartI.Ch05.partSign (PartI.Ch05.shiftedStaircasePartition d k) :=
  PartI.Ch05.franklinUpMove_shiftedStaircasePartition_strict_weight_sign hk hup

theorem exercise5_franklinDownMove_shiftedStaircasePartition_strict_weight_sign
    {d k : Nat} (hk : 0 < k) (hdown : k < d) :
    PartI.Ch05.IsStrictPartition
        (PartI.Ch05.franklinDownMove (PartI.Ch05.shiftedStaircasePartition d k)) ∧
      partitionWeight
          (PartI.Ch05.franklinDownMove (PartI.Ch05.shiftedStaircasePartition d k)) =
        partitionWeight (PartI.Ch05.shiftedStaircasePartition d k) ∧
      PartI.Ch05.partSign
          (PartI.Ch05.franklinDownMove (PartI.Ch05.shiftedStaircasePartition d k)) =
        - PartI.Ch05.partSign (PartI.Ch05.shiftedStaircasePartition d k) :=
  PartI.Ch05.franklinDownMove_shiftedStaircasePartition_strict_weight_sign hk hdown

theorem exercise5_franklinUpMove_shiftedStaircasePartition_branch_package
    {d k : Nat} (hk : 0 < k) (hup : d + 2 = k) :
    PartI.Ch05.IsStrictPartition
        (PartI.Ch05.franklinUpMove (PartI.Ch05.shiftedStaircasePartition d k)) ∧
      partitionWeight
          (PartI.Ch05.franklinUpMove (PartI.Ch05.shiftedStaircasePartition d k)) =
        partitionWeight (PartI.Ch05.shiftedStaircasePartition d k) ∧
      PartI.Ch05.partSign
          (PartI.Ch05.franklinUpMove (PartI.Ch05.shiftedStaircasePartition d k)) =
        - PartI.Ch05.partSign (PartI.Ch05.shiftedStaircasePartition d k) ∧
      PartI.Ch05.IsFranklinDownBranchInput
        (PartI.Ch05.franklinUpMove (PartI.Ch05.shiftedStaircasePartition d k)) ∧
      PartI.Ch05.franklinDownMove
          (PartI.Ch05.franklinUpMove (PartI.Ch05.shiftedStaircasePartition d k)) =
        PartI.Ch05.shiftedStaircasePartition d k :=
  PartI.Ch05.franklinUpMove_shiftedStaircasePartition_branch_package hk hup

theorem exercise5_franklinDownMove_shiftedStaircasePartition_branch_package
    {d k : Nat} (hk : 0 < k) (hdown : k < d) :
    PartI.Ch05.IsStrictPartition
        (PartI.Ch05.franklinDownMove (PartI.Ch05.shiftedStaircasePartition d k)) ∧
      partitionWeight
          (PartI.Ch05.franklinDownMove (PartI.Ch05.shiftedStaircasePartition d k)) =
        partitionWeight (PartI.Ch05.shiftedStaircasePartition d k) ∧
      PartI.Ch05.partSign
          (PartI.Ch05.franklinDownMove (PartI.Ch05.shiftedStaircasePartition d k)) =
        - PartI.Ch05.partSign (PartI.Ch05.shiftedStaircasePartition d k) ∧
      PartI.Ch05.IsFranklinUpBranchInput
        (PartI.Ch05.franklinDownMove (PartI.Ch05.shiftedStaircasePartition d k)) ∧
      PartI.Ch05.franklinUpMove
          (PartI.Ch05.franklinDownMove (PartI.Ch05.shiftedStaircasePartition d k)) =
        PartI.Ch05.shiftedStaircasePartition d k :=
  PartI.Ch05.franklinDownMove_shiftedStaircasePartition_branch_package hk hdown

theorem exercise5_shiftedStaircasePartition_low_offset_no_boundary
    {d k : Nat} (hk : 0 < k) (hdk : d + 2 < k) :
    ¬ PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.shiftedStaircasePartition d k) ∧
      ¬ (∃ mu : List Nat,
        PartI.Ch05.shiftedStaircasePartition d k =
          mu ++ [PartI.Ch05.numberOfParts mu]) ∧
      ¬ (∀ n, n ∈ PartI.Ch05.shiftedStaircasePartition d k →
        PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) + 1 < n) :=
  PartI.Ch05.shiftedStaircasePartition_low_offset_no_boundary hk hdk

theorem exercise5_shiftedStaircasePartition_low_offset_no_branch_inputs
    {d k : Nat} (hk : 0 < k) (hdk : d + 2 < k) :
    ¬ PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.shiftedStaircasePartition d k) ∧
      ¬ PartI.Ch05.IsFranklinUpBranchInput (PartI.Ch05.shiftedStaircasePartition d k) ∧
      ¬ PartI.Ch05.IsFranklinDownBranchInput
        (PartI.Ch05.shiftedStaircasePartition d k) :=
  PartI.Ch05.shiftedStaircasePartition_low_offset_no_branch_inputs hk hdk

theorem exercise5_shiftedStaircasePartition_residual_branch_inputs_iff
    {d k : Nat} (hk : 0 < k) :
    (¬ PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.shiftedStaircasePartition d k) ∧
        ¬ PartI.Ch05.IsFranklinUpBranchInput
          (PartI.Ch05.shiftedStaircasePartition d k) ∧
        ¬ PartI.Ch05.IsFranklinDownBranchInput
          (PartI.Ch05.shiftedStaircasePartition d k)) ↔
      d + 2 < k :=
  PartI.Ch05.shiftedStaircasePartition_residual_branch_inputs_iff hk

theorem exercise5_shiftedStaircasePartition_offset_cases {d k : Nat} (hk : 0 < k) :
    (d + 2 < k ∧
        ¬ PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.shiftedStaircasePartition d k) ∧
        ¬ (∃ mu : List Nat,
          PartI.Ch05.shiftedStaircasePartition d k =
            mu ++ [PartI.Ch05.numberOfParts mu]) ∧
        ¬ (∀ n, n ∈ PartI.Ch05.shiftedStaircasePartition d k →
          PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) + 1 < n)) ∨
      (∃ mu : List Nat,
        PartI.Ch05.shiftedStaircasePartition d k =
          mu ++ [PartI.Ch05.numberOfParts mu]) ∨
      PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.shiftedStaircasePartition d k) ∨
      (∀ n, n ∈ PartI.Ch05.shiftedStaircasePartition d k →
        PartI.Ch05.numberOfParts (PartI.Ch05.shiftedStaircasePartition d k) + 1 < n) :=
  PartI.Ch05.shiftedStaircasePartition_offset_cases hk

theorem exercise5_shiftedStaircasePartition_branch_input_cases
    {d k : Nat} (hk : 0 < k) :
    (d + 2 < k ∧
        ¬ PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.shiftedStaircasePartition d k) ∧
        ¬ PartI.Ch05.IsFranklinUpBranchInput
          (PartI.Ch05.shiftedStaircasePartition d k) ∧
        ¬ PartI.Ch05.IsFranklinDownBranchInput
          (PartI.Ch05.shiftedStaircasePartition d k)) ∨
      PartI.Ch05.IsFranklinUpBranchInput (PartI.Ch05.shiftedStaircasePartition d k) ∨
      PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.shiftedStaircasePartition d k) ∨
      PartI.Ch05.IsFranklinDownBranchInput
        (PartI.Ch05.shiftedStaircasePartition d k) :=
  PartI.Ch05.shiftedStaircasePartition_branch_input_cases hk

theorem exercise5_shiftedStaircasePartition_up_or_fixed_or_down_of_not_low_offset
    {d k : Nat} (hk : 0 < k) (hlow : ¬ (d + 2 < k)) :
    PartI.Ch05.IsFranklinUpBranchInput (PartI.Ch05.shiftedStaircasePartition d k) ∨
      PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.shiftedStaircasePartition d k) ∨
      PartI.Ch05.IsFranklinDownBranchInput
        (PartI.Ch05.shiftedStaircasePartition d k) :=
  PartI.Ch05.shiftedStaircasePartition_up_or_fixed_or_down_of_not_low_offset hk hlow

theorem exercise5_shiftedStaircasePartition_up_or_fixed_or_down_iff_not_low_offset
    {d k : Nat} (hk : 0 < k) :
    (PartI.Ch05.IsFranklinUpBranchInput (PartI.Ch05.shiftedStaircasePartition d k) ∨
        PartI.Ch05.IsPentagonalFixedShape (PartI.Ch05.shiftedStaircasePartition d k) ∨
        PartI.Ch05.IsFranklinDownBranchInput
          (PartI.Ch05.shiftedStaircasePartition d k)) ↔
      ¬ (d + 2 < k) :=
  PartI.Ch05.shiftedStaircasePartition_up_or_fixed_or_down_iff_not_low_offset hk

/-- Exercise (Chapter 5 style): sign parity of lower pentagonal fixed shape is k % 2. -/
theorem exercise5_partParity_lowerPentagonalPartition (k : Nat) :
    PartI.Ch05.partParity (PartI.Ch05.lowerPentagonalPartition k) = k % 2 :=
  PartI.Ch05.partParity_lowerPentagonalPartition k

/-- Exercise (Chapter 5 style): sign parity of upper pentagonal fixed shape is k % 2. -/
theorem exercise5_partParity_upperPentagonalPartition (k : Nat) :
    PartI.Ch05.partParity (PartI.Ch05.upperPentagonalPartition k) = k % 2 :=
  PartI.Ch05.partParity_upperPentagonalPartition k

theorem exercise5_partSign_lowerPentagonalPartition (k : Nat) :
    PartI.Ch05.partSign (PartI.Ch05.lowerPentagonalPartition k) =
      if k % 2 = 0 then 1 else -1 :=
  PartI.Ch05.partSign_lowerPentagonalPartition k

theorem exercise5_partSign_upperPentagonalPartition (k : Nat) :
    PartI.Ch05.partSign (PartI.Ch05.upperPentagonalPartition k) =
      if k % 2 = 0 then 1 else -1 :=
  PartI.Ch05.partSign_upperPentagonalPartition k

theorem exercise5_partSign_lowerPentagonalPartition_eq_upper (k : Nat) :
    PartI.Ch05.partSign (PartI.Ch05.lowerPentagonalPartition k) =
      PartI.Ch05.partSign (PartI.Ch05.upperPentagonalPartition k) :=
  PartI.Ch05.partSign_lowerPentagonalPartition_eq_upper k

/-- Exercise (Chapter 5 style): Ferrers conjugation preserves diagram cardinality. -/
theorem exercise5_FerrersDiagramCells_card_FerrersConjugatePartition {lam : List Nat}
    (hpart : IsPartition lam) :
    (PartI.Ch05.FerrersDiagramCells (PartI.Ch05.FerrersConjugatePartition lam)).card =
      (PartI.Ch05.FerrersDiagramCells lam).card :=
  PartI.Ch05.FerrersDiagramCells_card_FerrersConjugatePartition hpart

/-- Exercise (Chapter 5 style): double Ferrers conjugation preserves weight. -/
theorem exercise5_partitionWeight_FerrersConjugatePartition_conjugate {lam : List Nat}
    (hpart : IsPartition lam) :
    partitionWeight
        (PartI.Ch05.FerrersConjugatePartition (PartI.Ch05.FerrersConjugatePartition lam)) =
      partitionWeight lam :=
  PartI.Ch05.partitionWeight_FerrersConjugatePartition_conjugate hpart

/-- Exercise (Chapter 5 style): partition parts are antitone (getD form). -/
theorem exercise5_IsPartition_getD_antitone {lam : List Nat} (hpart : IsPartition lam)
    {s r : Nat} (hsr : s ≤ r) (hr : r < lam.length) :
    lam.getD r 0 ≤ lam.getD s 0 :=
  PartI.Ch05.IsPartition.getD_antitone hpart hsr hr

/-- Exercise (Chapter 5 style): Ferrers cells are upward closed in the row index. -/
theorem exercise5_FerrersCell_of_le_row {lam : List Nat} (hpart : IsPartition lam)
    {s r c : Nat} (hsr : s ≤ r) (hcell : PartI.Ch05.FerrersCell lam r c) :
    PartI.Ch05.FerrersCell lam s c :=
  PartI.Ch05.FerrersCell_of_le_row hpart hsr hcell

/-- Exercise (Chapter 5 style): Ferrers column cells are upward closed in the row index. -/
theorem exercise5_FerrersColumnCells_mem_of_le_row {lam : List Nat} (hpart : IsPartition lam)
    {s r c : Nat} (hsr : s ≤ r) (hr : r ∈ PartI.Ch05.FerrersColumnCells lam c) :
    s ∈ PartI.Ch05.FerrersColumnCells lam c :=
  PartI.Ch05.FerrersColumnCells_mem_of_le_row hpart hsr hr

/-- Exercise (Chapter 5 style): earlier Ferrers columns contain later Ferrers columns. -/
theorem exercise5_FerrersColumnCells_subset_of_le_col (lam : List Nat) {c d : Nat}
    (hcd : c ≤ d) :
    PartI.Ch05.FerrersColumnCells lam d ⊆ PartI.Ch05.FerrersColumnCells lam c :=
  PartI.Ch05.FerrersColumnCells_subset_of_le_col lam hcd

/-- Exercise (Chapter 5 style): Ferrers column heights are weakly decreasing. -/
theorem exercise5_FerrersColumnCells_card_antitone (lam : List Nat) {c d : Nat}
    (hcd : c ≤ d) :
    (PartI.Ch05.FerrersColumnCells lam d).card ≤
      (PartI.Ch05.FerrersColumnCells lam c).card :=
  PartI.Ch05.FerrersColumnCells_card_antitone lam hcd

/-- Exercise (Chapter 5 style): partition Ferrers columns are initial row segments. -/
theorem exercise5_FerrersColumnCells_eq_range_card {lam : List Nat}
    (hpart : IsPartition lam) (c : Nat) :
    PartI.Ch05.FerrersColumnCells lam c =
      Finset.range (PartI.Ch05.FerrersColumnCells lam c).card :=
  PartI.Ch05.FerrersColumnCells_eq_range_card hpart c

/-- Exercise (Chapter 5 style): membership in the column-grouped Ferrers diagram with a bound. -/
theorem exercise5_mem_FerrersDiagramCellsByColumnsUpTo_iff {lam : List Nat} {N r c : Nat} :
    (r, c) ∈ PartI.Ch05.FerrersDiagramCellsByColumnsUpTo lam N ↔
      PartI.Ch05.FerrersCell lam r c ∧ c < N :=
  PartI.Ch05.mem_FerrersDiagramCellsByColumnsUpTo_iff

/-- Exercise (Chapter 5 style): grouping cells by columns recovers the diagram if the bound is safe. -/
theorem exercise5_FerrersDiagramCellsByColumnsUpTo_eq_of_bound (lam : List Nat) (N : Nat)
    (hbound : ∀ r : Nat, r < lam.length → lam.getD r 0 ≤ N) :
    PartI.Ch05.FerrersDiagramCellsByColumnsUpTo lam N = PartI.Ch05.FerrersDiagramCells lam :=
  PartI.Ch05.FerrersDiagramCellsByColumnsUpTo_eq_of_bound lam N hbound

/-- Exercise (Chapter 5 style): cardinality of the column-grouped diagram is the sum of heights. -/
theorem exercise5_FerrersDiagramCellsByColumnsUpTo_card (lam : List Nat) (N : Nat) :
    (PartI.Ch05.FerrersDiagramCellsByColumnsUpTo lam N).card =
      (Finset.range N).sum (fun c => (PartI.Ch05.FerrersColumnCells lam c).card) :=
  PartI.Ch05.FerrersDiagramCellsByColumnsUpTo_card lam N

/-- Exercise (Chapter 5 style): total Ferrers cells as a bounded sum of column heights. -/
theorem exercise5_FerrersDiagramCells_card_eq_sum_column_cards_of_bound (lam : List Nat) (N : Nat)
    (hbound : ∀ r : Nat, r < lam.length → lam.getD r 0 ≤ N) :
    (PartI.Ch05.FerrersDiagramCells lam).card =
      (Finset.range N).sum (fun c => (PartI.Ch05.FerrersColumnCells lam c).card) :=
  PartI.Ch05.FerrersDiagramCells_card_eq_sum_column_cards_of_bound lam N hbound

/-- Exercise (Chapter 5 style): the truncated column-height list has the requested width. -/
theorem exercise5_FerrersColumnHeightsUpTo_length (lam : List Nat) (N : Nat) :
    (PartI.Ch05.FerrersColumnHeightsUpTo lam N).length = N :=
  PartI.Ch05.FerrersColumnHeightsUpTo_length lam N

/-- Exercise (Chapter 5 style): reading a displayed column height below the width. -/
theorem exercise5_FerrersColumnHeightsUpTo_getD_of_lt (lam : List Nat) {c N : Nat}
    (hc : c < N) :
    (PartI.Ch05.FerrersColumnHeightsUpTo lam N).getD c 0 =
      (PartI.Ch05.FerrersColumnCells lam c).card :=
  PartI.Ch05.FerrersColumnHeightsUpTo_getD_of_lt lam hc

/-- Exercise (Chapter 5 style): reading a displayed column height past the width. -/
theorem exercise5_FerrersColumnHeightsUpTo_getD_of_ge (lam : List Nat) {c N : Nat}
    (hN : N ≤ c) :
    (PartI.Ch05.FerrersColumnHeightsUpTo lam N).getD c 0 = 0 :=
  PartI.Ch05.FerrersColumnHeightsUpTo_getD_of_ge lam hN

/-- Exercise (Chapter 5 style): truncated Ferrers column heights form a partition. -/
theorem exercise5_IsPartition_FerrersColumnHeightsUpTo (lam : List Nat) (N : Nat) :
    IsPartition (PartI.Ch05.FerrersColumnHeightsUpTo lam N) :=
  PartI.Ch05.IsPartition_FerrersColumnHeightsUpTo lam N

/-- Exercise (Chapter 5 style): column-height Ferrers cells transpose original cells. -/
theorem exercise5_FerrersCell_FerrersColumnHeightsUpTo_iff {lam : List Nat}
    (hpart : IsPartition lam) {N r c : Nat} :
    PartI.Ch05.FerrersCell (PartI.Ch05.FerrersColumnHeightsUpTo lam N) c r ↔
      c < N ∧ PartI.Ch05.FerrersCell lam r c :=
  PartI.Ch05.FerrersCell_FerrersColumnHeightsUpTo_iff hpart

/-- Exercise (Chapter 5 style): column-height diagrams transpose original diagram membership. -/
theorem exercise5_mem_FerrersDiagramCells_FerrersColumnHeightsUpTo_iff {lam : List Nat}
    (hpart : IsPartition lam) {N r c : Nat} :
    (c, r) ∈ PartI.Ch05.FerrersDiagramCells (PartI.Ch05.FerrersColumnHeightsUpTo lam N) ↔
      (r, c) ∈ PartI.Ch05.FerrersDiagramCells lam ∧ c < N :=
  PartI.Ch05.mem_FerrersDiagramCells_FerrersColumnHeightsUpTo_iff hpart

/-- Exercise (Chapter 5 style): bounded column-height cells exactly transpose original cells. -/
theorem exercise5_FerrersCell_FerrersColumnHeightsUpTo_iff_of_bound {lam : List Nat}
    (hpart : IsPartition lam) {N r c : Nat}
    (hbound : ∀ s : Nat, s < lam.length → lam.getD s 0 ≤ N) :
    PartI.Ch05.FerrersCell (PartI.Ch05.FerrersColumnHeightsUpTo lam N) c r ↔
      PartI.Ch05.FerrersCell lam r c :=
  PartI.Ch05.FerrersCell_FerrersColumnHeightsUpTo_iff_of_bound hpart hbound

/-- Exercise (Chapter 5 style): bounded column-height diagrams transpose membership. -/
theorem exercise5_mem_FerrersDiagramCells_FerrersColumnHeightsUpTo_iff_of_bound
    {lam : List Nat} (hpart : IsPartition lam) {N r c : Nat}
    (hbound : ∀ s : Nat, s < lam.length → lam.getD s 0 ≤ N) :
    (c, r) ∈ PartI.Ch05.FerrersDiagramCells (PartI.Ch05.FerrersColumnHeightsUpTo lam N) ↔
      (r, c) ∈ PartI.Ch05.FerrersDiagramCells lam :=
  PartI.Ch05.mem_FerrersDiagramCells_FerrersColumnHeightsUpTo_iff_of_bound hpart hbound

/-- Exercise (Chapter 5 style): every row length is bounded by the first row. -/
theorem exercise5_IsPartition_getD_le_first {lam : List Nat} (hpart : IsPartition lam)
    {r : Nat} (hr : r < lam.length) :
    lam.getD r 0 ≤ lam.getD 0 0 :=
  PartI.Ch05.IsPartition.getD_le_first hpart hr

/-- Exercise (Chapter 5 style): conjugate length is the first row length. -/
theorem exercise5_FerrersConjugatePartition_length (lam : List Nat) :
    (PartI.Ch05.FerrersConjugatePartition lam).length = lam.getD 0 0 :=
  PartI.Ch05.FerrersConjugatePartition_length lam

/-- Exercise (Chapter 5 style): reading a conjugate part below the first row length. -/
theorem exercise5_FerrersConjugatePartition_getD_of_lt (lam : List Nat) {c : Nat}
    (hc : c < lam.getD 0 0) :
    (PartI.Ch05.FerrersConjugatePartition lam).getD c 0 =
      (PartI.Ch05.FerrersColumnCells lam c).card :=
  PartI.Ch05.FerrersConjugatePartition_getD_of_lt lam hc

/-- Exercise (Chapter 5 style): reading a conjugate part past the first row length. -/
theorem exercise5_FerrersConjugatePartition_getD_of_ge (lam : List Nat) {c : Nat}
    (hc : lam.getD 0 0 ≤ c) :
    (PartI.Ch05.FerrersConjugatePartition lam).getD c 0 = 0 :=
  PartI.Ch05.FerrersConjugatePartition_getD_of_ge lam hc

/-- Exercise (Chapter 5 style): for positive parts, the zeroth Ferrers column is all rows. -/
theorem exercise5_FerrersColumnCells_zero_eq_range_length_of_positive {lam : List Nat}
    (hpos : PartI.Ch05.PositiveParts lam) :
    PartI.Ch05.FerrersColumnCells lam 0 = Finset.range lam.length :=
  PartI.Ch05.FerrersColumnCells_zero_eq_range_length_of_positive hpos

/-- Exercise (Chapter 5 style): the first conjugate part counts rows. -/
theorem exercise5_FerrersConjugatePartition_getD_zero_eq_length_of_positive {lam : List Nat}
    (hpos : PartI.Ch05.PositiveParts lam) :
    (PartI.Ch05.FerrersConjugatePartition lam).getD 0 0 = lam.length :=
  PartI.Ch05.FerrersConjugatePartition_getD_zero_eq_length_of_positive hpos

theorem exercise5_FerrersConjugatePartition_nil :
    PartI.Ch05.FerrersConjugatePartition [] = [] :=
  PartI.Ch05.FerrersConjugatePartition_nil

theorem exercise5_FerrersConjugatePartition_three_two_one :
    PartI.Ch05.FerrersConjugatePartition [3, 2, 1] = [3, 2, 1] :=
  PartI.Ch05.FerrersConjugatePartition_three_two_one

theorem exercise5_FerrersConjugatePartition_four_two :
    PartI.Ch05.FerrersConjugatePartition [4, 2] = [2, 2, 1, 1] :=
  PartI.Ch05.FerrersConjugatePartition_four_two

theorem exercise5_FerrersConjugatePartition_two_two_one_one :
    PartI.Ch05.FerrersConjugatePartition [2, 2, 1, 1] = [4, 2] :=
  PartI.Ch05.FerrersConjugatePartition_two_two_one_one

theorem exercise5_FerrersColumnCells_staircasePartition_eq_range_sub (n c : Nat) :
    PartI.Ch05.FerrersColumnCells (PartI.Ch05.staircasePartition n) c =
      Finset.range (n - c) :=
  PartI.Ch05.FerrersColumnCells_staircasePartition_eq_range_sub n c

theorem exercise5_FerrersConjugatePartition_staircasePartition (n : Nat) :
    PartI.Ch05.FerrersConjugatePartition (PartI.Ch05.staircasePartition n) =
      PartI.Ch05.staircasePartition n :=
  PartI.Ch05.FerrersConjugatePartition_staircasePartition n

/-- Exercise (Chapter 5 style): the Ferrers conjugate list is a partition. -/
theorem exercise5_IsPartition_FerrersConjugatePartition (lam : List Nat) :
    IsPartition (PartI.Ch05.FerrersConjugatePartition lam) :=
  PartI.Ch05.IsPartition_FerrersConjugatePartition lam

/-- Exercise (Chapter 5 style): displayed conjugate parts are positive. -/
theorem exercise5_PositiveParts_FerrersConjugatePartition (lam : List Nat) :
    PartI.Ch05.PositiveParts (PartI.Ch05.FerrersConjugatePartition lam) :=
  PartI.Ch05.PositiveParts_FerrersConjugatePartition lam

/-- Exercise (Chapter 5 style): Ferrers conjugation preserves weight. -/
theorem exercise5_partitionWeight_FerrersConjugatePartition {lam : List Nat}
    (hpart : IsPartition lam) :
    partitionWeight (PartI.Ch05.FerrersConjugatePartition lam) = partitionWeight lam :=
  PartI.Ch05.partitionWeight_FerrersConjugatePartition hpart

/-- Exercise (Chapter 5 style): conjugate Ferrers cells transpose original cells. -/
theorem exercise5_FerrersCell_FerrersConjugatePartition_iff {lam : List Nat}
    (hpart : IsPartition lam) {r c : Nat} :
    PartI.Ch05.FerrersCell (PartI.Ch05.FerrersConjugatePartition lam) c r ↔
      PartI.Ch05.FerrersCell lam r c :=
  PartI.Ch05.FerrersCell_FerrersConjugatePartition_iff hpart

/-- Exercise (Chapter 5 style): double conjugation preserves length for positive parts. -/
theorem exercise5_FerrersConjugatePartition_conjugate_length {lam : List Nat}
    (hpos : PartI.Ch05.PositiveParts lam) :
    (PartI.Ch05.FerrersConjugatePartition
      (PartI.Ch05.FerrersConjugatePartition lam)).length = lam.length :=
  PartI.Ch05.FerrersConjugatePartition_conjugate_length hpos

/-- Exercise (Chapter 5 style): double Ferrers conjugation returns the original partition list. -/
theorem exercise5_FerrersConjugatePartition_conjugate_eq {lam : List Nat}
    (hpart : IsPartition lam) (hpos : PartI.Ch05.PositiveParts lam) :
    PartI.Ch05.FerrersConjugatePartition
      (PartI.Ch05.FerrersConjugatePartition lam) = lam :=
  PartI.Ch05.FerrersConjugatePartition_conjugate_eq hpart hpos

/-- Exercise (Chapter 5 style): conjugate Ferrers diagrams transpose membership. -/
theorem exercise5_mem_FerrersDiagramCells_FerrersConjugatePartition_iff {lam : List Nat}
    (hpart : IsPartition lam) {r c : Nat} :
    (c, r) ∈ PartI.Ch05.FerrersDiagramCells (PartI.Ch05.FerrersConjugatePartition lam) ↔
      (r, c) ∈ PartI.Ch05.FerrersDiagramCells lam :=
  PartI.Ch05.mem_FerrersDiagramCells_FerrersConjugatePartition_iff hpart

/-- Exercise (Chapter 5 style): double conjugation preserves Ferrers-cell membership. -/
theorem exercise5_FerrersCell_FerrersConjugatePartition_conjugate_iff
    {lam : List Nat} (hpart : IsPartition lam) {r c : Nat} :
    PartI.Ch05.FerrersCell
        (PartI.Ch05.FerrersConjugatePartition (PartI.Ch05.FerrersConjugatePartition lam))
        r c ↔
      PartI.Ch05.FerrersCell lam r c :=
  PartI.Ch05.FerrersCell_FerrersConjugatePartition_conjugate_iff hpart

/-- Exercise (Chapter 5 style): double conjugation preserves Ferrers-diagram membership. -/
theorem exercise5_mem_FerrersDiagramCells_FerrersConjugatePartition_conjugate_iff
    {lam : List Nat} (hpart : IsPartition lam) {r c : Nat} :
    (r, c) ∈ PartI.Ch05.FerrersDiagramCells
        (PartI.Ch05.FerrersConjugatePartition (PartI.Ch05.FerrersConjugatePartition lam)) ↔
      (r, c) ∈ PartI.Ch05.FerrersDiagramCells lam :=
  PartI.Ch05.mem_FerrersDiagramCells_FerrersConjugatePartition_conjugate_iff hpart

/-- Exercise (Chapter 5 style): the weight of the truncated column-height list is the sum of its heights. -/
theorem exercise5_partitionWeight_FerrersColumnHeightsUpTo (lam : List Nat) (N : Nat) :
    partitionWeight (PartI.Ch05.FerrersColumnHeightsUpTo lam N) =
      (Finset.range N).sum (fun c => (PartI.Ch05.FerrersColumnCells lam c).card) :=
  PartI.Ch05.partitionWeight_FerrersColumnHeightsUpTo lam N

/-- Exercise (Chapter 5 style): bounded column heights preserve Ferrers diagram weight. -/
theorem exercise5_partitionWeight_FerrersColumnHeightsUpTo_eq_of_bound (lam : List Nat) (N : Nat)
    (hbound : ∀ r : Nat, r < lam.length → lam.getD r 0 ≤ N) :
    partitionWeight (PartI.Ch05.FerrersColumnHeightsUpTo lam N) = partitionWeight lam :=
  PartI.Ch05.partitionWeight_FerrersColumnHeightsUpTo_eq_of_bound lam N hbound

end Chapter5Exercises

section Chapter6Exercises

variable {R : Type*} [Field R]

theorem exercise6_dedekindEtaTrunc_one (q : R) :
    PartI.Ch06.dedekindEtaTrunc q 1 = 1 - q :=
  PartI.Ch06.dedekindEtaTrunc_one q

theorem exercise6_dedekindEtaTrunc_two (q : R) :
    PartI.Ch06.dedekindEtaTrunc q 2 = (1 - q) * (1 - q ^ 2) :=
  PartI.Ch06.dedekindEtaTrunc_two q

theorem exercise6_dedekindEtaTrunc_three (q : R) :
    PartI.Ch06.dedekindEtaTrunc q 3 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) :=
  PartI.Ch06.dedekindEtaTrunc_three q

theorem exercise6_dedekindEtaTrunc_four (q : R) :
    PartI.Ch06.dedekindEtaTrunc q 4 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) :=
  PartI.Ch06.dedekindEtaTrunc_four q

end Chapter6Exercises

section Chapter7Exercises

variable {R : Type*} [Field R]

/-- Exercise: rogersRamanujanLHSTrunc at N=0 equals 1. -/
theorem exercise7_lhs_zero (q : R) (a : Nat) :
    PartII.Ch07.rogersRamanujanLHSTrunc q a 0 = 1 := by
  simp [PartII.Ch07.rogersRamanujanLHSTrunc, natSum, qPochhammer]

/-- Exercise: rrJ at x=0 equals 1 for all N. -/
theorem exercise7_rrJ_at_zero (q : ℂ) (N : ℕ) :
    PartII.Ch07.rrJ (0 : ℂ) q N = 1 :=
  PartII.Ch07.rrJ_at_zero q N

/-- Exercise: rrJ connects to LHS truncation at x=1 (parameter a=0). -/
theorem exercise7_rrJ_one_eq_lhs_zero (q : ℂ) (N : ℕ) :
    PartII.Ch07.rrJ 1 q N = PartII.Ch07.rogersRamanujanLHSTrunc q 0 N :=
  PartII.Ch07.rrJ_one_eq_lhsTrunc_zero q N

/-- Exercise: rrJ connects to LHS truncation at x=q (parameter a=1). -/
theorem exercise7_rrJ_q_eq_lhs_one (q : ℂ) (N : ℕ) :
    PartII.Ch07.rrJ q q N = PartII.Ch07.rogersRamanujanLHSTrunc q 1 N :=
  PartII.Ch07.rrJ_q_eq_lhsTrunc_one q N

/-- Exercise: the finite functional equation for rrJ. -/
theorem exercise7_rrJ_functional_eq (x q : ℂ) (hq : ‖q‖ < 1) (N : ℕ) :
    PartII.Ch07.rrJ x q (N + 1) - PartII.Ch07.rrJ (x * q) q (N + 1) =
      x * q * PartII.Ch07.rrJ (x * q ^ 2) q N :=
  PartII.Ch07.rrJ_functional_eq_complex x q hq N

/-- Exercise: the infinite functional equation for rrJInf. -/
theorem exercise7_rrJInf_functional_eq (x q : ℂ) (hq : ‖q‖ < 1) :
    PartII.Ch07.rrJInf x q - PartII.Ch07.rrJInf (x * q) q =
      x * q * PartII.Ch07.rrJInf (x * q ^ 2) q :=
  PartII.Ch07.rrJInf_functional_eq x q hq

/-- Exercise: J(0, q) = 1 for the infinite series. -/
theorem exercise7_rrJInf_zero (q : ℂ) (hq : ‖q‖ < 1) :
    PartII.Ch07.rrJInf 0 q = 1 :=
  PartII.Ch07.rrJInf_zero q hq

/-- Exercise: summability of the Rogers-Ramanujan series terms. -/
theorem exercise7_summable (x q : ℂ) (hq : ‖q‖ < 1) :
    Summable (PartII.Ch07.rrJTerm x q) :=
  PartII.Ch07.summable_rrJTerm x q hq

/-- Exercise: G - H = q · J(q²). -/
theorem exercise7_GH_diff (q : ℂ) (hq : ‖q‖ < 1) :
    PartII.Ch07.rrJInf 1 q - PartII.Ch07.rrJInf q q =
      q * PartII.Ch07.rrJInf (q ^ 2) q :=
  PartII.Ch07.rrJInf_GH_diff q hq

/-- Exercise: iterated FE at k=0. -/
theorem exercise7_iterate_zero (x q : ℂ) (hq : ‖q‖ < 1) :
    PartII.Ch07.rrJInf x q =
      PartII.Ch07.rrJInf (x * q) q +
        x * q * PartII.Ch07.rrJInf (x * q ^ 2) q :=
  PartII.Ch07.rrJInf_eq_shift_add x q hq

/-- Exercise: pentagonal exponent λ(1) = 3 (Chan Eq. 7.5). -/
theorem exercise7_lambdaRR_one : PartII.Ch07.lambdaRR 1 = 3 :=
  PartII.Ch07.lambdaRR_one

/-- Exercise: pentagonal exponent λ(2) = 11 (Chan Eq. 7.5). -/
theorem exercise7_lambdaRR_two : PartII.Ch07.lambdaRR 2 = 11 :=
  PartII.Ch07.lambdaRR_two

/-- Exercise: pentagonal exponent λ(3) = 24 (Chan Eq. 7.5). -/
theorem exercise7_lambdaRR_three : PartII.Ch07.lambdaRR 3 = 24 :=
  PartII.Ch07.lambdaRR_three

/-- Exercise: the ε-shift operator on powers (Chan Def. 7.1). -/
theorem exercise7_epsilonShift_pow (q a : R) (n : Nat) :
    PartII.Ch07.epsilonShift (fun x => x ^ n) q a = (a * q) ^ n :=
  PartII.Ch07.epsilonShift_pow q a n

/-- Exercise: crTrunc at r=0 simplifies (Chan Eq. 7.6). -/
theorem exercise7_crTrunc_zero (a q : R) (N : Nat) :
    PartII.Ch07.crTrunc a q 0 N = 1 / qPoch a q N :=
  PartII.Ch07.crTrunc_zero a q N

/-- Exercise: the Rogers-Ramanujan ratio satisfies a functional equation. -/
theorem exercise7_ratio_fe (q : ℂ) (hq : ‖q‖ < 1)
    (hG : PartII.Ch07.rrJInf 1 q ≠ 0) :
    PartII.Ch07.rogersRamanujanRatio q =
      PartII.Ch07.rrJInf q q / (PartII.Ch07.rrJInf q q +
        q * PartII.Ch07.rrJInf (q ^ 2) q) := by
  exact PartII.Ch07.rogersRamanujanRatio_functional_eq q hq hG

/-- **Theorem 7.1, first identity** (Chan Eq. 7.1, unconditional):
`G(q) · (q;q⁵)_∞ · (q⁴;q⁵)_∞ = 1` for `‖q‖ < 1`, `q ≠ 0`. -/
theorem exercise7_rogersRamanujan_first (q : ℂ) (hq : ‖q‖ < 1) (hq_ne : q ≠ 0) :
    PartII.Ch07.rrJInf 1 q * (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 1 n)
      * (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 4 n) = 1 :=
  PartII.Ch07.rogersRamanujan_first q hq hq_ne

/-- **Theorem 7.1, second identity** (Chan Eq. 7.2, unconditional):
`H(q) · (q²;q⁵)_∞ · (q³;q⁵)_∞ = 1` for `‖q‖ < 1`, `q ≠ 0`. -/
theorem exercise7_rogersRamanujan_second (q : ℂ) (hq : ‖q‖ < 1) (hq_ne : q ≠ 0) :
    PartII.Ch07.rrJInf q q * (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 2 n)
      * (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 3 n) = 1 :=
  PartII.Ch07.rogersRamanujan_second q hq hq_ne

end Chapter7Exercises

section Chapter8Exercises

variable {R : Type*} [Field R]

theorem exercise8_D_partialSum_zero (q : R) (a : Nat) :
    PartII.Ch08.D_partialSum q a 0 = 1 / qPochhammer q 0 :=
  PartII.Ch08.D_partialSum_zero q a

theorem exercise8_D_trunc_one (q : R) (a : Nat) :
    PartII.Ch08.D_trunc q a 1 = 1 + q ^ (1 + a) / (1 - q) :=
  PartII.Ch08.D_trunc_one q a

theorem exercise8_D_partialSum_two (q : R) (a : Nat) :
    PartII.Ch08.D_partialSum q a 2 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) :=
  PartII.Ch08.D_partialSum_two q a

theorem exercise8_D_trunc_two (q : R) (a : Nat) :
    PartII.Ch08.D_trunc q a 2 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) :=
  PartII.Ch08.D_trunc_two q a

end Chapter8Exercises

section Chapter9Exercises

variable {R : Type*} [Field R]

theorem exercise9_rrAlpha_two (a q : R) :
    PartII.Ch09.rrAlpha a q 2 = q * (1 - a * q ^ 4) / (1 - a) :=
  PartII.Ch09.rrAlpha_two a q

theorem exercise9_rrAlpha_three (a q : R) :
    PartII.Ch09.rrAlpha a q 3 = -(q ^ 3 * (1 - a * q ^ 6)) / (1 - a) :=
  PartII.Ch09.rrAlpha_three a q

theorem exercise9_rrAlpha_four (a q : R) :
    PartII.Ch09.rrAlpha a q 4 = q ^ 6 * (1 - a * q ^ 8) / (1 - a) :=
  PartII.Ch09.rrAlpha_four a q

theorem exercise9_rrAlpha_five (a q : R) :
    PartII.Ch09.rrAlpha a q 5 = -(q ^ 10 * (1 - a * q ^ 10)) / (1 - a) :=
  PartII.Ch09.rrAlpha_five a q

theorem exercise9_rrAlpha_six (a q : R) :
    PartII.Ch09.rrAlpha a q 6 = q ^ 15 * (1 - a * q ^ 12) / (1 - a) :=
  PartII.Ch09.rrAlpha_six a q

theorem exercise9_isBaileyPair_rrAlpha_rrBeta (a q : R) :
    PartII.Ch09.IsBaileyPair a q (PartII.Ch09.rrAlpha a q) (PartII.Ch09.rrBeta a q) :=
  PartII.Ch09.isBaileyPair_rrAlpha_rrBeta a q

theorem exercise9_isBaileyPairUpTo_rrAlpha_rrBeta (a q : R) (N : Nat) :
    PartII.Ch09.IsBaileyPairUpTo a q (PartII.Ch09.rrAlpha a q) (PartII.Ch09.rrBeta a q) N :=
  PartII.Ch09.isBaileyPairUpTo_rrAlpha_rrBeta a q N

theorem exercise9_rrBeta_zero (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.rrBeta a q 0 = 1 :=
  PartII.Ch09.rrBeta_zero a q ha

theorem exercise9_BaileyBeta_zero_expand (a q : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q α 0 = PartII.Ch09.BaileyTerm a q α 0 0 :=
  PartII.Ch09.BaileyBeta_zero_expand a q α

theorem exercise9_BaileyBeta_zero (a q : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q α 0 = α 0 :=
  PartII.Ch09.BaileyBeta_zero a q α

theorem exercise9_BaileyBeta_one_expand (a q : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q α 1 =
      PartII.Ch09.BaileyTerm a q α 1 0 + PartII.Ch09.BaileyTerm a q α 1 1 :=
  PartII.Ch09.BaileyBeta_one_expand a q α

theorem exercise9_BaileyBeta_one_terms (a q : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q α 1 =
      α 0 / ((1 - q) * (1 - a * q)) + α 1 / qPoch (a * q) q 2 :=
  PartII.Ch09.BaileyBeta_one_terms a q α

theorem exercise9_BaileyBeta_two_expand (a q : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q α 2 =
      PartII.Ch09.BaileyTerm a q α 2 0 +
      PartII.Ch09.BaileyTerm a q α 2 1 +
      PartII.Ch09.BaileyTerm a q α 2 2 :=
  PartII.Ch09.BaileyBeta_two_expand a q α

theorem exercise9_BaileyBeta_two_terms (a q : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q α 2 =
      α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
      α 1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
      α 2 / qPoch (a * q) q 4 :=
  PartII.Ch09.BaileyBeta_two_terms a q α

theorem exercise9_BaileyBeta_three_expand (a q : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q α 3 =
      PartII.Ch09.BaileyTerm a q α 3 0 +
      PartII.Ch09.BaileyTerm a q α 3 1 +
      PartII.Ch09.BaileyTerm a q α 3 2 +
      PartII.Ch09.BaileyTerm a q α 3 3 :=
  PartII.Ch09.BaileyBeta_three_expand a q α

theorem exercise9_BaileyBeta_three_terms (a q : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q α 3 =
      α 0 / (qPochhammer q 3 * qPoch (a * q) q 3) +
      α 1 / (qPochhammer q 2 * qPoch (a * q) q 4) +
      α 2 / (qPochhammer q 1 * qPoch (a * q) q 5) +
      α 3 / qPoch (a * q) q 6 :=
  PartII.Ch09.BaileyBeta_three_terms a q α

theorem exercise9_BaileyBeta_four_terms (a q : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q α 4 =
      α 0 / (qPochhammer q 4 * qPoch (a * q) q 4) +
      α 1 / (qPochhammer q 3 * qPoch (a * q) q 5) +
      α 2 / (qPochhammer q 2 * qPoch (a * q) q 6) +
      α 3 / (qPochhammer q 1 * qPoch (a * q) q 7) +
      α 4 / qPoch (a * q) q 8 :=
  PartII.Ch09.BaileyBeta_four_terms a q α

theorem exercise9_BaileyBeta_transformAlpha_zero (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 0 = α 0 :=
  PartII.Ch09.BaileyBeta_transformAlpha_zero a q ρ₁ ρ₂ α

theorem exercise9_BaileyTransform_preserves_pair_zero (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 0) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 0 =
      PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 0 :=
  PartII.Ch09.BaileyTransform_preserves_pair_zero a q ρ₁ ρ₂ h

theorem exercise9_BaileyTransform_preserves_pair_upTo_zero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 0) :
    PartII.Ch09.IsBaileyPairUpTo a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α)
      (PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β) 0 :=
  PartII.Ch09.BaileyTransform_preserves_pair_upTo_zero a q ρ₁ ρ₂ h

theorem exercise9_BaileyTransformBeta_rrBeta_zero (a q ρ₁ ρ₂ : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ (PartII.Ch09.rrBeta a q) 0 = 1 :=
  PartII.Ch09.BaileyTransformBeta_rrBeta_zero a q ρ₁ ρ₂ ha

theorem exercise9_BaileyTransform_preserves_rr_pair_zero (a q ρ₁ ρ₂ : R) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ (PartII.Ch09.rrBeta a q) 0 =
      PartII.Ch09.BaileyBeta a q
        (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ (PartII.Ch09.rrAlpha a q)) 0 :=
  PartII.Ch09.BaileyTransform_preserves_rr_pair_zero a q ρ₁ ρ₂

theorem exercise9_BaileyTransform_preserves_rr_pair_upTo_zero (a q ρ₁ ρ₂ : R) :
    PartII.Ch09.IsBaileyPairUpTo a q
      (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ (PartII.Ch09.rrAlpha a q))
      (PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ (PartII.Ch09.rrBeta a q)) 0 :=
  PartII.Ch09.BaileyTransform_preserves_rr_pair_upTo_zero a q ρ₁ ρ₂

theorem exercise9_BaileyBeta_transformAlpha_one_expand (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 =
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 0 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 1 :=
  PartII.Ch09.BaileyBeta_transformAlpha_one_expand a q ρ₁ ρ₂ α

theorem exercise9_BaileyBeta_transformAlpha_two_expand (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 =
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 0 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 1 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 2 :=
  PartII.Ch09.BaileyBeta_transformAlpha_two_expand a q ρ₁ ρ₂ α

theorem exercise9_BaileyBeta_transformAlpha_three_expand (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 =
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 0 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 1 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 2 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 3 :=
  PartII.Ch09.BaileyBeta_transformAlpha_three_expand a q ρ₁ ρ₂ α

theorem exercise9_BaileyBeta_transformAlpha_four_expand (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 =
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 0 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 1 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 2 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 3 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 4 :=
  PartII.Ch09.BaileyBeta_transformAlpha_four_expand a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_two_zero (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 0 =
      α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) :=
  PartII.Ch09.BaileyTerm_transformAlpha_two_zero a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_two_one (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 1 =
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 1 * qPoch (a * q) q 3) :=
  PartII.Ch09.BaileyTerm_transformAlpha_two_one a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_two_two (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 2 =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) * α 2) /
        qPoch (a * q) q 4 :=
  PartII.Ch09.BaileyTerm_transformAlpha_two_two a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_three_zero (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 0 =
      α 0 / (qPochhammer q 3 * qPoch (a * q) q 3) :=
  PartII.Ch09.BaileyTerm_transformAlpha_three_zero a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_three_one (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 1 =
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 2 * qPoch (a * q) q 4) :=
  PartII.Ch09.BaileyTerm_transformAlpha_three_one a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_three_two (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 2 =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) * α 2) /
        (qPochhammer q 1 * qPoch (a * q) q 5) :=
  PartII.Ch09.BaileyTerm_transformAlpha_three_two a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_three_three (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 3 =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) * α 3) /
        qPoch (a * q) q 6 :=
  PartII.Ch09.BaileyTerm_transformAlpha_three_three a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_four_zero (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 0 =
      α 0 / (qPochhammer q 4 * qPoch (a * q) q 4) :=
  PartII.Ch09.BaileyTerm_transformAlpha_four_zero a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_four_one (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 1 =
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 3 * qPoch (a * q) q 5) :=
  PartII.Ch09.BaileyTerm_transformAlpha_four_one a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_four_two (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 2 =
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) * α 2) /
        (qPochhammer q 2 * qPoch (a * q) q 6) :=
  PartII.Ch09.BaileyTerm_transformAlpha_four_two a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_four_three (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 3 =
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) * α 3) /
        (qPochhammer q 1 * qPoch (a * q) q 7) :=
  PartII.Ch09.BaileyTerm_transformAlpha_four_three a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_four_four (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 4 =
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) * α 4) /
        qPoch (a * q) q 8 :=
  PartII.Ch09.BaileyTerm_transformAlpha_four_four a q ρ₁ ρ₂ α

theorem exercise9_BaileyBeta_transformAlpha_two_terms (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 =
      α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 1 * qPoch (a * q) q 3)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) * α 2) /
        qPoch (a * q) q 4) :=
  PartII.Ch09.BaileyBeta_transformAlpha_two_terms a q ρ₁ ρ₂ α

theorem exercise9_BaileyBeta_transformAlpha_three_terms (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 =
      α 0 / (qPochhammer q 3 * qPoch (a * q) q 3) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 2 * qPoch (a * q) q 4)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) * α 2) /
        (qPochhammer q 1 * qPoch (a * q) q 5)) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) * α 3) /
        qPoch (a * q) q 6) :=
  PartII.Ch09.BaileyBeta_transformAlpha_three_terms a q ρ₁ ρ₂ α

theorem exercise9_BaileyBeta_transformAlpha_three_terms_linear
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 =
      (1 / (qPochhammer q 3 * qPoch (a * q) q 3)) * α 0 +
        (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 2 * qPoch (a * q) q 4)) * α 1 +
        (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 1 * qPoch (a * q) q 5)) * α 2) +
        (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          qPoch (a * q) q 6) * α 3) :=
  PartII.Ch09.BaileyBeta_transformAlpha_three_terms_linear a q ρ₁ ρ₂ α

theorem exercise9_BaileyBeta_transformAlpha_four_terms (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 =
      α 0 / (qPochhammer q 4 * qPoch (a * q) q 4) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 3 * qPoch (a * q) q 5)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) * α 2) /
        (qPochhammer q 2 * qPoch (a * q) q 6)) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) * α 3) /
        (qPochhammer q 1 * qPoch (a * q) q 7)) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) * α 4) /
        qPoch (a * q) q 8) :=
  PartII.Ch09.BaileyBeta_transformAlpha_four_terms a q ρ₁ ρ₂ α

theorem exercise9_BaileyBeta_transformAlpha_four_terms_linear
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 =
      (1 / (qPochhammer q 4 * qPoch (a * q) q 4)) * α 0 +
        (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 3 * qPoch (a * q) q 5)) * α 1 +
        (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 2 * qPoch (a * q) q 6)) * α 2) +
        (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          (qPochhammer q 1 * qPoch (a * q) q 7)) * α 3) +
        (((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
          (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
          qPoch (a * q) q 8) * α 4) :=
  PartII.Ch09.BaileyBeta_transformAlpha_four_terms_linear a q ρ₁ ρ₂ α

theorem exercise9_BaileyBeta_transformAlpha_five_expand
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 =
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 0 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 1 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 2 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 3 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 4 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 5 :=
  PartII.Ch09.BaileyBeta_transformAlpha_five_expand a q ρ₁ ρ₂ α

theorem exercise9_BaileyBeta_transformAlpha_six_expand
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 =
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 0 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 1 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 2 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 3 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 4 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 5 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 6 :=
  PartII.Ch09.BaileyBeta_transformAlpha_six_expand a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_six_zero
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 0 =
      α 0 / (qPochhammer q 6 * qPoch (a * q) q 6) :=
  PartII.Ch09.BaileyTerm_transformAlpha_six_zero a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_six_one
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 1 =
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 5 * qPoch (a * q) q 7) :=
  PartII.Ch09.BaileyTerm_transformAlpha_six_one a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_six_two
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 2 =
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) * α 2) /
        (qPochhammer q 4 * qPoch (a * q) q 8) :=
  PartII.Ch09.BaileyTerm_transformAlpha_six_two a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_six_three
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 3 =
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) * α 3) /
        (qPochhammer q 3 * qPoch (a * q) q 9) :=
  PartII.Ch09.BaileyTerm_transformAlpha_six_three a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_six_four
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 4 =
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) * α 4) /
        (qPochhammer q 2 * qPoch (a * q) q 10) :=
  PartII.Ch09.BaileyTerm_transformAlpha_six_four a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_six_five
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 5 =
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) * α 5) /
        (qPochhammer q 1 * qPoch (a * q) q 11) :=
  PartII.Ch09.BaileyTerm_transformAlpha_six_five a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_six_six
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 6 =
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
        (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) * α 6) /
        qPoch (a * q) q 12 :=
  PartII.Ch09.BaileyTerm_transformAlpha_six_six a q ρ₁ ρ₂ α

theorem exercise9_BaileyBeta_transformAlpha_six_terms
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 =
      α 0 / (qPochhammer q 6 * qPoch (a * q) q 6) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 5 * qPoch (a * q) q 7)) +
      (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) * α 2) /
        (qPochhammer q 4 * qPoch (a * q) q 8)) +
      (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) * α 3) /
        (qPochhammer q 3 * qPoch (a * q) q 9)) +
      (((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) * α 4) /
        (qPochhammer q 2 * qPoch (a * q) q 10)) +
      (((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) * α 5) /
        (qPochhammer q 1 * qPoch (a * q) q 11)) +
      (((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
        (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) * α 6) /
        qPoch (a * q) q 12) :=
  PartII.Ch09.BaileyBeta_transformAlpha_six_terms a q ρ₁ ρ₂ α

theorem exercise9_BaileyBeta_transformAlpha_five_terms_linear
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 =
      (1 / (qPochhammer q 5 * qPoch (a * q) q 5)) * α 0 +
        (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 4 * qPoch (a * q) q 6)) * α 1 +
        (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 3 * qPoch (a * q) q 7)) * α 2) +
        (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          (qPochhammer q 2 * qPoch (a * q) q 8)) * α 3) +
        (((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
          (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
          (qPochhammer q 1 * qPoch (a * q) q 9)) * α 4) +
        (((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
          (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) /
          qPoch (a * q) q 10) * α 5) :=
  PartII.Ch09.BaileyBeta_transformAlpha_five_terms_linear a q ρ₁ ρ₂ α

theorem exercise9_BaileyTransform_four_alpha_one_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 3)) / qPoch (a * q) q 2 +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 2)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 1)) /
        (qPochhammer q 2 * qPoch (a * q) q 4) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0)) /
        (qPochhammer q 3 * qPoch (a * q) q 5) =
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
        (qPochhammer q 3 * qPoch (a * q) q 5) :=
  PartII.Ch09.BaileyTransform_four_alpha_one_coefficient_identity
    a q ρ₁ ρ₂ hρ hD1 hD2 hD1one hD2one hQ1 hQ2 hQ3 hA2 hA3 hA4 hA5

theorem exercise9_BaileyTransform_four_alpha_four_coefficient_identity (a q ρ₁ ρ₂ : R) :
    ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0)) / qPoch (a * q) q 8 =
      (qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
        qPoch (a * q) q 8 :=
  PartII.Ch09.BaileyTransform_four_alpha_four_coefficient_identity a q ρ₁ ρ₂

theorem exercise9_BaileyTransform_five_alpha_five_coefficient_identity (a q ρ₁ ρ₂ : R) :
    ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0)) / qPoch (a * q) q 10 =
      (qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) /
        qPoch (a * q) q 10 :=
  PartII.Ch09.BaileyTransform_five_alpha_five_coefficient_identity a q ρ₁ ρ₂

theorem exercise9_BaileyTransform_six_alpha_six_coefficient_identity (a q ρ₁ ρ₂ : R) :
    ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0)) / qPoch (a * q) q 12 =
      (qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
        (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) /
        qPoch (a * q) q 12 :=
  PartII.Ch09.BaileyTransform_six_alpha_six_coefficient_identity a q ρ₁ ρ₂

theorem exercise9_BaileyTransform_five_alpha_four_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 1)) / qPoch (a * q) q 8 +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0)) /
        (qPochhammer q 1 * qPoch (a * q) q 9) =
      (qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
        (qPochhammer q 1 * qPoch (a * q) q 9) :=
  PartII.Ch09.BaileyTransform_five_alpha_four_coefficient_identity
    a q ρ₁ ρ₂ hρ hD1 hD2 hD1four hD2four hQ1 hA8 hA9

theorem exercise9_BaileyTransform_five_alpha_three_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0) :
    ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 2)) / qPoch (a * q) q 6 +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 1)) /
        (qPochhammer q 1 * qPoch (a * q) q 7) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0)) /
        (qPochhammer q 2 * qPoch (a * q) q 8) =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
        (qPochhammer q 2 * qPoch (a * q) q 8) :=
  PartII.Ch09.BaileyTransform_five_alpha_three_coefficient_identity
    a q ρ₁ ρ₂ hρ hD1 hD2 hD1three hD2three hQ1 hQ2 hA6 hA7 hA8

theorem exercise9_BaileyTransform_five_alpha_two_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 3)) / qPoch (a * q) q 4 +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 2)) /
        (qPochhammer q 1 * qPoch (a * q) q 5) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 1)) /
        (qPochhammer q 2 * qPoch (a * q) q 6) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0)) /
        (qPochhammer q 3 * qPoch (a * q) q 7) =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
        (qPochhammer q 3 * qPoch (a * q) q 7) :=
  PartII.Ch09.BaileyTransform_five_alpha_two_coefficient_identity
    a q ρ₁ ρ₂ hρ hD1 hD2 hD1two hD2two hQ1 hQ2 hQ3 hA4 hA5 hA6 hA7

theorem exercise9_BaileyTransform_five_alpha_one_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 4)) / qPoch (a * q) q 2 +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 3)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 2)) /
        (qPochhammer q 2 * qPoch (a * q) q 4) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 1)) /
        (qPochhammer q 3 * qPoch (a * q) q 5) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0)) /
        (qPochhammer q 4 * qPoch (a * q) q 6) =
      (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
        (qPochhammer q 4 * qPoch (a * q) q 6) :=
  PartII.Ch09.BaileyTransform_five_alpha_one_coefficient_identity
    a q ρ₁ ρ₂ hρ hD1 hD2 hD1one hD2one hQ1 hQ2 hQ3 hQ4 hA2 hA3 hA4 hA5 hA6

theorem exercise9_BaileyTransform_five_alpha_zero_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 5)) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 4)) /
        (qPochhammer q 1 * qPoch (a * q) q 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 3)) /
        (qPochhammer q 2 * qPoch (a * q) q 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 2)) /
        (qPochhammer q 3 * qPoch (a * q) q 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 1)) /
        (qPochhammer q 4 * qPoch (a * q) q 4) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0)) /
        (qPochhammer q 5 * qPoch (a * q) q 5) =
      1 / (qPochhammer q 5 * qPoch (a * q) q 5) :=
  PartII.Ch09.BaileyTransform_five_alpha_zero_coefficient_identity
    a q ρ₁ ρ₂ hρ hD1 hD2 hQ1 hQ2 hQ3 hQ4 hQ5 hA1 hA2 hA3 hA4 hA5

theorem exercise9_BaileyTransformBeta_one_expand (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 1 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 1) * β 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 0) * β 1) :=
  PartII.Ch09.BaileyTransformBeta_one_expand a q ρ₁ ρ₂ β

theorem exercise9_BaileyTransformBeta_one_terms (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 1 =
      ((1 - a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂) * (1 - q)) * β 0) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂))) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * β 1) :=
  PartII.Ch09.BaileyTransformBeta_one_terms a q ρ₁ ρ₂ β

theorem exercise9_BaileyTransformBeta_two_expand (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 2 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2) * β 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1) * β 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0) * β 2) :=
  PartII.Ch09.BaileyTransformBeta_two_expand a q ρ₁ ρ₂ β

theorem exercise9_BaileyTransformBeta_three_expand (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 3 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3) * β 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2) * β 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1) * β 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0) * β 3) :=
  PartII.Ch09.BaileyTransformBeta_three_expand a q ρ₁ ρ₂ β

theorem exercise9_BaileyTransformBeta_four_expand (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 4 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 4) * β 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 3) * β 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 2) * β 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 1) * β 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0) * β 4) :=
  PartII.Ch09.BaileyTransformBeta_four_expand a q ρ₁ ρ₂ β

theorem exercise9_BaileyTransformBeta_six_expand (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 6 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 6) * β 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 5) * β 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 4) * β 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 3) * β 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 2) * β 4) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 1) * β 5) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0) * β 6) :=
  PartII.Ch09.BaileyTransformBeta_six_expand a q ρ₁ ρ₂ β

theorem exercise9_BaileyTransformBeta_of_pair_one_expand
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 1) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 1 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 1) * PartII.Ch09.BaileyBeta a q α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 0) * PartII.Ch09.BaileyBeta a q α 1) :=
  PartII.Ch09.BaileyTransformBeta_of_pair_one_expand a q ρ₁ ρ₂ h

theorem exercise9_BaileyTransformBeta_of_pair_one_terms
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 1) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 1 =
      ((1 - a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂) * (1 - q)) * α 0) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂))) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) *
          (α 0 / ((1 - q) * (1 - a * q)) + α 1 / qPoch (a * q) q 2)) :=
  PartII.Ch09.BaileyTransformBeta_of_pair_one_terms a q ρ₁ ρ₂ h

theorem exercise9_BaileyTransformBeta_of_pair_two_expand
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 2) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 2 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2) * PartII.Ch09.BaileyBeta a q α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1) * PartII.Ch09.BaileyBeta a q α 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0) * PartII.Ch09.BaileyBeta a q α 2) :=
  PartII.Ch09.BaileyTransformBeta_of_pair_two_expand a q ρ₁ ρ₂ h

theorem exercise9_BaileyTransformBeta_of_pair_three_expand
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 3) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 3 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3) * PartII.Ch09.BaileyBeta a q α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2) * PartII.Ch09.BaileyBeta a q α 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1) * PartII.Ch09.BaileyBeta a q α 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0) * PartII.Ch09.BaileyBeta a q α 3) :=
  PartII.Ch09.BaileyTransformBeta_of_pair_three_expand a q ρ₁ ρ₂ h

theorem exercise9_BaileyTransformBeta_of_pair_three_terms
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 3) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 3 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3) * α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2) *
        (α 0 / ((1 - q) * (1 - a * q)) + α 1 / qPoch (a * q) q 2)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1) *
        (α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
          α 1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
          α 2 / qPoch (a * q) q 4)) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0) *
        (α 0 / (qPochhammer q 3 * qPoch (a * q) q 3) +
          α 1 / (qPochhammer q 2 * qPoch (a * q) q 4) +
          α 2 / (qPochhammer q 1 * qPoch (a * q) q 5) +
          α 3 / qPoch (a * q) q 6)) :=
  PartII.Ch09.BaileyTransformBeta_of_pair_three_terms a q ρ₁ ρ₂ h

theorem exercise9_BaileyTransformBeta_of_pair_four_expand
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 4) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 4 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 4) * PartII.Ch09.BaileyBeta a q α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 3) * PartII.Ch09.BaileyBeta a q α 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 2) * PartII.Ch09.BaileyBeta a q α 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 1) * PartII.Ch09.BaileyBeta a q α 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0) * PartII.Ch09.BaileyBeta a q α 4) :=
  PartII.Ch09.BaileyTransformBeta_of_pair_four_expand a q ρ₁ ρ₂ h

theorem exercise9_BaileyTransformBeta_of_pair_six_expand
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 6) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 6 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 6) * PartII.Ch09.BaileyBeta a q α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 5) * PartII.Ch09.BaileyBeta a q α 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 4) * PartII.Ch09.BaileyBeta a q α 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 3) * PartII.Ch09.BaileyBeta a q α 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 2) * PartII.Ch09.BaileyBeta a q α 4) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 1) * PartII.Ch09.BaileyBeta a q α 5) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0) * PartII.Ch09.BaileyBeta a q α 6) :=
  PartII.Ch09.BaileyTransformBeta_of_pair_six_expand a q ρ₁ ρ₂ h

theorem exercise9_BaileyTransformBeta_of_pair_six_terms
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 6) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 6 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 6) * α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 5) *
        (α 0 / ((1 - q) * (1 - a * q)) + α 1 / qPoch (a * q) q 2)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 4) *
        (α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
          α 1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
          α 2 / qPoch (a * q) q 4)) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 3) *
        (α 0 / (qPochhammer q 3 * qPoch (a * q) q 3) +
          α 1 / (qPochhammer q 2 * qPoch (a * q) q 4) +
          α 2 / (qPochhammer q 1 * qPoch (a * q) q 5) +
          α 3 / qPoch (a * q) q 6)) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 2) *
        (α 0 / (qPochhammer q 4 * qPoch (a * q) q 4) +
          α 1 / (qPochhammer q 3 * qPoch (a * q) q 5) +
          α 2 / (qPochhammer q 2 * qPoch (a * q) q 6) +
          α 3 / (qPochhammer q 1 * qPoch (a * q) q 7) +
          α 4 / qPoch (a * q) q 8)) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 1) *
        (α 0 / (qPochhammer q 5 * qPoch (a * q) q 5) +
          α 1 / (qPochhammer q 4 * qPoch (a * q) q 6) +
          α 2 / (qPochhammer q 3 * qPoch (a * q) q 7) +
          α 3 / (qPochhammer q 2 * qPoch (a * q) q 8) +
          α 4 / (qPochhammer q 1 * qPoch (a * q) q 9) +
          α 5 / qPoch (a * q) q 10)) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0) *
        (α 0 / (qPochhammer q 6 * qPoch (a * q) q 6) +
          α 1 / (qPochhammer q 5 * qPoch (a * q) q 7) +
          α 2 / (qPochhammer q 4 * qPoch (a * q) q 8) +
          α 3 / (qPochhammer q 3 * qPoch (a * q) q 9) +
          α 4 / (qPochhammer q 2 * qPoch (a * q) q 10) +
          α 5 / (qPochhammer q 1 * qPoch (a * q) q 11) +
          α 6 / qPoch (a * q) q 12)) :=
  PartII.Ch09.BaileyTransformBeta_of_pair_six_terms a q ρ₁ ρ₂ h

theorem exercise9_BaileyTransformBeta_rrBeta_one_expand (a q ρ₁ ρ₂ : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ (PartII.Ch09.rrBeta a q) 1 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 1) * 1) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 0) * PartII.Ch09.rrBeta a q 1) :=
  PartII.Ch09.BaileyTransformBeta_rrBeta_one_expand a q ρ₁ ρ₂ ha

theorem exercise9_BaileyTransformBeta_rrBeta_one_terms (a q ρ₁ ρ₂ : R)
    (ha : 1 - a ≠ 0) (haq : 1 - a * q ≠ 0) (haq2 : 1 - a * q ^ 2 ≠ 0) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ (PartII.Ch09.rrBeta a q) 1 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 1) * 1) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 0) *
        (1 / ((1 - q) * (1 - a * q)) +
        (-(1 - a * q ^ 2) / ((1 - a) * ((1 - a * q) * (1 - a * q ^ 2)))))) :=
  PartII.Ch09.BaileyTransformBeta_rrBeta_one_terms a q ρ₁ ρ₂ ha haq haq2

theorem exercise9_BaileyTransformBeta_rrBeta_two_expand (a q ρ₁ ρ₂ : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ (PartII.Ch09.rrBeta a q) 2 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2) * 1) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1) * PartII.Ch09.rrBeta a q 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0) * PartII.Ch09.rrBeta a q 2) :=
  PartII.Ch09.BaileyTransformBeta_rrBeta_two_expand a q ρ₁ ρ₂ ha

theorem exercise9_BaileyTransformBeta_rrBeta_two_terms (a q ρ₁ ρ₂ : R)
    (ha : 1 - a ≠ 0) (haq : 1 - a * q ≠ 0) (haq2 : 1 - a * q ^ 2 ≠ 0) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ (PartII.Ch09.rrBeta a q) 2 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2) * 1) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1) *
        (1 / ((1 - q) * (1 - a * q)) +
        (-(1 - a * q ^ 2) / ((1 - a) * ((1 - a * q) * (1 - a * q ^ 2)))))) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0) *
        (1 / (qPochhammer q 2 * qPoch (a * q) q 2) +
        ((-(1 - a * q ^ 2) / (1 - a)) /
          (qPochhammer q 1 * qPoch (a * q) q 3)) +
        ((q * (1 - a * q ^ 4) / (1 - a)) / qPoch (a * q) q 4))) :=
  PartII.Ch09.BaileyTransformBeta_rrBeta_two_terms a q ρ₁ ρ₂ ha haq haq2

theorem exercise9_BaileyTransformBeta_rrBeta_three_expand (a q ρ₁ ρ₂ : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ (PartII.Ch09.rrBeta a q) 3 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3) * 1) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2) * PartII.Ch09.rrBeta a q 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1) * PartII.Ch09.rrBeta a q 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0) * PartII.Ch09.rrBeta a q 3) :=
  PartII.Ch09.BaileyTransformBeta_rrBeta_three_expand a q ρ₁ ρ₂ ha

theorem exercise9_BaileyTransformBeta_rrBeta_three_terms (a q ρ₁ ρ₂ : R)
    (ha : 1 - a ≠ 0) (haq : 1 - a * q ≠ 0) (haq2 : 1 - a * q ^ 2 ≠ 0) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ (PartII.Ch09.rrBeta a q) 3 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3) * 1) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2) *
        (1 / ((1 - q) * (1 - a * q)) +
        (-(1 - a * q ^ 2) / ((1 - a) * ((1 - a * q) * (1 - a * q ^ 2)))))) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1) *
        (1 / (qPochhammer q 2 * qPoch (a * q) q 2) +
        ((-(1 - a * q ^ 2) / (1 - a)) /
          (qPochhammer q 1 * qPoch (a * q) q 3)) +
        ((q * (1 - a * q ^ 4) / (1 - a)) / qPoch (a * q) q 4))) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0) *
        (1 / (qPochhammer q 3 * qPoch (a * q) q 3) +
        ((-(1 - a * q ^ 2) / (1 - a)) /
          (qPochhammer q 2 * qPoch (a * q) q 4)) +
        ((q * (1 - a * q ^ 4) / (1 - a)) /
          (qPochhammer q 1 * qPoch (a * q) q 5)) +
        ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) / qPoch (a * q) q 6))) :=
  PartII.Ch09.BaileyTransformBeta_rrBeta_three_terms a q ρ₁ ρ₂ ha haq haq2

theorem exercise9_IsBaileyPairUpTo_mono {a q : R} {α β : Nat → R} {M N : Nat}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β N) (hMN : M ≤ N) :
    PartII.Ch09.IsBaileyPairUpTo a q α β M :=
  PartII.Ch09.IsBaileyPairUpTo.mono h hMN

theorem exercise9_IsBaileyPairUpTo_zero {a q : R} {α β : Nat → R} {N : Nat}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β N) :
    β 0 = PartII.Ch09.BaileyBeta a q α 0 :=
  PartII.Ch09.IsBaileyPairUpTo.zero h

theorem exercise9_IsBaileyPairUpTo_zero_of_one {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 1) :
    β 0 = PartII.Ch09.BaileyBeta a q α 0 :=
  PartII.Ch09.IsBaileyPairUpTo.zero_of_one h

theorem exercise9_IsBaileyPairUpTo_one {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 1) :
    β 1 = PartII.Ch09.BaileyBeta a q α 1 :=
  PartII.Ch09.IsBaileyPairUpTo.one h

theorem exercise9_IsBaileyPairUpTo_two {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 2) :
    β 2 = PartII.Ch09.BaileyBeta a q α 2 :=
  PartII.Ch09.IsBaileyPairUpTo.two h

theorem exercise9_IsBaileyPairUpTo_one_of_two {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 2) :
    β 1 = PartII.Ch09.BaileyBeta a q α 1 :=
  PartII.Ch09.IsBaileyPairUpTo.one_of_two h

theorem exercise9_IsBaileyPairUpTo_three {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 3) :
    β 3 = PartII.Ch09.BaileyBeta a q α 3 :=
  PartII.Ch09.IsBaileyPairUpTo.three h

theorem exercise9_IsBaileyPairUpTo_one_of_three {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 3) :
    β 1 = PartII.Ch09.BaileyBeta a q α 1 :=
  PartII.Ch09.IsBaileyPairUpTo.one_of_three h

theorem exercise9_IsBaileyPairUpTo_two_of_three {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 3) :
    β 2 = PartII.Ch09.BaileyBeta a q α 2 :=
  PartII.Ch09.IsBaileyPairUpTo.two_of_three h

theorem exercise9_IsBaileyPairUpTo_four {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 4) :
    β 4 = PartII.Ch09.BaileyBeta a q α 4 :=
  PartII.Ch09.IsBaileyPairUpTo.four h

theorem exercise9_IsBaileyPairUpTo_one_of_four {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 4) :
    β 1 = PartII.Ch09.BaileyBeta a q α 1 :=
  PartII.Ch09.IsBaileyPairUpTo.one_of_four h

theorem exercise9_IsBaileyPairUpTo_two_of_four {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 4) :
    β 2 = PartII.Ch09.BaileyBeta a q α 2 :=
  PartII.Ch09.IsBaileyPairUpTo.two_of_four h

theorem exercise9_IsBaileyPairUpTo_three_of_four {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 4) :
    β 3 = PartII.Ch09.BaileyBeta a q α 3 :=
  PartII.Ch09.IsBaileyPairUpTo.three_of_four h

theorem exercise9_IsBaileyPairUpTo_five {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 5) :
    β 5 = PartII.Ch09.BaileyBeta a q α 5 :=
  PartII.Ch09.IsBaileyPairUpTo.five h

theorem exercise9_IsBaileyPairUpTo_one_of_five {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 5) :
    β 1 = PartII.Ch09.BaileyBeta a q α 1 :=
  PartII.Ch09.IsBaileyPairUpTo.one_of_five h

theorem exercise9_IsBaileyPairUpTo_two_of_five {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 5) :
    β 2 = PartII.Ch09.BaileyBeta a q α 2 :=
  PartII.Ch09.IsBaileyPairUpTo.two_of_five h

theorem exercise9_IsBaileyPairUpTo_three_of_five {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 5) :
    β 3 = PartII.Ch09.BaileyBeta a q α 3 :=
  PartII.Ch09.IsBaileyPairUpTo.three_of_five h

theorem exercise9_IsBaileyPairUpTo_four_of_five {a q : R} {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 5) :
    β 4 = PartII.Ch09.BaileyBeta a q α 4 :=
  PartII.Ch09.IsBaileyPairUpTo.four_of_five h

theorem exercise9_IsBaileyPairUpTo_of_zero {a q : R} {α β : Nat → R}
    (h0 : β 0 = PartII.Ch09.BaileyBeta a q α 0) :
    PartII.Ch09.IsBaileyPairUpTo a q α β 0 :=
  PartII.Ch09.IsBaileyPairUpTo.of_zero h0

theorem exercise9_IsBaileyPairUpTo_of_one {a q : R} {α β : Nat → R}
    (h0 : β 0 = PartII.Ch09.BaileyBeta a q α 0)
    (h1 : β 1 = PartII.Ch09.BaileyBeta a q α 1) :
    PartII.Ch09.IsBaileyPairUpTo a q α β 1 :=
  PartII.Ch09.IsBaileyPairUpTo.of_one h0 h1

theorem exercise9_IsBaileyPairUpTo_of_two {a q : R} {α β : Nat → R}
    (h0 : β 0 = PartII.Ch09.BaileyBeta a q α 0)
    (h1 : β 1 = PartII.Ch09.BaileyBeta a q α 1)
    (h2 : β 2 = PartII.Ch09.BaileyBeta a q α 2) :
    PartII.Ch09.IsBaileyPairUpTo a q α β 2 :=
  PartII.Ch09.IsBaileyPairUpTo.of_two h0 h1 h2

theorem exercise9_IsBaileyPairUpTo_of_three {a q : R} {α β : Nat → R}
    (h0 : β 0 = PartII.Ch09.BaileyBeta a q α 0)
    (h1 : β 1 = PartII.Ch09.BaileyBeta a q α 1)
    (h2 : β 2 = PartII.Ch09.BaileyBeta a q α 2)
    (h3 : β 3 = PartII.Ch09.BaileyBeta a q α 3) :
    PartII.Ch09.IsBaileyPairUpTo a q α β 3 :=
  PartII.Ch09.IsBaileyPairUpTo.of_three h0 h1 h2 h3

theorem exercise9_IsBaileyPairUpTo_of_four {a q : R} {α β : Nat → R}
    (h0 : β 0 = PartII.Ch09.BaileyBeta a q α 0)
    (h1 : β 1 = PartII.Ch09.BaileyBeta a q α 1)
    (h2 : β 2 = PartII.Ch09.BaileyBeta a q α 2)
    (h3 : β 3 = PartII.Ch09.BaileyBeta a q α 3)
    (h4 : β 4 = PartII.Ch09.BaileyBeta a q α 4) :
    PartII.Ch09.IsBaileyPairUpTo a q α β 4 :=
  PartII.Ch09.IsBaileyPairUpTo.of_four h0 h1 h2 h3 h4

theorem exercise9_IsBaileyPairUpTo_of_five {a q : R} {α β : Nat → R}
    (h0 : β 0 = PartII.Ch09.BaileyBeta a q α 0)
    (h1 : β 1 = PartII.Ch09.BaileyBeta a q α 1)
    (h2 : β 2 = PartII.Ch09.BaileyBeta a q α 2)
    (h3 : β 3 = PartII.Ch09.BaileyBeta a q α 3)
    (h4 : β 4 = PartII.Ch09.BaileyBeta a q α 4)
    (h5 : β 5 = PartII.Ch09.BaileyBeta a q α 5) :
    PartII.Ch09.IsBaileyPairUpTo a q α β 5 :=
  PartII.Ch09.IsBaileyPairUpTo.of_five h0 h1 h2 h3 h4 h5

theorem exercise9_IsBaileyPairUpTo_of_six {a q : R} {α β : Nat → R}
    (h0 : β 0 = PartII.Ch09.BaileyBeta a q α 0)
    (h1 : β 1 = PartII.Ch09.BaileyBeta a q α 1)
    (h2 : β 2 = PartII.Ch09.BaileyBeta a q α 2)
    (h3 : β 3 = PartII.Ch09.BaileyBeta a q α 3)
    (h4 : β 4 = PartII.Ch09.BaileyBeta a q α 4)
    (h5 : β 5 = PartII.Ch09.BaileyBeta a q α 5)
    (h6 : β 6 = PartII.Ch09.BaileyBeta a q α 6) :
    PartII.Ch09.IsBaileyPairUpTo a q α β 6 :=
  PartII.Ch09.IsBaileyPairUpTo.of_six h0 h1 h2 h3 h4 h5 h6

theorem exercise9_isBaileyPairUpTo_one_iff {a q : R} {α β : Nat → R} :
    PartII.Ch09.IsBaileyPairUpTo a q α β 1 ↔
      β 0 = PartII.Ch09.BaileyBeta a q α 0 ∧
        β 1 = PartII.Ch09.BaileyBeta a q α 1 :=
  PartII.Ch09.isBaileyPairUpTo_one_iff

theorem exercise9_isBaileyPairUpTo_two_iff {a q : R} {α β : Nat → R} :
    PartII.Ch09.IsBaileyPairUpTo a q α β 2 ↔
      β 0 = PartII.Ch09.BaileyBeta a q α 0 ∧
        β 1 = PartII.Ch09.BaileyBeta a q α 1 ∧
        β 2 = PartII.Ch09.BaileyBeta a q α 2 :=
  PartII.Ch09.isBaileyPairUpTo_two_iff

theorem exercise9_isBaileyPairUpTo_three_iff {a q : R} {α β : Nat → R} :
    PartII.Ch09.IsBaileyPairUpTo a q α β 3 ↔
      β 0 = PartII.Ch09.BaileyBeta a q α 0 ∧
        β 1 = PartII.Ch09.BaileyBeta a q α 1 ∧
        β 2 = PartII.Ch09.BaileyBeta a q α 2 ∧
        β 3 = PartII.Ch09.BaileyBeta a q α 3 :=
  PartII.Ch09.isBaileyPairUpTo_three_iff

theorem exercise9_isBaileyPairUpTo_four_iff {a q : R} {α β : Nat → R} :
    PartII.Ch09.IsBaileyPairUpTo a q α β 4 ↔
      β 0 = PartII.Ch09.BaileyBeta a q α 0 ∧
        β 1 = PartII.Ch09.BaileyBeta a q α 1 ∧
        β 2 = PartII.Ch09.BaileyBeta a q α 2 ∧
        β 3 = PartII.Ch09.BaileyBeta a q α 3 ∧
        β 4 = PartII.Ch09.BaileyBeta a q α 4 :=
  PartII.Ch09.isBaileyPairUpTo_four_iff

theorem exercise9_isBaileyPairUpTo_five_iff {a q : R} {α β : Nat → R} :
    PartII.Ch09.IsBaileyPairUpTo a q α β 5 ↔
      β 0 = PartII.Ch09.BaileyBeta a q α 0 ∧
        β 1 = PartII.Ch09.BaileyBeta a q α 1 ∧
        β 2 = PartII.Ch09.BaileyBeta a q α 2 ∧
        β 3 = PartII.Ch09.BaileyBeta a q α 3 ∧
        β 4 = PartII.Ch09.BaileyBeta a q α 4 ∧
        β 5 = PartII.Ch09.BaileyBeta a q α 5 :=
  PartII.Ch09.isBaileyPairUpTo_five_iff

theorem exercise9_isBaileyPairUpTo_six_iff {a q : R} {α β : Nat → R} :
    PartII.Ch09.IsBaileyPairUpTo a q α β 6 ↔
      β 0 = PartII.Ch09.BaileyBeta a q α 0 ∧
        β 1 = PartII.Ch09.BaileyBeta a q α 1 ∧
        β 2 = PartII.Ch09.BaileyBeta a q α 2 ∧
        β 3 = PartII.Ch09.BaileyBeta a q α 3 ∧
        β 4 = PartII.Ch09.BaileyBeta a q α 4 ∧
        β 5 = PartII.Ch09.BaileyBeta a q α 5 ∧
        β 6 = PartII.Ch09.BaileyBeta a q α 6 :=
  PartII.Ch09.isBaileyPairUpTo_six_iff

theorem exercise9_BaileyBeta_four_expand (a q : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q α 4 =
      PartII.Ch09.BaileyTerm a q α 4 0 +
      PartII.Ch09.BaileyTerm a q α 4 1 +
      PartII.Ch09.BaileyTerm a q α 4 2 +
      PartII.Ch09.BaileyTerm a q α 4 3 +
      PartII.Ch09.BaileyTerm a q α 4 4 :=
  PartII.Ch09.BaileyBeta_four_expand a q α

theorem exercise9_BaileyBeta_five_expand (a q : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q α 5 =
      PartII.Ch09.BaileyTerm a q α 5 0 +
      PartII.Ch09.BaileyTerm a q α 5 1 +
      PartII.Ch09.BaileyTerm a q α 5 2 +
      PartII.Ch09.BaileyTerm a q α 5 3 +
      PartII.Ch09.BaileyTerm a q α 5 4 +
      PartII.Ch09.BaileyTerm a q α 5 5 :=
  PartII.Ch09.BaileyBeta_five_expand a q α

theorem exercise9_BaileyBeta_six_expand (a q : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q α 6 =
      PartII.Ch09.BaileyTerm a q α 6 0 +
      PartII.Ch09.BaileyTerm a q α 6 1 +
      PartII.Ch09.BaileyTerm a q α 6 2 +
      PartII.Ch09.BaileyTerm a q α 6 3 +
      PartII.Ch09.BaileyTerm a q α 6 4 +
      PartII.Ch09.BaileyTerm a q α 6 5 +
      PartII.Ch09.BaileyTerm a q α 6 6 :=
  PartII.Ch09.BaileyBeta_six_expand a q α

theorem exercise9_BaileyBeta_five_terms (a q : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q α 5 =
      α 0 / (qPochhammer q 5 * qPoch (a * q) q 5) +
      α 1 / (qPochhammer q 4 * qPoch (a * q) q 6) +
      α 2 / (qPochhammer q 3 * qPoch (a * q) q 7) +
      α 3 / (qPochhammer q 2 * qPoch (a * q) q 8) +
      α 4 / (qPochhammer q 1 * qPoch (a * q) q 9) +
      α 5 / qPoch (a * q) q 10 :=
  PartII.Ch09.BaileyBeta_five_terms a q α

theorem exercise9_BaileyBeta_six_terms (a q : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q α 6 =
      α 0 / (qPochhammer q 6 * qPoch (a * q) q 6) +
      α 1 / (qPochhammer q 5 * qPoch (a * q) q 7) +
      α 2 / (qPochhammer q 4 * qPoch (a * q) q 8) +
      α 3 / (qPochhammer q 3 * qPoch (a * q) q 9) +
      α 4 / (qPochhammer q 2 * qPoch (a * q) q 10) +
      α 5 / (qPochhammer q 1 * qPoch (a * q) q 11) +
      α 6 / qPoch (a * q) q 12 :=
  PartII.Ch09.BaileyBeta_six_terms a q α

theorem exercise9_bailey_beta_rrAlpha_two_expand (a q : R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.rrAlpha a q) 2 =
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 2 0 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 2 1 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 2 2 :=
  PartII.Ch09.BaileyBeta_rrAlpha_two_expand a q

theorem exercise9_bailey_term_rrAlpha_two_zero (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 2 0 =
      1 / (qPochhammer q 2 * qPoch (a * q) q 2) :=
  PartII.Ch09.BaileyTerm_rrAlpha_two_zero a q ha

theorem exercise9_bailey_term_rrAlpha_two_one (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 2 1 =
      (-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) :=
  PartII.Ch09.BaileyTerm_rrAlpha_two_one a q

theorem exercise9_bailey_term_rrAlpha_two_two (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 2 2 =
      (q * (1 - a * q ^ 4) / (1 - a)) / qPoch (a * q) q 4 :=
  PartII.Ch09.BaileyTerm_rrAlpha_two_two a q

theorem exercise9_bailey_beta_rrAlpha_two_terms (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.rrAlpha a q) 2 =
      1 / (qPochhammer q 2 * qPoch (a * q) q 2) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 3)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) / qPoch (a * q) q 4) :=
  PartII.Ch09.BaileyBeta_rrAlpha_two_terms a q ha

theorem exercise9_rrBeta_two_terms (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.rrBeta a q 2 =
      1 / (qPochhammer q 2 * qPoch (a * q) q 2) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 3)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) / qPoch (a * q) q 4) :=
  PartII.Ch09.rrBeta_two_terms a q ha

theorem exercise9_bailey_beta_rrAlpha_three_expand (a q : R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.rrAlpha a q) 3 =
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 3 0 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 3 1 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 3 2 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 3 3 :=
  PartII.Ch09.BaileyBeta_rrAlpha_three_expand a q

theorem exercise9_bailey_term_rrAlpha_three_zero (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 3 0 =
      1 / (qPochhammer q 3 * qPoch (a * q) q 3) :=
  PartII.Ch09.BaileyTerm_rrAlpha_three_zero a q ha

theorem exercise9_bailey_term_rrAlpha_three_one (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 3 1 =
      (-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 4) :=
  PartII.Ch09.BaileyTerm_rrAlpha_three_one a q

theorem exercise9_bailey_term_rrAlpha_three_two (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 3 2 =
      (q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 5) :=
  PartII.Ch09.BaileyTerm_rrAlpha_three_two a q

theorem exercise9_bailey_term_rrAlpha_three_three (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 3 3 =
      (-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) / qPoch (a * q) q 6 :=
  PartII.Ch09.BaileyTerm_rrAlpha_three_three a q

theorem exercise9_bailey_beta_rrAlpha_three_terms (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.rrAlpha a q) 3 =
      1 / (qPochhammer q 3 * qPoch (a * q) q 3) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 4)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 5)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) / qPoch (a * q) q 6) :=
  PartII.Ch09.BaileyBeta_rrAlpha_three_terms a q ha

theorem exercise9_rrBeta_three_terms (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.rrBeta a q 3 =
      1 / (qPochhammer q 3 * qPoch (a * q) q 3) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 4)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 5)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) / qPoch (a * q) q 6) :=
  PartII.Ch09.rrBeta_three_terms a q ha

theorem exercise9_bailey_beta_rrAlpha_four_expand (a q : R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.rrAlpha a q) 4 =
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 4 0 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 4 1 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 4 2 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 4 3 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 4 4 :=
  PartII.Ch09.BaileyBeta_rrAlpha_four_expand a q

theorem exercise9_bailey_term_rrAlpha_four_zero (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 4 0 =
      1 / (qPochhammer q 4 * qPoch (a * q) q 4) :=
  PartII.Ch09.BaileyTerm_rrAlpha_four_zero a q ha

theorem exercise9_bailey_term_rrAlpha_four_one (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 4 1 =
      (-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 5) :=
  PartII.Ch09.BaileyTerm_rrAlpha_four_one a q

theorem exercise9_bailey_term_rrAlpha_four_two (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 4 2 =
      (q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 6) :=
  PartII.Ch09.BaileyTerm_rrAlpha_four_two a q

theorem exercise9_bailey_term_rrAlpha_four_three (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 4 3 =
      (-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 7) :=
  PartII.Ch09.BaileyTerm_rrAlpha_four_three a q

theorem exercise9_bailey_term_rrAlpha_four_four (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 4 4 =
      (q ^ 6 * (1 - a * q ^ 8) / (1 - a)) / qPoch (a * q) q 8 :=
  PartII.Ch09.BaileyTerm_rrAlpha_four_four a q

theorem exercise9_bailey_beta_rrAlpha_four_terms (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.rrAlpha a q) 4 =
      1 / (qPochhammer q 4 * qPoch (a * q) q 4) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 5)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 6)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 7)) +
      ((q ^ 6 * (1 - a * q ^ 8) / (1 - a)) / qPoch (a * q) q 8) :=
  PartII.Ch09.BaileyBeta_rrAlpha_four_terms a q ha

theorem exercise9_rrBeta_four_terms (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.rrBeta a q 4 =
      1 / (qPochhammer q 4 * qPoch (a * q) q 4) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 5)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 6)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 7)) +
      ((q ^ 6 * (1 - a * q ^ 8) / (1 - a)) / qPoch (a * q) q 8) :=
  PartII.Ch09.rrBeta_four_terms a q ha

theorem exercise9_bailey_beta_rrAlpha_five_expand (a q : R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.rrAlpha a q) 5 =
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 5 0 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 5 1 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 5 2 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 5 3 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 5 4 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 5 5 :=
  PartII.Ch09.BaileyBeta_rrAlpha_five_expand a q

theorem exercise9_bailey_term_rrAlpha_five_zero (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 5 0 =
      1 / (qPochhammer q 5 * qPoch (a * q) q 5) :=
  PartII.Ch09.BaileyTerm_rrAlpha_five_zero a q ha

theorem exercise9_bailey_term_rrAlpha_five_one (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 5 1 =
      (-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 4 * qPoch (a * q) q 6) :=
  PartII.Ch09.BaileyTerm_rrAlpha_five_one a q

theorem exercise9_bailey_term_rrAlpha_five_two (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 5 2 =
      (q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 7) :=
  PartII.Ch09.BaileyTerm_rrAlpha_five_two a q

theorem exercise9_bailey_term_rrAlpha_five_three (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 5 3 =
      (-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 8) :=
  PartII.Ch09.BaileyTerm_rrAlpha_five_three a q

theorem exercise9_bailey_term_rrAlpha_five_four (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 5 4 =
      (q ^ 6 * (1 - a * q ^ 8) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 9) :=
  PartII.Ch09.BaileyTerm_rrAlpha_five_four a q

theorem exercise9_bailey_term_rrAlpha_five_five (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 5 5 =
      (-(q ^ 10 * (1 - a * q ^ 10)) / (1 - a)) /
        qPoch (a * q) q 10 :=
  PartII.Ch09.BaileyTerm_rrAlpha_five_five a q

theorem exercise9_bailey_beta_rrAlpha_five_terms (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.rrAlpha a q) 5 =
      1 / (qPochhammer q 5 * qPoch (a * q) q 5) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 4 * qPoch (a * q) q 6)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 7)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 8)) +
      ((q ^ 6 * (1 - a * q ^ 8) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 9)) +
      ((-(q ^ 10 * (1 - a * q ^ 10)) / (1 - a)) /
        qPoch (a * q) q 10) :=
  PartII.Ch09.BaileyBeta_rrAlpha_five_terms a q ha

theorem exercise9_rrBeta_five_terms (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.rrBeta a q 5 =
      1 / (qPochhammer q 5 * qPoch (a * q) q 5) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 4 * qPoch (a * q) q 6)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 7)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 8)) +
      ((q ^ 6 * (1 - a * q ^ 8) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 9)) +
      ((-(q ^ 10 * (1 - a * q ^ 10)) / (1 - a)) /
        qPoch (a * q) q 10) :=
  PartII.Ch09.rrBeta_five_terms a q ha

theorem exercise9_bailey_beta_rrAlpha_six_expand (a q : R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.rrAlpha a q) 6 =
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 6 0 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 6 1 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 6 2 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 6 3 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 6 4 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 6 5 +
      PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 6 6 :=
  PartII.Ch09.BaileyBeta_rrAlpha_six_expand a q

theorem exercise9_bailey_term_rrAlpha_six_zero (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 6 0 =
      1 / (qPochhammer q 6 * qPoch (a * q) q 6) :=
  PartII.Ch09.BaileyTerm_rrAlpha_six_zero a q ha

theorem exercise9_bailey_term_rrAlpha_six_one (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 6 1 =
      (-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 5 * qPoch (a * q) q 7) :=
  PartII.Ch09.BaileyTerm_rrAlpha_six_one a q

theorem exercise9_bailey_term_rrAlpha_six_two (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 6 2 =
      (q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 4 * qPoch (a * q) q 8) :=
  PartII.Ch09.BaileyTerm_rrAlpha_six_two a q

theorem exercise9_bailey_term_rrAlpha_six_three (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 6 3 =
      (-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 9) :=
  PartII.Ch09.BaileyTerm_rrAlpha_six_three a q

theorem exercise9_bailey_term_rrAlpha_six_four (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 6 4 =
      (q ^ 6 * (1 - a * q ^ 8) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 10) :=
  PartII.Ch09.BaileyTerm_rrAlpha_six_four a q

theorem exercise9_bailey_term_rrAlpha_six_five (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 6 5 =
      (-(q ^ 10 * (1 - a * q ^ 10)) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 11) :=
  PartII.Ch09.BaileyTerm_rrAlpha_six_five a q

theorem exercise9_bailey_term_rrAlpha_six_six (a q : R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.rrAlpha a q) 6 6 =
      (q ^ 15 * (1 - a * q ^ 12) / (1 - a)) /
        qPoch (a * q) q 12 :=
  PartII.Ch09.BaileyTerm_rrAlpha_six_six a q

theorem exercise9_bailey_beta_rrAlpha_six_terms (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.rrAlpha a q) 6 =
      1 / (qPochhammer q 6 * qPoch (a * q) q 6) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 5 * qPoch (a * q) q 7)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 4 * qPoch (a * q) q 8)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 9)) +
      ((q ^ 6 * (1 - a * q ^ 8) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 10)) +
      ((-(q ^ 10 * (1 - a * q ^ 10)) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 11)) +
      ((q ^ 15 * (1 - a * q ^ 12) / (1 - a)) /
        qPoch (a * q) q 12) :=
  PartII.Ch09.BaileyBeta_rrAlpha_six_terms a q ha

theorem exercise9_rrBeta_six_terms (a q : R) (ha : 1 - a ≠ 0) :
    PartII.Ch09.rrBeta a q 6 =
      1 / (qPochhammer q 6 * qPoch (a * q) q 6) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 5 * qPoch (a * q) q 7)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 4 * qPoch (a * q) q 8)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 9)) +
      ((q ^ 6 * (1 - a * q ^ 8) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 10)) +
      ((-(q ^ 10 * (1 - a * q ^ 10)) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 11)) +
      ((q ^ 15 * (1 - a * q ^ 12) / (1 - a)) /
        qPoch (a * q) q 12) :=
  PartII.Ch09.rrBeta_six_terms a q ha

theorem exercise9_BaileyTransformAlpha_two (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α 2 =
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) * α 2 :=
  PartII.Ch09.BaileyTransformAlpha_two a q ρ₁ ρ₂ α

theorem exercise9_BaileyTransformAlpha_three (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α 3 =
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) * α 3 :=
  PartII.Ch09.BaileyTransformAlpha_three a q ρ₁ ρ₂ α

theorem exercise9_BaileyTransformAlpha_four (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α 4 =
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) * α 4 :=
  PartII.Ch09.BaileyTransformAlpha_four a q ρ₁ ρ₂ α

theorem exercise9_BaileyTransformAlpha_five (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α 5 =
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) * α 5 :=
  PartII.Ch09.BaileyTransformAlpha_five a q ρ₁ ρ₂ α

theorem exercise9_BaileyTransformAlpha_six (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α 6 =
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) * α 6 :=
  PartII.Ch09.BaileyTransformAlpha_six a q ρ₁ ρ₂ α

theorem exercise9_BaileyTransformAlpha_rrAlpha_two (a q ρ₁ ρ₂ : R) :
    PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ (PartII.Ch09.rrAlpha a q) 2 =
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) *
        (q * (1 - a * q ^ 4) / (1 - a)) :=
  PartII.Ch09.BaileyTransformAlpha_rrAlpha_two a q ρ₁ ρ₂

theorem exercise9_BaileyTransformAlpha_rrAlpha_three (a q ρ₁ ρ₂ : R) :
    PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ (PartII.Ch09.rrAlpha a q) 3 =
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) *
        (-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) :=
  PartII.Ch09.BaileyTransformAlpha_rrAlpha_three a q ρ₁ ρ₂

theorem exercise9_BaileyTransformAlpha_rrAlpha_four (a q ρ₁ ρ₂ : R) :
    PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ (PartII.Ch09.rrAlpha a q) 4 =
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) *
        (q ^ 6 * (1 - a * q ^ 8) / (1 - a)) :=
  PartII.Ch09.BaileyTransformAlpha_rrAlpha_four a q ρ₁ ρ₂

theorem exercise9_BaileyTransformAlpha_rrAlpha_five (a q ρ₁ ρ₂ : R) :
    PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ (PartII.Ch09.rrAlpha a q) 5 =
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) *
        (-(q ^ 10 * (1 - a * q ^ 10)) / (1 - a)) :=
  PartII.Ch09.BaileyTransformAlpha_rrAlpha_five a q ρ₁ ρ₂

theorem exercise9_bailey_beta_rrAlpha_one_terms (a q : R) (ha : 1 - a ≠ 0)
    (haq : 1 - a * q ≠ 0) (haq2 : 1 - a * q ^ 2 ≠ 0) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.rrAlpha a q) 1 =
      1 / ((1 - q) * (1 - a * q)) +
      (-(1 - a * q ^ 2) / ((1 - a) * ((1 - a * q) * (1 - a * q ^ 2)))) :=
  PartII.Ch09.BaileyBeta_rrAlpha_one_terms a q ha haq haq2

theorem exercise9_rrBeta_one_terms (a q : R) (ha : 1 - a ≠ 0)
    (haq : 1 - a * q ≠ 0) (haq2 : 1 - a * q ^ 2 ≠ 0) :
    PartII.Ch09.rrBeta a q 1 =
      1 / ((1 - q) * (1 - a * q)) +
      (-(1 - a * q ^ 2) / ((1 - a) * ((1 - a * q) * (1 - a * q ^ 2)))) :=
  PartII.Ch09.rrBeta_one_terms a q ha haq haq2

theorem exercise9_BaileyTerm_transformAlpha_one_zero (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 0 =
      α 0 / (qPochhammer q 1 * qPoch (a * q) q 1) :=
  PartII.Ch09.BaileyTerm_transformAlpha_one_zero a q ρ₁ ρ₂ α

theorem exercise9_BaileyTerm_transformAlpha_one_one (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyTerm a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 1 =
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        qPoch (a * q) q 2 :=
  PartII.Ch09.BaileyTerm_transformAlpha_one_one a q ρ₁ ρ₂ α

theorem exercise9_BaileyBeta_transformAlpha_one_terms (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 =
      α 0 / (qPochhammer q 1 * qPoch (a * q) q 1) +
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        qPoch (a * q) q 2 :=
  PartII.Ch09.BaileyBeta_transformAlpha_one_terms a q ρ₁ ρ₂ α

theorem exercise9_BaileyBeta_transformAlpha_one_terms_simplified
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 =
      α 0 / ((1 - q) * (1 - a * q)) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂))) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        qPoch (a * q) q 2 :=
  PartII.Ch09.BaileyBeta_transformAlpha_one_terms_simplified a q ρ₁ ρ₂ α

theorem exercise9_BaileyTransform_one_alpha_zero_coefficient_identity
    (a q ρ₁ ρ₂ : R) (hρ : ρ₁ * ρ₂ ≠ 0) :
    (1 - a * q) * (1 - a * q / (ρ₁ * ρ₂)) +
        (1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) =
      (1 - a * q / ρ₁) * (1 - a * q / ρ₂) :=
  PartII.Ch09.BaileyTransform_one_alpha_zero_coefficient_identity a q ρ₁ ρ₂ hρ

theorem exercise9_BaileyTransform_one_alpha_zero_fraction_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0) (hq : 1 - q ≠ 0) (haq : 1 - a * q ≠ 0)
    (hρ₁ : 1 - a * q / ρ₁ ≠ 0) (hρ₂ : 1 - a * q / ρ₂ ≠ 0) :
    (1 - a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂) * (1 - q)) +
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂))) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) /
          ((1 - q) * (1 - a * q)) =
      1 / ((1 - q) * (1 - a * q)) :=
  PartII.Ch09.BaileyTransform_one_alpha_zero_fraction_identity a q ρ₁ ρ₂
    hρ hq haq hρ₁ hρ₂

theorem exercise9_BaileyTransform_one_standard_terms_eq_transformAlpha_one_terms
    (a q ρ₁ ρ₂ α0 α1 : R)
    (hρ : ρ₁ * ρ₂ ≠ 0) (hq : 1 - q ≠ 0) (haq : 1 - a * q ≠ 0)
    (hρ₁ : 1 - a * q / ρ₁ ≠ 0) (hρ₂ : 1 - a * q / ρ₂ ≠ 0) :
    ((1 - a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂) * (1 - q)) * α0) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂))) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) *
          (α0 / ((1 - q) * (1 - a * q)) + α1 / qPoch (a * q) q 2)) =
      α0 / ((1 - q) * (1 - a * q)) +
        (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂))) /
          ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α1) /
          qPoch (a * q) q 2 :=
  PartII.Ch09.BaileyTransform_one_standard_terms_eq_transformAlpha_one_terms
    a q ρ₁ ρ₂ α0 α1 hρ hq haq hρ₁ hρ₂

theorem exercise9_BaileyTransform_preserves_pair_one_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 1)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hq : 1 - q ≠ 0) (haq : 1 - a * q ≠ 0)
    (hρ₁ : 1 - a * q / ρ₁ ≠ 0) (hρ₂ : 1 - a * q / ρ₂ ≠ 0) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 1 =
      PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 :=
  PartII.Ch09.BaileyTransform_preserves_pair_one_of_nonzero a q ρ₁ ρ₂ h
    hρ hq haq hρ₁ hρ₂

theorem exercise9_BaileyTransform_preserves_pair_upTo_one_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 1)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hq : 1 - q ≠ 0) (haq : 1 - a * q ≠ 0)
    (hρ₁ : 1 - a * q / ρ₁ ≠ 0) (hρ₂ : 1 - a * q / ρ₂ ≠ 0) :
    PartII.Ch09.IsBaileyPairUpTo a q
      (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α)
      (PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β) 1 :=
  PartII.Ch09.BaileyTransform_preserves_pair_upTo_one_of_nonzero a q ρ₁ ρ₂ h
    hρ hq haq hρ₁ hρ₂

theorem exercise9_BaileyTransformBeta_of_pair_two_terms
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 2) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 2 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2) * α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1) *
        (α 0 / ((1 - q) * (1 - a * q)) + α 1 / qPoch (a * q) q 2)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0) *
        (α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
          α 1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
          α 2 / qPoch (a * q) q 4)) :=
  PartII.Ch09.BaileyTransformBeta_of_pair_two_terms a q ρ₁ ρ₂ h

theorem exercise9_BaileyTransform_two_qpoch_ratio
    (a q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hB1 : (1 - q) * (1 - a * q) ≠ 0) :
    qPochhammer q 2 * qPoch (a * q) q 2 /
        (qPochhammer q 1 * ((1 - q) * (1 - a * q))) =
      (1 + q) * (1 - a * q ^ 2) :=
  PartII.Ch09.BaileyTransform_two_qpoch_ratio a q hQ1 hB1

theorem exercise9_BaileyTransform_two_alpha_zero_common_denominator_identity
    (a q ρ₁ ρ₂ : R) (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hB1 : (1 - q) * (1 - a * q) ≠ 0) :
    qPoch (a * q) q 2 * qPoch (a * q / (ρ₁ * ρ₂)) q 2 +
      qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 2 * qPoch (a * q) q 2 /
          (qPochhammer q 1 * ((1 - q) * (1 - a * q)))) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 =
      qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 :=
  PartII.Ch09.BaileyTransform_two_alpha_zero_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hB1

theorem exercise9_BaileyTransform_common_denominator_fraction_identity
    (P0 P1 P2 D Q1 Q2 A2 B : R)
    (hD : D ≠ 0) (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0)
    (hA2 : A2 ≠ 0) (hB : B ≠ 0)
    (hcommon : A2 * P0 + P1 * (Q2 * A2 / (Q1 * B)) + P2 = D) :
    P0 / (D * Q2) + (P1 / (D * Q1)) / B + (P2 / D) / (Q2 * A2) =
      1 / (Q2 * A2) :=
  PartII.Ch09.BaileyTransform_common_denominator_fraction_identity
    P0 P1 P2 D Q1 Q2 A2 B hD hQ1 hQ2 hA2 hB hcommon

theorem exercise9_BaileyTransform_three_coefficient_linear_identity
    (C0 C1 C2 D0 D1 E0 E1 E2 T0 T1 T2 α0 α1 α2 : R)
    (h0 : C0 + C1 / D0 + C2 / D1 = T0)
    (h1 : C1 / E0 + C2 / E1 = T1)
    (h2 : C2 / E2 = T2) :
    C0 * α0 + C1 * (α0 / D0 + α1 / E0) +
      C2 * (α0 / D1 + α1 / E1 + α2 / E2) =
      T0 * α0 + T1 * α1 + T2 * α2 :=
  PartII.Ch09.BaileyTransform_three_coefficient_linear_identity
    C0 C1 C2 D0 D1 E0 E1 E2 T0 T1 T2 α0 α1 α2 h0 h1 h2

theorem exercise9_BaileyTransform_four_coefficient_linear_identity
    (C0 C1 C2 C3 D10 D20 D30 E10 E21 E31 E22 E32 E33
      T0 T1 T2 T3 α0 α1 α2 α3 : R)
    (h0 : C0 + C1 / D10 + C2 / D20 + C3 / D30 = T0)
    (h1 : C1 / E10 + C2 / E21 + C3 / E31 = T1)
    (h2 : C2 / E22 + C3 / E32 = T2)
    (h3 : C3 / E33 = T3) :
    C0 * α0 + C1 * (α0 / D10 + α1 / E10) +
      C2 * (α0 / D20 + α1 / E21 + α2 / E22) +
      C3 * (α0 / D30 + α1 / E31 + α2 / E32 + α3 / E33) =
      T0 * α0 + T1 * α1 + T2 * α2 + T3 * α3 :=
  PartII.Ch09.BaileyTransform_four_coefficient_linear_identity
    C0 C1 C2 C3 D10 D20 D30 E10 E21 E31 E22 E32 E33
      T0 T1 T2 T3 α0 α1 α2 α3 h0 h1 h2 h3

theorem exercise9_BaileyTransform_five_coefficient_linear_identity
    (C0 C1 C2 C3 C4 D10 D20 D30 D40 E10 E21 E31 E41
      E22 E32 E42 E33 E43 E44 T0 T1 T2 T3 T4 α0 α1 α2 α3 α4 : R)
    (h0 : C0 + C1 / D10 + C2 / D20 + C3 / D30 + C4 / D40 = T0)
    (h1 : C1 / E10 + C2 / E21 + C3 / E31 + C4 / E41 = T1)
    (h2 : C2 / E22 + C3 / E32 + C4 / E42 = T2)
    (h3 : C3 / E33 + C4 / E43 = T3)
    (h4 : C4 / E44 = T4) :
    C0 * α0 + C1 * (α0 / D10 + α1 / E10) +
      C2 * (α0 / D20 + α1 / E21 + α2 / E22) +
      C3 * (α0 / D30 + α1 / E31 + α2 / E32 + α3 / E33) +
      C4 * (α0 / D40 + α1 / E41 + α2 / E42 + α3 / E43 + α4 / E44) =
      T0 * α0 + T1 * α1 + T2 * α2 + T3 * α3 + T4 * α4 :=
  PartII.Ch09.BaileyTransform_five_coefficient_linear_identity
    C0 C1 C2 C3 C4 D10 D20 D30 D40 E10 E21 E31 E41 E22 E32 E42 E33 E43 E44
    T0 T1 T2 T3 T4 α0 α1 α2 α3 α4 h0 h1 h2 h3 h4

theorem exercise9_BaileyTransform_six_coefficient_linear_identity
    (C0 C1 C2 C3 C4 C5 D10 D20 D30 D40 D50 E10 E21 E31 E41 E51
      E22 E32 E42 E52 E33 E43 E53 E44 E54 E55
      T0 T1 T2 T3 T4 T5 α0 α1 α2 α3 α4 α5 : R)
    (h0 : C0 + C1 / D10 + C2 / D20 + C3 / D30 + C4 / D40 + C5 / D50 = T0)
    (h1 : C1 / E10 + C2 / E21 + C3 / E31 + C4 / E41 + C5 / E51 = T1)
    (h2 : C2 / E22 + C3 / E32 + C4 / E42 + C5 / E52 = T2)
    (h3 : C3 / E33 + C4 / E43 + C5 / E53 = T3)
    (h4 : C4 / E44 + C5 / E54 = T4)
    (h5 : C5 / E55 = T5) :
    C0 * α0 + C1 * (α0 / D10 + α1 / E10) +
      C2 * (α0 / D20 + α1 / E21 + α2 / E22) +
      C3 * (α0 / D30 + α1 / E31 + α2 / E32 + α3 / E33) +
      C4 * (α0 / D40 + α1 / E41 + α2 / E42 + α3 / E43 + α4 / E44) +
      C5 * (α0 / D50 + α1 / E51 + α2 / E52 + α3 / E53 + α4 / E54 +
        α5 / E55) =
      T0 * α0 + T1 * α1 + T2 * α2 + T3 * α3 + T4 * α4 + T5 * α5 :=
  PartII.Ch09.BaileyTransform_six_coefficient_linear_identity
    C0 C1 C2 C3 C4 C5 D10 D20 D30 D40 D50 E10 E21 E31 E41 E51
    E22 E32 E42 E52 E33 E43 E53 E44 E54 E55 T0 T1 T2 T3 T4 T5
    α0 α1 α2 α3 α4 α5 h0 h1 h2 h3 h4 h5

theorem exercise9_BaileyTransform_seven_coefficient_linear_identity
    (C0 C1 C2 C3 C4 C5 C6
      D10 D20 D30 D40 D50 D60
      E10 E21 E31 E41 E51 E61
      E22 E32 E42 E52 E62
      E33 E43 E53 E63
      E44 E54 E64
      E55 E65 E66
      T0 T1 T2 T3 T4 T5 T6
      α0 α1 α2 α3 α4 α5 α6 : R)
    (h0 : C0 + C1 / D10 + C2 / D20 + C3 / D30 + C4 / D40 +
      C5 / D50 + C6 / D60 = T0)
    (h1 : C1 / E10 + C2 / E21 + C3 / E31 + C4 / E41 + C5 / E51 +
      C6 / E61 = T1)
    (h2 : C2 / E22 + C3 / E32 + C4 / E42 + C5 / E52 + C6 / E62 = T2)
    (h3 : C3 / E33 + C4 / E43 + C5 / E53 + C6 / E63 = T3)
    (h4 : C4 / E44 + C5 / E54 + C6 / E64 = T4)
    (h5 : C5 / E55 + C6 / E65 = T5)
    (h6 : C6 / E66 = T6) :
    C0 * α0 + C1 * (α0 / D10 + α1 / E10) +
      C2 * (α0 / D20 + α1 / E21 + α2 / E22) +
      C3 * (α0 / D30 + α1 / E31 + α2 / E32 + α3 / E33) +
      C4 * (α0 / D40 + α1 / E41 + α2 / E42 + α3 / E43 + α4 / E44) +
      C5 * (α0 / D50 + α1 / E51 + α2 / E52 + α3 / E53 + α4 / E54 +
        α5 / E55) +
      C6 * (α0 / D60 + α1 / E61 + α2 / E62 + α3 / E63 + α4 / E64 +
        α5 / E65 + α6 / E66) =
      T0 * α0 + T1 * α1 + T2 * α2 + T3 * α3 + T4 * α4 + T5 * α5 +
        T6 * α6 :=
  PartII.Ch09.BaileyTransform_seven_coefficient_linear_identity
    C0 C1 C2 C3 C4 C5 C6 D10 D20 D30 D40 D50 D60 E10 E21 E31 E41 E51 E61
    E22 E32 E42 E52 E62 E33 E43 E53 E63 E44 E54 E64 E55 E65 E66
    T0 T1 T2 T3 T4 T5 T6 α0 α1 α2 α3 α4 α5 α6 h0 h1 h2 h3 h4 h5 h6

theorem exercise9_BaileyTransform_two_alpha_zero_fraction_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hB1 : (1 - q) * (1 - a * q) ≠ 0) :
    ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2)) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1)) / ((1 - q) * (1 - a * q)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0)) /
        (qPochhammer q 2 * qPoch (a * q) q 2) =
      1 / (qPochhammer q 2 * qPoch (a * q) q 2) :=
  PartII.Ch09.BaileyTransform_two_alpha_zero_fraction_identity
    a q ρ₁ ρ₂ hρ hD1 hD2 hQ1 hQ2 hA2 hB1

theorem exercise9_BaileyTransform_two_alpha_one_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1)) / qPoch (a * q) q 2 +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) =
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) :=
  PartII.Ch09.BaileyTransform_two_alpha_one_coefficient_identity a q ρ₁ ρ₂
    hρ hD1 hD2 hD1one hD2one hQ1 hA2 hA3

theorem exercise9_BaileyTransform_two_alpha_two_coefficient_identity
    (a q ρ₁ ρ₂ : R) :
    ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0)) / qPoch (a * q) q 4 =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
        qPoch (a * q) q 4 :=
  PartII.Ch09.BaileyTransform_two_alpha_two_coefficient_identity a q ρ₁ ρ₂

theorem exercise9_BaileyTransform_two_standard_terms_eq_transformAlpha_two_terms
    (a q ρ₁ ρ₂ α0 α1 α2 : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hB1 : (1 - q) * (1 - a * q) ≠ 0) :
    (((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2)) * α0) +
      (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1)) *
        (α0 / ((1 - q) * (1 - a * q)) + α1 / qPoch (a * q) q 2)) +
      (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0)) *
        (α0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
          α1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
          α2 / qPoch (a * q) q 4)) =
      (1 / (qPochhammer q 2 * qPoch (a * q) q 2)) * α0 +
        (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 1 * qPoch (a * q) q 3)) * α1 +
        (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          qPoch (a * q) q 4)) * α2 :=
  PartII.Ch09.BaileyTransform_two_standard_terms_eq_transformAlpha_two_terms
    a q ρ₁ ρ₂ α0 α1 α2 hρ hD1 hD2 hD1one hD2one hQ1 hQ2 hA2 hA3 hB1

theorem exercise9_BaileyTransform_ratio_mul (x y u v X U : R)
    (hy : y ≠ 0) (hv : v ≠ 0)
    (hx : x / y = X) (hu : u / v = U) :
    x * u / (y * v) = X * U :=
  PartII.Ch09.BaileyTransform_ratio_mul x y u v X U hy hv hx hu

theorem exercise9_BaileyTransform_three_alpha_zero_common_denominator_simplified
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0) :
    qPoch (a * q / (ρ₁ * ρ₂)) q 3 * qPoch (a * q) q 3 +
      qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        ((1 + q + q ^ 2) * ((1 - a * q ^ 2) * (1 - a * q ^ 3))) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        ((1 + q + q ^ 2) * (1 - a * q ^ 3)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 =
      qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 :=
  PartII.Ch09.BaileyTransform_three_alpha_zero_common_denominator_simplified
    a q ρ₁ ρ₂ hρ

theorem exercise9_BaileyTransform_three_qpochhammer_three_over_one_two
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0) :
    qPochhammer q 3 / (qPochhammer q 2 * qPochhammer q 1) =
      1 + q + q ^ 2 :=
  PartII.Ch09.BaileyTransform_three_qpochhammer_three_over_one_two q hQ1 hQ2

theorem exercise9_BaileyTransform_three_qpoch_aq_three_over_one
    (a q : R) (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPoch (a * q) q 3 / qPoch (a * q) q 1 =
      (1 - a * q ^ 2) * (1 - a * q ^ 3) :=
  PartII.Ch09.BaileyTransform_three_qpoch_aq_three_over_one a q hA1

theorem exercise9_BaileyTransform_three_qpoch_aq_three_over_two
    (a q : R) (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q) q 3 / qPoch (a * q) q 2 =
      1 - a * q ^ 3 :=
  PartII.Ch09.BaileyTransform_three_qpoch_aq_three_over_two a q hA2

theorem exercise9_BaileyTransform_three_alpha_zero_first_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPochhammer q 3 * qPoch (a * q) q 3 /
        (qPochhammer q 2 * qPochhammer q 1 * qPoch (a * q) q 1) =
      (1 + q + q ^ 2) * ((1 - a * q ^ 2) * (1 - a * q ^ 3)) :=
  PartII.Ch09.BaileyTransform_three_alpha_zero_first_ratio a q hQ1 hQ2 hA1

theorem exercise9_BaileyTransform_three_alpha_zero_second_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPochhammer q 3 * qPoch (a * q) q 3 /
        (qPochhammer q 1 * qPochhammer q 2 * qPoch (a * q) q 2) =
      (1 + q + q ^ 2) * (1 - a * q ^ 3) :=
  PartII.Ch09.BaileyTransform_three_alpha_zero_second_ratio a q hQ1 hQ2 hA2

theorem exercise9_BaileyTransform_three_alpha_zero_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q / (ρ₁ * ρ₂)) q 3 * qPoch (a * q) q 3 +
      qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 3 * qPoch (a * q) q 3 /
          (qPochhammer q 2 * qPochhammer q 1 * qPoch (a * q) q 1)) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 3 * qPoch (a * q) q 3 /
          (qPochhammer q 1 * qPochhammer q 2 * qPoch (a * q) q 2)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 =
      qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 :=
  PartII.Ch09.BaileyTransform_three_alpha_zero_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hA1 hA2

theorem exercise9_BaileyTransform_four_term_fraction_from_common
    (P0 P1 P2 P3 D Q1 Q2 Q3 A1 A2 A3 : R)
    (hD : D ≠ 0) (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0) (hQ3 : Q3 ≠ 0)
    (hA1 : A1 ≠ 0) (hA2 : A2 ≠ 0) (hA3 : A3 ≠ 0)
    (hcommon : P0 * A3 + P1 * (Q3 * A3 / (Q2 * Q1 * A1)) +
      P2 * (Q3 * A3 / (Q1 * Q2 * A2)) + P3 = D) :
    P0 / (D * Q3) + (P1 / (D * Q2)) / (Q1 * A1) +
      (P2 / (D * Q1)) / (Q2 * A2) + (P3 / D) / (Q3 * A3) =
      1 / (Q3 * A3) :=
  PartII.Ch09.BaileyTransform_four_term_fraction_from_common
    P0 P1 P2 P3 D Q1 Q2 Q3 A1 A2 A3
    hD hQ1 hQ2 hQ3 hA1 hA2 hA3 hcommon

theorem exercise9_BaileyTransform_three_alpha_zero_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3)) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2)) /
        (qPochhammer q 1 * qPoch (a * q) q 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1)) /
        (qPochhammer q 2 * qPoch (a * q) q 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0)) /
        (qPochhammer q 3 * qPoch (a * q) q 3) =
      1 / (qPochhammer q 3 * qPoch (a * q) q 3) :=
  PartII.Ch09.BaileyTransform_three_alpha_zero_coefficient_identity
    a q ρ₁ ρ₂ hρ hD1 hD2 hQ1 hQ2 hQ3 hA1 hA2 hA3

theorem exercise9_BaileyTransform_three_qpochhammer_two_over_one_sq
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0) :
    qPochhammer q 2 / (qPochhammer q 1 * qPochhammer q 1) = 1 + q :=
  PartII.Ch09.BaileyTransform_three_qpochhammer_two_over_one_sq q hQ1

theorem exercise9_BaileyTransform_three_qpoch_aq_four_over_three
    (a q : R) (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPoch (a * q) q 4 / qPoch (a * q) q 3 = 1 - a * q ^ 4 :=
  PartII.Ch09.BaileyTransform_three_qpoch_aq_four_over_three a q hA3

theorem exercise9_BaileyTransform_three_qpochhammer_aq_alpha_one_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPochhammer q 2 * qPoch (a * q) q 4 /
        (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 3) =
      (1 + q) * (1 - a * q ^ 4) :=
  PartII.Ch09.BaileyTransform_three_qpochhammer_aq_alpha_one_middle_ratio
    a q hQ1 hA3

theorem exercise9_BaileyTransform_three_qpoch_aq_four_over_two
    (a q : R) (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q) q 4 / qPoch (a * q) q 2 =
      (1 - a * q ^ 3) * (1 - a * q ^ 4) :=
  PartII.Ch09.BaileyTransform_three_qpoch_aq_four_over_two a q hA2

theorem exercise9_BaileyTransform_three_qpoch_pair_ratio_one_three
    (a q ρ₁ ρ₂ : R)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0) :
    (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) =
      ((1 - (a * q / ρ₁) * q) * (1 - (a * q / ρ₁) * q ^ 2)) *
        ((1 - (a * q / ρ₂) * q) * (1 - (a * q / ρ₂) * q ^ 2)) :=
  PartII.Ch09.BaileyTransform_three_qpoch_pair_ratio_one_three
    a q ρ₁ ρ₂ hD1one hD2one

theorem exercise9_BaileyTransform_three_alpha_one_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0) :
    qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPoch (a * q) q 4 / qPoch (a * q) q 2) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 2 * qPoch (a * q) q 4 /
          (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 3)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 =
      (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) *
        ((qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) :=
  PartII.Ch09.BaileyTransform_three_alpha_one_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hA2 hA3 hD1one hD2one

theorem exercise9_BaileyTransform_three_term_fraction_from_common_ratio
    (P1 P2 P3 B D D1 Q1 Q2 A2 A3 A4 : R)
    (hD : D ≠ 0) (hD1 : D1 ≠ 0)
    (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0)
    (hA2 : A2 ≠ 0) (hA3 : A3 ≠ 0) (hA4 : A4 ≠ 0)
    (hcommon : P1 * (A4 / A2) + P2 * (Q2 * A4 / (Q1 * Q1 * A3)) +
      P3 = B * (D / D1)) :
    (P1 / (D * Q2)) / A2 + (P2 / (D * Q1)) / (Q1 * A3) +
      (P3 / D) / (Q2 * A4) =
      (B / D1) / (Q2 * A4) :=
  PartII.Ch09.BaileyTransform_three_term_fraction_from_common_ratio
    P1 P2 P3 B D D1 Q1 Q2 A2 A3 A4 hD hD1 hQ1 hQ2 hA2 hA3 hA4 hcommon

theorem exercise9_BaileyTransform_three_alpha_one_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0) :
    ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2)) / qPoch (a * q) q 2 +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0)) /
        (qPochhammer q 2 * qPoch (a * q) q 4) =
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
        (qPochhammer q 2 * qPoch (a * q) q 4) :=
  PartII.Ch09.BaileyTransform_three_alpha_one_coefficient_identity
    a q ρ₁ ρ₂ hρ hD1 hD2 hD1one hD2one hQ1 hQ2 hA2 hA3 hA4

theorem exercise9_BaileyTransform_three_qpoch_ratio_four_five
    (a q : R) (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPoch (a * q) q 5 / qPoch (a * q) q 4 = 1 - a * q ^ 5 :=
  PartII.Ch09.BaileyTransform_three_qpoch_ratio_four_five a q hA4

theorem exercise9_BaileyTransform_three_qpoch_pair_ratio_two_three
    (a q ρ₁ ρ₂ : R)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) =
      (1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 2) :=
  PartII.Ch09.BaileyTransform_three_qpoch_pair_ratio_two_three
    a q ρ₁ ρ₂ hD1two hD2two

theorem exercise9_BaileyTransform_three_alpha_two_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPoch (a * q) q 5 / qPoch (a * q) q 4) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2) *
        ((qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) :=
  PartII.Ch09.BaileyTransform_three_alpha_two_common_denominator_identity
    a q ρ₁ ρ₂ hρ hA4 hD1two hD2two

theorem exercise9_BaileyTransform_two_term_fraction_from_common_ratio
    (P0 P1 B D D2 Q A4 A5 : R)
    (hD : D ≠ 0) (hD2 : D2 ≠ 0) (hQ : Q ≠ 0)
    (hA4 : A4 ≠ 0) (hA5 : A5 ≠ 0)
    (hcommon : P0 * (A5 / A4) + P1 = B * (D / D2)) :
    (P0 / (D * Q)) / A4 + (P1 / D) / (Q * A5) =
      (B / D2) / (Q * A5) :=
  PartII.Ch09.BaileyTransform_two_term_fraction_from_common_ratio
    P0 P1 B D D2 Q A4 A5 hD hD2 hQ hA4 hA5 hcommon

theorem exercise9_BaileyTransform_three_alpha_two_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1)) / qPoch (a * q) q 4 +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0)) /
        (qPochhammer q 1 * qPoch (a * q) q 5) =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
        (qPochhammer q 1 * qPoch (a * q) q 5) :=
  PartII.Ch09.BaileyTransform_three_alpha_two_coefficient_identity
    a q ρ₁ ρ₂ hρ hD1 hD2 hD1two hD2two hQ1 hA4 hA5

theorem exercise9_BaileyTransform_three_alpha_three_coefficient_identity
    (a q ρ₁ ρ₂ : R) :
    ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0)) / qPoch (a * q) q 6 =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
        qPoch (a * q) q 6 :=
  PartII.Ch09.BaileyTransform_three_alpha_three_coefficient_identity a q ρ₁ ρ₂

theorem exercise9_BaileyTransform_four_qpoch_ratio_six_seven
    (a q : R) (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 6 = 1 - a * q ^ 7 :=
  PartII.Ch09.BaileyTransform_four_qpoch_ratio_six_seven a q hA6

theorem exercise9_BaileyTransform_four_qpoch_pair_ratio_three_four
    (a q ρ₁ ρ₂ : R)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0) :
    (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) =
      (1 - (a * q / ρ₁) * q ^ 3) *
        (1 - (a * q / ρ₂) * q ^ 3) :=
  PartII.Ch09.BaileyTransform_four_qpoch_pair_ratio_three_four
    a q ρ₁ ρ₂ hD1three hD2three

theorem exercise9_BaileyTransform_four_qpoch_aq_six_over_four
    (a q : R) (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPoch (a * q) q 6 / qPoch (a * q) q 4 =
      (1 - a * q ^ 5) * (1 - a * q ^ 6) :=
  PartII.Ch09.BaileyTransform_four_qpoch_aq_six_over_four a q hA4

theorem exercise9_BaileyTransform_four_qpoch_aq_six_over_five
    (a q : R) (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPoch (a * q) q 6 / qPoch (a * q) q 5 = 1 - a * q ^ 6 :=
  PartII.Ch09.BaileyTransform_four_qpoch_aq_six_over_five a q hA5

theorem exercise9_BaileyTransform_four_qpochhammer_aq_alpha_two_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPochhammer q 2 * qPoch (a * q) q 6 /
        (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 5) =
      (1 + q) * (1 - a * q ^ 6) :=
  PartII.Ch09.BaileyTransform_four_qpochhammer_aq_alpha_two_middle_ratio
    a q hQ1 hA5

theorem exercise9_BaileyTransform_four_qpoch_pair_ratio_two_four
    (a q ρ₁ ρ₂ : R)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) =
      ((1 - (a * q / ρ₁) * q ^ 2) * (1 - (a * q / ρ₁) * q ^ 3)) *
        ((1 - (a * q / ρ₂) * q ^ 2) * (1 - (a * q / ρ₂) * q ^ 3)) :=
  PartII.Ch09.BaileyTransform_four_qpoch_pair_ratio_two_four
    a q ρ₁ ρ₂ hD1two hD2two

theorem exercise9_BaileyTransform_four_alpha_two_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPoch (a * q) q 6 / qPoch (a * q) q 4) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 2 * qPoch (a * q) q 6 /
          (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 5)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2) *
        ((qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) :=
  PartII.Ch09.BaileyTransform_four_alpha_two_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hA4 hA5 hD1two hD2two

theorem exercise9_BaileyTransform_four_alpha_two_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 2)) / qPoch (a * q) q 4 +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 1)) /
        (qPochhammer q 1 * qPoch (a * q) q 5) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0)) /
        (qPochhammer q 2 * qPoch (a * q) q 6) =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
        (qPochhammer q 2 * qPoch (a * q) q 6) :=
  PartII.Ch09.BaileyTransform_four_alpha_two_coefficient_identity
    a q ρ₁ ρ₂ hρ hD1 hD2 hD1two hD2two hQ1 hQ2 hA4 hA5 hA6

theorem exercise9_BaileyTransform_four_alpha_three_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0) :
    qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPoch (a * q) q 7 / qPoch (a * q) q 6) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3) *
        ((qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) :=
  PartII.Ch09.BaileyTransform_four_alpha_three_common_denominator_identity
    a q ρ₁ ρ₂ hρ hA6 hD1three hD2three

theorem exercise9_BaileyTransform_four_alpha_three_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 1)) / qPoch (a * q) q 6 +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0)) /
        (qPochhammer q 1 * qPoch (a * q) q 7) =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
        (qPochhammer q 1 * qPoch (a * q) q 7) :=
  PartII.Ch09.BaileyTransform_four_alpha_three_coefficient_identity
    a q ρ₁ ρ₂ hρ hD1 hD2 hD1three hD2three hQ1 hA6 hA7

theorem exercise9_BaileyTransform_three_standard_terms_eq_transformAlpha_three_terms
    (a q ρ₁ ρ₂ α0 α1 α2 α3 : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    (((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3)) * α0) +
      (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2)) *
        (α0 / (qPochhammer q 1 * qPoch (a * q) q 1) +
          α1 / qPoch (a * q) q 2)) +
      (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1)) *
        (α0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
          α1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
          α2 / qPoch (a * q) q 4)) +
      (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0)) *
        (α0 / (qPochhammer q 3 * qPoch (a * q) q 3) +
          α1 / (qPochhammer q 2 * qPoch (a * q) q 4) +
          α2 / (qPochhammer q 1 * qPoch (a * q) q 5) +
          α3 / qPoch (a * q) q 6)) =
      (1 / (qPochhammer q 3 * qPoch (a * q) q 3)) * α0 +
        (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 2 * qPoch (a * q) q 4)) * α1 +
        (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 1 * qPoch (a * q) q 5)) * α2) +
        (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          qPoch (a * q) q 6) * α3) :=
  PartII.Ch09.BaileyTransform_three_standard_terms_eq_transformAlpha_three_terms
    a q ρ₁ ρ₂ α0 α1 α2 α3 hρ hD1 hD2 hD1one hD2one hD1two hD2two
    hQ1 hQ2 hQ3 hA1 hA2 hA3 hA4 hA5

theorem exercise9_BaileyBeta_transformAlpha_two_terms_linear
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 =
      (1 / (qPochhammer q 2 * qPoch (a * q) q 2)) * α 0 +
        (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 1 * qPoch (a * q) q 3)) * α 1 +
        (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          qPoch (a * q) q 4)) * α 2 :=
  PartII.Ch09.BaileyBeta_transformAlpha_two_terms_linear a q ρ₁ ρ₂ α

theorem exercise9_BaileyTransform_preserves_pair_two_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 2)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hB1 : (1 - q) * (1 - a * q) ≠ 0) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 2 =
      PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 :=
  PartII.Ch09.BaileyTransform_preserves_pair_two_of_nonzero a q ρ₁ ρ₂ h
    hρ hD1 hD2 hD1one hD2one hQ1 hQ2 hA2 hA3 hB1

theorem exercise9_BaileyTransform_preserves_pair_upTo_two_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 2)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hB1 : (1 - q) * (1 - a * q) ≠ 0) :
    PartII.Ch09.IsBaileyPairUpTo a q
      (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α)
      (PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β) 2 :=
  PartII.Ch09.BaileyTransform_preserves_pair_upTo_two_of_nonzero a q ρ₁ ρ₂ h
    hρ hD1 hD2 hD1one hD2one hQ1 hQ2 hA2 hA3 hB1

theorem exercise9_BaileyTransform_preserves_pair_three_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 3)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 3 =
      PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 :=
  PartII.Ch09.BaileyTransform_preserves_pair_three_of_nonzero a q ρ₁ ρ₂ h
    hρ hD1 hD2 hD1one hD2one hD1two hD2two hQ1 hQ2 hQ3 hA1 hA2 hA3 hA4 hA5

theorem exercise9_BaileyTransform_preserves_pair_upTo_three_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 3)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    PartII.Ch09.IsBaileyPairUpTo a q
      (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α)
      (PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β) 3 :=
  PartII.Ch09.BaileyTransform_preserves_pair_upTo_three_of_nonzero a q ρ₁ ρ₂ h
    hρ hD1 hD2 hD1one hD2one hD1two hD2two hQ1 hQ2 hQ3 hA1 hA2 hA3 hA4 hA5

theorem exercise9_BaileyTransform_preserves_pair_four_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 4)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 4 =
      PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 :=
  PartII.Ch09.BaileyTransform_preserves_pair_four_of_nonzero a q ρ₁ ρ₂ h
    hρ hD1 hD2 hD1one hD2one hD1two hD2two hD1three hD2three
    hQ1 hQ2 hQ3 hQ4 hA1 hA2 hA3 hA4 hA5 hA6 hA7

theorem exercise9_BaileyTransform_preserves_pair_upTo_four_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 4)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    PartII.Ch09.IsBaileyPairUpTo a q
      (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α)
      (PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β) 4 :=
  PartII.Ch09.BaileyTransform_preserves_pair_upTo_four_of_nonzero a q ρ₁ ρ₂ h
    hρ hD1 hD2 hD1one hD2one hD1two hD2two hD1three hD2three
    hQ1 hQ2 hQ3 hQ4 hA1 hA2 hA3 hA4 hA5 hA6 hA7

theorem exercise9_BaileyTransform_preserves_pair_five_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 5)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β 5 =
      PartII.Ch09.BaileyBeta a q (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 :=
  PartII.Ch09.BaileyTransform_preserves_pair_five_of_nonzero a q ρ₁ ρ₂ h
    hρ hD1 hD2 hD1one hD2one hD1two hD2two hD1three hD2three
    hD1four hD2four hQ1 hQ2 hQ3 hQ4 hQ5 hA1 hA2 hA3 hA4 hA5 hA6 hA7 hA8 hA9

theorem exercise9_BaileyTransform_preserves_pair_upTo_five_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : PartII.Ch09.IsBaileyPairUpTo a q α β 5)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    PartII.Ch09.IsBaileyPairUpTo a q
      (PartII.Ch09.BaileyTransformAlpha a q ρ₁ ρ₂ α)
      (PartII.Ch09.BaileyTransformBeta a q ρ₁ ρ₂ β) 5 :=
  PartII.Ch09.BaileyTransform_preserves_pair_upTo_five_of_nonzero a q ρ₁ ρ₂ h
    hρ hD1 hD2 hD1one hD2one hD1two hD2two hD1three hD2three
    hD1four hD2four hQ1 hQ2 hQ3 hQ4 hQ5 hA1 hA2 hA3 hA4 hA5 hA6 hA7 hA8 hA9

/-- Exercise: the RR Bailey pair b* at n=0 (Chan Eq. 9.17). -/
theorem exercise9_rrBStar_zero (q : R) :
    PartII.Ch09.rrBStar q 0 = 1 :=
  PartII.Ch09.rrBStar_zero q

/-- Exercise: the RR Bailey pair b* at n≥1 (Chan Eq. 9.17). -/
theorem exercise9_rrBStar_succ (q : R) (n : Nat) :
    PartII.Ch09.rrBStar q (n + 1) = 0 :=
  PartII.Ch09.rrBStar_succ q n

/-- Exercise: the RR Bailey pair a* at k=0 (Chan Eq. 9.18). -/
theorem exercise9_rrAStar_zero (q : R) :
    PartII.Ch09.rrAStar q 0 = 1 :=
  PartII.Ch09.rrAStar_zero q

/-- Exercise: the RR Bailey pair a* at k=1 (Chan Eq. 9.18). -/
theorem exercise9_rrAStar_one (q : R) :
    PartII.Ch09.rrAStar q 1 = -(1 + q) :=
  PartII.Ch09.rrAStar_one q

/-- Exercise: the RR Bailey pair a* at k=2 (Chan Eq. 9.18). -/
theorem exercise9_rrAStar_two (q : R) :
    PartII.Ch09.rrAStar q 2 = q * (1 + q ^ 2) :=
  PartII.Ch09.rrAStar_two q

/-- Exercise: Lemma 9.1 base case N=0. -/
theorem exercise9_lemma91_base_zero (x q : R) :
    PartII.Ch09.lemma91Base x q 0 = PartII.Ch09.lemma91Target x q 0 := by
  rw [PartII.Ch09.lemma91Base_zero, PartII.Ch09.lemma91Target_zero]

/-- Exercise: Lemma 9.1 base case N=1. -/
theorem exercise9_lemma91_base_one (x q : R) (hxq : (1 : R) - x * q ≠ 0) :
    PartII.Ch09.lemma91Base x q 1 = PartII.Ch09.lemma91Target x q 1 :=
  PartII.Ch09.lemma91_base_one x q hxq

/-- Exercise: qPoch shift identity (a;q)_{n+1} = (1-a)·(aq;q)_n. -/
theorem exercise9_qPoch_shift (a q : R) (n : Nat) :
    qPoch a q (n + 1) = (1 - a) * qPoch (a * q) q n :=
  PartII.Ch09.qPoch_succ_shift a q n

/-- Exercise: Lemma 9.1 base case general (Eq. 9.26). -/
theorem exercise9_lemma91_base_general (q : R) (N : Nat) (x : R)
    (hxq : ∀ k, k < N → (1 : R) - x * q ^ (k + 1) ≠ 0) :
    PartII.Ch09.lemma91Base x q N = PartII.Ch09.lemma91Target x q N :=
  PartII.Ch09.lemma91_base_general q N x hxq

/-- Exercise: a*_k general formula for k ≥ 1. -/
theorem exercise9_rrAStar_pos (q : R) (k : Nat) (hk : 1 ≤ k) :
    PartII.Ch09.rrAStar q k =
      (-1 : R) ^ k * q ^ (k * (k - 1) / 2) * (1 + q ^ k) :=
  PartII.Ch09.rrAStar_pos q k hk

/-- Exercise: b*_n = 0 for n ≥ 1. -/
theorem exercise9_rrBStar_eq_zero (q : R) (n : Nat) (hn : 1 ≤ n) :
    PartII.Ch09.rrBStar q n = 0 :=
  PartII.Ch09.rrBStar_eq_zero q n hn

/-- Exercise: finiteRRLHS recurrence. -/
theorem exercise9_finiteRRLHS_succ (q : R) (n : Nat) :
    PartII.Ch09.finiteRRLHS q (n + 1) =
      PartII.Ch09.finiteRRLHS q n + q ^ ((n + 1) * (n + 1)) / qPochhammer q (n + 1) :=
  PartII.Ch09.finiteRRLHS_succ q n

/-- Exercise: finite RR identity at n=1. -/
theorem exercise9_finiteRR_one (q : R) (hq : (1 : R) - q ≠ 0)
    (hq2 : (1 : R) - q ^ 2 ≠ 0) (hq3 : (1 : R) - q ^ 3 ≠ 0) :
    PartII.Ch09.finiteRRLHS q 1 = PartII.Ch09.finiteRRRHS q 1 :=
  PartII.Ch09.finiteRR_one q hq hq2 hq3

/-- Exercise: **General Lemma 9.1** (Chan Eq. 9.10/9.27): m-parameter form. -/
theorem exercise9_lemma91BaseM_eq (x q : R) (m N : Nat)
    (hxq : ∀ k, k < N + m → (1 : R) - x * q ^ (k + 1) ≠ 0) :
    PartII.Ch09.lemma91BaseM x q m N = PartII.Ch09.lemma91TargetM x q m N :=
  PartII.Ch09.lemma91BaseM_eq x q m N hxq

/-- Exercise: qPoch splitting `(a;q)_{k+m} = (a;q)_m · (aq^m;q)_k`. -/
theorem exercise9_qPoch_split (a q : R) (m k : Nat) :
    qPoch a q (k + m) = qPoch a q m * qPoch (a * q ^ m) q k :=
  PartII.Ch09.qPoch_split a q m k

/-- Exercise: gaussianBinom [n+1; 1]_q = ∑ q^i geometric form. -/
theorem exercise9_gaussianBinom_succ_one (q : R) (n : Nat) :
    gaussianBinom q (n + 1) 1 = ∑ i ∈ Finset.range (n + 1), q ^ i :=
  PartII.Ch09.gaussianBinom_succ_one q n

end Chapter9Exercises

section Chapter10Exercises

variable {R : Type*} [Field R]

theorem exercise10_ramanujanMockF_trunc_zero (q : R) :
    PartII.Ch10.ramanujanMockF_trunc q 0 = 1 :=
  PartII.Ch10.ramanujanMockF_trunc_zero q

theorem exercise10_ramanujanMockF_trunc_one (q : R) :
    PartII.Ch10.ramanujanMockF_trunc q 1 = 1 + q / (1 + q) ^ 2 :=
  PartII.Ch10.ramanujanMockF_trunc_one q

theorem exercise10_ramanujanMockF_trunc_two (q : R) :
    PartII.Ch10.ramanujanMockF_trunc q 2 =
      1 + q / (1 + q) ^ 2 + q ^ 4 / ((1 + q) ^ 2 * (1 + q ^ 2) ^ 2) :=
  PartII.Ch10.ramanujanMockF_trunc_two q

end Chapter10Exercises

section Chapter11Exercises

/-- Exercise: α + β = 1. -/
theorem exercise11_α_add_β : PartIII.Ch11.α + PartIII.Ch11.β = 1 :=
  PartIII.Ch11.α_add_β

/-- Exercise: α · β = -1. -/
theorem exercise11_α_mul_β : PartIII.Ch11.α * PartIII.Ch11.β = -1 :=
  PartIII.Ch11.α_mul_β

/-- Exercise: α² = α + 1. -/
theorem exercise11_α_sq : PartIII.Ch11.α ^ 2 = PartIII.Ch11.α + 1 :=
  PartIII.Ch11.α_sq

/-- Exercise: β² = β + 1. -/
theorem exercise11_β_sq : PartIII.Ch11.β ^ 2 = PartIII.Ch11.β + 1 :=
  PartIII.Ch11.β_sq

/-- Exercise: α³ = 2α + 1. -/
theorem exercise11_α_cubed : PartIII.Ch11.α ^ 3 = 2 * PartIII.Ch11.α + 1 :=
  PartIII.Ch11.α_cubed

/-- Exercise: β³ = 2β + 1. -/
theorem exercise11_β_cubed : PartIII.Ch11.β ^ 3 = 2 * PartIII.Ch11.β + 1 :=
  PartIII.Ch11.β_cubed

/-- Exercise: α⁻¹ = α - 1. -/
theorem exercise11_α_inv : PartIII.Ch11.α⁻¹ = PartIII.Ch11.α - 1 :=
  PartIII.Ch11.α_inv

end Chapter11Exercises

section Chapter12Exercises

theorem exercise12_R_trunc_one_eq_inv_one_plus_q (q : ℂ) :
    PartIII.Ch11.R_trunc q 1 = 1 / (1 + q) :=
  PartIII.Ch12.R_trunc_one_eq_inv_one_plus_q q

theorem exercise12_R_trunc_two_eq (q : ℂ) :
    PartIII.Ch11.R_trunc q 2 = 1 / (1 + q ^ 2 / (1 + q)) :=
  PartIII.Ch12.R_trunc_two_eq q

theorem exercise12_R_trunc_three_eq (q : ℂ) :
    PartIII.Ch11.R_trunc q 3 = 1 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q))) :=
  PartIII.Ch12.R_trunc_three_eq q

theorem exercise12_R_trunc_four_eq (q : ℂ) :
    PartIII.Ch11.R_trunc q 4 =
      1 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q)))) :=
  PartIII.Ch12.R_trunc_four_eq q

theorem exercise12_R_trunc_five_eq (q : ℂ) :
    PartIII.Ch11.R_trunc q 5 =
      1 / (1 + q ^ 5 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q))))) :=
  PartIII.Ch12.R_trunc_five_eq q

end Chapter12Exercises

section Chapter13Exercises

variable {R : Type*} [Field R]

theorem exercise13_deepIdentityLHSTrunc_zero (q : R) :
    PartIII.Ch13.deepIdentityLHSTrunc q 0 = 1 :=
  PartIII.Ch13.deepIdentityLHSTrunc_zero q

theorem exercise13_deepIdentityLHSTrunc_one (q : R) :
    PartIII.Ch13.deepIdentityLHSTrunc q 1 = 1 + q / (1 - q) ^ 2 :=
  PartIII.Ch13.deepIdentityLHSTrunc_one q

theorem exercise13_deepIdentityLHSTrunc_two (q : R) :
    PartIII.Ch13.deepIdentityLHSTrunc q 2 =
      1 + q / (1 - q) ^ 2 + q ^ 4 / ((1 - q) * (1 - q ^ 2)) ^ 2 :=
  PartIII.Ch13.deepIdentityLHSTrunc_two q

end Chapter13Exercises

section Chapter14Exercises

variable {R : Type*} [Field R]

theorem exercise14_crankGenTrunc_zero (z q : R) :
    PartIII.Ch14.crankGenTrunc z q 0 = 1 :=
  PartIII.Ch14.crankGenTrunc_zero z q

theorem exercise14_crankGenNumeratorTrunc_one (q : R) :
    PartIII.Ch14.crankGenNumeratorTrunc q 1 = 1 - q :=
  PartIII.Ch14.crankGenNumeratorTrunc_one q

theorem exercise14_crankGenDenominatorTrunc_one (z q : R) :
    PartIII.Ch14.crankGenDenominatorTrunc z q 1 = (1 - z * q) * (1 - z⁻¹ * q) :=
  PartIII.Ch14.crankGenDenominatorTrunc_one z q

end Chapter14Exercises

section Chapter15Exercises

variable {R : Type*} [Field R]

theorem exercise15_qTaylorMonomialTopTerm_zero (q x : R) :
    PartIII.Ch15.qTaylorMonomialTopTerm q x 0 = 1 :=
  PartIII.Ch15.qTaylorMonomialTopTerm_zero q x

theorem exercise15_qTaylorMonomialTopTerm_one (q x : R) (hqx : (q - 1) * x ≠ 0) :
    PartIII.Ch15.qTaylorMonomialTopTerm q x 1 = x :=
  PartIII.Ch15.qTaylorMonomialTopTerm_one q x hqx

theorem exercise15_qTaylorMonomialTopTerm_two (q x : R)
    (h0 : (q - 1) * x ≠ 0) (h1 : (q - 1) * (q * x) ≠ 0)
    (hfac : 1 + q ≠ 0) :
    PartIII.Ch15.qTaylorMonomialTopTerm q x 2 = x ^ 2 :=
  PartIII.Ch15.qTaylorMonomialTopTerm_two q x h0 h1 hfac

theorem exercise15_qInt_three (q : R) :
    PartIII.Ch15.qInt q 3 = q ^ 2 + q + 1 :=
  PartIII.Ch15.qInt_three q

theorem exercise15_qFactorial_three (q : R) :
    PartIII.Ch15.qFactorial q 3 = (1 + q) * (q ^ 2 + q + 1) :=
  PartIII.Ch15.qFactorial_three q

theorem exercise15_qTaylorMonomialTopTerm_three (q x : R)
    (h0 : (q - 1) * x ≠ 0) (h1 : (q - 1) * (q * x) ≠ 0)
    (h2 : (q - 1) * (q ^ 2 * x) ≠ 0)
    (hfac : (1 + q) * (q ^ 2 + q + 1) ≠ 0) :
    PartIII.Ch15.qTaylorMonomialTopTerm q x 3 = x ^ 3 :=
  PartIII.Ch15.qTaylorMonomialTopTerm_three q x h0 h1 h2 hfac

theorem exercise15_qPolynomialTrunc_succ (coeff : ℕ → R) (N : ℕ) (x : R) :
    PartIII.Ch15.qPolynomialTrunc coeff (N + 1) x =
      PartIII.Ch15.qPolynomialTrunc coeff N x + coeff (N + 1) * x ^ (N + 1) :=
  PartIII.Ch15.qPolynomialTrunc_succ coeff N x

theorem exercise15_qTaylorPolynomialTopTrunc_succ (coeff : ℕ → R) (q x : R) (N : ℕ) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x (N + 1) =
      PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x N +
        coeff (N + 1) * PartIII.Ch15.qTaylorMonomialTopTerm q x (N + 1) :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_succ coeff q x N

theorem exercise15_qPolynomialTrunc_zero (coeff : ℕ → R) (x : R) :
    PartIII.Ch15.qPolynomialTrunc coeff 0 x = coeff 0 :=
  PartIII.Ch15.qPolynomialTrunc_zero coeff x

theorem exercise15_qPolynomialTrunc_one (coeff : ℕ → R) (x : R) :
    PartIII.Ch15.qPolynomialTrunc coeff 1 x = coeff 0 + coeff 1 * x :=
  PartIII.Ch15.qPolynomialTrunc_one coeff x

theorem exercise15_qPolynomialTrunc_two (coeff : ℕ → R) (x : R) :
    PartIII.Ch15.qPolynomialTrunc coeff 2 x = coeff 0 + coeff 1 * x + coeff 2 * x ^ 2 :=
  PartIII.Ch15.qPolynomialTrunc_two coeff x

theorem exercise15_qPolynomialTrunc_three (coeff : ℕ → R) (x : R) :
    PartIII.Ch15.qPolynomialTrunc coeff 3 x =
      coeff 0 + coeff 1 * x + coeff 2 * x ^ 2 + coeff 3 * x ^ 3 :=
  PartIII.Ch15.qPolynomialTrunc_three coeff x

theorem exercise15_qTaylorPolynomialTopTrunc_zero (coeff : ℕ → R) (q x : R) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x 0 = coeff 0 :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_zero coeff q x

theorem exercise15_qTaylorPolynomialTopTrunc_one (coeff : ℕ → R) (q x : R)
    (hqx : (q - 1) * x ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x 1 = coeff 0 + coeff 1 * x :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_one coeff q x hqx

theorem exercise15_qTaylorPolynomialTopTrunc_two (coeff : ℕ → R) (q x : R)
    (h0 : (q - 1) * x ≠ 0) (h1 : (q - 1) * (q * x) ≠ 0)
    (hfac : 1 + q ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x 2 =
      coeff 0 + coeff 1 * x + coeff 2 * x ^ 2 :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_two coeff q x h0 h1 hfac

theorem exercise15_qTaylorPolynomialTopTrunc_three (coeff : ℕ → R) (q x : R)
    (h0 : (q - 1) * x ≠ 0) (h1 : (q - 1) * (q * x) ≠ 0)
    (h2 : (q - 1) * (q ^ 2 * x) ≠ 0)
    (hfac2 : 1 + q ≠ 0)
    (hfac3 : (1 + q) * (q ^ 2 + q + 1) ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x 3 =
      coeff 0 + coeff 1 * x + coeff 2 * x ^ 2 + coeff 3 * x ^ 3 :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_three coeff q x h0 h1 h2 hfac2 hfac3

theorem exercise15_qTaylorPolynomialTopTrunc_three_of_nonzero (coeff : ℕ → R) (q x : R)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → PartIII.Ch15.qInt q k ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x 3 =
      coeff 0 + coeff 1 * x + coeff 2 * x ^ 2 + coeff 3 * x ^ 3 :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_three_of_nonzero coeff q x hq0 hq1 hx hq_int

theorem exercise15_qPolynomialTrunc_zero_coeff (N : Nat) (x : R) :
    PartIII.Ch15.qPolynomialTrunc (fun _ => (0 : R)) N x = 0 :=
  PartIII.Ch15.qPolynomialTrunc_zero_coeff N x

theorem exercise15_qTaylorPolynomialTopTrunc_zero_coeff (q x : R) (N : Nat) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc (fun _ => (0 : R)) q x N = 0 :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_zero_coeff q x N

theorem exercise15_qPolynomialTrunc_add (coeff₁ coeff₂ : ℕ → R) (N : Nat) (x : R) :
    PartIII.Ch15.qPolynomialTrunc (fun n => coeff₁ n + coeff₂ n) N x =
      PartIII.Ch15.qPolynomialTrunc coeff₁ N x + PartIII.Ch15.qPolynomialTrunc coeff₂ N x :=
  PartIII.Ch15.qPolynomialTrunc_add coeff₁ coeff₂ N x

theorem exercise15_qPolynomialTrunc_smul (c : R) (coeff : ℕ → R) (N : Nat) (x : R) :
    PartIII.Ch15.qPolynomialTrunc (fun n => c * coeff n) N x =
      c * PartIII.Ch15.qPolynomialTrunc coeff N x :=
  PartIII.Ch15.qPolynomialTrunc_smul c coeff N x

theorem exercise15_qPolynomialTrunc_neg (coeff : ℕ → R) (N : Nat) (x : R) :
    PartIII.Ch15.qPolynomialTrunc (fun n => - coeff n) N x =
      - PartIII.Ch15.qPolynomialTrunc coeff N x :=
  PartIII.Ch15.qPolynomialTrunc_neg coeff N x

theorem exercise15_qPolynomialTrunc_sub (coeff₁ coeff₂ : ℕ → R) (N : Nat) (x : R) :
    PartIII.Ch15.qPolynomialTrunc (fun n => coeff₁ n - coeff₂ n) N x =
      PartIII.Ch15.qPolynomialTrunc coeff₁ N x - PartIII.Ch15.qPolynomialTrunc coeff₂ N x :=
  PartIII.Ch15.qPolynomialTrunc_sub coeff₁ coeff₂ N x

theorem exercise15_qPolynomialTrunc_congr {coeff₁ coeff₂ : ℕ → R} {N : Nat} (x : R)
    (hcoeff : ∀ n : ℕ, n ≤ N → coeff₁ n = coeff₂ n) :
    PartIII.Ch15.qPolynomialTrunc coeff₁ N x =
      PartIII.Ch15.qPolynomialTrunc coeff₂ N x :=
  PartIII.Ch15.qPolynomialTrunc_congr x hcoeff

theorem exercise15_qPolynomialTrunc_eq_of_coeff_zero_above
    {coeff : ℕ → R} {M N : ℕ} (x : R) (hMN : M ≤ N)
    (hzero : ∀ n : ℕ, M < n → n ≤ N → coeff n = 0) :
    PartIII.Ch15.qPolynomialTrunc coeff N x =
      PartIII.Ch15.qPolynomialTrunc coeff M x :=
  PartIII.Ch15.qPolynomialTrunc_eq_of_coeff_zero_above x hMN hzero

theorem exercise15_natSum_eq_sum_range (f : ℕ → R) (N : ℕ) :
    natSum f N = ∑ n ∈ Finset.range (N + 1), f n :=
  PartIII.Ch15.natSum_eq_sum_range f N

theorem exercise15_qPolynomialTrunc_coeff_natDegree_eq_eval (p : Polynomial R) (x : R) :
    PartIII.Ch15.qPolynomialTrunc (fun n => p.coeff n) p.natDegree x = p.eval x :=
  PartIII.Ch15.qPolynomialTrunc_coeff_natDegree_eq_eval p x

theorem exercise15_qPolynomialTrunc_coeff_eq_eval_of_natDegree_le (p : Polynomial R) (x : R)
    {N : ℕ} (hN : p.natDegree ≤ N) :
    PartIII.Ch15.qPolynomialTrunc (fun n => p.coeff n) N x = p.eval x :=
  PartIII.Ch15.qPolynomialTrunc_coeff_eq_eval_of_natDegree_le p x hN

theorem exercise15_qPolynomialTrunc_coeff_eq_eval_of_natDegree_lt (p : Polynomial R) (x : R)
    {N : ℕ} (hN : p.natDegree < N) :
    PartIII.Ch15.qPolynomialTrunc (fun n => p.coeff n) N x = p.eval x :=
  PartIII.Ch15.qPolynomialTrunc_coeff_eq_eval_of_natDegree_lt p x hN

theorem exercise15_qPolynomialTrunc_coeff_eq_natDegree_of_natDegree_le
    (p : Polynomial R) (x : R) {N : ℕ} (hN : p.natDegree ≤ N) :
    PartIII.Ch15.qPolynomialTrunc (fun n => p.coeff n) N x =
      PartIII.Ch15.qPolynomialTrunc (fun n => p.coeff n) p.natDegree x :=
  PartIII.Ch15.qPolynomialTrunc_coeff_eq_natDegree_of_natDegree_le p x hN

theorem exercise15_qPolynomialTrunc_coeff_congr_zero_tail_eq_eval
    (p : Polynomial R) (coeff : ℕ → R) (x : R) {N : ℕ}
    (hN : p.natDegree ≤ N)
    (hcoeff : ∀ n : ℕ, n ≤ p.natDegree → coeff n = p.coeff n)
    (hzero : ∀ n : ℕ, p.natDegree < n → n ≤ N → coeff n = 0) :
    PartIII.Ch15.qPolynomialTrunc coeff N x = p.eval x :=
  PartIII.Ch15.qPolynomialTrunc_coeff_congr_zero_tail_eq_eval
    p coeff x hN hcoeff hzero

theorem exercise15_qPolynomialTrunc_coeff_congr_zero_tail_eq_eval_of_natDegree_lt
    (p : Polynomial R) (coeff : ℕ → R) (x : R) {N : ℕ}
    (hN : p.natDegree < N)
    (hcoeff : ∀ n : ℕ, n ≤ p.natDegree → coeff n = p.coeff n)
    (hzero : ∀ n : ℕ, p.natDegree < n → n ≤ N → coeff n = 0) :
    PartIII.Ch15.qPolynomialTrunc coeff N x = p.eval x :=
  PartIII.Ch15.qPolynomialTrunc_coeff_congr_zero_tail_eq_eval_of_natDegree_lt
    p coeff x hN hcoeff hzero

theorem exercise15_qPolynomialTrunc_coeff_congr_global_zero_tail_eq_eval
    (p : Polynomial R) (coeff : ℕ → R) (x : R) {N : ℕ}
    (hN : p.natDegree ≤ N)
    (hcoeff : ∀ n : ℕ, n ≤ p.natDegree → coeff n = p.coeff n)
    (hzero : ∀ n : ℕ, p.natDegree < n → coeff n = 0) :
    PartIII.Ch15.qPolynomialTrunc coeff N x = p.eval x :=
  PartIII.Ch15.qPolynomialTrunc_coeff_congr_global_zero_tail_eq_eval
    p coeff x hN hcoeff hzero

theorem exercise15_qTaylorPolynomialTopTrunc_add (coeff₁ coeff₂ : ℕ → R) (q x : R) (N : Nat) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc (fun n => coeff₁ n + coeff₂ n) q x N =
      PartIII.Ch15.qTaylorPolynomialTopTrunc coeff₁ q x N +
      PartIII.Ch15.qTaylorPolynomialTopTrunc coeff₂ q x N :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_add coeff₁ coeff₂ q x N

theorem exercise15_qTaylorPolynomialTopTrunc_smul (c : R) (coeff : ℕ → R) (q x : R) (N : Nat) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc (fun n => c * coeff n) q x N =
      c * PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x N :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_smul c coeff q x N

theorem exercise15_qTaylorPolynomialTopTrunc_neg (coeff : ℕ → R) (q x : R) (N : Nat) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc (fun n => - coeff n) q x N =
      - PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x N :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_neg coeff q x N

theorem exercise15_qTaylorPolynomialTopTrunc_sub (coeff₁ coeff₂ : ℕ → R) (q x : R) (N : Nat) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc (fun n => coeff₁ n - coeff₂ n) q x N =
      PartIII.Ch15.qTaylorPolynomialTopTrunc coeff₁ q x N -
        PartIII.Ch15.qTaylorPolynomialTopTrunc coeff₂ q x N :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_sub coeff₁ coeff₂ q x N

theorem exercise15_qTaylorPolynomialTopTrunc_congr {coeff₁ coeff₂ : ℕ → R}
    {N : Nat} (q x : R)
    (hcoeff : ∀ n : ℕ, n ≤ N → coeff₁ n = coeff₂ n) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff₁ q x N =
      PartIII.Ch15.qTaylorPolynomialTopTrunc coeff₂ q x N :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_congr q x hcoeff

theorem exercise15_qTaylorPolynomialTopTrunc_eq_of_coeff_zero_above
    {coeff : ℕ → R} {M N : ℕ} (q x : R) (hMN : M ≤ N)
    (hzero : ∀ n : ℕ, M < n → n ≤ N → coeff n = 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x N =
      PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x M :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_eq_of_coeff_zero_above q x hMN hzero

theorem exercise15_qTaylorPolynomialTopTrunc_eq (coeff : ℕ → R) (q x : R) (N : ℕ)
    (hiter : ∀ n : ℕ, n ≤ N →
      ∀ j : ℕ, j < n → (q - 1) * (q ^ j * x) ≠ 0)
    (hfac : ∀ n : ℕ, n ≤ N → PartIII.Ch15.qFactorial q n ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x N =
      PartIII.Ch15.qPolynomialTrunc coeff N x :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_eq coeff q x N hiter hfac

theorem exercise15_qTaylorPolynomialTopTrunc_eq_of_nonzero (coeff : ℕ → R) (q x : R) (N : ℕ)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → PartIII.Ch15.qInt q k ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x N =
      PartIII.Ch15.qPolynomialTrunc coeff N x :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_eq_of_nonzero coeff q x N hq0 hq1 hx hq_int

theorem exercise15_qTaylorPolynomialTopTrunc_eq_of_coeff_congr
    {coeff₁ coeff₂ : ℕ → R} (q x : R) (N : ℕ)
    (hcoeff : ∀ n : ℕ, n ≤ N → coeff₁ n = coeff₂ n)
    (hiter : ∀ n : ℕ, n ≤ N →
      ∀ j : ℕ, j < n → (q - 1) * (q ^ j * x) ≠ 0)
    (hfac : ∀ n : ℕ, n ≤ N → PartIII.Ch15.qFactorial q n ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff₁ q x N =
      PartIII.Ch15.qPolynomialTrunc coeff₂ N x :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_eq_of_coeff_congr q x N hcoeff hiter hfac

theorem exercise15_qTaylorPolynomialTopTrunc_eq_of_coeff_congr_nonzero
    {coeff₁ coeff₂ : ℕ → R} (q x : R) (N : ℕ)
    (hcoeff : ∀ n : ℕ, n ≤ N → coeff₁ n = coeff₂ n)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → PartIII.Ch15.qInt q k ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff₁ q x N =
      PartIII.Ch15.qPolynomialTrunc coeff₂ N x :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_eq_of_coeff_congr_nonzero
    q x N hcoeff hq0 hq1 hx hq_int

theorem exercise15_qTaylorPolynomialTopTrunc_coeff_natDegree_eq_eval
    (p : Polynomial R) (q x : R)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → PartIII.Ch15.qInt q k ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc (fun n => p.coeff n) q x p.natDegree =
      p.eval x :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_coeff_natDegree_eq_eval
    p q x hq0 hq1 hx hq_int

theorem exercise15_qTaylorPolynomialTopTrunc_coeff_eq_eval_of_natDegree_le
    (p : Polynomial R) (q x : R) {N : ℕ} (hN : p.natDegree ≤ N)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → PartIII.Ch15.qInt q k ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc (fun n => p.coeff n) q x N =
      p.eval x :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_coeff_eq_eval_of_natDegree_le
    p q x hN hq0 hq1 hx hq_int

theorem exercise15_qTaylorPolynomialTopTrunc_coeff_eq_eval_of_natDegree_lt
    (p : Polynomial R) (q x : R) {N : ℕ} (hN : p.natDegree < N)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → PartIII.Ch15.qInt q k ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc (fun n => p.coeff n) q x N =
      p.eval x :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_coeff_eq_eval_of_natDegree_lt
    p q x hN hq0 hq1 hx hq_int

theorem exercise15_qTaylorPolynomialTopTrunc_coeff_eq_natDegree_of_natDegree_le
    (p : Polynomial R) (q x : R) {N : ℕ} (hN : p.natDegree ≤ N) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc (fun n => p.coeff n) q x N =
      PartIII.Ch15.qTaylorPolynomialTopTrunc (fun n => p.coeff n) q x p.natDegree :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_coeff_eq_natDegree_of_natDegree_le p q x hN

theorem exercise15_qTaylorPolynomialTopTrunc_coeff_congr_zero_tail_eq_eval
    (p : Polynomial R) (coeff : ℕ → R) (q x : R) {N : ℕ}
    (hN : p.natDegree ≤ N)
    (hcoeff : ∀ n : ℕ, n ≤ p.natDegree → coeff n = p.coeff n)
    (hzero : ∀ n : ℕ, p.natDegree < n → n ≤ N → coeff n = 0)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → PartIII.Ch15.qInt q k ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x N = p.eval x :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_coeff_congr_zero_tail_eq_eval
    p coeff q x hN hcoeff hzero hq0 hq1 hx hq_int

theorem exercise15_qTaylorPolynomialTopTrunc_coeff_congr_zero_tail_eq_eval_of_natDegree_lt
    (p : Polynomial R) (coeff : ℕ → R) (q x : R) {N : ℕ}
    (hN : p.natDegree < N)
    (hcoeff : ∀ n : ℕ, n ≤ p.natDegree → coeff n = p.coeff n)
    (hzero : ∀ n : ℕ, p.natDegree < n → n ≤ N → coeff n = 0)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → PartIII.Ch15.qInt q k ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x N = p.eval x :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_coeff_congr_zero_tail_eq_eval_of_natDegree_lt
    p coeff q x hN hcoeff hzero hq0 hq1 hx hq_int

theorem exercise15_qTaylorPolynomialTopTrunc_coeff_congr_global_zero_tail_eq_eval
    (p : Polynomial R) (coeff : ℕ → R) (q x : R) {N : ℕ}
    (hN : p.natDegree ≤ N)
    (hcoeff : ∀ n : ℕ, n ≤ p.natDegree → coeff n = p.coeff n)
    (hzero : ∀ n : ℕ, p.natDegree < n → coeff n = 0)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → PartIII.Ch15.qInt q k ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x N = p.eval x :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_coeff_congr_global_zero_tail_eq_eval
    p coeff q x hN hcoeff hzero hq0 hq1 hx hq_int

theorem exercise15_qTaylorPolynomialTopTrunc_coeff_congr_eq_eval_of_natDegree_le
    (p : Polynomial R) (coeff : ℕ → R) (q x : R) {N : ℕ}
    (hcoeff : ∀ n : ℕ, n ≤ N → coeff n = p.coeff n)
    (hN : p.natDegree ≤ N)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → PartIII.Ch15.qInt q k ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x N = p.eval x :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_coeff_congr_eq_eval_of_natDegree_le
    p coeff q x hcoeff hN hq0 hq1 hx hq_int

theorem exercise15_qTaylorPolynomialTopTrunc_coeff_congr_eq_eval_of_natDegree_lt
    (p : Polynomial R) (coeff : ℕ → R) (q x : R) {N : ℕ}
    (hcoeff : ∀ n : ℕ, n ≤ N → coeff n = p.coeff n)
    (hN : p.natDegree < N)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → PartIII.Ch15.qInt q k ≠ 0) :
    PartIII.Ch15.qTaylorPolynomialTopTrunc coeff q x N = p.eval x :=
  PartIII.Ch15.qTaylorPolynomialTopTrunc_coeff_congr_eq_eval_of_natDegree_lt
    p coeff q x hcoeff hN hq0 hq1 hx hq_int

end Chapter15Exercises

section Chapter16Exercises

variable {R : Type*} [Field R]

theorem exercise16_mbiLHSTrunc_one (q : R) :
    PartIV.Ch16.mbiLHSTrunc q 1 =
      (Ch01.partitionCount 4 : R) + (Ch01.partitionCount 9 : R) * q :=
  PartIV.Ch16.mbiLHSTrunc_one q

theorem exercise16_mbiRHSNumeratorTrunc_one (q : R) :
    PartIV.Ch16.mbiRHSNumeratorTrunc q 1 = (1 - q ^ 5) ^ 5 :=
  PartIV.Ch16.mbiRHSNumeratorTrunc_one q

theorem exercise16_mbiRHSDenominatorTrunc_one (q : R) :
    PartIV.Ch16.mbiRHSDenominatorTrunc q 1 = (1 - q) ^ 6 :=
  PartIV.Ch16.mbiRHSDenominatorTrunc_one q

theorem exercise16_mbi_truncated_zero (q : R) :
    PartIV.Ch16.mbiLHSTrunc q 0 = (Ch01.partitionCount 4 : R) ∧
    PartIV.Ch16.mbiRHSTrunc q 0 = 5 :=
  PartIV.Ch16.mbi_truncated_zero q

end Chapter16Exercises

section Chapter17Exercises

/-- Exercise: p(4) divisible by 5 (smallest case of p(5n+4) ≡ 0 mod 5). -/
theorem exercise17_partition_4_mod_5 :
    Ch01.partitionCount 4 % 5 = 0 :=
  PartIV.Ch17.partition_5n_plus_4_mod_5_n_zero

end Chapter17Exercises

section Chapter18Exercises

theorem exercise18_hookLength_four_two_zero_one :
    PartIV.Ch18.hookLength [4, 2] 0 1 = 4 :=
  PartIV.Ch18.hookLength_four_two_zero_one

theorem exercise18_hookLength_two_two_one_one_zero_zero :
    PartIV.Ch18.hookLength [2, 2, 1, 1] 0 0 = 5 :=
  PartIV.Ch18.hookLength_two_two_one_one_zero_zero

theorem exercise18_hookLength_two_two_one_one_zero_one :
    PartIV.Ch18.hookLength [2, 2, 1, 1] 0 1 = 2 :=
  PartIV.Ch18.hookLength_two_two_one_one_zero_one

theorem exercise18_hookLength_two_two_one_one_one_zero :
    PartIV.Ch18.hookLength [2, 2, 1, 1] 1 0 = 4 :=
  PartIV.Ch18.hookLength_two_two_one_one_one_zero

theorem exercise18_hookLength_two_two_one_one_one_one :
    PartIV.Ch18.hookLength [2, 2, 1, 1] 1 1 = 1 :=
  PartIV.Ch18.hookLength_two_two_one_one_one_one

theorem exercise18_hookLength_two_two_one_one_two_zero :
    PartIV.Ch18.hookLength [2, 2, 1, 1] 2 0 = 2 :=
  PartIV.Ch18.hookLength_two_two_one_one_two_zero

theorem exercise18_hookLength_two_two_one_one_three_zero :
    PartIV.Ch18.hookLength [2, 2, 1, 1] 3 0 = 1 :=
  PartIV.Ch18.hookLength_two_two_one_one_three_zero

theorem exercise18_armLength_add_one_of_FerrersCell {lam : List Nat} {r c : Nat}
    (hcell : PartIV.Ch18.FerrersCell lam r c) :
    PartIV.Ch18.armLength lam r c + 1 = lam.getD r 0 - c :=
  PartIV.Ch18.armLength_add_one_of_FerrersCell hcell

theorem exercise18_armLength_lt_rowLength_of_FerrersCell {lam : List Nat} {r c : Nat}
    (hcell : PartIV.Ch18.FerrersCell lam r c) :
    PartIV.Ch18.armLength lam r c < lam.getD r 0 :=
  PartIV.Ch18.armLength_lt_rowLength_of_FerrersCell hcell

theorem exercise18_hookLength_eq_row_sub_col_add_leg_of_FerrersCell
    {lam : List Nat} {r c : Nat} (hcell : PartIV.Ch18.FerrersCell lam r c) :
    PartIV.Ch18.hookLength lam r c =
      (lam.getD r 0 - c) + PartIV.Ch18.legLength lam r c :=
  PartIV.Ch18.hookLength_eq_row_sub_col_add_leg_of_FerrersCell hcell

theorem exercise18_armLength_lt_hookLength (lam : List Nat) (r c : Nat) :
    PartIV.Ch18.armLength lam r c < PartIV.Ch18.hookLength lam r c :=
  PartIV.Ch18.armLength_lt_hookLength lam r c

theorem exercise18_legLength_lt_hookLength (lam : List Nat) (r c : Nat) :
    PartIV.Ch18.legLength lam r c < PartIV.Ch18.hookLength lam r c :=
  PartIV.Ch18.legLength_lt_hookLength lam r c

theorem exercise18_hookLength_pos (lam : List Nat) (r c : Nat) :
    0 < PartIV.Ch18.hookLength lam r c :=
  PartIV.Ch18.hookLength_pos lam r c

theorem exercise18_hookLength_ne_zero (lam : List Nat) (r c : Nat) :
    PartIV.Ch18.hookLength lam r c ≠ 0 :=
  PartIV.Ch18.hookLength_ne_zero lam r c

theorem exercise18_filter_length_eq_FerrersColumnCells_card (lam : List Nat) (c : Nat) :
    (lam.filter (fun rowLength => c < rowLength)).length =
      (PartI.Ch05.FerrersColumnCells lam c).card :=
  PartIV.Ch18.filter_length_eq_FerrersColumnCells_card lam c

theorem exercise18_legLength_eq_FerrersColumnCells_drop_card
    (lam : List Nat) (r c : Nat) :
    PartIV.Ch18.legLength lam r c =
      (PartI.Ch05.FerrersColumnCells (lam.drop (r + 1)) c).card :=
  PartIV.Ch18.legLength_eq_FerrersColumnCells_drop_card lam r c

theorem exercise18_legLength_eq_column_card_sub_succ_of_FerrersCell
    {lam : List Nat} (hpart : IsPartition lam) {r c : Nat}
    (hcell : PartIV.Ch18.FerrersCell lam r c) :
    PartIV.Ch18.legLength lam r c =
      (PartI.Ch05.FerrersColumnCells lam c).card - (r + 1) :=
  PartIV.Ch18.legLength_eq_column_card_sub_succ_of_FerrersCell hpart hcell

theorem exercise18_FerrersColumnCells_FerrersConjugatePartition_card_eq_getD
    {lam : List Nat} (hpart : IsPartition lam) {r : Nat} (hr : r < lam.length) :
    (PartI.Ch05.FerrersColumnCells (PartI.Ch05.FerrersConjugatePartition lam) r).card =
      lam.getD r 0 :=
  PartIV.Ch18.FerrersColumnCells_FerrersConjugatePartition_card_eq_getD hpart hr

theorem exercise18_hookLength_FerrersConjugatePartition_cell {lam : List Nat}
    (hpart : IsPartition lam) {r c : Nat} (hcell : PartIV.Ch18.FerrersCell lam r c) :
    PartIV.Ch18.FerrersCell (PartI.Ch05.FerrersConjugatePartition lam) c r ∧
      PartIV.Ch18.hookLength (PartI.Ch05.FerrersConjugatePartition lam) c r =
        PartIV.Ch18.hookLength lam r c :=
  PartIV.Ch18.hookLength_FerrersConjugatePartition_cell hpart hcell

theorem exercise18_hasHookDivisibleBy_FerrersConjugatePartition_iff
    {t : Nat} {lam : List Nat} (hpart : IsPartition lam) :
    PartIV.Ch18.HasHookDivisibleBy t lam ↔
      PartIV.Ch18.HasHookDivisibleBy t (PartI.Ch05.FerrersConjugatePartition lam) :=
  PartIV.Ch18.hasHookDivisibleBy_FerrersConjugatePartition_iff hpart

theorem exercise18_isTCoreByHooks_FerrersConjugatePartition_iff
    {t : Nat} {lam : List Nat} (hpart : IsPartition lam) :
    PartIV.Ch18.IsTCoreByHooks t lam ↔
      PartIV.Ch18.IsTCoreByHooks t (PartI.Ch05.FerrersConjugatePartition lam) :=
  PartIV.Ch18.isTCoreByHooks_FerrersConjugatePartition_iff hpart

theorem exercise18_hasHookDivisibleBy_two_four_two :
    PartIV.Ch18.HasHookDivisibleBy 2 [4, 2] :=
  PartIV.Ch18.hasHookDivisibleBy_two_four_two

theorem exercise18_hasHookDivisibleBy_four_four_two :
    PartIV.Ch18.HasHookDivisibleBy 4 [4, 2] :=
  PartIV.Ch18.hasHookDivisibleBy_four_four_two

theorem exercise18_hasHookDivisibleBy_five_four_two :
    PartIV.Ch18.HasHookDivisibleBy 5 [4, 2] :=
  PartIV.Ch18.hasHookDivisibleBy_five_four_two

theorem exercise18_hasHookDivisibleBy_one_four_two :
    PartIV.Ch18.HasHookDivisibleBy 1 [4, 2] :=
  PartIV.Ch18.hasHookDivisibleBy_one_four_two

theorem exercise18_hasHookDivisibleBy_two_two_one_one :
    PartIV.Ch18.HasHookDivisibleBy 2 [2, 2, 1, 1] :=
  PartIV.Ch18.hasHookDivisibleBy_two_two_one_one

theorem exercise18_hasHookDivisibleBy_four_two_two_one_one :
    PartIV.Ch18.HasHookDivisibleBy 4 [2, 2, 1, 1] :=
  PartIV.Ch18.hasHookDivisibleBy_four_two_two_one_one

theorem exercise18_hasHookDivisibleBy_five_two_two_one_one :
    PartIV.Ch18.HasHookDivisibleBy 5 [2, 2, 1, 1] :=
  PartIV.Ch18.hasHookDivisibleBy_five_two_two_one_one

theorem exercise18_hasHookDivisibleBy_one_two_two_one_one :
    PartIV.Ch18.HasHookDivisibleBy 1 [2, 2, 1, 1] :=
  PartIV.Ch18.hasHookDivisibleBy_one_two_two_one_one

theorem exercise18_hasHookDivisibleBy_three_three_two_one :
    PartIV.Ch18.HasHookDivisibleBy 3 [3, 2, 1] :=
  PartIV.Ch18.hasHookDivisibleBy_three_three_two_one

theorem exercise18_hasHookDivisibleBy_five_three_two_one :
    PartIV.Ch18.HasHookDivisibleBy 5 [3, 2, 1] :=
  PartIV.Ch18.hasHookDivisibleBy_five_three_two_one

theorem exercise18_hasHookDivisibleBy_one_three_two_one :
    PartIV.Ch18.HasHookDivisibleBy 1 [3, 2, 1] :=
  PartIV.Ch18.hasHookDivisibleBy_one_three_two_one

theorem exercise18_not_twoCoreByHooks_four_two :
    ¬ PartIV.Ch18.IsTCoreByHooks 2 [4, 2] :=
  PartIV.Ch18.not_twoCoreByHooks_four_two

theorem exercise18_not_fourCoreByHooks_four_two :
    ¬ PartIV.Ch18.IsTCoreByHooks 4 [4, 2] :=
  PartIV.Ch18.not_fourCoreByHooks_four_two

theorem exercise18_not_fiveCoreByHooks_four_two :
    ¬ PartIV.Ch18.IsTCoreByHooks 5 [4, 2] :=
  PartIV.Ch18.not_fiveCoreByHooks_four_two

theorem exercise18_not_oneCoreByHooks_four_two :
    ¬ PartIV.Ch18.IsTCoreByHooks 1 [4, 2] :=
  PartIV.Ch18.not_oneCoreByHooks_four_two

theorem exercise18_not_twoCoreByHooks_two_two_one_one :
    ¬ PartIV.Ch18.IsTCoreByHooks 2 [2, 2, 1, 1] :=
  PartIV.Ch18.not_twoCoreByHooks_two_two_one_one

theorem exercise18_not_fourCoreByHooks_two_two_one_one :
    ¬ PartIV.Ch18.IsTCoreByHooks 4 [2, 2, 1, 1] :=
  PartIV.Ch18.not_fourCoreByHooks_two_two_one_one

theorem exercise18_not_fiveCoreByHooks_two_two_one_one :
    ¬ PartIV.Ch18.IsTCoreByHooks 5 [2, 2, 1, 1] :=
  PartIV.Ch18.not_fiveCoreByHooks_two_two_one_one

theorem exercise18_not_oneCoreByHooks_two_two_one_one :
    ¬ PartIV.Ch18.IsTCoreByHooks 1 [2, 2, 1, 1] :=
  PartIV.Ch18.not_oneCoreByHooks_two_two_one_one

theorem exercise18_hookLength_four_two_conjugate_cell {r c : Nat}
    (hcell : PartIV.Ch18.FerrersCell [4, 2] r c) :
    PartIV.Ch18.FerrersCell [2, 2, 1, 1] c r ∧
      PartIV.Ch18.hookLength [2, 2, 1, 1] c r =
        PartIV.Ch18.hookLength [4, 2] r c :=
  PartIV.Ch18.hookLength_four_two_conjugate_cell hcell

theorem exercise18_hookLength_two_two_one_one_conjugate_cell {r c : Nat}
    (hcell : PartIV.Ch18.FerrersCell [2, 2, 1, 1] r c) :
    PartIV.Ch18.FerrersCell [4, 2] c r ∧
      PartIV.Ch18.hookLength [4, 2] c r =
        PartIV.Ch18.hookLength [2, 2, 1, 1] r c :=
  PartIV.Ch18.hookLength_two_two_one_one_conjugate_cell hcell

theorem exercise18_hasHookDivisibleBy_four_two_conjugate_iff (t : Nat) :
    PartIV.Ch18.HasHookDivisibleBy t [4, 2] ↔
      PartIV.Ch18.HasHookDivisibleBy t [2, 2, 1, 1] :=
  PartIV.Ch18.hasHookDivisibleBy_four_two_conjugate_iff t

theorem exercise18_isTCoreByHooks_four_two_conjugate_iff (t : Nat) :
    PartIV.Ch18.IsTCoreByHooks t [4, 2] ↔
      PartIV.Ch18.IsTCoreByHooks t [2, 2, 1, 1] :=
  PartIV.Ch18.isTCoreByHooks_four_two_conjugate_iff t

theorem exercise18_hookLength_three_two_one_transpose_cell {r c : Nat}
    (hcell : PartIV.Ch18.FerrersCell [3, 2, 1] r c) :
    PartIV.Ch18.FerrersCell [3, 2, 1] c r ∧
      PartIV.Ch18.hookLength [3, 2, 1] c r =
        PartIV.Ch18.hookLength [3, 2, 1] r c :=
  PartIV.Ch18.hookLength_three_two_one_transpose_cell hcell

theorem exercise18_hasHookDivisibleBy_three_two_one_transpose_iff (t : Nat) :
    PartIV.Ch18.HasHookDivisibleBy t [3, 2, 1] ↔
      PartIV.Ch18.HasHookDivisibleBy t [3, 2, 1] :=
  PartIV.Ch18.hasHookDivisibleBy_three_two_one_transpose_iff t

theorem exercise18_not_threeCoreByHooks_three_two_one :
    ¬ PartIV.Ch18.IsTCoreByHooks 3 [3, 2, 1] :=
  PartIV.Ch18.not_threeCoreByHooks_three_two_one

theorem exercise18_not_fiveCoreByHooks_three_two_one :
    ¬ PartIV.Ch18.IsTCoreByHooks 5 [3, 2, 1] :=
  PartIV.Ch18.not_fiveCoreByHooks_three_two_one

theorem exercise18_not_oneCoreByHooks_three_two_one :
    ¬ PartIV.Ch18.IsTCoreByHooks 1 [3, 2, 1] :=
  PartIV.Ch18.not_oneCoreByHooks_three_two_one

theorem exercise18_hookLength_lt_six_three_two_one {r c : Nat}
    (hcell : PartIV.Ch18.FerrersCell [3, 2, 1] r c) :
    PartIV.Ch18.hookLength [3, 2, 1] r c < 6 :=
  PartIV.Ch18.hookLength_lt_six_three_two_one hcell

theorem exercise18_isTCoreByHooks_three_two_one_of_six_le {t : Nat} (ht : 6 ≤ t) :
    PartIV.Ch18.IsTCoreByHooks t [3, 2, 1] :=
  PartIV.Ch18.isTCoreByHooks_three_two_one_of_six_le ht

theorem exercise18_isSixCoreByHooks_three_two_one :
    PartIV.Ch18.IsTCoreByHooks 6 [3, 2, 1] :=
  PartIV.Ch18.isSixCoreByHooks_three_two_one

theorem exercise18_isSevenCoreByHooks_three_two_one :
    PartIV.Ch18.IsTCoreByHooks 7 [3, 2, 1] :=
  PartIV.Ch18.isSevenCoreByHooks_three_two_one

theorem exercise18_hookLength_lt_six_four_two {r c : Nat}
    (hcell : PartIV.Ch18.FerrersCell [4, 2] r c) :
    PartIV.Ch18.hookLength [4, 2] r c < 6 :=
  PartIV.Ch18.hookLength_lt_six_four_two hcell

theorem exercise18_isTCoreByHooks_four_two_of_six_le {t : Nat} (ht : 6 ≤ t) :
    PartIV.Ch18.IsTCoreByHooks t [4, 2] :=
  PartIV.Ch18.isTCoreByHooks_four_two_of_six_le ht

theorem exercise18_isSixCoreByHooks_four_two :
    PartIV.Ch18.IsTCoreByHooks 6 [4, 2] :=
  PartIV.Ch18.isSixCoreByHooks_four_two

theorem exercise18_isSevenCoreByHooks_four_two :
    PartIV.Ch18.IsTCoreByHooks 7 [4, 2] :=
  PartIV.Ch18.isSevenCoreByHooks_four_two

theorem exercise18_isTCoreByHooks_two_two_one_one_of_six_le {t : Nat} (ht : 6 ≤ t) :
    PartIV.Ch18.IsTCoreByHooks t [2, 2, 1, 1] :=
  PartIV.Ch18.isTCoreByHooks_two_two_one_one_of_six_le ht

theorem exercise18_isSixCoreByHooks_two_two_one_one :
    PartIV.Ch18.IsTCoreByHooks 6 [2, 2, 1, 1] :=
  PartIV.Ch18.isSixCoreByHooks_two_two_one_one

theorem exercise18_isSevenCoreByHooks_two_two_one_one :
    PartIV.Ch18.IsTCoreByHooks 7 [2, 2, 1, 1] :=
  PartIV.Ch18.isSevenCoreByHooks_two_two_one_one

theorem exercise18_hasHookDivisibleBy_hookLength_of_cell {lam : List Nat} {r c : Nat}
    (hcell : PartIV.Ch18.FerrersCell lam r c) :
    PartIV.Ch18.HasHookDivisibleBy (PartIV.Ch18.hookLength lam r c) lam :=
  PartIV.Ch18.hasHookDivisibleBy_hookLength_of_cell hcell

theorem exercise18_hasHookDivisibleBy_of_hookLength_eq_mul
    {t : Nat} {lam : List Nat} {r c k : Nat}
    (hcell : PartIV.Ch18.FerrersCell lam r c)
    (hhook : PartIV.Ch18.hookLength lam r c = t * k) :
    PartIV.Ch18.HasHookDivisibleBy t lam :=
  PartIV.Ch18.hasHookDivisibleBy_of_hookLength_eq_mul hcell hhook

theorem exercise18_hasHookDivisibleBy_iff_exists_hookLength_eq_mul
    (t : Nat) (lam : List Nat) :
    PartIV.Ch18.HasHookDivisibleBy t lam ↔
      ∃ r c k, PartIV.Ch18.FerrersCell lam r c ∧
        PartIV.Ch18.hookLength lam r c = t * k :=
  PartIV.Ch18.hasHookDivisibleBy_iff_exists_hookLength_eq_mul t lam

theorem exercise18_HasHookDivisibleBy_map_hookLength {t : Nat} {lam mu : List Nat}
    (hmap : ∀ ⦃r c : Nat⦄, PartIV.Ch18.FerrersCell lam r c →
      ∃ r' c', PartIV.Ch18.FerrersCell mu r' c' ∧
        PartIV.Ch18.hookLength mu r' c' = PartIV.Ch18.hookLength lam r c)
    (h : PartIV.Ch18.HasHookDivisibleBy t lam) :
    PartIV.Ch18.HasHookDivisibleBy t mu :=
  PartIV.Ch18.HasHookDivisibleBy.map_hookLength hmap h

theorem exercise18_hasHookDivisibleBy_iff_of_hookLength_maps {t : Nat}
    {lam mu : List Nat}
    (hmap_lm : ∀ ⦃r c : Nat⦄, PartIV.Ch18.FerrersCell lam r c →
      ∃ r' c', PartIV.Ch18.FerrersCell mu r' c' ∧
        PartIV.Ch18.hookLength mu r' c' = PartIV.Ch18.hookLength lam r c)
    (hmap_ml : ∀ ⦃r c : Nat⦄, PartIV.Ch18.FerrersCell mu r c →
      ∃ r' c', PartIV.Ch18.FerrersCell lam r' c' ∧
        PartIV.Ch18.hookLength lam r' c' = PartIV.Ch18.hookLength mu r c) :
    PartIV.Ch18.HasHookDivisibleBy t lam ↔ PartIV.Ch18.HasHookDivisibleBy t mu :=
  PartIV.Ch18.hasHookDivisibleBy_iff_of_hookLength_maps hmap_lm hmap_ml

theorem exercise18_isTCoreByHooks_iff_of_hookLength_maps {t : Nat}
    {lam mu : List Nat}
    (hmap_lm : ∀ ⦃r c : Nat⦄, PartIV.Ch18.FerrersCell lam r c →
      ∃ r' c', PartIV.Ch18.FerrersCell mu r' c' ∧
        PartIV.Ch18.hookLength mu r' c' = PartIV.Ch18.hookLength lam r c)
    (hmap_ml : ∀ ⦃r c : Nat⦄, PartIV.Ch18.FerrersCell mu r c →
      ∃ r' c', PartIV.Ch18.FerrersCell lam r' c' ∧
        PartIV.Ch18.hookLength lam r' c' = PartIV.Ch18.hookLength mu r c) :
    PartIV.Ch18.IsTCoreByHooks t lam ↔ PartIV.Ch18.IsTCoreByHooks t mu :=
  PartIV.Ch18.isTCoreByHooks_iff_of_hookLength_maps hmap_lm hmap_ml

theorem exercise18_not_isTCoreByHooks_hookLength_of_cell {lam : List Nat} {r c : Nat}
    (hcell : PartIV.Ch18.FerrersCell lam r c) :
    ¬ PartIV.Ch18.IsTCoreByHooks (PartIV.Ch18.hookLength lam r c) lam :=
  PartIV.Ch18.not_isTCoreByHooks_hookLength_of_cell hcell

theorem exercise18_not_isTCoreByHooks_of_hookLength_eq_mul
    {t : Nat} {lam : List Nat} {r c k : Nat}
    (hcell : PartIV.Ch18.FerrersCell lam r c)
    (hhook : PartIV.Ch18.hookLength lam r c = t * k) :
    ¬ PartIV.Ch18.IsTCoreByHooks t lam :=
  PartIV.Ch18.not_isTCoreByHooks_of_hookLength_eq_mul hcell hhook

theorem exercise18_hookLength_ne_of_isTCoreByHooks {t : Nat} {lam : List Nat}
    (hcore : PartIV.Ch18.IsTCoreByHooks t lam) {r c : Nat}
    (hcell : PartIV.Ch18.FerrersCell lam r c) :
    PartIV.Ch18.hookLength lam r c ≠ t :=
  PartIV.Ch18.hookLength_ne_of_isTCoreByHooks hcore hcell

theorem exercise18_not_dvd_hookLength_of_isTCoreByHooks {t : Nat} {lam : List Nat}
    (hcore : PartIV.Ch18.IsTCoreByHooks t lam) {r c : Nat}
    (hcell : PartIV.Ch18.FerrersCell lam r c) :
    ¬ t ∣ PartIV.Ch18.hookLength lam r c :=
  PartIV.Ch18.not_dvd_hookLength_of_isTCoreByHooks hcore hcell

theorem exercise18_hookLength_ne_mul_of_isTCoreByHooks {t : Nat} {lam : List Nat}
    (hcore : PartIV.Ch18.IsTCoreByHooks t lam) {r c k : Nat}
    (hcell : PartIV.Ch18.FerrersCell lam r c) :
    PartIV.Ch18.hookLength lam r c ≠ t * k :=
  PartIV.Ch18.hookLength_ne_mul_of_isTCoreByHooks hcore hcell

theorem exercise18_tCore_hookLength_ne_mul_characterization (t : Nat) (lam : List Nat) :
    PartIV.Ch18.IsTCoreByHooks t lam ↔
      ∀ r c k, PartIV.Ch18.FerrersCell lam r c →
        PartIV.Ch18.hookLength lam r c ≠ t * k :=
  PartIV.Ch18.tCore_hookLength_ne_mul_characterization t lam

theorem exercise18_zeroCoreByHooks (lam : List Nat) :
    PartIV.Ch18.IsTCoreByHooks 0 lam :=
  PartIV.Ch18.zeroCoreByHooks lam

theorem exercise18_nilCoreByHooks (t : Nat) :
    PartIV.Ch18.IsTCoreByHooks t [] :=
  PartIV.Ch18.nilCoreByHooks t

theorem exercise18_oneCoreByHooks_iff_no_FerrersCell (lam : List Nat) :
    PartIV.Ch18.IsTCoreByHooks 1 lam ↔ ∀ r c, ¬ PartIV.Ch18.FerrersCell lam r c :=
  PartIV.Ch18.oneCoreByHooks_iff_no_FerrersCell lam

theorem exercise18_oneCoreByHooks_iff_eq_nil_of_positive {lam : List Nat}
    (hpos : PartI.Ch05.PositiveParts lam) :
    PartIV.Ch18.IsTCoreByHooks 1 lam ↔ lam = [] :=
  PartIV.Ch18.oneCoreByHooks_iff_eq_nil_of_positive hpos

theorem exercise18_hasHookDivisibleBy_one_iff_exists_FerrersCell (lam : List Nat) :
    PartIV.Ch18.HasHookDivisibleBy 1 lam ↔ ∃ r c, PartIV.Ch18.FerrersCell lam r c :=
  PartIV.Ch18.hasHookDivisibleBy_one_iff_exists_FerrersCell lam

theorem exercise18_not_oneCoreByHooks_of_FerrersCell {lam : List Nat} {r c : Nat}
    (hcell : PartIV.Ch18.FerrersCell lam r c) :
    ¬ PartIV.Ch18.IsTCoreByHooks 1 lam :=
  PartIV.Ch18.not_oneCoreByHooks_of_FerrersCell hcell

theorem exercise18_FerrersCell_cons_zero_zero {n : Nat} {tail : List Nat} (hn : 0 < n) :
    PartIV.Ch18.FerrersCell (n :: tail) 0 0 :=
  PartIV.Ch18.FerrersCell_cons_zero_zero hn

theorem exercise18_not_oneCoreByHooks_cons_pos {n : Nat} {tail : List Nat} (hn : 0 < n) :
    ¬ PartIV.Ch18.IsTCoreByHooks 1 (n :: tail) :=
  PartIV.Ch18.not_oneCoreByHooks_cons_pos hn

theorem exercise18_not_oneCoreByHooks_iff_exists_FerrersCell (lam : List Nat) :
    ¬ PartIV.Ch18.IsTCoreByHooks 1 lam ↔ ∃ r c, PartIV.Ch18.FerrersCell lam r c :=
  PartIV.Ch18.not_oneCoreByHooks_iff_exists_FerrersCell lam

theorem exercise18_filter_staircasePartition_length (n c : Nat) :
    ((PartI.Ch05.staircasePartition n).filter (fun rowLength => c < rowLength)).length =
      n - c :=
  PartIV.Ch18.filter_staircasePartition_length n c

theorem exercise18_legLength_staircasePartition (n r c : Nat)
    (hcell : PartIV.Ch18.FerrersCell (PartI.Ch05.staircasePartition n) r c) :
    PartIV.Ch18.legLength (PartI.Ch05.staircasePartition n) r c =
      n - c - (r + 1) :=
  PartIV.Ch18.legLength_staircasePartition n r c hcell

theorem exercise18_hookLength_staircasePartition (n r c : Nat)
    (hcell : PartIV.Ch18.FerrersCell (PartI.Ch05.staircasePartition n) r c) :
    PartIV.Ch18.hookLength (PartI.Ch05.staircasePartition n) r c =
      2 * (n - r - c) - 1 :=
  PartIV.Ch18.hookLength_staircasePartition n r c hcell

theorem exercise18_hookLength_staircasePartition_transpose_cell (n r c : Nat)
    (hcell : PartIV.Ch18.FerrersCell (PartI.Ch05.staircasePartition n) r c) :
    PartIV.Ch18.FerrersCell (PartI.Ch05.staircasePartition n) c r ∧
      PartIV.Ch18.hookLength (PartI.Ch05.staircasePartition n) c r =
        PartIV.Ch18.hookLength (PartI.Ch05.staircasePartition n) r c :=
  PartIV.Ch18.hookLength_staircasePartition_transpose_cell n r c hcell

theorem exercise18_hookLength_staircasePartition_lt_two_mul (n r c : Nat)
    (hcell : PartIV.Ch18.FerrersCell (PartI.Ch05.staircasePartition n) r c) :
    PartIV.Ch18.hookLength (PartI.Ch05.staircasePartition n) r c < 2 * n :=
  PartIV.Ch18.hookLength_staircasePartition_lt_two_mul n r c hcell

theorem exercise18_hookLength_staircasePartition_le_two_mul_sub_one (n r c : Nat)
    (hcell : PartIV.Ch18.FerrersCell (PartI.Ch05.staircasePartition n) r c) :
    PartIV.Ch18.hookLength (PartI.Ch05.staircasePartition n) r c ≤ 2 * n - 1 :=
  PartIV.Ch18.hookLength_staircasePartition_le_two_mul_sub_one n r c hcell

theorem exercise18_not_two_dvd_hookLength_staircasePartition (n r c : Nat)
    (hcell : PartIV.Ch18.FerrersCell (PartI.Ch05.staircasePartition n) r c) :
    ¬ 2 ∣ PartIV.Ch18.hookLength (PartI.Ch05.staircasePartition n) r c :=
  PartIV.Ch18.not_two_dvd_hookLength_staircasePartition n r c hcell

theorem exercise18_isTCoreByHooks_two_staircasePartition (n : Nat) :
    PartIV.Ch18.IsTCoreByHooks 2 (PartI.Ch05.staircasePartition n) :=
  PartIV.Ch18.isTCoreByHooks_two_staircasePartition n

theorem exercise18_isTCoreByHooks_staircasePartition_of_two_dvd {n t : Nat}
    (ht : 2 ∣ t) :
    PartIV.Ch18.IsTCoreByHooks t (PartI.Ch05.staircasePartition n) :=
  PartIV.Ch18.isTCoreByHooks_staircasePartition_of_two_dvd ht

theorem exercise18_isTCoreByHooks_staircasePartition_of_two_mul_le {n t : Nat}
    (ht : 2 * n ≤ t) :
    PartIV.Ch18.IsTCoreByHooks t (PartI.Ch05.staircasePartition n) :=
  PartIV.Ch18.isTCoreByHooks_staircasePartition_of_two_mul_le ht

theorem exercise18_FerrersCell_staircasePartition_zero_zero {n : Nat} (hn : 0 < n) :
    PartIV.Ch18.FerrersCell (PartI.Ch05.staircasePartition n) 0 0 :=
  PartIV.Ch18.FerrersCell_staircasePartition_zero_zero hn

theorem exercise18_hookLength_staircasePartition_zero_zero {n : Nat} (hn : 0 < n) :
    PartIV.Ch18.hookLength (PartI.Ch05.staircasePartition n) 0 0 = 2 * n - 1 :=
  PartIV.Ch18.hookLength_staircasePartition_zero_zero hn

theorem exercise18_FerrersCell_staircasePartition_zero_sub_succ {n k : Nat}
    (hk : k < n) :
    PartIV.Ch18.FerrersCell (PartI.Ch05.staircasePartition n) 0 (n - (k + 1)) :=
  PartIV.Ch18.FerrersCell_staircasePartition_zero_sub_succ hk

theorem exercise18_hookLength_staircasePartition_zero_sub_succ {n k : Nat}
    (hk : k < n) :
    PartIV.Ch18.hookLength (PartI.Ch05.staircasePartition n) 0 (n - (k + 1)) =
      2 * k + 1 :=
  PartIV.Ch18.hookLength_staircasePartition_zero_sub_succ hk

theorem exercise18_hasHookDivisibleBy_odd_staircasePartition_of_lt {n k : Nat}
    (hk : k < n) :
    PartIV.Ch18.HasHookDivisibleBy (2 * k + 1) (PartI.Ch05.staircasePartition n) :=
  PartIV.Ch18.hasHookDivisibleBy_odd_staircasePartition_of_lt hk

theorem exercise18_not_isTCoreByHooks_odd_staircasePartition_of_lt {n k : Nat}
    (hk : k < n) :
    ¬ PartIV.Ch18.IsTCoreByHooks (2 * k + 1) (PartI.Ch05.staircasePartition n) :=
  PartIV.Ch18.not_isTCoreByHooks_odd_staircasePartition_of_lt hk

theorem exercise18_isTCoreByHooks_odd_staircasePartition_iff_le (n k : Nat) :
    PartIV.Ch18.IsTCoreByHooks (2 * k + 1) (PartI.Ch05.staircasePartition n) ↔
      n ≤ k :=
  PartIV.Ch18.isTCoreByHooks_odd_staircasePartition_iff_le n k

theorem exercise18_isTCoreByHooks_staircasePartition_iff (n t : Nat) :
    PartIV.Ch18.IsTCoreByHooks t (PartI.Ch05.staircasePartition n) ↔
      2 ∣ t ∨ 2 * n ≤ t :=
  PartIV.Ch18.isTCoreByHooks_staircasePartition_iff n t

theorem exercise18_exists_FerrersCell_hookLength_staircasePartition_iff (n t : Nat) :
    (∃ r c, PartIV.Ch18.FerrersCell (PartI.Ch05.staircasePartition n) r c ∧
      PartIV.Ch18.hookLength (PartI.Ch05.staircasePartition n) r c = t) ↔
      ¬ 2 ∣ t ∧ t < 2 * n :=
  PartIV.Ch18.exists_FerrersCell_hookLength_staircasePartition_iff n t

theorem exercise18_mem_StaircaseHookCellsOfLength_iff {n t : Nat} {cell : Nat × Nat} :
    cell ∈ PartIV.Ch18.StaircaseHookCellsOfLength n t ↔
      PartIV.Ch18.FerrersCell (PartI.Ch05.staircasePartition n) cell.1 cell.2 ∧
        PartIV.Ch18.hookLength (PartI.Ch05.staircasePartition n) cell.1 cell.2 = t :=
  PartIV.Ch18.mem_StaircaseHookCellsOfLength_iff

theorem exercise18_StaircaseHookCellsOfLength_odd_eq_antidiagonal {n k : Nat}
    (hk : k < n) :
    PartIV.Ch18.StaircaseHookCellsOfLength n (2 * k + 1) =
      Finset.antidiagonal (n - (k + 1)) :=
  PartIV.Ch18.StaircaseHookCellsOfLength_odd_eq_antidiagonal hk

theorem exercise18_StaircaseHookCellsOfLength_odd_card {n k : Nat} (hk : k < n) :
    (PartIV.Ch18.StaircaseHookCellsOfLength n (2 * k + 1)).card = n - k :=
  PartIV.Ch18.StaircaseHookCellsOfLength_odd_card hk

theorem exercise18_StaircaseHookCellsOfLength_eq_empty_iff (n t : Nat) :
    PartIV.Ch18.StaircaseHookCellsOfLength n t = ∅ ↔ 2 ∣ t ∨ 2 * n ≤ t :=
  PartIV.Ch18.StaircaseHookCellsOfLength_eq_empty_iff n t

theorem exercise18_StaircaseHookCellsOfLength_card_eq_zero_iff (n t : Nat) :
    (PartIV.Ch18.StaircaseHookCellsOfLength n t).card = 0 ↔ 2 ∣ t ∨ 2 * n ≤ t :=
  PartIV.Ch18.StaircaseHookCellsOfLength_card_eq_zero_iff n t

theorem exercise18_StaircaseHookCellsOfLength_odd_card_eq_sub (n k : Nat) :
    (PartIV.Ch18.StaircaseHookCellsOfLength n (2 * k + 1)).card = n - k :=
  PartIV.Ch18.StaircaseHookCellsOfLength_odd_card_eq_sub n k

theorem exercise18_StaircaseHookCellsOfLength_even_eq_empty (n k : Nat) :
    PartIV.Ch18.StaircaseHookCellsOfLength n (2 * k) = ∅ :=
  PartIV.Ch18.StaircaseHookCellsOfLength_even_eq_empty n k

theorem exercise18_StaircaseHookCellsOfLength_even_card (n k : Nat) :
    (PartIV.Ch18.StaircaseHookCellsOfLength n (2 * k)).card = 0 :=
  PartIV.Ch18.StaircaseHookCellsOfLength_even_card n k

theorem exercise18_StaircaseHookCellsOfLength_card_eq_if (n t : Nat) :
    (PartIV.Ch18.StaircaseHookCellsOfLength n t).card =
      if 2 ∣ t then 0 else n - t / 2 :=
  PartIV.Ch18.StaircaseHookCellsOfLength_card_eq_if n t

theorem exercise18_StaircaseHookCellsOfLength_card_eq_sub_div_two_of_odd
    {n t : Nat} (ht : ¬ 2 ∣ t) :
    (PartIV.Ch18.StaircaseHookCellsOfLength n t).card = n - t / 2 :=
  PartIV.Ch18.StaircaseHookCellsOfLength_card_eq_sub_div_two_of_odd ht

theorem exercise18_StaircaseHookCellsOfLength_eq_antidiagonal_of_odd_lt
    {n t : Nat} (ht : ¬ 2 ∣ t) (hlt : t < 2 * n) :
    PartIV.Ch18.StaircaseHookCellsOfLength n t =
      Finset.antidiagonal (n - (t / 2 + 1)) :=
  PartIV.Ch18.StaircaseHookCellsOfLength_eq_antidiagonal_of_odd_lt ht hlt

theorem exercise18_sum_range_sub_eq_triangular (n : Nat) :
    (Finset.range n).sum (fun k => n - k) = triangular n :=
  PartIV.Ch18.sum_range_sub_eq_triangular n

theorem exercise18_sum_StaircaseHookCellsOfLength_odd_cards (n : Nat) :
    (Finset.range n).sum
        (fun k => (PartIV.Ch18.StaircaseHookCellsOfLength n (2 * k + 1)).card) =
      triangular n :=
  PartIV.Ch18.sum_StaircaseHookCellsOfLength_odd_cards n

theorem exercise18_sum_StaircaseHookCellsOfLength_odd_cards_eq_weight (n : Nat) :
    (Finset.range n).sum
        (fun k => (PartIV.Ch18.StaircaseHookCellsOfLength n (2 * k + 1)).card) =
      partitionWeight (PartI.Ch05.staircasePartition n) :=
  PartIV.Ch18.sum_StaircaseHookCellsOfLength_odd_cards_eq_weight n

theorem exercise18_StaircaseHookCellsOfLength_nonempty_iff (n t : Nat) :
    (PartIV.Ch18.StaircaseHookCellsOfLength n t).Nonempty ↔ ¬ 2 ∣ t ∧ t < 2 * n :=
  PartIV.Ch18.StaircaseHookCellsOfLength_nonempty_iff n t

theorem exercise18_StaircaseHookCellsOfLength_card_pos_iff (n t : Nat) :
    0 < (PartIV.Ch18.StaircaseHookCellsOfLength n t).card ↔
      ¬ 2 ∣ t ∧ t < 2 * n :=
  PartIV.Ch18.StaircaseHookCellsOfLength_card_pos_iff n t

theorem exercise18_hasHookDivisibleBy_staircasePartition_iff (n t : Nat) :
    PartIV.Ch18.HasHookDivisibleBy t (PartI.Ch05.staircasePartition n) ↔
      ¬ 2 ∣ t ∧ t < 2 * n :=
  PartIV.Ch18.hasHookDivisibleBy_staircasePartition_iff n t

theorem exercise18_hasHookDivisibleBy_two_mul_sub_one_staircasePartition {n : Nat}
    (hn : 0 < n) :
    PartIV.Ch18.HasHookDivisibleBy (2 * n - 1) (PartI.Ch05.staircasePartition n) :=
  PartIV.Ch18.hasHookDivisibleBy_two_mul_sub_one_staircasePartition hn

theorem exercise18_hasHookDivisibleBy_staircasePartition_of_dvd_two_mul_sub_one
    {n t : Nat} (hn : 0 < n) (hdiv : t ∣ 2 * n - 1) :
    PartIV.Ch18.HasHookDivisibleBy t (PartI.Ch05.staircasePartition n) :=
  PartIV.Ch18.hasHookDivisibleBy_staircasePartition_of_dvd_two_mul_sub_one hn hdiv

theorem exercise18_not_isTCoreByHooks_two_mul_sub_one_staircasePartition {n : Nat}
    (hn : 0 < n) :
    ¬ PartIV.Ch18.IsTCoreByHooks (2 * n - 1) (PartI.Ch05.staircasePartition n) :=
  PartIV.Ch18.not_isTCoreByHooks_two_mul_sub_one_staircasePartition hn

theorem exercise18_not_isTCoreByHooks_staircasePartition_of_dvd_two_mul_sub_one
    {n t : Nat} (hn : 0 < n) (hdiv : t ∣ 2 * n - 1) :
    ¬ PartIV.Ch18.IsTCoreByHooks t (PartI.Ch05.staircasePartition n) :=
  PartIV.Ch18.not_isTCoreByHooks_staircasePartition_of_dvd_two_mul_sub_one hn hdiv

theorem exercise18_not_isTCoreByHooks_iff_hasHookDivisibleBy (t : Nat) (lam : List Nat) :
    ¬ PartIV.Ch18.IsTCoreByHooks t lam ↔ PartIV.Ch18.HasHookDivisibleBy t lam :=
  PartIV.Ch18.not_isTCoreByHooks_iff_hasHookDivisibleBy t lam

theorem exercise18_not_dvd_of_pos_lt {t n : Nat} (hn : 0 < n) (hnt : n < t) :
    ¬ t ∣ n :=
  PartIV.Ch18.not_dvd_of_pos_lt hn hnt

theorem exercise18_not_hasHookDivisibleBy_of_hookLength_lt {t : Nat} {lam : List Nat}
    (hbound : ∀ r c, PartIV.Ch18.FerrersCell lam r c →
      PartIV.Ch18.hookLength lam r c < t) :
    ¬ PartIV.Ch18.HasHookDivisibleBy t lam :=
  PartIV.Ch18.not_hasHookDivisibleBy_of_hookLength_lt hbound

theorem exercise18_isTCoreByHooks_of_hookLength_lt {t : Nat} {lam : List Nat}
    (hbound : ∀ r c, PartIV.Ch18.FerrersCell lam r c →
      PartIV.Ch18.hookLength lam r c < t) :
    PartIV.Ch18.IsTCoreByHooks t lam :=
  PartIV.Ch18.isTCoreByHooks_of_hookLength_lt hbound

theorem exercise18_not_hasHookDivisibleBy_of_hookLength_le_bound
    {t B : Nat} {lam : List Nat} (hB : B < t)
    (hbound : ∀ r c, PartIV.Ch18.FerrersCell lam r c →
      PartIV.Ch18.hookLength lam r c ≤ B) :
    ¬ PartIV.Ch18.HasHookDivisibleBy t lam :=
  PartIV.Ch18.not_hasHookDivisibleBy_of_hookLength_le_bound hB hbound

theorem exercise18_isTCoreByHooks_of_hookLength_le_bound
    {t B : Nat} {lam : List Nat} (hB : B < t)
    (hbound : ∀ r c, PartIV.Ch18.FerrersCell lam r c →
      PartIV.Ch18.hookLength lam r c ≤ B) :
    PartIV.Ch18.IsTCoreByHooks t lam :=
  PartIV.Ch18.isTCoreByHooks_of_hookLength_le_bound hB hbound

theorem exercise18_isTCoreByHooks_of_no_FerrersCell {t : Nat} {lam : List Nat}
    (hcellless : ∀ r c, ¬ PartIV.Ch18.FerrersCell lam r c) :
    PartIV.Ch18.IsTCoreByHooks t lam :=
  PartIV.Ch18.isTCoreByHooks_of_no_FerrersCell hcellless

theorem exercise18_hasHookDivisibleBy_of_dvd {t u : Nat} {lam : List Nat}
    (htu : t ∣ u) (h : PartIV.Ch18.HasHookDivisibleBy u lam) :
    PartIV.Ch18.HasHookDivisibleBy t lam :=
  PartIV.Ch18.hasHookDivisibleBy_of_dvd htu h

theorem exercise18_hasHookDivisibleBy_left_of_lcm {t u : Nat} {lam : List Nat}
    (h : PartIV.Ch18.HasHookDivisibleBy (Nat.lcm t u) lam) :
    PartIV.Ch18.HasHookDivisibleBy t lam :=
  PartIV.Ch18.hasHookDivisibleBy_left_of_lcm h

theorem exercise18_hasHookDivisibleBy_right_of_lcm {t u : Nat} {lam : List Nat}
    (h : PartIV.Ch18.HasHookDivisibleBy (Nat.lcm t u) lam) :
    PartIV.Ch18.HasHookDivisibleBy u lam :=
  PartIV.Ch18.hasHookDivisibleBy_right_of_lcm h

theorem exercise18_hasHookDivisibleBy_pair_of_lcm {t u : Nat} {lam : List Nat}
    (h : PartIV.Ch18.HasHookDivisibleBy (Nat.lcm t u) lam) :
    PartIV.Ch18.HasHookDivisibleBy t lam ∧ PartIV.Ch18.HasHookDivisibleBy u lam :=
  PartIV.Ch18.hasHookDivisibleBy_pair_of_lcm h

theorem exercise18_hasHookDivisibleBy_gcd_of_left {t u : Nat} {lam : List Nat}
    (h : PartIV.Ch18.HasHookDivisibleBy t lam) :
    PartIV.Ch18.HasHookDivisibleBy (Nat.gcd t u) lam :=
  PartIV.Ch18.hasHookDivisibleBy_gcd_of_left h

theorem exercise18_hasHookDivisibleBy_gcd_of_right {t u : Nat} {lam : List Nat}
    (h : PartIV.Ch18.HasHookDivisibleBy u lam) :
    PartIV.Ch18.HasHookDivisibleBy (Nat.gcd t u) lam :=
  PartIV.Ch18.hasHookDivisibleBy_gcd_of_right h

theorem exercise18_IsTCoreByHooks_of_dvd {t u : Nat} {lam : List Nat}
    (hcore : PartIV.Ch18.IsTCoreByHooks t lam) (htu : t ∣ u) :
    PartIV.Ch18.IsTCoreByHooks u lam :=
  PartIV.Ch18.IsTCoreByHooks.of_dvd hcore htu

theorem exercise18_IsTCoreByHooks_lcm_left {t u : Nat} {lam : List Nat}
    (hcore : PartIV.Ch18.IsTCoreByHooks t lam) :
    PartIV.Ch18.IsTCoreByHooks (Nat.lcm t u) lam :=
  PartIV.Ch18.IsTCoreByHooks.lcm_left hcore

theorem exercise18_IsTCoreByHooks_lcm_right {t u : Nat} {lam : List Nat}
    (hcore : PartIV.Ch18.IsTCoreByHooks u lam) :
    PartIV.Ch18.IsTCoreByHooks (Nat.lcm t u) lam :=
  PartIV.Ch18.IsTCoreByHooks.lcm_right hcore

theorem exercise18_IsTCoreByHooks_gcd_left {t u : Nat} {lam : List Nat}
    (hcore : PartIV.Ch18.IsTCoreByHooks (Nat.gcd t u) lam) :
    PartIV.Ch18.IsTCoreByHooks t lam :=
  PartIV.Ch18.IsTCoreByHooks.gcd_left hcore

theorem exercise18_IsTCoreByHooks_gcd_right {t u : Nat} {lam : List Nat}
    (hcore : PartIV.Ch18.IsTCoreByHooks (Nat.gcd t u) lam) :
    PartIV.Ch18.IsTCoreByHooks u lam :=
  PartIV.Ch18.IsTCoreByHooks.gcd_right hcore

theorem exercise18_IsTCoreByHooks_gcd_pair {t u : Nat} {lam : List Nat}
    (hcore : PartIV.Ch18.IsTCoreByHooks (Nat.gcd t u) lam) :
    PartIV.Ch18.IsTCoreByHooks t lam ∧ PartIV.Ch18.IsTCoreByHooks u lam :=
  PartIV.Ch18.IsTCoreByHooks.gcd_pair hcore

theorem exercise18_not_isTCoreByHooks_of_dvd_not_isTCoreByHooks
    {t u : Nat} {lam : List Nat} (htu : t ∣ u)
    (hnot : ¬ PartIV.Ch18.IsTCoreByHooks u lam) :
    ¬ PartIV.Ch18.IsTCoreByHooks t lam :=
  PartIV.Ch18.not_isTCoreByHooks_of_dvd_not_isTCoreByHooks htu hnot

theorem exercise18_not_isTCoreByHooks_left_of_not_lcm
    {t u : Nat} {lam : List Nat}
    (hnot : ¬ PartIV.Ch18.IsTCoreByHooks (Nat.lcm t u) lam) :
    ¬ PartIV.Ch18.IsTCoreByHooks t lam :=
  PartIV.Ch18.not_isTCoreByHooks_left_of_not_lcm hnot

theorem exercise18_not_isTCoreByHooks_right_of_not_lcm
    {t u : Nat} {lam : List Nat}
    (hnot : ¬ PartIV.Ch18.IsTCoreByHooks (Nat.lcm t u) lam) :
    ¬ PartIV.Ch18.IsTCoreByHooks u lam :=
  PartIV.Ch18.not_isTCoreByHooks_right_of_not_lcm hnot

theorem exercise18_not_isTCoreByHooks_gcd_of_not_left
    {t u : Nat} {lam : List Nat}
    (hnot : ¬ PartIV.Ch18.IsTCoreByHooks t lam) :
    ¬ PartIV.Ch18.IsTCoreByHooks (Nat.gcd t u) lam :=
  PartIV.Ch18.not_isTCoreByHooks_gcd_of_not_left hnot

theorem exercise18_not_isTCoreByHooks_gcd_of_not_right
    {t u : Nat} {lam : List Nat}
    (hnot : ¬ PartIV.Ch18.IsTCoreByHooks u lam) :
    ¬ PartIV.Ch18.IsTCoreByHooks (Nat.gcd t u) lam :=
  PartIV.Ch18.not_isTCoreByHooks_gcd_of_not_right hnot

/-- Exercise (Chapter 18 style): hook-divisibility is preserved by Ferrers conjugation
if hook lengths are preserved by cell transposition. -/
theorem exercise18_hasHookDivisibleBy_FerrersConjugatePartition_iff_of_hookLength_eq
    {t : Nat} {lam : List Nat} (hpart : IsPartition lam)
    (hforward : ∀ ⦃r c : Nat⦄, PartIV.Ch18.FerrersCell lam r c →
      PartIV.Ch18.hookLength (PartI.Ch05.FerrersConjugatePartition lam) c r =
      PartIV.Ch18.hookLength lam r c)
    (hback : ∀ ⦃r c : Nat⦄, PartIV.Ch18.FerrersCell (PartI.Ch05.FerrersConjugatePartition lam) r c →
      PartIV.Ch18.hookLength lam c r =
      PartIV.Ch18.hookLength (PartI.Ch05.FerrersConjugatePartition lam) r c) :
    PartIV.Ch18.HasHookDivisibleBy t lam ↔
      PartIV.Ch18.HasHookDivisibleBy t (PartI.Ch05.FerrersConjugatePartition lam) :=
  PartIV.Ch18.hasHookDivisibleBy_FerrersConjugatePartition_iff_of_hookLength_eq
    hpart hforward hback

/-- Exercise (Chapter 18 style): the t-core property is preserved by Ferrers conjugation
if hook lengths are preserved by cell transposition. -/
theorem exercise18_isTCoreByHooks_FerrersConjugatePartition_iff_of_hookLength_eq
    {t : Nat} {lam : List Nat} (hpart : IsPartition lam)
    (hforward : ∀ ⦃r c : Nat⦄, PartIV.Ch18.FerrersCell lam r c →
      PartIV.Ch18.hookLength (PartI.Ch05.FerrersConjugatePartition lam) c r =
      PartIV.Ch18.hookLength lam r c)
    (hback : ∀ ⦃r c : Nat⦄, PartIV.Ch18.FerrersCell (PartI.Ch05.FerrersConjugatePartition lam) r c →
      PartIV.Ch18.hookLength lam c r =
      PartIV.Ch18.hookLength (PartI.Ch05.FerrersConjugatePartition lam) r c) :
    PartIV.Ch18.IsTCoreByHooks t lam ↔
      PartIV.Ch18.IsTCoreByHooks t (PartI.Ch05.FerrersConjugatePartition lam) :=
  PartIV.Ch18.isTCoreByHooks_FerrersConjugatePartition_iff_of_hookLength_eq
    hpart hforward hback

end Chapter18Exercises

section Chapter19Exercises

theorem exercise19_ramanujan_5_n0 : 5 ∣ Ch01.partitionCount (5 * 0 + 4) :=
  PartIV.Ch19.ramanujan_5_n0

theorem exercise19_ramanujan_7_n0 : 7 ∣ Ch01.partitionCount (7 * 0 + 5) :=
  PartIV.Ch19.ramanujan_7_n0

theorem exercise19_ramanujan_11_n0 : 11 ∣ Ch01.partitionCount (11 * 0 + 6) :=
  PartIV.Ch19.ramanujan_11_n0

theorem exercise19_p10_mod_7 : Ch01.partitionCount 10 % 7 = 0 :=
  PartIV.Ch19.p10_mod_7

theorem exercise19_p6_mod_11 : Ch01.partitionCount 6 % 11 = 0 :=
  PartIV.Ch19.p6_mod_11

end Chapter19Exercises

section Chapter20Exercises

variable {R : Type*} [Field R]

theorem exercise20_etaPolyPart_one (q : R) :
    PartIV.Ch20.etaPolyPart q 1 = 1 - q :=
  PartIV.Ch20.etaPolyPart_one q

theorem exercise20_etaPolyPart_two (q : R) :
    PartIV.Ch20.etaPolyPart q 2 = (1 - q) * (1 - q ^ 2) :=
  PartIV.Ch20.etaPolyPart_two q

theorem exercise20_discriminantPolyPart_one (q : R) :
    PartIV.Ch20.discriminantPolyPart q 1 = q * (1 - q) ^ 24 :=
  PartIV.Ch20.discriminantPolyPart_one q

end Chapter20Exercises

end QseriesFormalization
