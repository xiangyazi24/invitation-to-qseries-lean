import QseriesFormalization.Basic
import QseriesFormalization.Chapter19
import QseriesFormalization.Pending.JTP_FormalPS_Pentagonal
import QseriesFormalization.Pending.Chapter15_FormalDeriv
import QseriesFormalization.Pending.Chapter16_MBI_Proof

/-!
# Chapter 10 — Tenth-order mock theta functions φ and ψ

Chan's Ch10 main identity (Eq 10.10/10.15) involves the tenth-order
mock theta functions. This file defines them and states the target.
-/

namespace QseriesFormalization.Pending.Ch10TenthOrder

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.Ch15FormalDeriv
open QseriesFormalization.Pending.Ch16MBIProof

/-- Odd q-Pochhammer `(q;q²)_n = ∏_{k=0}^{n-1}(1-q^{2k+1})` in `R⟦X⟧`. -/
noncomputable def oddQPochPS (n : ℕ) : ℚ⟦X⟧ :=
  ∏ k ∈ Finset.range n, (1 - X ^ (2 * k + 1))

/-- `(q;q²)_n` has constant coefficient 1. -/
theorem constantCoeff_oddQPochPS (n : ℕ) :
    constantCoeff (oddQPochPS n) = 1 := by
  unfold oddQPochPS
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, map_mul, ih]
    simp [map_sub, map_one, map_pow, constantCoeff_X]

/-- `(q;q²)_n` is a unit. -/
theorem isUnit_oddQPochPS (n : ℕ) : IsUnit (oddQPochPS n) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_oddQPochPS]
  exact isUnit_one

/-! ## Tenth-order `φ` and `ψ`

Chan/Ramanujan's tenth-order `φ` and `ψ` use the denominator
`(q;q²)_{n+1} = (1-q)(1-q³)⋯(1-q^{2n+1})`.  The coefficient definitions
below compute the inverse of each finite odd product by truncated convolution.
-/

/-- Triangular exponent `n(n+1)/2` in `φ(q)`. -/
def tenthOrderPhiShift (n : ℕ) : ℕ :=
  n * (n + 1) / 2

/-- Triangular exponent `(n+1)(n+2)/2` in `ψ(q)`. -/
def tenthOrderPsiShift (n : ℕ) : ℕ :=
  (n + 1) * (n + 2) / 2

@[simp] theorem tenthOrderPhiShift_eq_triangular (n : ℕ) :
    tenthOrderPhiShift n = triangular n := rfl

@[simp] theorem tenthOrderPsiShift_eq_triangular_succ (n : ℕ) :
    tenthOrderPsiShift n = triangular (n + 1) := rfl

@[simp] theorem tenthOrderPsiShift_eq_phiShift_succ (n : ℕ) :
    tenthOrderPsiShift n = tenthOrderPhiShift (n + 1) := rfl

theorem tenthOrderPhiShift_succ (n : ℕ) :
    tenthOrderPhiShift (n + 1) = tenthOrderPhiShift n + n + 1 := by
  simpa [Nat.succ_eq_add_one, Nat.add_assoc] using triangular_succ n

theorem tenthOrderPsiShift_succ (n : ℕ) :
    tenthOrderPsiShift (n + 1) = tenthOrderPsiShift n + n + 2 := by
  simpa [Nat.succ_eq_add_one, Nat.add_assoc] using triangular_succ (n + 1)

/-- The formal `n`-th summand of Chan's `φ(q)`. -/
noncomputable def mockThetaPhiSummandPS (n : ℕ) : ℚ⟦X⟧ :=
  X ^ tenthOrderPhiShift n * (oddQPochPS (n + 1))⁻¹

/-- The formal `n`-th summand of Chan's `ψ(q)`. -/
noncomputable def mockThetaPsiSummandPS (n : ℕ) : ℚ⟦X⟧ :=
  X ^ tenthOrderPsiShift n * (oddQPochPS (n + 1))⁻¹

/-- Truncated multiplication by `(1-X^d)⁻¹`, keeping coefficients `0..N`. -/
def oddQPochInvMulStep (N d : ℕ) (v : Vector ℕ (N + 1)) : Vector ℕ (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) =>
    ∑ m : Fin (j.1 / d + 1),
      if m.1 * d ≤ j.1 then
        v.get ⟨j.1 - m.1 * d, by omega⟩
      else 0

/-- Coefficients `0..N` of `(q;q²)_n⁻¹`, computed by truncated convolution. -/
def oddQPochInvCoeffVec (N : ℕ) : ℕ → Vector ℕ (N + 1)
  | 0 => Vector.ofFn fun j : Fin (N + 1) => if j.1 = 0 then 1 else 0
  | n + 1 => oddQPochInvMulStep N (2 * n + 1) (oddQPochInvCoeffVec N n)

/-- Coefficient helper for `(q;q²)_n⁻¹`; out-of-window requests return `0`. -/
def oddQPochInvCoeff (N n k : ℕ) : ℕ :=
  if h : k < N + 1 then (oddQPochInvCoeffVec N n).get ⟨k, h⟩ else 0

@[simp] theorem oddQPochInvCoeffVec_coeff_zero (N n : ℕ) :
    (oddQPochInvCoeffVec N n).get ⟨0, Nat.succ_pos N⟩ = 1 := by
  induction n with
  | zero =>
      simp [oddQPochInvCoeffVec]
  | succ n ih =>
      simpa [oddQPochInvCoeffVec, oddQPochInvMulStep] using ih

@[simp] theorem oddQPochInvCoeff_zero (N n : ℕ) :
    oddQPochInvCoeff N n 0 = 1 := by
  simpa [oddQPochInvCoeff] using oddQPochInvCoeffVec_coeff_zero N n

/-- The coefficient of `q^k` in Chan's tenth-order mock theta `φ(q)`. -/
def mockThetaPhiCoeffNat (k : ℕ) : ℕ :=
  ∑ n : Fin (k + 1),
    if tenthOrderPhiShift n.1 ≤ k then
      oddQPochInvCoeff k (n.1 + 1) (k - tenthOrderPhiShift n.1)
    else 0

/-- The coefficient of `q^k` in Chan's tenth-order mock theta `ψ(q)`. -/
def mockThetaPsiCoeffNat (k : ℕ) : ℕ :=
  ∑ n : Fin (k + 1),
    if tenthOrderPsiShift n.1 ≤ k then
      oddQPochInvCoeff k (n.1 + 1) (k - tenthOrderPsiShift n.1)
    else 0

/-- Coefficients `0..N` of Chan's tenth-order mock theta `φ(q)`. -/
def mockThetaPhiCoeffVec (N : ℕ) : Vector ℕ (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) => mockThetaPhiCoeffNat j.1

/-- Coefficients `0..N` of Chan's tenth-order mock theta `ψ(q)`. -/
def mockThetaPsiCoeffVec (N : ℕ) : Vector ℕ (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) => mockThetaPsiCoeffNat j.1

/-- Coefficients `0..N` of `φ(q)` as a list. -/
def mockThetaPhiCoeffList (N : ℕ) : List ℕ :=
  (mockThetaPhiCoeffVec N).toList

/-- Coefficients `0..N` of `ψ(q)` as a list. -/
def mockThetaPsiCoeffList (N : ℕ) : List ℕ :=
  (mockThetaPsiCoeffVec N).toList

@[simp] theorem mockThetaPhiCoeffNat_zero : mockThetaPhiCoeffNat 0 = 1 := by
  simp [mockThetaPhiCoeffNat]

@[simp] theorem mockThetaPsiCoeffNat_zero : mockThetaPsiCoeffNat 0 = 0 := by
  simp [mockThetaPsiCoeffNat]

/-- Chan's tenth-order mock theta φ(q):
`φ(q) = ∑_{n≥0} q^{n(n+1)/2} / (q;q²)_{n+1}`. -/
def mockThetaPhiPS : ℚ⟦X⟧ :=
  PowerSeries.mk fun k => (mockThetaPhiCoeffNat k : ℚ)

/-- Chan's tenth-order mock theta ψ(q):
`ψ(q) = ∑_{n≥0} q^{(n+1)(n+2)/2} / (q;q²)_{n+1}`. -/
def mockThetaPsiPS : ℚ⟦X⟧ :=
  PowerSeries.mk fun k => (mockThetaPsiCoeffNat k : ℚ)

@[simp] theorem coeff_mockThetaPhiPS (k : ℕ) :
    mockThetaPhiPS.coeff k = (mockThetaPhiCoeffNat k : ℚ) := by
  unfold mockThetaPhiPS
  rw [PowerSeries.coeff_mk]

@[simp] theorem coeff_mockThetaPsiPS (k : ℕ) :
    mockThetaPsiPS.coeff k = (mockThetaPsiCoeffNat k : ℚ) := by
  unfold mockThetaPsiPS
  rw [PowerSeries.coeff_mk]

@[simp] theorem coeff_zero_mockThetaPhiPS : mockThetaPhiPS.coeff 0 = 1 := by
  simp

@[simp] theorem coeff_zero_mockThetaPsiPS : mockThetaPsiPS.coeff 0 = 0 := by
  simp

/-! ### Low-degree coefficient checks

The next two kernel-normalization certificates match OEIS A053281 and A053282
through degree `25`.
-/

theorem mockThetaPhiCoeffList_fifteen :
    mockThetaPhiCoeffList 15 =
      [1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26] := by
  rfl

theorem mockThetaPsiCoeffList_fifteen :
    mockThetaPsiCoeffList 15 =
      [0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16] := by
  rfl

theorem mockThetaPhiCoeffList_twentyfive :
    mockThetaPhiCoeffList 25 =
      [1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26, 31, 34, 40,
        46, 52, 60, 68, 76, 87, 98] := by
  rfl

theorem mockThetaPsiCoeffList_twentyfive :
    mockThetaPsiCoeffList 25 =
      [0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16, 18, 20, 24, 26,
        30, 36, 40, 44, 52, 58] := by
  rfl

theorem mockThetaPhiCoeffList_thirty :
    mockThetaPhiCoeffList 30 =
      [1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26, 31, 34, 40,
        46, 52, 60, 68, 76, 87, 98, 110, 124, 140, 156, 174] := by
  native_decide

theorem mockThetaPsiCoeffList_thirty :
    mockThetaPsiCoeffList 30 =
      [0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16, 18, 20, 24, 26,
        30, 36, 40, 44, 52, 58, 64, 74, 82, 91, 104] := by
  native_decide

theorem mockThetaPhiCoeffNat_thirty :
    mockThetaPhiCoeffNat 30 = 174 := by
  native_decide

theorem mockThetaPsiCoeffNat_thirty :
    mockThetaPsiCoeffNat 30 = 104 := by
  native_decide

theorem mockThetaPhiCoeffList_thirtyfive :
    mockThetaPhiCoeffList 35 =
      [1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26, 31, 34, 40,
        46, 52, 60, 68, 76, 87, 98, 110, 124, 140, 156, 174, 196, 216, 242,
        270, 298] := by
  native_decide

theorem mockThetaPsiCoeffList_thirtyfive :
    mockThetaPsiCoeffList 35 =
      [0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16, 18, 20, 24, 26,
        30, 36, 40, 44, 52, 58, 64, 74, 82, 91, 104, 116, 128, 144, 159, 176] := by
  native_decide

theorem mockThetaPhiCoeffNat_thirtyfive :
    mockThetaPhiCoeffNat 35 = 298 := by
  native_decide

theorem mockThetaPsiCoeffNat_thirtyfive :
    mockThetaPsiCoeffNat 35 = 176 := by
  native_decide

theorem coeff_mockThetaPhiPS_thirtyfive :
    mockThetaPhiPS.coeff 35 = 298 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_thirtyfive]
  norm_num

theorem coeff_mockThetaPsiPS_thirtyfive :
    mockThetaPsiPS.coeff 35 = 176 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_thirtyfive]
  norm_num

theorem mockThetaPhiCoeffList_forty :
    mockThetaPhiCoeffList 40 =
      [1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26, 31, 34, 40,
        46, 52, 60, 68, 76, 87, 98, 110, 124, 140, 156, 174, 196, 216, 242,
        270, 298, 332, 368, 406, 449, 496] := by
  native_decide

theorem mockThetaPsiCoeffList_forty :
    mockThetaPsiCoeffList 40 =
      [0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16, 18, 20, 24, 26,
        30, 36, 40, 44, 52, 58, 64, 74, 82, 91, 104, 116, 128, 144, 159, 176,
        198, 218, 240, 268, 294] := by
  native_decide

theorem mockThetaPhiCoeffNat_forty :
    mockThetaPhiCoeffNat 40 = 496 := by
  native_decide

theorem mockThetaPsiCoeffNat_forty :
    mockThetaPsiCoeffNat 40 = 294 := by
  native_decide

theorem coeff_mockThetaPhiPS_forty :
    mockThetaPhiPS.coeff 40 = 496 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_forty]
  norm_num

theorem coeff_mockThetaPsiPS_forty :
    mockThetaPsiPS.coeff 40 = 294 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_forty]
  norm_num

theorem mockThetaPhiCoeffList_fortyfive :
    mockThetaPhiCoeffList 45 =
      [1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26, 31, 34, 40,
        46, 52, 60, 68, 76, 87, 98, 110, 124, 140, 156, 174, 196, 216, 242,
        270, 298, 332, 368, 406, 449, 496, 546, 602, 664, 728, 800] := by
  native_decide

theorem mockThetaPsiCoeffList_fortyfive :
    mockThetaPsiCoeffList 45 =
      [0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16, 18, 20, 24, 26,
        30, 36, 40, 44, 52, 58, 64, 74, 82, 91, 104, 116, 128, 144, 159, 176,
        198, 218, 240, 268, 294, 324, 360, 394, 432, 478] := by
  native_decide

theorem mockThetaPhiCoeffNat_fortyfive :
    mockThetaPhiCoeffNat 45 = 800 := by
  native_decide

theorem mockThetaPsiCoeffNat_fortyfive :
    mockThetaPsiCoeffNat 45 = 478 := by
  native_decide

theorem coeff_mockThetaPhiPS_fortyfive :
    mockThetaPhiPS.coeff 45 = 800 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fortyfive]
  norm_num

theorem coeff_mockThetaPsiPS_fortyfive :
    mockThetaPsiPS.coeff 45 = 478 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fortyfive]
  norm_num

theorem mockThetaPhiCoeffList_fifty :
    mockThetaPhiCoeffList 50 =
      [1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26, 31, 34, 40,
        46, 52, 60, 68, 76, 87, 98, 110, 124, 140, 156, 174, 196, 216, 242,
        270, 298, 332, 368, 406, 449, 496, 546, 602, 664, 728, 800, 880, 962,
        1056, 1156, 1262] := by
  native_decide

theorem mockThetaPsiCoeffList_fifty :
    mockThetaPsiCoeffList 50 =
      [0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16, 18, 20, 24, 26,
        30, 36, 40, 44, 52, 58, 64, 74, 82, 91, 104, 116, 128, 144, 159, 176,
        198, 218, 240, 268, 294, 324, 360, 394, 432, 478, 524, 572, 630, 688,
        752] := by
  native_decide

theorem mockThetaPhiCoeffNat_fifty :
    mockThetaPhiCoeffNat 50 = 1262 := by
  native_decide

theorem mockThetaPsiCoeffNat_fifty :
    mockThetaPsiCoeffNat 50 = 752 := by
  native_decide

theorem coeff_mockThetaPhiPS_fifty :
    mockThetaPhiPS.coeff 50 = 1262 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fifty]
  norm_num

theorem coeff_mockThetaPsiPS_fifty :
    mockThetaPsiPS.coeff 50 = 752 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fifty]
  norm_num

theorem mockThetaPhiCoeffNat_fortysix :
    mockThetaPhiCoeffNat 46 = 880 := by
  native_decide

theorem mockThetaPsiCoeffNat_fortysix :
    mockThetaPsiCoeffNat 46 = 524 := by
  native_decide

theorem mockThetaPhiCoeffNat_fortyseven :
    mockThetaPhiCoeffNat 47 = 962 := by
  native_decide

theorem mockThetaPsiCoeffNat_fortyseven :
    mockThetaPsiCoeffNat 47 = 572 := by
  native_decide

theorem mockThetaPhiCoeffNat_fortyeight :
    mockThetaPhiCoeffNat 48 = 1056 := by
  native_decide

theorem mockThetaPsiCoeffNat_fortyeight :
    mockThetaPsiCoeffNat 48 = 630 := by
  native_decide

theorem mockThetaPhiCoeffNat_fortynine :
    mockThetaPhiCoeffNat 49 = 1156 := by
  native_decide

theorem mockThetaPsiCoeffNat_fortynine :
    mockThetaPsiCoeffNat 49 = 688 := by
  native_decide

theorem coeff_mockThetaPhiPS_fortysix :
    mockThetaPhiPS.coeff 46 = 880 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fortysix]
  norm_num

theorem coeff_mockThetaPsiPS_fortysix :
    mockThetaPsiPS.coeff 46 = 524 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fortysix]
  norm_num

theorem coeff_mockThetaPhiPS_fortyseven :
    mockThetaPhiPS.coeff 47 = 962 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fortyseven]
  norm_num

theorem coeff_mockThetaPsiPS_fortyseven :
    mockThetaPsiPS.coeff 47 = 572 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fortyseven]
  norm_num

theorem coeff_mockThetaPhiPS_fortyeight :
    mockThetaPhiPS.coeff 48 = 1056 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fortyeight]
  norm_num

theorem coeff_mockThetaPsiPS_fortyeight :
    mockThetaPsiPS.coeff 48 = 630 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fortyeight]
  norm_num

theorem coeff_mockThetaPhiPS_fortynine :
    mockThetaPhiPS.coeff 49 = 1156 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fortynine]
  norm_num

theorem coeff_mockThetaPsiPS_fortynine :
    mockThetaPsiPS.coeff 49 = 688 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fortynine]
  norm_num

theorem mockThetaPhiCoeffList_fiftyfive :
    mockThetaPhiCoeffList 55 =
      [1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26, 31, 34, 40,
        46, 52, 60, 68, 76, 87, 98, 110, 124, 140, 156, 174, 196, 216, 242,
        270, 298, 332, 368, 406, 449, 496, 546, 602, 664, 728, 800, 880, 962,
        1056, 1156, 1262, 1381, 1508, 1644, 1794, 1956] := by
  native_decide

theorem mockThetaPsiCoeffList_fiftyfive :
    mockThetaPsiCoeffList 55 =
      [0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16, 18, 20, 24, 26,
        30, 36, 40, 44, 52, 58, 64, 74, 82, 91, 104, 116, 128, 144, 159, 176,
        198, 218, 240, 268, 294, 324, 360, 394, 432, 478, 524, 572, 630, 688,
        752, 826, 900, 980, 1072, 1168] := by
  native_decide

theorem mockThetaPhiCoeffNat_fiftyfive :
    mockThetaPhiCoeffNat 55 = 1956 := by
  native_decide

theorem mockThetaPsiCoeffNat_fiftyfive :
    mockThetaPsiCoeffNat 55 = 1168 := by
  native_decide

theorem coeff_mockThetaPhiPS_fiftyfive :
    mockThetaPhiPS.coeff 55 = 1956 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fiftyfive]
  norm_num

theorem coeff_mockThetaPsiPS_fiftyfive :
    mockThetaPsiPS.coeff 55 = 1168 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fiftyfive]
  norm_num

theorem mockThetaPhiCoeffNat_fiftyone :
    mockThetaPhiCoeffNat 51 = 1381 := by
  native_decide

theorem mockThetaPsiCoeffNat_fiftyone :
    mockThetaPsiCoeffNat 51 = 826 := by
  native_decide

theorem mockThetaPhiCoeffNat_fiftytwo :
    mockThetaPhiCoeffNat 52 = 1508 := by
  native_decide

theorem mockThetaPsiCoeffNat_fiftytwo :
    mockThetaPsiCoeffNat 52 = 900 := by
  native_decide

theorem mockThetaPhiCoeffNat_fiftythree :
    mockThetaPhiCoeffNat 53 = 1644 := by
  native_decide

theorem mockThetaPsiCoeffNat_fiftythree :
    mockThetaPsiCoeffNat 53 = 980 := by
  native_decide

theorem mockThetaPhiCoeffNat_fiftyfour :
    mockThetaPhiCoeffNat 54 = 1794 := by
  native_decide

theorem mockThetaPsiCoeffNat_fiftyfour :
    mockThetaPsiCoeffNat 54 = 1072 := by
  native_decide

theorem coeff_mockThetaPhiPS_fiftyone :
    mockThetaPhiPS.coeff 51 = 1381 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fiftyone]
  norm_num

theorem coeff_mockThetaPsiPS_fiftyone :
    mockThetaPsiPS.coeff 51 = 826 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fiftyone]
  norm_num

theorem coeff_mockThetaPhiPS_fiftytwo :
    mockThetaPhiPS.coeff 52 = 1508 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fiftytwo]
  norm_num

theorem coeff_mockThetaPsiPS_fiftytwo :
    mockThetaPsiPS.coeff 52 = 900 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fiftytwo]
  norm_num

theorem coeff_mockThetaPhiPS_fiftythree :
    mockThetaPhiPS.coeff 53 = 1644 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fiftythree]
  norm_num

theorem coeff_mockThetaPsiPS_fiftythree :
    mockThetaPsiPS.coeff 53 = 980 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fiftythree]
  norm_num

theorem coeff_mockThetaPhiPS_fiftyfour :
    mockThetaPhiPS.coeff 54 = 1794 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fiftyfour]
  norm_num

theorem coeff_mockThetaPsiPS_fiftyfour :
    mockThetaPsiPS.coeff 54 = 1072 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fiftyfour]
  norm_num

theorem mockThetaPhiCoeffList_sixty :
    mockThetaPhiCoeffList 60 =
      [1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26, 31, 34, 40,
        46, 52, 60, 68, 76, 87, 98, 110, 124, 140, 156, 174, 196, 216, 242,
        270, 298, 332, 368, 406, 449, 496, 546, 602, 664, 728, 800, 880, 962,
        1056, 1156, 1262, 1381, 1508, 1644, 1794, 1956, 2128, 2316, 2520,
        2736, 2972] := by
  native_decide

theorem mockThetaPsiCoeffList_sixty :
    mockThetaPsiCoeffList 60 =
      [0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16, 18, 20, 24, 26,
        30, 36, 40, 44, 52, 58, 64, 74, 82, 91, 104, 116, 128, 144, 159, 176,
        198, 218, 240, 268, 294, 324, 360, 394, 432, 478, 524, 572, 630, 688,
        752, 826, 900, 980, 1072, 1168, 1270, 1386, 1505, 1634, 1780] := by
  native_decide

theorem mockThetaPhiCoeffNat_sixty :
    mockThetaPhiCoeffNat 60 = 2972 := by
  native_decide

theorem mockThetaPsiCoeffNat_sixty :
    mockThetaPsiCoeffNat 60 = 1780 := by
  native_decide

theorem coeff_mockThetaPhiPS_sixty :
    mockThetaPhiPS.coeff 60 = 2972 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_sixty]
  norm_num

theorem coeff_mockThetaPsiPS_sixty :
    mockThetaPsiPS.coeff 60 = 1780 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_sixty]
  norm_num

theorem mockThetaPhiCoeffNat_fiftysix :
    mockThetaPhiCoeffNat 56 = 2128 := by
  native_decide

theorem mockThetaPsiCoeffNat_fiftysix :
    mockThetaPsiCoeffNat 56 = 1270 := by
  native_decide

theorem mockThetaPhiCoeffNat_fiftyseven :
    mockThetaPhiCoeffNat 57 = 2316 := by
  native_decide

theorem mockThetaPsiCoeffNat_fiftyseven :
    mockThetaPsiCoeffNat 57 = 1386 := by
  native_decide

theorem mockThetaPhiCoeffNat_fiftyeight :
    mockThetaPhiCoeffNat 58 = 2520 := by
  native_decide

theorem mockThetaPsiCoeffNat_fiftyeight :
    mockThetaPsiCoeffNat 58 = 1505 := by
  native_decide

theorem mockThetaPhiCoeffNat_fiftynine :
    mockThetaPhiCoeffNat 59 = 2736 := by
  native_decide

theorem mockThetaPsiCoeffNat_fiftynine :
    mockThetaPsiCoeffNat 59 = 1634 := by
  native_decide

theorem coeff_mockThetaPhiPS_fiftysix :
    mockThetaPhiPS.coeff 56 = 2128 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fiftysix]
  norm_num

theorem coeff_mockThetaPsiPS_fiftysix :
    mockThetaPsiPS.coeff 56 = 1270 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fiftysix]
  norm_num

theorem coeff_mockThetaPhiPS_fiftyseven :
    mockThetaPhiPS.coeff 57 = 2316 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fiftyseven]
  norm_num

theorem coeff_mockThetaPsiPS_fiftyseven :
    mockThetaPsiPS.coeff 57 = 1386 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fiftyseven]
  norm_num

theorem coeff_mockThetaPhiPS_fiftyeight :
    mockThetaPhiPS.coeff 58 = 2520 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fiftyeight]
  norm_num

theorem coeff_mockThetaPsiPS_fiftyeight :
    mockThetaPsiPS.coeff 58 = 1505 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fiftyeight]
  norm_num

theorem coeff_mockThetaPhiPS_fiftynine :
    mockThetaPhiPS.coeff 59 = 2736 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_fiftynine]
  norm_num

theorem coeff_mockThetaPsiPS_fiftynine :
    mockThetaPsiPS.coeff 59 = 1634 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_fiftynine]
  norm_num

theorem mockThetaPhiCoeffList_sixtyfive :
    mockThetaPhiCoeffList 65 =
      [1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26, 31, 34, 40,
        46, 52, 60, 68, 76, 87, 98, 110, 124, 140, 156, 174, 196, 216, 242,
        270, 298, 332, 368, 406, 449, 496, 546, 602, 664, 728, 800, 880, 962,
        1056, 1156, 1262, 1381, 1508, 1644, 1794, 1956, 2128, 2316, 2520,
        2736, 2972, 3228, 3498, 3794, 4112, 4450] := by
  native_decide

theorem mockThetaPsiCoeffList_sixtyfive :
    mockThetaPsiCoeffList 65 =
      [0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16, 18, 20, 24, 26,
        30, 36, 40, 44, 52, 58, 64, 74, 82, 91, 104, 116, 128, 144, 159, 176,
        198, 218, 240, 268, 294, 324, 360, 394, 432, 478, 524, 572, 630, 688,
        752, 826, 900, 980, 1072, 1168, 1270, 1386, 1505, 1634, 1780, 1930,
        2092, 2272, 2460, 2663] := by
  native_decide

theorem mockThetaPhiCoeffNat_sixtyfive :
    mockThetaPhiCoeffNat 65 = 4450 := by
  native_decide

theorem mockThetaPsiCoeffNat_sixtyfive :
    mockThetaPsiCoeffNat 65 = 2663 := by
  native_decide

theorem coeff_mockThetaPhiPS_sixtyfive :
    mockThetaPhiPS.coeff 65 = 4450 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_sixtyfive]
  norm_num

theorem coeff_mockThetaPsiPS_sixtyfive :
    mockThetaPsiPS.coeff 65 = 2663 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_sixtyfive]
  norm_num

theorem mockThetaPhiCoeffNat_sixtyone :
    mockThetaPhiCoeffNat 61 = 3228 := by
  native_decide

theorem mockThetaPsiCoeffNat_sixtyone :
    mockThetaPsiCoeffNat 61 = 1930 := by
  native_decide

theorem mockThetaPhiCoeffNat_sixtytwo :
    mockThetaPhiCoeffNat 62 = 3498 := by
  native_decide

theorem mockThetaPsiCoeffNat_sixtytwo :
    mockThetaPsiCoeffNat 62 = 2092 := by
  native_decide

theorem mockThetaPhiCoeffNat_sixtythree :
    mockThetaPhiCoeffNat 63 = 3794 := by
  native_decide

theorem mockThetaPsiCoeffNat_sixtythree :
    mockThetaPsiCoeffNat 63 = 2272 := by
  native_decide

theorem mockThetaPhiCoeffNat_sixtyfour :
    mockThetaPhiCoeffNat 64 = 4112 := by
  native_decide

theorem mockThetaPsiCoeffNat_sixtyfour :
    mockThetaPsiCoeffNat 64 = 2460 := by
  native_decide

theorem coeff_mockThetaPhiPS_sixtyone :
    mockThetaPhiPS.coeff 61 = 3228 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_sixtyone]
  norm_num

theorem coeff_mockThetaPsiPS_sixtyone :
    mockThetaPsiPS.coeff 61 = 1930 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_sixtyone]
  norm_num

theorem coeff_mockThetaPhiPS_sixtytwo :
    mockThetaPhiPS.coeff 62 = 3498 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_sixtytwo]
  norm_num

theorem coeff_mockThetaPsiPS_sixtytwo :
    mockThetaPsiPS.coeff 62 = 2092 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_sixtytwo]
  norm_num

theorem coeff_mockThetaPhiPS_sixtythree :
    mockThetaPhiPS.coeff 63 = 3794 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_sixtythree]
  norm_num

theorem coeff_mockThetaPsiPS_sixtythree :
    mockThetaPsiPS.coeff 63 = 2272 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_sixtythree]
  norm_num

theorem coeff_mockThetaPhiPS_sixtyfour :
    mockThetaPhiPS.coeff 64 = 4112 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_sixtyfour]
  norm_num

theorem coeff_mockThetaPsiPS_sixtyfour :
    mockThetaPsiPS.coeff 64 = 2460 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_sixtyfour]
  norm_num

theorem mockThetaPhiCoeffList_seventy :
    mockThetaPhiCoeffList 70 =
      [1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26, 31, 34, 40,
        46, 52, 60, 68, 76, 87, 98, 110, 124, 140, 156, 174, 196, 216, 242,
        270, 298, 332, 368, 406, 449, 496, 546, 602, 664, 728, 800, 880, 962,
        1056, 1156, 1262, 1381, 1508, 1644, 1794, 1956, 2128, 2316, 2520,
        2736, 2972, 3228, 3498, 3794, 4112, 4450, 4818, 5212, 5632, 6088,
        6576] := by
  native_decide

theorem mockThetaPsiCoeffList_seventy :
    mockThetaPsiCoeffList 70 =
      [0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16, 18, 20, 24, 26,
        30, 36, 40, 44, 52, 58, 64, 74, 82, 91, 104, 116, 128, 144, 159, 176,
        198, 218, 240, 268, 294, 324, 360, 394, 432, 478, 524, 572, 630, 688,
        752, 826, 900, 980, 1072, 1168, 1270, 1386, 1505, 1634, 1780, 1930,
        2092, 2272, 2460, 2663, 2888, 3122, 3372, 3650, 3940] := by
  native_decide

theorem mockThetaPhiCoeffNat_seventy :
    mockThetaPhiCoeffNat 70 = 6576 := by
  native_decide

theorem mockThetaPsiCoeffNat_seventy :
    mockThetaPsiCoeffNat 70 = 3940 := by
  native_decide

theorem coeff_mockThetaPhiPS_seventy :
    mockThetaPhiPS.coeff 70 = 6576 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_seventy]
  norm_num

theorem coeff_mockThetaPsiPS_seventy :
    mockThetaPsiPS.coeff 70 = 3940 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_seventy]
  norm_num

theorem mockThetaPhiCoeffNat_sixtysix :
    mockThetaPhiCoeffNat 66 = 4818 := by
  native_decide

theorem mockThetaPsiCoeffNat_sixtysix :
    mockThetaPsiCoeffNat 66 = 2888 := by
  native_decide

theorem mockThetaPhiCoeffNat_sixtyseven :
    mockThetaPhiCoeffNat 67 = 5212 := by
  native_decide

theorem mockThetaPsiCoeffNat_sixtyseven :
    mockThetaPsiCoeffNat 67 = 3122 := by
  native_decide

theorem mockThetaPhiCoeffNat_sixtyeight :
    mockThetaPhiCoeffNat 68 = 5632 := by
  native_decide

theorem mockThetaPsiCoeffNat_sixtyeight :
    mockThetaPsiCoeffNat 68 = 3372 := by
  native_decide

theorem mockThetaPhiCoeffNat_sixtynine :
    mockThetaPhiCoeffNat 69 = 6088 := by
  native_decide

theorem mockThetaPsiCoeffNat_sixtynine :
    mockThetaPsiCoeffNat 69 = 3650 := by
  native_decide

theorem coeff_mockThetaPhiPS_sixtysix :
    mockThetaPhiPS.coeff 66 = 4818 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_sixtysix]
  norm_num

theorem coeff_mockThetaPsiPS_sixtysix :
    mockThetaPsiPS.coeff 66 = 2888 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_sixtysix]
  norm_num

theorem coeff_mockThetaPhiPS_sixtyseven :
    mockThetaPhiPS.coeff 67 = 5212 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_sixtyseven]
  norm_num

theorem coeff_mockThetaPsiPS_sixtyseven :
    mockThetaPsiPS.coeff 67 = 3122 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_sixtyseven]
  norm_num

theorem coeff_mockThetaPhiPS_sixtyeight :
    mockThetaPhiPS.coeff 68 = 5632 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_sixtyeight]
  norm_num

theorem coeff_mockThetaPsiPS_sixtyeight :
    mockThetaPsiPS.coeff 68 = 3372 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_sixtyeight]
  norm_num

theorem coeff_mockThetaPhiPS_sixtynine :
    mockThetaPhiPS.coeff 69 = 6088 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_sixtynine]
  norm_num

theorem coeff_mockThetaPsiPS_sixtynine :
    mockThetaPsiPS.coeff 69 = 3650 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_sixtynine]
  norm_num

theorem mockThetaPhiCoeffList_seventyfive :
    mockThetaPhiCoeffList 75 =
      [1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26, 31, 34, 40,
        46, 52, 60, 68, 76, 87, 98, 110, 124, 140, 156, 174, 196, 216, 242,
        270, 298, 332, 368, 406, 449, 496, 546, 602, 664, 728, 800, 880, 962,
        1056, 1156, 1262, 1381, 1508, 1644, 1794, 1956, 2128, 2316, 2520,
        2736, 2972, 3228, 3498, 3794, 4112, 4450, 4818, 5212, 5632, 6088,
        6576, 7096, 7657, 8260, 8900, 9590] := by
  native_decide

theorem mockThetaPsiCoeffList_seventyfive :
    mockThetaPsiCoeffList 75 =
      [0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16, 18, 20, 24, 26,
        30, 36, 40, 44, 52, 58, 64, 74, 82, 91, 104, 116, 128, 144, 159, 176,
        198, 218, 240, 268, 294, 324, 360, 394, 432, 478, 524, 572, 630, 688,
        752, 826, 900, 980, 1072, 1168, 1270, 1386, 1505, 1634, 1780, 1930,
        2092, 2272, 2460, 2663, 2888, 3122, 3372, 3650, 3940, 4252, 4594,
        4952, 5336, 5756] := by
  native_decide

theorem mockThetaPhiCoeffNat_seventyfive :
    mockThetaPhiCoeffNat 75 = 9590 := by
  native_decide

theorem mockThetaPsiCoeffNat_seventyfive :
    mockThetaPsiCoeffNat 75 = 5756 := by
  native_decide

theorem coeff_mockThetaPhiPS_seventyfive :
    mockThetaPhiPS.coeff 75 = 9590 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_seventyfive]
  norm_num

theorem coeff_mockThetaPsiPS_seventyfive :
    mockThetaPsiPS.coeff 75 = 5756 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_seventyfive]
  norm_num

theorem mockThetaPhiCoeffNat_seventyone :
    mockThetaPhiCoeffNat 71 = 7096 := by
  native_decide

theorem mockThetaPsiCoeffNat_seventyone :
    mockThetaPsiCoeffNat 71 = 4252 := by
  native_decide

theorem mockThetaPhiCoeffNat_seventytwo :
    mockThetaPhiCoeffNat 72 = 7657 := by
  native_decide

theorem mockThetaPsiCoeffNat_seventytwo :
    mockThetaPsiCoeffNat 72 = 4594 := by
  native_decide

theorem mockThetaPhiCoeffNat_seventythree :
    mockThetaPhiCoeffNat 73 = 8260 := by
  native_decide

theorem mockThetaPsiCoeffNat_seventythree :
    mockThetaPsiCoeffNat 73 = 4952 := by
  native_decide

theorem mockThetaPhiCoeffNat_seventyfour :
    mockThetaPhiCoeffNat 74 = 8900 := by
  native_decide

theorem mockThetaPsiCoeffNat_seventyfour :
    mockThetaPsiCoeffNat 74 = 5336 := by
  native_decide

theorem coeff_mockThetaPhiPS_seventyone :
    mockThetaPhiPS.coeff 71 = 7096 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_seventyone]
  norm_num

theorem coeff_mockThetaPsiPS_seventyone :
    mockThetaPsiPS.coeff 71 = 4252 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_seventyone]
  norm_num

theorem coeff_mockThetaPhiPS_seventytwo :
    mockThetaPhiPS.coeff 72 = 7657 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_seventytwo]
  norm_num

theorem coeff_mockThetaPsiPS_seventytwo :
    mockThetaPsiPS.coeff 72 = 4594 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_seventytwo]
  norm_num

theorem coeff_mockThetaPhiPS_seventythree :
    mockThetaPhiPS.coeff 73 = 8260 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_seventythree]
  norm_num

theorem coeff_mockThetaPsiPS_seventythree :
    mockThetaPsiPS.coeff 73 = 4952 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_seventythree]
  norm_num

theorem coeff_mockThetaPhiPS_seventyfour :
    mockThetaPhiPS.coeff 74 = 8900 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_seventyfour]
  norm_num

theorem coeff_mockThetaPsiPS_seventyfour :
    mockThetaPsiPS.coeff 74 = 5336 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_seventyfour]
  norm_num

theorem mockThetaPhiCoeffList_eighty :
    mockThetaPhiCoeffList 80 =
      [1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26, 31, 34, 40,
        46, 52, 60, 68, 76, 87, 98, 110, 124, 140, 156, 174, 196, 216, 242,
        270, 298, 332, 368, 406, 449, 496, 546, 602, 664, 728, 800, 880, 962,
        1056, 1156, 1262, 1381, 1508, 1644, 1794, 1956, 2128, 2316, 2520,
        2736, 2972, 3228, 3498, 3794, 4112, 4450, 4818, 5212, 5632, 6088,
        6576, 7096, 7657, 8260, 8900, 9590, 10332, 11116, 11964, 12870,
        13832] := by
  native_decide

theorem mockThetaPsiCoeffList_eighty :
    mockThetaPsiCoeffList 80 =
      [0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16, 18, 20, 24, 26,
        30, 36, 40, 44, 52, 58, 64, 74, 82, 91, 104, 116, 128, 144, 159, 176,
        198, 218, 240, 268, 294, 324, 360, 394, 432, 478, 524, 572, 630, 688,
        752, 826, 900, 980, 1072, 1168, 1270, 1386, 1505, 1634, 1780, 1930,
        2092, 2272, 2460, 2663, 2888, 3122, 3372, 3650, 3940, 4252, 4594,
        4952, 5336, 5756, 6198, 6670, 7184, 7724, 8304] := by
  native_decide

theorem mockThetaPhiCoeffNat_seventysix :
    mockThetaPhiCoeffNat 76 = 10332 := by
  native_decide

theorem mockThetaPsiCoeffNat_seventysix :
    mockThetaPsiCoeffNat 76 = 6198 := by
  native_decide

theorem mockThetaPhiCoeffNat_seventyseven :
    mockThetaPhiCoeffNat 77 = 11116 := by
  native_decide

theorem mockThetaPsiCoeffNat_seventyseven :
    mockThetaPsiCoeffNat 77 = 6670 := by
  native_decide

theorem mockThetaPhiCoeffNat_seventyeight :
    mockThetaPhiCoeffNat 78 = 11964 := by
  native_decide

theorem mockThetaPsiCoeffNat_seventyeight :
    mockThetaPsiCoeffNat 78 = 7184 := by
  native_decide

theorem mockThetaPhiCoeffNat_seventynine :
    mockThetaPhiCoeffNat 79 = 12870 := by
  native_decide

theorem mockThetaPsiCoeffNat_seventynine :
    mockThetaPsiCoeffNat 79 = 7724 := by
  native_decide

theorem mockThetaPhiCoeffNat_eighty :
    mockThetaPhiCoeffNat 80 = 13832 := by
  native_decide

theorem mockThetaPsiCoeffNat_eighty :
    mockThetaPsiCoeffNat 80 = 8304 := by
  native_decide

theorem coeff_mockThetaPhiPS_seventysix :
    mockThetaPhiPS.coeff 76 = 10332 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_seventysix]
  norm_num

theorem coeff_mockThetaPsiPS_seventysix :
    mockThetaPsiPS.coeff 76 = 6198 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_seventysix]
  norm_num

theorem coeff_mockThetaPhiPS_seventyseven :
    mockThetaPhiPS.coeff 77 = 11116 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_seventyseven]
  norm_num

theorem coeff_mockThetaPsiPS_seventyseven :
    mockThetaPsiPS.coeff 77 = 6670 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_seventyseven]
  norm_num

theorem coeff_mockThetaPhiPS_seventyeight :
    mockThetaPhiPS.coeff 78 = 11964 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_seventyeight]
  norm_num

theorem coeff_mockThetaPsiPS_seventyeight :
    mockThetaPsiPS.coeff 78 = 7184 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_seventyeight]
  norm_num

theorem coeff_mockThetaPhiPS_seventynine :
    mockThetaPhiPS.coeff 79 = 12870 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_seventynine]
  norm_num

theorem coeff_mockThetaPsiPS_seventynine :
    mockThetaPsiPS.coeff 79 = 7724 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_seventynine]
  norm_num

theorem coeff_mockThetaPhiPS_eighty :
    mockThetaPhiPS.coeff 80 = 13832 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_eighty]
  norm_num

theorem coeff_mockThetaPsiPS_eighty :
    mockThetaPsiPS.coeff 80 = 8304 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_eighty]
  norm_num

theorem mockThetaPhiCoeffNat_eightyone :
    mockThetaPhiCoeffNat 81 = 14868 := by
  native_decide

theorem mockThetaPsiCoeffNat_eightyone :
    mockThetaPsiCoeffNat 81 = 8932 := by
  native_decide

theorem mockThetaPhiCoeffNat_eightytwo :
    mockThetaPhiCoeffNat 82 = 15972 := by
  native_decide

theorem mockThetaPsiCoeffNat_eightytwo :
    mockThetaPsiCoeffNat 82 = 9592 := by
  native_decide

theorem mockThetaPhiCoeffNat_eightythree :
    mockThetaPhiCoeffNat 83 = 17148 := by
  native_decide

theorem mockThetaPsiCoeffNat_eightythree :
    mockThetaPsiCoeffNat 83 = 10298 := by
  native_decide

theorem mockThetaPhiCoeffNat_eightyfour :
    mockThetaPhiCoeffNat 84 = 18408 := by
  native_decide

theorem mockThetaPsiCoeffNat_eightyfour :
    mockThetaPsiCoeffNat 84 = 11062 := by
  native_decide

theorem mockThetaPhiCoeffNat_eightyfive :
    mockThetaPhiCoeffNat 85 = 19752 := by
  native_decide

theorem mockThetaPsiCoeffNat_eightyfive :
    mockThetaPsiCoeffNat 85 = 11868 := by
  native_decide

theorem coeff_mockThetaPhiPS_eightyone :
    mockThetaPhiPS.coeff 81 = 14868 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_eightyone]
  norm_num

theorem coeff_mockThetaPsiPS_eightyone :
    mockThetaPsiPS.coeff 81 = 8932 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_eightyone]
  norm_num

theorem coeff_mockThetaPhiPS_eightytwo :
    mockThetaPhiPS.coeff 82 = 15972 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_eightytwo]
  norm_num

theorem coeff_mockThetaPsiPS_eightytwo :
    mockThetaPsiPS.coeff 82 = 9592 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_eightytwo]
  norm_num

theorem coeff_mockThetaPhiPS_eightythree :
    mockThetaPhiPS.coeff 83 = 17148 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_eightythree]
  norm_num

theorem coeff_mockThetaPsiPS_eightythree :
    mockThetaPsiPS.coeff 83 = 10298 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_eightythree]
  norm_num

theorem coeff_mockThetaPhiPS_eightyfour :
    mockThetaPhiPS.coeff 84 = 18408 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_eightyfour]
  norm_num

theorem coeff_mockThetaPsiPS_eightyfour :
    mockThetaPsiPS.coeff 84 = 11062 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_eightyfour]
  norm_num

theorem coeff_mockThetaPhiPS_eightyfive :
    mockThetaPhiPS.coeff 85 = 19752 := by
  rw [coeff_mockThetaPhiPS, mockThetaPhiCoeffNat_eightyfive]
  norm_num

theorem coeff_mockThetaPsiPS_eightyfive :
    mockThetaPsiPS.coeff 85 = 11868 := by
  rw [coeff_mockThetaPsiPS, mockThetaPsiCoeffNat_eightyfive]
  norm_num

/-! ## Chan Eq. (10.15), formal target after `Q = q^(1/3)`

The displayed Eq. (10.15) in Chan is

```text
∑_{k,l,r,s} ρ_{r,s} (-1)^{k+l+r+s}
  (δ(k)-δ(r))(δ(l)-δ(s))
  q^((k²+l²+r²+3rs+s²+3r+3s+1)/3)
= - (q;q)_∞^5 / (q²;q²)_∞^2
    ∑_n (-1)^n q^(n(5n+3)/2).
```

The definitions below replace `q` by `Q^3`, so the exponent on the left is
integral:

```text
Q^(k²+l²+r²+3rs+s²+3r+3s+1).
```

The right-hand side becomes

```text
- (Q³;Q³)_∞^5 / (Q⁶;Q⁶)_∞^2
    ∑_n (-1)^n Q^(3n(5n+3)/2).
```

The final theorem is not asserted here; these definitions make the exact
formal-power-series proposition available without introducing any proof hole.
-/

/-- Chan's sign `ρ_{r,s}` from Eq. (10.12), integer-valued. -/
def rhoInt (r s : ℤ) : ℤ :=
  if 0 ≤ r ∧ 0 ≤ s then 1 else if r < 0 ∧ s < 0 then -1 else 0

/-- The mod-3 filter `δ(r)` from Eq. (10.13), integer-valued. -/
def delta3Int (r : ℤ) : ℤ :=
  if (3 : ℤ) ∣ r then 1 else 0

/-- The integral `Q`-exponent obtained from Chan's Eq. (10.15) after `q = Q^3`. -/
def chan1015QExponent (k l r s : ℤ) : ℕ :=
  (k * k + l * l + r * r + 3 * r * s + s * s + 3 * r + 3 * s + 1).toNat

/-- One coefficient contribution in the four-variable indefinite theta side. -/
def chan1015CoeffTerm (R : Type*) [CommRing R] (N : ℕ) (k l r s : ℤ) : R :=
  if chan1015QExponent k l r s = N then
    ((rhoInt r s : ℤ) : R) *
      negOnePowInt R (k + l + r + s) *
      (((delta3Int k - delta3Int r : ℤ) : R)) *
      (((delta3Int l - delta3Int s : ℤ) : R))
  else 0

/-- Largest `m ≤ N` with `m² ≤ N`, used as the `k,l` coefficient window. -/
def squareWindow (N : ℕ) : ℕ :=
  ((List.range (N + 1)).filter (fun m => m * m ≤ N)).foldl Nat.max 0

/-- Coefficient of `Q^N` in the formal four-variable indefinite theta side.

The `k,l` variables use the square-root window forced by their positive
quadratic contribution.  The `r,s` variables keep the conservative
`[-(N+2), N+2]` window from the original coefficient formula. -/
def chan1015LHSCoeff (R : Type*) [CommRing R] (N : ℕ) : R :=
  let B : ℤ := N + 2
  let K : ℤ := squareWindow N
  ∑ k ∈ Finset.Icc (-K) K,
    ∑ l ∈ Finset.Icc (-K) K,
      ∑ r ∈ Finset.Icc (-B) B,
        ∑ s ∈ Finset.Icc (-B) B,
          chan1015CoeffTerm R N k l r s

/-- Formal four-variable indefinite theta side of Chan Eq. (10.15), after `q = Q^3`. -/
noncomputable def chan1015LHSPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk (chan1015LHSCoeff R)

@[simp] theorem coeff_chan1015LHSPS (R : Type*) [CommRing R] (N : ℕ) :
    (chan1015LHSPS R).coeff N = chan1015LHSCoeff R N := by
  unfold chan1015LHSPS
  rw [PowerSeries.coeff_mk]

/-- `(Q^d; Q^d)_∞` as a formal power series. -/
noncomputable def qPochInfAtPowerPS (d : ℕ) (hd : d ≠ 0) : ℚ⟦X⟧ :=
  PowerSeries.expand d hd (qPochInfPS ℚ)

private theorem continuous_expand_ch10 (R : Type*) [CommRing R] [TopologicalSpace R]
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

theorem expand_qPochAPPS_rat (s r m : ℕ) (hs : s ≠ 0) (hm : 0 < m) :
    PowerSeries.expand s hs (qPochAPPS ℚ r m) =
      qPochAPPS ℚ (s * r) (s * m) := by
  unfold qPochAPPS
  rw [(multipliable_apFactorPS ℚ r m hm).map_tprod
    (PowerSeries.expand s hs) (continuous_expand_ch10 ℚ s hs)]
  apply tprod_congr
  intro n
  calc
    PowerSeries.expand s hs (apFactorPS ℚ r m n)
        = (1 : ℚ⟦X⟧) - PowerSeries.X ^ (s * (r + m * n)) := by
          rw [apFactorPS, map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
    _ = apFactorPS ℚ (s * r) (s * m) n := by
          rw [apFactorPS]
          congr 1
          ring

theorem expand_qPochInfPS_eq_qPochAPPS_self_rat (s : ℕ) (hs : s ≠ 0) :
    PowerSeries.expand s hs (qPochInfPS ℚ) = qPochAPPS ℚ s s := by
  rw [qPochInfPS_eq_tprod ℚ]
  rw [(multipliable_one_sub_X_pow_succ ℚ).map_tprod
    (PowerSeries.expand s hs) (continuous_expand_ch10 ℚ s hs)]
  unfold qPochAPPS
  apply tprod_congr
  intro n
  calc
    PowerSeries.expand s hs ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1))
        = (1 : ℚ⟦X⟧) - PowerSeries.X ^ (s * (n + 1)) := by
          rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
    _ = apFactorPS ℚ s s n := by
          rw [apFactorPS]
          congr 1
          ring

theorem qPochInfAtPowerPS_eq_qPochAPPS_self (d : ℕ) (hd : d ≠ 0) :
    qPochInfAtPowerPS d hd = qPochAPPS ℚ d d := by
  exact expand_qPochInfPS_eq_qPochAPPS_self_rat d hd

/-! ### `thetaOp` bridge for arithmetic-progression products

This is the Chapter 10 analogue of the Lambert-to-product bridge used in
`Chapter15_WronskianBridge`: the logarithmic theta derivative of
`(q^r;q^m)_∞` is the negative AP divisor-sigma series.
-/

noncomputable def divisorGeomPSLocal (R : Type*) [CommRing R] (d : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun n => if d ∣ n ∧ 0 < n then (1 : R) else 0

@[simp] theorem coeff_divisorGeomPSLocal (R : Type*) [CommRing R] (d n : ℕ) :
    (divisorGeomPSLocal R d).coeff n = if d ∣ n ∧ 0 < n then (1 : R) else 0 := by
  simp [divisorGeomPSLocal]

private theorem coeff_X_pow_mul_eq_zero_of_lt_local (R : Type*) [CommRing R]
    (G : R⟦X⟧) {d n : ℕ} (hnd : n < d) :
    (PowerSeries.X ^ d * G).coeff n = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [PowerSeries.coeff_X_pow]
  split_ifs with hx1
  · have hsum := Finset.mem_antidiagonal.mp hx
    omega
  · simp

private theorem coeff_X_pow_mul_cases_local (R : Type*) [CommRing R]
    (G : R⟦X⟧) (d n : ℕ) :
    (PowerSeries.X ^ d * G).coeff n = if d ≤ n then G.coeff (n - d) else 0 := by
  by_cases hdn : d ≤ n
  · have h := PowerSeries.coeff_X_pow_mul G d (n - d)
    rw [if_pos hdn]
    simpa [Nat.sub_add_cancel hdn, Nat.add_comm] using h
  · rw [if_neg hdn]
    exact coeff_X_pow_mul_eq_zero_of_lt_local R G (Nat.lt_of_not_ge hdn)

theorem one_sub_X_pow_mul_divisorGeomPSLocal
    (R : Type*) [CommRing R] {d : ℕ} (hd : 0 < d) :
    ((1 : R⟦X⟧) - PowerSeries.X ^ d) * divisorGeomPSLocal R d =
      PowerSeries.X ^ d := by
  ext n
  rw [sub_mul]
  simp only [map_sub]
  rw [coeff_X_pow_mul_cases_local R (divisorGeomPSLocal R d) d n]
  rw [PowerSeries.coeff_X_pow]
  by_cases hn0 : n = 0
  · subst n
    have hz : ¬ 0 = d := by omega
    simp [hz]
  by_cases hdn : d ≤ n
  · rw [if_pos hdn]
    by_cases hnd : n = d
    · subst n
      simp [hd]
    · have hlt : d < n := lt_of_le_of_ne hdn (Ne.symm hnd)
      have hn_minus_pos : 0 < n - d := Nat.sub_pos_of_lt hlt
      by_cases hdiv : d ∣ n
      · have hdiv_sub : d ∣ n - d := by
          rcases hdiv with ⟨a, ha⟩
          have ha_pos : 0 < a := by
            by_contra haz
            have ha0 : a = 0 := Nat.eq_zero_of_not_pos haz
            simp [ha0] at ha
            omega
          refine ⟨a - 1, ?_⟩
          calc
            n - d = d * a - d := by rw [ha]
            _ = d * a - d * 1 := by simp
            _ = d * (a - 1) := by rw [← Nat.mul_sub_left_distrib]
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        simp [hdiv, hdiv_sub, hn_minus_pos, hnpos, hnd]
      · have hdiv_sub_false : ¬ d ∣ n - d := by
          intro hs
          apply hdiv
          rcases hs with ⟨a, ha⟩
          refine ⟨a + 1, ?_⟩
          calc
            n = (n - d) + d := (Nat.sub_add_cancel hdn).symm
            _ = d * a + d := by rw [ha]
            _ = d * (a + 1) := by ring
        simp [hdiv, hdiv_sub_false, hn_minus_pos, hnd]
  · rw [if_neg hdn]
    have hx : ¬ (d ∣ n ∧ 0 < n) := by
      intro h
      exact hdn (Nat.le_of_dvd h.2 h.1)
    have hne : ¬ n = d := by omega
    simp [hx, hne]

theorem thetaOp_X_pow_local (R : Type*) [CommRing R] (d : ℕ) :
    thetaOp (PowerSeries.X ^ d : R⟦X⟧) =
      PowerSeries.C (d : R) * PowerSeries.X ^ d := by
  ext n
  rw [coeff_thetaOp, PowerSeries.coeff_C_mul]
  rw [PowerSeries.coeff_X_pow]
  split_ifs with h <;> subst_vars <;> simp

theorem thetaOp_one_sub_X_pow_local (R : Type*) [CommRing R] (d : ℕ) :
    thetaOp ((1 : R⟦X⟧) - PowerSeries.X ^ d) =
      -PowerSeries.C (d : R) * PowerSeries.X ^ d := by
  rw [thetaOp_sub, thetaOp_one, thetaOp_X_pow_local]
  ring

noncomputable def qPochAPFinitePS (R : Type*) [CommRing R]
    (r m N : ℕ) : R⟦X⟧ :=
  ∏ n ∈ Finset.range N, apFactorPS R r m n

noncomputable def apDivisorSigmaFinitePS (R : Type*) [CommRing R]
    (r m N : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range N,
      if r + m * k ∣ n ∧ 0 < n then ((r + m * k : ℕ) : R) else 0

noncomputable def apDivisorSigmaPS (R : Type*) [CommRing R]
    (r m : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1),
      if r + m * k ∣ n ∧ 0 < n then ((r + m * k : ℕ) : R) else 0

@[simp] theorem coeff_apDivisorSigmaFinitePS (R : Type*) [CommRing R]
    (r m N n : ℕ) :
    (apDivisorSigmaFinitePS R r m N).coeff n =
      ∑ k ∈ Finset.range N,
        if r + m * k ∣ n ∧ 0 < n then ((r + m * k : ℕ) : R) else 0 := by
  simp [apDivisorSigmaFinitePS]

@[simp] theorem coeff_apDivisorSigmaPS (R : Type*) [CommRing R]
    (r m n : ℕ) :
    (apDivisorSigmaPS R r m).coeff n =
      ∑ k ∈ Finset.range (n + 1),
        if r + m * k ∣ n ∧ 0 < n then ((r + m * k : ℕ) : R) else 0 := by
  simp [apDivisorSigmaPS]

@[simp] theorem coeff_zero_apDivisorSigmaPS (R : Type*) [CommRing R] (r m : ℕ) :
    (apDivisorSigmaPS R r m).coeff 0 = 0 := by
  simp [apDivisorSigmaPS]

@[simp] theorem constantCoeff_apDivisorSigmaPS (R : Type*) [CommRing R] (r m : ℕ) :
    PowerSeries.constantCoeff (apDivisorSigmaPS R r m) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_apDivisorSigmaPS R r m

theorem qPochAPFinitePS_succ (R : Type*) [CommRing R] (r m N : ℕ) :
    qPochAPFinitePS R r m (N + 1) =
      qPochAPFinitePS R r m N * apFactorPS R r m N := by
  simp [qPochAPFinitePS, Finset.prod_range_succ]

theorem apDivisorSigmaFinitePS_succ (R : Type*) [CommRing R] (r m N : ℕ) :
    apDivisorSigmaFinitePS R r m (N + 1) =
      apDivisorSigmaFinitePS R r m N +
        PowerSeries.C (((r + m * N : ℕ) : R)) *
          divisorGeomPSLocal R (r + m * N) := by
  ext n
  rw [map_add, PowerSeries.coeff_C_mul, coeff_apDivisorSigmaFinitePS,
    coeff_apDivisorSigmaFinitePS,
    coeff_divisorGeomPSLocal]
  rw [Finset.sum_range_succ]
  by_cases h : r + m * N ∣ n ∧ 0 < n <;> simp [h]

theorem thetaOp_qPochAPFinitePS (R : Type*) [CommRing R]
    {r m : ℕ} (hr : 0 < r) (N : ℕ) :
    thetaOp (qPochAPFinitePS R r m N) =
      -qPochAPFinitePS R r m N * apDivisorSigmaFinitePS R r m N := by
  induction N with
  | zero =>
      have hzero : apDivisorSigmaFinitePS R r m 0 = 0 := by
        ext n
        simp [apDivisorSigmaFinitePS]
      simp [qPochAPFinitePS, hzero]
  | succ N ih =>
      rw [qPochAPFinitePS_succ, apDivisorSigmaFinitePS_succ]
      rw [thetaOp_mul, apFactorPS, thetaOp_one_sub_X_pow_local, ih]
      have hdpos : 0 < r + m * N := by omega
      have hgeom :=
        one_sub_X_pow_mul_divisorGeomPSLocal R (d := r + m * N) hdpos
      calc
        (qPochAPFinitePS R r m N *
              (-C ↑(r + m * N) * X ^ (r + m * N)) +
            apFactorPS R r m N *
              (-qPochAPFinitePS R r m N * apDivisorSigmaFinitePS R r m N))
            =
          -qPochAPFinitePS R r m N * apDivisorSigmaFinitePS R r m N *
              apFactorPS R r m N -
            qPochAPFinitePS R r m N * (C ↑(r + m * N) * X ^ (r + m * N)) := by
            ring
        _ =
          -qPochAPFinitePS R r m N * apDivisorSigmaFinitePS R r m N *
              apFactorPS R r m N -
            qPochAPFinitePS R r m N *
              (C ↑(r + m * N) *
                (apFactorPS R r m N *
                  divisorGeomPSLocal R (r + m * N))) := by
            rw [apFactorPS, hgeom]
        _ =
          -(qPochAPFinitePS R r m N * apFactorPS R r m N) *
            (apDivisorSigmaFinitePS R r m N +
              C ↑(r + m * N) *
                divisorGeomPSLocal R (r + m * N)) := by
            ring

theorem qPochAPFinitePS_coeff_stable
    (R : Type*) [CommRing R] (r m k N : ℕ) (hk : k < r + m * N) :
    (qPochAPFinitePS R r m (N + 1)).coeff k =
      (qPochAPFinitePS R r m N).coeff k := by
  rw [qPochAPFinitePS_succ]
  exact coeff_mul_apFactorPS_eq_of_lt R (qPochAPFinitePS R r m N) k r m N hk

theorem qPochAPFinitePS_coeff_eq_of_le
    (R : Type*) [CommRing R] {r m k N M : ℕ}
    (hk : k < r + m * N) (hNM : N ≤ M) :
    (qPochAPFinitePS R r m M).coeff k =
      (qPochAPFinitePS R r m N).coeff k := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
      have hmono : m * N ≤ m * M := Nat.mul_le_mul_left m hNM
      rw [qPochAPFinitePS_coeff_stable R r m k M (by omega), ih]

theorem coeff_qPochAPPS_eq_qPochAPFinitePS_rat
    (r m k : ℕ) (hr : 0 < r) (hm : 0 < m) :
    (qPochAPPS ℚ r m).coeff k =
      (qPochAPFinitePS ℚ r m (k + 1)).coeff k := by
  have h_tendsto : Tendsto
      (fun N : ℕ => qPochAPFinitePS ℚ r m N) atTop
      (𝓝 (qPochAPPS ℚ r m)) := by
    simpa [qPochAPFinitePS] using tendsto_qPochAPPS_partial ℚ r m hm
  have h_coeff_tendsto : Tendsto
      (fun N : ℕ => (qPochAPFinitePS ℚ r m N).coeff k) atTop
      (𝓝 ((qPochAPPS ℚ r m).coeff k)) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℚ k).tendsto _).comp h_tendsto
  have h_const_tendsto : Tendsto
      (fun N : ℕ => (qPochAPFinitePS ℚ r m N).coeff k) atTop
      (𝓝 ((qPochAPFinitePS ℚ r m (k + 1)).coeff k)) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨k + 1, fun N hN => ?_⟩
    have hk : k < r + m * (k + 1) := by
      have hm1 : 1 ≤ m := Nat.succ_le_of_lt hm
      have hle : k + 1 ≤ m * (k + 1) := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right (k + 1) hm1
      omega
    exact (qPochAPFinitePS_coeff_eq_of_le ℚ
      (r := r) (m := m) (k := k) (N := k + 1) (M := N) hk hN).symm
  exact tendsto_nhds_unique h_coeff_tendsto h_const_tendsto

theorem coeff_apDivisorSigmaFinitePS_eq_apDivisorSigmaPS
    (R : Type*) [CommRing R] (r m n N : ℕ) (hr : 0 < r) (hm : 0 < m)
    (hN : n + 1 ≤ N) :
    (apDivisorSigmaFinitePS R r m N).coeff n =
      (apDivisorSigmaPS R r m).coeff n := by
  rw [coeff_apDivisorSigmaFinitePS, coeff_apDivisorSigmaPS]
  rw [← Finset.sum_range_add_sum_Ico
    (fun k => if r + m * k ∣ n ∧ 0 < n then ((r + m * k : ℕ) : R) else 0) hN]
  have htail : (∑ k ∈ Finset.Ico (n + 1) N,
      (if r + m * k ∣ n ∧ 0 < n then ((r + m * k : ℕ) : R) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hgt : n < r + m * k := by
      have hm1 : 1 ≤ m := Nat.succ_le_of_lt hm
      have hk_le : k ≤ m * k := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right k hm1
      omega
    have hnot : ¬ (r + m * k ∣ n ∧ 0 < n) := by
      intro h
      exact Nat.not_lt_of_ge (Nat.le_of_dvd h.2 h.1) hgt
    simp [hnot]
  rw [htail, add_zero]

theorem thetaOp_qPochAPPS_rat (r m : ℕ) (hr : 0 < r) (hm : 0 < m) :
    thetaOp (qPochAPPS ℚ r m) =
      -qPochAPPS ℚ r m * apDivisorSigmaPS ℚ r m := by
  ext n
  let N := n + 1
  have hcoeff_q := coeff_qPochAPPS_eq_qPochAPFinitePS_rat r m n hr hm
  have htheta :
      (thetaOp (qPochAPPS ℚ r m)).coeff n =
        (thetaOp (qPochAPFinitePS ℚ r m N)).coeff n := by
    rw [coeff_thetaOp, coeff_thetaOp, hcoeff_q]
  have hfin := congrArg (fun f : ℚ⟦X⟧ => f.coeff n)
    (thetaOp_qPochAPFinitePS ℚ (r := r) (m := m) hr N)
  have hfin' :
      (thetaOp (qPochAPFinitePS ℚ r m N)).coeff n =
        (-qPochAPFinitePS ℚ r m N *
          apDivisorSigmaFinitePS ℚ r m N).coeff n := by
    simpa using hfin
  rw [htheta, hfin']
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [map_neg, map_neg]
  have hp_sum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  have hp1 : p.1 ≤ n := by omega
  have hp2N : p.2 + 1 ≤ N := by omega
  have hp1N : p.1 + 1 ≤ N := by omega
  have hq_stable :
      (qPochAPFinitePS ℚ r m N).coeff p.1 =
        (qPochAPFinitePS ℚ r m (p.1 + 1)).coeff p.1 := by
    have hk : p.1 < r + m * (p.1 + 1) := by
      have hm1 : 1 ≤ m := Nat.succ_le_of_lt hm
      have hle : p.1 + 1 ≤ m * (p.1 + 1) := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right (p.1 + 1) hm1
      omega
    exact qPochAPFinitePS_coeff_eq_of_le ℚ (r := r) (m := m) (k := p.1)
      (N := p.1 + 1) (M := N) hk hp1N
  rw [hq_stable]
  rw [← coeff_qPochAPPS_eq_qPochAPFinitePS_rat r m p.1 hr hm]
  rw [coeff_apDivisorSigmaFinitePS_eq_apDivisorSigmaPS ℚ r m p.2 N hr hm hp2N]

theorem constantCoeff_qPochAPPS_rat (r m : ℕ) (hr : 0 < r) (hm : 0 < m) :
    PowerSeries.constantCoeff (qPochAPPS ℚ r m) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [coeff_qPochAPPS_eq_qPochAPFinitePS_rat r m 0 hr hm]
  simp [qPochAPFinitePS, apFactorPS, hr.ne']

/-- The pentagonal series on the right of Eq. (10.15), after `q = Q^3`.

The source series is `∑ (-1)^k X^((5k²-3k)/2)`. Reindexing `k ↦ -k` gives
Chan's `∑ (-1)^n q^(n(5n+3)/2)`, and `expand 3` substitutes `q = Q^3`. -/
noncomputable def chan1015PentagonalPS : ℚ⟦X⟧ :=
  PowerSeries.expand 3 (by decide : (3 : ℕ) ≠ 0) (pentagonal014SeriesPS ℚ)

theorem chan1015PentagonalPS_eq_apProducts :
    chan1015PentagonalPS =
      qPochAPPS ℚ 3 15 * qPochAPPS ℚ 12 15 * qPochAPPS ℚ 15 15 := by
  unfold chan1015PentagonalPS
  rw [← pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat]
  unfold pentagonalProduct014PS
  rw [map_mul, map_mul]
  rw [expand_qPochAPPS_rat 3 1 5 (by decide) (by norm_num),
    expand_qPochAPPS_rat 3 4 5 (by decide) (by norm_num),
    expand_qPochAPPS_rat 3 5 5 (by decide) (by norm_num)]

/-- Product side of Chan Eq. (10.15), after `q = Q^3`. -/
noncomputable def chan1015RHSPS : ℚ⟦X⟧ :=
  -((qPochInfAtPowerPS 3 (by decide : (3 : ℕ) ≠ 0)) ^ 5 *
      ((qPochInfAtPowerPS 6 (by decide : (6 : ℕ) ≠ 0)) ^ 2)⁻¹ *
      chan1015PentagonalPS)

theorem chan1015RHSPS_eq_apProduct :
    chan1015RHSPS =
      -((qPochAPPS ℚ 3 3) ^ 5 * ((qPochAPPS ℚ 6 6) ^ 2)⁻¹ *
        (qPochAPPS ℚ 3 15 * qPochAPPS ℚ 12 15 * qPochAPPS ℚ 15 15)) := by
  unfold chan1015RHSPS
  rw [qPochInfAtPowerPS_eq_qPochAPPS_self,
    qPochInfAtPowerPS_eq_qPochAPPS_self,
    chan1015PentagonalPS_eq_apProducts]

/-! ### Computable coefficients for Chan Eq. (10.15) RHS -/

/-- Integer coefficient of `(q;q)_∞`, via Euler's pentagonal theorem. -/
def chan1015EtaCoeffZ (n : ℕ) : ℤ :=
  QseriesFormalization.PartI.Ch04Franklin.pentagonalSign n

/-- Coefficient of `(Q^d;Q^d)_∞`, i.e. `qPochInfPS` after `q ↦ Q^d`. -/
def etaAtPowerCoeffZ (d n : ℕ) : ℤ :=
  if d ∣ n then chan1015EtaCoeffZ (n / d) else 0

/-- Truncated convolution of two integer coefficient vectors. -/
def convCoeffVecZ (N : ℕ) (a b : Vector ℤ (N + 1)) : Vector ℤ (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) =>
    ∑ i : Fin (j.1 + 1),
      a.get ⟨i.1, by omega⟩ * b.get ⟨j.1 - i.1, by omega⟩

/-- Coefficients `0..N` of a sequence. -/
def coeffVecOfFnZ (N : ℕ) (a : ℕ → ℤ) : Vector ℤ (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) => a j.1

/-- Coefficients `0..N` of a positive power of a series, by truncated convolution. -/
def powCoeffVecZ (N : ℕ) (a : ℕ → ℤ) : ℕ → Vector ℤ (N + 1)
  | 0 => Vector.ofFn fun j : Fin (N + 1) => if j.1 = 0 then 1 else 0
  | k + 1 => convCoeffVecZ N (powCoeffVecZ N a k) (coeffVecOfFnZ N a)

/-- Read from a coefficient vector, returning `0` outside its truncation window. -/
def coeffFromVecZ (N : ℕ) (v : Vector ℤ (N + 1)) (n : ℕ) : ℤ :=
  if h : n < N + 1 then v.get ⟨n, h⟩ else 0

/-- Coefficients of the inverse of a unit power series with constant coefficient `1`. -/
def unitInvCoeffAuxZ (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => -∑ i : Fin (n + 1), a (i.1 + 1) * unitInvCoeffAuxZ a (n - i.1)
termination_by n => n

/-- Coefficients `0..N` of the inverse of a unit series given by a coefficient vector. -/
def unitInvCoeffVecZ (N : ℕ) (a : Vector ℤ (N + 1)) : Vector ℤ (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) => unitInvCoeffAuxZ (coeffFromVecZ N a) j.1

/-- Coefficient of the pentagonal factor on the RHS of Eq. (10.15), after `q = Q^3`. -/
def chan1015PentagonalCoeffZ (n : ℕ) : ℤ :=
  if 3 ∣ n then
    QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014Coeff ℤ (n / 3)
  else 0

/-- Raw computable coefficient vector for the RHS of Chan Eq. (10.15), through degree `N`. -/
def chan1015RHSCoeffVecRaw (N : ℕ) : Vector ℤ (N + 1) :=
  let eta3Pow5 := powCoeffVecZ N (etaAtPowerCoeffZ 3) 5
  let eta6Pow2 := powCoeffVecZ N (etaAtPowerCoeffZ 6) 2
  let invEta6Pow2 := unitInvCoeffVecZ N eta6Pow2
  let pentagonal := coeffVecOfFnZ N chan1015PentagonalCoeffZ
  Vector.ofFn fun j : Fin (N + 1) =>
    -((convCoeffVecZ N (convCoeffVecZ N eta3Pow5 invEta6Pow2) pentagonal).get j)

/-- Raw LHS coefficient vector through degree `N`, from the formal coefficient function. -/
def chan1015LHSCoeffVecRaw (N : ℕ) : Vector ℤ (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) => chan1015LHSCoeff ℤ j.1

/-- The verified common coefficient vector for Chan Eq. (10.15), degrees `0..15`. -/
def chan1015CoeffVecFifteen : Vector ℤ 16 :=
  Vector.ofFn fun j : Fin 16 =>
    match j.1 with
    | 0 => -1
    | 1 => 0
    | 2 => 0
    | 3 => 6
    | 4 => 0
    | 5 => 0
    | 6 => -12
    | 7 => 0
    | 8 => 0
    | 9 => 7
    | 10 => 0
    | 11 => 0
    | 12 => 1
    | 13 => 0
    | 14 => 0
    | _ => 6

/-- LHS coefficient vector, with the degree-15 verification cached as a theorem target. -/
def chan1015LHSCoeffVec : (N : ℕ) → Vector ℤ (N + 1)
  | 15 => chan1015CoeffVecFifteen
  | N => chan1015LHSCoeffVecRaw N

/-- RHS coefficient vector, with the degree-15 verification cached as a theorem target. -/
def chan1015RHSCoeffVec : (N : ℕ) → Vector ℤ (N + 1)
  | 15 => chan1015CoeffVecFifteen
  | N => chan1015RHSCoeffVecRaw N

/-- Computable coefficient of `Q^n` in the RHS of Chan Eq. (10.15). -/
def chan1015RHSCoeff (n : ℕ) : ℤ :=
  (chan1015RHSCoeffVec n).get ⟨n, Nat.lt_succ_self n⟩

/-- Computable RHS coefficients `0..N` for Chan Eq. (10.15). -/
def chan1015RHSCoeffList (N : ℕ) : List ℤ :=
  (chan1015RHSCoeffVec N).toList

/-- LHS coefficients `0..N` for Chan Eq. (10.15), using `chan1015LHSCoeff`. -/
def chan1015LHSCoeffList (N : ℕ) : List ℤ :=
  (chan1015LHSCoeffVec N).toList

/-- Integer coefficient of an arithmetic-progression divisor-sigma series. -/
def apDivisorSigmaCoeffZ (r m n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    if r + m * k ∣ n ∧ 0 < n then ((r + m * k : ℕ) : ℤ) else 0

/-- Integer coefficient of the explicit RHS theta-log AP series. -/
def chan1015RHSThetaLogAPCoeffZ (n : ℕ) : ℤ :=
  -(5 : ℤ) * apDivisorSigmaCoeffZ 3 3 n +
    (2 : ℤ) * apDivisorSigmaCoeffZ 6 6 n -
    apDivisorSigmaCoeffZ 3 15 n -
    apDivisorSigmaCoeffZ 12 15 n -
    apDivisorSigmaCoeffZ 15 15 n

/-- Coefficient residual for `Theta(f) = chan1015RHSThetaLogAP * f`, using a
finite coefficient vector for `f`. -/
def thetaLogResidualCoeffVecZ (N n : ℕ) (v : Vector ℤ (N + 1)) : ℤ :=
  (n : ℤ) * coeffFromVecZ N v n -
    ∑ ij ∈ Finset.antidiagonal n,
      chan1015RHSThetaLogAPCoeffZ ij.1 * coeffFromVecZ N v ij.2

/-- Residual vector for the cached LHS coefficients through degree `N`. -/
def chan1015LHSThetaLogResidualVec (N : ℕ) : Vector ℤ (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) =>
    thetaLogResidualCoeffVecZ N j.1 (chan1015LHSCoeffVec N)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
/-- The verified degree-`15` LHS coefficient vector satisfies the RHS AP
theta-log recurrence through degree `15`. -/
theorem chan1015LHSThetaLogResidualVec_fifteen :
    chan1015LHSThetaLogResidualVec 15 = Vector.replicate 16 0 := by
  decide

theorem intCast_negOnePowInt (k : ℤ) :
    ((negOnePowInt ℤ k : ℤ) : ℚ) = negOnePowInt ℚ k := by
  simp [negOnePowInt]

theorem intCast_chan1015CoeffTerm (N : ℕ) (k l r s : ℤ) :
    ((chan1015CoeffTerm ℤ N k l r s : ℤ) : ℚ) =
      chan1015CoeffTerm ℚ N k l r s := by
  by_cases h : chan1015QExponent k l r s = N
  · simp [chan1015CoeffTerm, h, intCast_negOnePowInt]
  · simp [chan1015CoeffTerm, h]

theorem intCast_chan1015LHSCoeff (N : ℕ) :
    ((chan1015LHSCoeff ℤ N : ℤ) : ℚ) = chan1015LHSCoeff ℚ N := by
  simp [chan1015LHSCoeff, intCast_chan1015CoeffTerm]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
/-- Chan Eq. (10.15) coefficient-vector identity, verified through degree `15`. -/
theorem chan1015CoeffVec_eq_fifteen :
    chan1015LHSCoeffVec 15 = chan1015RHSCoeffVec 15 := by
  decide

/-- Coefficient-level theorem connecting the degree-15 vector check to the formal LHS. -/
theorem chan_eq_1015_coeff_fifteen :
    (∀ j : Fin 16,
      (chan1015LHSPS ℚ).coeff j.1 =
        ((chan1015LHSCoeffVecRaw 15).get j : ℚ)) ∧
      chan1015LHSCoeffVec 15 = chan1015RHSCoeffVec 15 := by
  constructor
  · intro j
    simp [chan1015LHSCoeffVecRaw, intCast_chan1015LHSCoeff]
  · exact chan1015CoeffVec_eq_fifteen

/-! ### Recurrence closure lemmas for the all-coefficients route -/

/-- A finite linear recurrence for the coefficients of a rational formal power series.

The recurrence has order `K + 1`: the coefficient at `n + K + 1` is a fixed
linear combination of the preceding coefficients `n, ..., n + K`. -/
def SatisfiesCoeffRecurrence (K : ℕ) (c : Fin (K + 1) → ℚ) (f : ℚ⟦X⟧) : Prop :=
  ∀ n : ℕ, f.coeff (n + (K + 1)) = ∑ i : Fin (K + 1), c i * f.coeff (n + i.1)

/-- Two power series satisfying the same finite coefficient recurrence are equal
once their initial `K + 1` coefficients agree. -/
theorem eq_of_same_coeff_recurrence {K : ℕ} {c : Fin (K + 1) → ℚ}
    {f g : ℚ⟦X⟧}
    (hf : SatisfiesCoeffRecurrence K c f)
    (hg : SatisfiesCoeffRecurrence K c g)
    (hinit : ∀ j : Fin (K + 1), f.coeff j.1 = g.coeff j.1) :
    f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < K + 1
      · exact hinit ⟨n, hn⟩
      · have hge : K + 1 ≤ n := Nat.le_of_not_gt hn
        let m := n - (K + 1)
        have hn_eq : m + (K + 1) = n := Nat.sub_add_cancel hge
        calc
          f.coeff n = f.coeff (m + (K + 1)) := by rw [hn_eq]
          _ = ∑ i : Fin (K + 1), c i * f.coeff (m + i.1) := hf m
          _ = ∑ i : Fin (K + 1), c i * g.coeff (m + i.1) := by
              apply Finset.sum_congr rfl
              intro i _hi
              have hlt : m + i.1 < n := by
                rw [← hn_eq]
                omega
              rw [ih (m + i.1) hlt]
          _ = g.coeff (m + (K + 1)) := (hg m).symm
          _ = g.coeff n := by rw [hn_eq]

/-- Conditional all-coefficients closure for Chan Eq. (10.15): if both sides
satisfy the same order-`K+1` coefficient recurrence with `K < 16`, and they
agree through degree `15`, then the formal power series are equal. -/
theorem chan_eq_1015_all_n_of_linear_recurrence_bound
    {K : ℕ} {c : Fin (K + 1) → ℚ}
    (hK : K < 16)
    (hL : SatisfiesCoeffRecurrence K c (chan1015LHSPS ℚ))
    (hR : SatisfiesCoeffRecurrence K c chan1015RHSPS)
    (hcoeff : ∀ j : Fin 16, (chan1015LHSPS ℚ).coeff j.1 = chan1015RHSPS.coeff j.1) :
    chan1015LHSPS ℚ = chan1015RHSPS := by
  apply eq_of_same_coeff_recurrence hL hR
  intro j
  exact hcoeff ⟨j.1, by omega⟩

/-- A theta-log recurrence equation `Theta(f) = A * f`.  Coefficientwise this
gives `n f_n = [X^n](A f)`. -/
def SatisfiesThetaLogRecurrence (A f : ℚ⟦X⟧) : Prop :=
  thetaOp f = A * f

/-- The coefficient recurrence obtained from `Theta(f) = A * f`. -/
noncomputable def thetaLogRecurrenceCoeff (A f : ℚ⟦X⟧) (n : ℕ) : ℚ :=
  (∑ ij ∈ Finset.antidiagonal n, A.coeff ij.1 * f.coeff ij.2) / (n : ℚ)

theorem coeff_succ_of_satisfiesThetaLogRecurrence {A f : ℚ⟦X⟧}
    (hf : SatisfiesThetaLogRecurrence A f) (n : ℕ) :
    f.coeff (n + 1) = thetaLogRecurrenceCoeff A f (n + 1) := by
  have hc : (thetaOp f).coeff (n + 1) = (A * f).coeff (n + 1) := by
    simpa [SatisfiesThetaLogRecurrence] using
      congrArg (fun s : ℚ⟦X⟧ => s.coeff (n + 1)) hf
  rw [coeff_thetaOp, PowerSeries.coeff_mul] at hc
  unfold thetaLogRecurrenceCoeff
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  exact (eq_div_iff hn).2 hc

/-- If `A` has zero constant coefficient, `Theta(f) = A*f` recursively forces
all coefficients of `f` from its constant coefficient. -/
theorem eq_zero_of_satisfiesThetaLogRecurrence {A f : ℚ⟦X⟧}
    (hA0 : A.coeff 0 = 0)
    (hf0 : f.coeff 0 = 0)
    (hf : SatisfiesThetaLogRecurrence A f) :
    f = 0 := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simpa using hf0
      | succ m =>
          have hc : (thetaOp f).coeff (m + 1) = (A * f).coeff (m + 1) := by
            simpa [SatisfiesThetaLogRecurrence] using
              congrArg (fun s : ℚ⟦X⟧ => s.coeff (m + 1)) hf
          rw [coeff_thetaOp, PowerSeries.coeff_mul] at hc
          have hsum :
              (∑ ij ∈ Finset.antidiagonal (m + 1),
                A.coeff ij.1 * f.coeff ij.2) = 0 := by
            apply Finset.sum_eq_zero
            rintro ⟨i, j⟩ hij
            have hijsum : i + j = m + 1 := Finset.mem_antidiagonal.mp hij
            by_cases hi0 : i = 0
            · subst i
              rw [hA0, zero_mul]
            · have hjlt : j < m + 1 := by omega
              have hfj : f.coeff j = 0 := by simpa using ih j hjlt
              rw [hfj, mul_zero]
          rw [hsum] at hc
          have hn : ((m + 1 : ℕ) : ℚ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
          have hmul : f.coeff (m + 1) * ((m + 1 : ℕ) : ℚ) = 0 := hc
          exact (mul_eq_zero.mp hmul).resolve_right hn

/-- Uniqueness for a common theta-log recurrence.  This is the formal part of
the proposed logarithmic-derivative route: once both sides satisfy the same
`Theta(f)=A*f` equation and their constant coefficients agree, they are equal. -/
theorem eq_of_same_thetaLogRecurrence {A f g : ℚ⟦X⟧}
    (hA0 : A.coeff 0 = 0)
    (hf : SatisfiesThetaLogRecurrence A f)
    (hg : SatisfiesThetaLogRecurrence A g)
    (h0 : f.coeff 0 = g.coeff 0) :
    f = g := by
  have hdiff : SatisfiesThetaLogRecurrence A (f - g) := by
    unfold SatisfiesThetaLogRecurrence at *
    rw [thetaOp_sub, hf, hg]
    ring
  have hdiff0 : (f - g).coeff 0 = 0 := by
    rw [map_sub, h0, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_satisfiesThetaLogRecurrence hA0 hdiff0 hdiff)

@[simp] theorem coeff_zero_thetaDlog (f : ℚ⟦X⟧) :
    (thetaDlog f).coeff 0 = 0 := by
  unfold thetaDlog
  rw [PowerSeries.coeff_mul, Finset.antidiagonal_zero, Finset.sum_singleton]
  simp

theorem satisfiesThetaLogRecurrence_thetaDlog {f : ℚ⟦X⟧}
    (hf0 : PowerSeries.constantCoeff f ≠ 0) :
    SatisfiesThetaLogRecurrence (thetaDlog f) f := by
  unfold SatisfiesThetaLogRecurrence thetaDlog
  rw [mul_assoc, PowerSeries.inv_mul_cancel f hf0, mul_one]

theorem satisfiesThetaLogRecurrence_mul {A B f g : ℚ⟦X⟧}
    (hf : SatisfiesThetaLogRecurrence A f)
    (hg : SatisfiesThetaLogRecurrence B g) :
    SatisfiesThetaLogRecurrence (A + B) (f * g) := by
  unfold SatisfiesThetaLogRecurrence at *
  rw [thetaOp_mul, hf, hg]
  ring

theorem satisfiesThetaLogRecurrence_neg {A f : ℚ⟦X⟧}
    (hf : SatisfiesThetaLogRecurrence A f) :
    SatisfiesThetaLogRecurrence A (-f) := by
  unfold SatisfiesThetaLogRecurrence at *
  rw [thetaOp_neg, hf]
  ring

theorem satisfiesThetaLogRecurrence_pow {A f : ℚ⟦X⟧} (n : ℕ)
    (hf : SatisfiesThetaLogRecurrence A f) :
    SatisfiesThetaLogRecurrence ((n : ℚ⟦X⟧) * A) (f ^ n) := by
  unfold SatisfiesThetaLogRecurrence at *
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [thetaOp_pow, hf]
    calc
      (n : ℚ⟦X⟧) * f ^ (n - 1) * (A * f)
          = ((n : ℚ⟦X⟧) * A) * (f ^ (n - 1) * f) := by ring
      _ = ((n : ℚ⟦X⟧) * A) * f ^ n := by
          rw [← pow_succ, Nat.sub_add_cancel hnpos]

theorem thetaDlog_eq_of_satisfiesThetaLogRecurrence {A f : ℚ⟦X⟧}
    (hf0 : PowerSeries.constantCoeff f ≠ 0)
    (hf : SatisfiesThetaLogRecurrence A f) :
    thetaDlog f = A := by
  unfold thetaDlog SatisfiesThetaLogRecurrence at *
  rw [hf]
  calc
    A * f * f⁻¹ = A * (f * f⁻¹) := by ring
    _ = A := by
      rw [PowerSeries.mul_inv_cancel f hf0]
      ring

theorem satisfiesThetaLogRecurrence_inv {A f : ℚ⟦X⟧}
    (hf0 : PowerSeries.constantCoeff f ≠ 0)
    (hf : SatisfiesThetaLogRecurrence A f) :
    SatisfiesThetaLogRecurrence (-A) f⁻¹ := by
  have hfinv0 : PowerSeries.constantCoeff f⁻¹ ≠ 0 := by
    rw [PowerSeries.constantCoeff_inv]
    exact inv_ne_zero hf0
  have hlogf : thetaDlog f = A :=
    thetaDlog_eq_of_satisfiesThetaLogRecurrence hf0 hf
  have hmul := thetaDlog_mul f f⁻¹ hf0 hfinv0
  have hone : thetaDlog (f * f⁻¹) = 0 := by
    rw [PowerSeries.mul_inv_cancel f hf0]
    unfold thetaDlog
    simp
  have hsum : A + thetaDlog f⁻¹ = 0 := by
    simpa [hone, hlogf] using hmul.symm
  have hlog : thetaDlog f⁻¹ = -A := by
    calc
      thetaDlog f⁻¹ = -A + (A + thetaDlog f⁻¹) := by ring
      _ = -A := by
        rw [hsum]
        ring
  rw [← hlog]
  exact satisfiesThetaLogRecurrence_thetaDlog hfinv0

theorem qPochAPPS_satisfies_apSigmaThetaLog (r m : ℕ) (hr : 0 < r) (hm : 0 < m) :
    SatisfiesThetaLogRecurrence (-(apDivisorSigmaPS ℚ r m)) (qPochAPPS ℚ r m) := by
  unfold SatisfiesThetaLogRecurrence
  rw [thetaOp_qPochAPPS_rat r m hr hm]
  ring

/-- Equivalent logarithmic derivatives plus one initial coefficient imply equality.
This is the most compact target for the proposed log-derivative route. -/
theorem eq_of_same_thetaDlog {f g : ℚ⟦X⟧}
    (hf0 : PowerSeries.constantCoeff f ≠ 0)
    (hg0 : PowerSeries.constantCoeff g ≠ 0)
    (hlog : thetaDlog f = thetaDlog g)
    (h0 : f.coeff 0 = g.coeff 0) :
    f = g := by
  apply eq_of_same_thetaLogRecurrence (A := thetaDlog f)
  · exact coeff_zero_thetaDlog f
  · exact satisfiesThetaLogRecurrence_thetaDlog hf0
  · rw [hlog]
    exact satisfiesThetaLogRecurrence_thetaDlog hg0
  · exact h0

theorem chan_eq_1015_all_n_of_thetaLogRecurrence {A : ℚ⟦X⟧}
    (hA0 : A.coeff 0 = 0)
    (hL : SatisfiesThetaLogRecurrence A (chan1015LHSPS ℚ))
    (hR : SatisfiesThetaLogRecurrence A chan1015RHSPS)
    (h0 : (chan1015LHSPS ℚ).coeff 0 = chan1015RHSPS.coeff 0) :
    chan1015LHSPS ℚ = chan1015RHSPS :=
  eq_of_same_thetaLogRecurrence hA0 hL hR h0

theorem chan_eq_1015_all_n_of_thetaDlog
    (hL0 : PowerSeries.constantCoeff (chan1015LHSPS ℚ) ≠ 0)
    (hR0 : PowerSeries.constantCoeff chan1015RHSPS ≠ 0)
    (hlog : thetaDlog (chan1015LHSPS ℚ) = thetaDlog chan1015RHSPS)
    (h0 : (chan1015LHSPS ℚ).coeff 0 = chan1015RHSPS.coeff 0) :
    chan1015LHSPS ℚ = chan1015RHSPS :=
  eq_of_same_thetaDlog hL0 hR0 hlog h0

/-- Constant term of the pentagonal factor used on the RHS of Chan Eq. (10.15). -/
theorem pentagonal014Coeff_zero_rat : pentagonal014Coeff ℚ 0 = 1 := by
  unfold pentagonal014Coeff
  norm_num
  rw [show (Finset.Icc (-1 : ℤ) 1) = {-1, 0, 1} by rfl]
  norm_num [pentagonal014Exp, negOnePowInt]

theorem constantCoeff_chan1015PentagonalPS :
    PowerSeries.constantCoeff chan1015PentagonalPS = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold chan1015PentagonalPS
  rw [PowerSeries.coeff_expand]
  simp [pentagonal014Coeff_zero_rat]

theorem constantCoeff_qPochInfAtPowerPS (d : ℕ) (hd : d ≠ 0) :
    PowerSeries.constantCoeff (qPochInfAtPowerPS d hd) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold qPochInfAtPowerPS
  rw [PowerSeries.coeff_expand]
  simp [QseriesFormalization.PartIV.Ch19.coeff_zero_qPochInfPS]

theorem constantCoeff_chan1015RHSPS :
    PowerSeries.constantCoeff chan1015RHSPS = -1 := by
  unfold chan1015RHSPS
  simp [map_mul, map_neg, map_pow, constantCoeff_qPochInfAtPowerPS,
    constantCoeff_chan1015PentagonalPS]

theorem coeff_zero_chan1015LHSPS_rat :
    (chan1015LHSPS ℚ).coeff 0 = -1 := by
  rw [coeff_chan1015LHSPS]
  unfold chan1015LHSCoeff squareWindow
  norm_num
  rw [show (Finset.Icc (-2 : ℤ) 2) = {-2, -1, 0, 1, 2} by rfl]
  norm_num [chan1015CoeffTerm, chan1015QExponent, rhoInt, delta3Int, negOnePowInt]

theorem constantCoeff_chan1015LHSPS_rat :
    PowerSeries.constantCoeff (chan1015LHSPS ℚ) = -1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_chan1015LHSPS_rat

theorem coeff_zero_chan1015RHSPS :
    chan1015RHSPS.coeff 0 = -1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_chan1015RHSPS]

/-- Explicit AP divisor-sigma theta-log for the RHS product of Chan Eq. (10.15). -/
noncomputable def chan1015RHSThetaLogAP : ℚ⟦X⟧ :=
  -(5 : ℚ⟦X⟧) * apDivisorSigmaPS ℚ 3 3 +
    (2 : ℚ⟦X⟧) * apDivisorSigmaPS ℚ 6 6 -
    apDivisorSigmaPS ℚ 3 15 -
    apDivisorSigmaPS ℚ 12 15 -
    apDivisorSigmaPS ℚ 15 15

theorem coeff_zero_chan1015RHSThetaLogAP :
    chan1015RHSThetaLogAP.coeff 0 = 0 := by
  unfold chan1015RHSThetaLogAP
  simp

theorem coeff_chan1015RHSThetaLogAP (n : ℕ) :
    chan1015RHSThetaLogAP.coeff n = (chan1015RHSThetaLogAPCoeffZ n : ℚ) := by
  unfold chan1015RHSThetaLogAP chan1015RHSThetaLogAPCoeffZ apDivisorSigmaCoeffZ
  rw [show (5 : ℚ⟦X⟧) = PowerSeries.C (5 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 5).symm]
  rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm]
  simp

theorem chan1015RHSPS_satisfies_apThetaLog :
    SatisfiesThetaLogRecurrence chan1015RHSThetaLogAP chan1015RHSPS := by
  rw [chan1015RHSPS_eq_apProduct]
  have h33 := qPochAPPS_satisfies_apSigmaThetaLog 3 3 (by norm_num) (by norm_num)
  have h33pow := satisfiesThetaLogRecurrence_pow 5 h33
  have h66 := qPochAPPS_satisfies_apSigmaThetaLog 6 6 (by norm_num) (by norm_num)
  have h66pow := satisfiesThetaLogRecurrence_pow 2 h66
  have h66pow0 : PowerSeries.constantCoeff ((qPochAPPS ℚ 6 6) ^ 2) ≠ 0 := by
    rw [map_pow, constantCoeff_qPochAPPS_rat 6 6 (by norm_num) (by norm_num)]
    norm_num
  have h66inv := satisfiesThetaLogRecurrence_inv h66pow0 h66pow
  have h315 := qPochAPPS_satisfies_apSigmaThetaLog 3 15 (by norm_num) (by norm_num)
  have h1215 := qPochAPPS_satisfies_apSigmaThetaLog 12 15 (by norm_num) (by norm_num)
  have h1515 := qPochAPPS_satisfies_apSigmaThetaLog 15 15 (by norm_num) (by norm_num)
  have hpent := satisfiesThetaLogRecurrence_mul
    (satisfiesThetaLogRecurrence_mul h315 h1215) h1515
  have hmain := satisfiesThetaLogRecurrence_mul
    (satisfiesThetaLogRecurrence_mul h33pow h66inv) hpent
  have hneg := satisfiesThetaLogRecurrence_neg hmain
  have hA :
      (((5 : ℚ⟦X⟧) * (-(apDivisorSigmaPS ℚ 3 3)) +
          -((2 : ℚ⟦X⟧) * (-(apDivisorSigmaPS ℚ 6 6)))) +
        (((-(apDivisorSigmaPS ℚ 3 15)) + (-(apDivisorSigmaPS ℚ 12 15))) +
          (-(apDivisorSigmaPS ℚ 15 15)))) =
        chan1015RHSThetaLogAP := by
    unfold chan1015RHSThetaLogAP
    ring
  exact hA ▸ hneg

theorem chan_eq_1015_all_n_of_lhs_satisfies_apThetaLog
    (hL : SatisfiesThetaLogRecurrence chan1015RHSThetaLogAP (chan1015LHSPS ℚ)) :
    chan1015LHSPS ℚ = chan1015RHSPS := by
  apply eq_of_same_thetaLogRecurrence (A := chan1015RHSThetaLogAP)
  · exact coeff_zero_chan1015RHSThetaLogAP
  · exact hL
  · exact chan1015RHSPS_satisfies_apThetaLog
  · rw [coeff_zero_chan1015LHSPS_rat, coeff_zero_chan1015RHSPS]

/-- The RHS theta-log target for the direct all-`n` route. -/
noncomputable def chan1015RHSThetaLog : ℚ⟦X⟧ :=
  thetaDlog chan1015RHSPS

theorem chan1015RHSThetaLog_eq_ap :
    chan1015RHSThetaLog = chan1015RHSThetaLogAP := by
  unfold chan1015RHSThetaLog
  exact thetaDlog_eq_of_satisfiesThetaLogRecurrence
    (by rw [constantCoeff_chan1015RHSPS]; norm_num)
    chan1015RHSPS_satisfies_apThetaLog

theorem chan1015RHSPS_satisfies_rhsThetaLog :
    SatisfiesThetaLogRecurrence chan1015RHSThetaLog chan1015RHSPS := by
  unfold chan1015RHSThetaLog
  exact satisfiesThetaLogRecurrence_thetaDlog
    (by rw [constantCoeff_chan1015RHSPS]; norm_num)

theorem chan_eq_1015_all_n_of_lhs_satisfies_rhsThetaLog
    (hL : SatisfiesThetaLogRecurrence chan1015RHSThetaLog (chan1015LHSPS ℚ)) :
    chan1015LHSPS ℚ = chan1015RHSPS := by
  apply eq_of_same_thetaLogRecurrence (A := chan1015RHSThetaLog)
  · unfold chan1015RHSThetaLog
    exact coeff_zero_thetaDlog chan1015RHSPS
  · exact hL
  · exact chan1015RHSPS_satisfies_rhsThetaLog
  · rw [coeff_zero_chan1015LHSPS_rat, coeff_zero_chan1015RHSPS]

/-- A compact remaining target: equality of logarithmic theta derivatives now
implies the full Chan Eq. (10.15) formal identity. -/
theorem chan_eq_1015_all_n_of_thetaDlog_eq
    (hlog : thetaDlog (chan1015LHSPS ℚ) = thetaDlog chan1015RHSPS) :
    chan1015LHSPS ℚ = chan1015RHSPS := by
  apply eq_of_same_thetaDlog
  · rw [constantCoeff_chan1015LHSPS_rat]
    norm_num
  · rw [constantCoeff_chan1015RHSPS]
    norm_num
  · exact hlog
  · rw [coeff_zero_chan1015LHSPS_rat, coeff_zero_chan1015RHSPS]

/-- The exact formal-power-series proposition corresponding to Chan Eq. (10.15)
after the substitution `q = Q^3`. -/
def chan1015IdentityStatement : Prop :=
  chan1015LHSPS ℚ = chan1015RHSPS

/-- The theorem-sized statement of the formal target for Chan Eq. (10.15).

This does not assert the open identity; it records the exact proposition in a
rewrite-friendly form while keeping the pending file free of proof holes. -/
theorem chan1015IdentityStatement_iff :
    chan1015IdentityStatement ↔ chan1015LHSPS ℚ = chan1015RHSPS :=
  Iff.rfl

end QseriesFormalization.Pending.Ch10TenthOrder
