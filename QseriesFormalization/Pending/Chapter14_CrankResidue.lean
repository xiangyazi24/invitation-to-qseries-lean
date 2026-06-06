import QseriesFormalization.Chapter14_CrankGenFun

/-!
# Pending Chapter 14 — Crank residue fibers

This file starts a residue-class layer for the Dyson-Garvan crank theorem.
For a modulus `M`, it groups partitions of `n` by the residue of their crank in
`ZMod M`.  The main theorem here is the finite bookkeeping identity that the
residue fibers add back up to the ordinary partition count.
-/

open scoped BigOperators
open scoped PowerSeries

namespace QseriesFormalization
namespace Pending
namespace Ch14Residue

open QseriesFormalization.PartIII.Ch14

noncomputable section

/-- The residue of the Andrews-Garvan crank modulo `M`. -/
def crankResidue (M : Nat) {n : Nat} (lam : Nat.Partition n) : ZMod M :=
  ((crank lam : Int) : ZMod M)

/-- `M_M(r,n)`: number of partitions of `n` whose crank is congruent to `r`
modulo `M`. -/
def crankResidueCount (M n : Nat) (r : ZMod M) : Nat :=
  Fintype.card {lam : Nat.Partition n // crankResidue M lam = r}

/-- The finite set of crank residues that actually occur among partitions of
`n`.  Summing over this support avoids any global finiteness requirement on
`ZMod M`. -/
def crankResidueSupport (M n : Nat) : Finset (ZMod M) :=
  (Finset.univ : Finset (Nat.Partition n)).image (fun lam => crankResidue M lam)

/-- Every partition contributes a residue in the finite support. -/
theorem crankResidue_mem_support (M : Nat) {n : Nat} (lam : Nat.Partition n) :
    crankResidue M lam ∈ crankResidueSupport M n := by
  classical
  exact Finset.mem_image.mpr ⟨lam, Finset.mem_univ lam, rfl⟩

/-- Summing crank-residue fibers recovers the number of partitions of `n`. -/
theorem sum_crankResidueCount_eq_partition_card (M n : Nat) :
    ∑ r ∈ crankResidueSupport M n, crankResidueCount M n r =
      Fintype.card (Nat.Partition n) := by
  classical
  unfold crankResidueSupport crankResidueCount
  rw [Fintype.card,
    Finset.card_eq_sum_card_image (fun lam : Nat.Partition n => crankResidue M lam)
      Finset.univ]
  congr 1
  ext r
  rw [Fintype.card_subtype]

/-- The same identity stated with this repository's `partitionCount`. -/
theorem sum_crankResidueCount_eq_partitionCount (M n : Nat) :
    ∑ r ∈ crankResidueSupport M n, crankResidueCount M n r =
      QseriesFormalization.Ch01.partitionCount n := by
  rw [sum_crankResidueCount_eq_partition_card]
  rfl

/-- A residue-weighted crank q-series:
`sum_n (sum_{lambda partition of n} w(crank(lambda) mod M)) X^n`. -/
def crankResidueSeriesEval (R : Type*) [Field R] (M : Nat) (w : ZMod M → R) : R⟦X⟧ :=
  PowerSeries.mk fun n => ∑ lam : Nat.Partition n, w (crankResidue M lam)

theorem coeff_crankResidueSeriesEval
    (R : Type*) [Field R] (M : Nat) (w : ZMod M → R) (n : Nat) :
    (crankResidueSeriesEval R M w).coeff n =
      ∑ lam : Nat.Partition n, w (crankResidue M lam) := by
  rw [crankResidueSeriesEval, PowerSeries.coeff_mk]

/-- Coefficient form after grouping by crank residue classes. -/
theorem coeff_crankResidueSeriesEval_eq_residue_sum
    (R : Type*) [Field R] (M : Nat) (w : ZMod M → R) (n : Nat) :
    (crankResidueSeriesEval R M w).coeff n =
      ∑ r ∈ crankResidueSupport M n, (crankResidueCount M n r : R) * w r := by
  classical
  rw [coeff_crankResidueSeriesEval]
  have hmaps :
      ∀ lam ∈ (Finset.univ : Finset (Nat.Partition n)),
        crankResidue M lam ∈ crankResidueSupport M n := by
    intro lam _h
    exact crankResidue_mem_support M lam
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Nat.Partition n)))
    (t := crankResidueSupport M n) (g := fun lam => crankResidue M lam) hmaps
    (fun lam => w (crankResidue M lam))]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  trans ∑ lam ∈
      (Finset.univ : Finset (Nat.Partition n)).filter (fun lam => crankResidue M lam = r),
      w r
  · apply Finset.sum_congr rfl
    intro lam hlam
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam
    rw [hlam]
  · simp [crankResidueCount, Fintype.card_subtype, Finset.sum_const]

/-- A coefficient of the residue-weighted crank series only depends on the
weights at residues that occur among partitions of that degree. -/
theorem coeff_crankResidueSeriesEval_eq_of_eq_on_support
    (R : Type*) [Field R] (M : Nat) (w v : ZMod M → R) (n : Nat)
    (h : ∀ r ∈ crankResidueSupport M n, w r = v r) :
    (crankResidueSeriesEval R M w).coeff n =
      (crankResidueSeriesEval R M v).coeff n := by
  rw [coeff_crankResidueSeriesEval_eq_residue_sum,
    coeff_crankResidueSeriesEval_eq_residue_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [h r hr]

/-- If the residue weight vanishes on the support for degree `n`, then the
degree-`n` coefficient is zero. -/
theorem coeff_crankResidueSeriesEval_eq_zero_of_weight_eq_zero_on_support
    (R : Type*) [Field R] (M : Nat) (w : ZMod M → R) (n : Nat)
    (h : ∀ r ∈ crankResidueSupport M n, w r = 0) :
    (crankResidueSeriesEval R M w).coeff n = 0 := by
  rw [coeff_crankResidueSeriesEval_eq_residue_sum]
  apply Finset.sum_eq_zero
  intro r hr
  rw [h r hr]
  simp

/-- If two weights agree on every residue that appears in every degree, then
their residue-weighted crank series are equal. -/
theorem crankResidueSeriesEval_eq_of_eq_on_all_supports
    (R : Type*) [Field R] (M : Nat) (w v : ZMod M → R)
    (h : ∀ n r, r ∈ crankResidueSupport M n → w r = v r) :
    crankResidueSeriesEval R M w = crankResidueSeriesEval R M v := by
  ext n
  exact coeff_crankResidueSeriesEval_eq_of_eq_on_support R M w v n
    (fun r hr => h n r hr)

/-- If a weight vanishes on every residue that appears in every degree, then
the corresponding residue-weighted crank series is zero. -/
theorem crankResidueSeriesEval_eq_zero_of_weight_eq_zero_on_all_supports
    (R : Type*) [Field R] (M : Nat) (w : ZMod M → R)
    (h : ∀ n r, r ∈ crankResidueSupport M n → w r = 0) :
    crankResidueSeriesEval R M w = 0 := by
  ext n
  exact coeff_crankResidueSeriesEval_eq_zero_of_weight_eq_zero_on_support
    R M w n (fun r hr => h n r hr)

/-- If every residue has weight `1`, the coefficient is just the partition
count. -/
theorem coeff_crankResidueSeriesEval_one
    (R : Type*) [Field R] (M n : Nat) :
    (crankResidueSeriesEval R M (fun _ => 1)).coeff n =
      (QseriesFormalization.Ch01.partitionCount n : R) := by
  rw [coeff_crankResidueSeriesEval]
  change (∑ _lam : Nat.Partition n, (1 : R)) =
    (Fintype.card (Nat.Partition n) : R)
  simp

/-- The all-residue-weight-one specialization is the ordinary partition
generating function. -/
theorem crankResidueSeriesEval_one_eq_partitionGenFun
    (R : Type*) [Field R] (M : Nat) :
    crankResidueSeriesEval R M (fun _ => 1) =
      QseriesFormalization.PartIV.Ch19.partitionGenFun R := by
  ext n
  rw [coeff_crankResidueSeriesEval_one,
    QseriesFormalization.PartIV.Ch19.coeff_partitionGenFun]
  rfl

/-! ## Single residue fibers -/

/-- The q-series counting only partitions whose crank is congruent to `r`
modulo `M`. -/
def crankResidueFiberSeries (R : Type*) [Field R] (M : Nat) (r : ZMod M) : R⟦X⟧ :=
  crankResidueSeriesEval R M (fun s => if s = r then 1 else 0)

/-- The coefficient of the single-residue fiber series is `crankResidueCount`. -/
theorem coeff_crankResidueFiberSeries
    (R : Type*) [Field R] (M : Nat) (r : ZMod M) (n : Nat) :
    (crankResidueFiberSeries R M r).coeff n = (crankResidueCount M n r : R) := by
  classical
  unfold crankResidueFiberSeries
  rw [coeff_crankResidueSeriesEval]
  unfold crankResidueCount
  rw [Fintype.card_subtype]
  change
    (∑ lam : Nat.Partition n,
        (if crankResidue M lam = r then (1 : R) else 0)) =
      (((Finset.univ : Finset (Nat.Partition n)).filter
        (fun lam => crankResidue M lam = r)).card : R)
  rw [← Finset.sum_boole]

/-- Coefficient decomposition through the actual support, expressed using the
single-residue fiber coefficients. -/
theorem coeff_crankResidueSeriesEval_eq_support_weighted_fiber_coeff
    (R : Type*) [Field R] (M : Nat) (w : ZMod M → R) (n : Nat) :
    (crankResidueSeriesEval R M w).coeff n =
      ∑ r ∈ crankResidueSupport M n,
        w r * (crankResidueFiberSeries R M r).coeff n := by
  rw [coeff_crankResidueSeriesEval_eq_residue_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [coeff_crankResidueFiberSeries]
  ring

/-- Degree-wise fiber decomposition over the actual support. -/
theorem sum_support_coeff_crankResidueFiberSeries_eq_partitionCount
    (R : Type*) [Field R] (M n : Nat) :
    ∑ r ∈ crankResidueSupport M n,
        (crankResidueFiberSeries R M r).coeff n =
      (QseriesFormalization.Ch01.partitionCount n : R) := by
  calc
    ∑ r ∈ crankResidueSupport M n,
        (crankResidueFiberSeries R M r).coeff n =
        ∑ r ∈ crankResidueSupport M n, (crankResidueCount M n r : R) := by
          apply Finset.sum_congr rfl
          intro r _hr
          rw [coeff_crankResidueFiberSeries]
    _ = (QseriesFormalization.Ch01.partitionCount n : R) := by
          have hnat :
              ∑ r ∈ crankResidueSupport M n, crankResidueCount M n r =
                QseriesFormalization.Ch01.partitionCount n :=
            sum_crankResidueCount_eq_partitionCount M n
          rw [← Nat.cast_sum]
          rw [hnat]

/-- If a residue does not occur among partitions of `n`, its fiber count is zero. -/
theorem crankResidueCount_eq_zero_of_not_mem_support
    {M n : Nat} {r : ZMod M} (hnot : r ∉ crankResidueSupport M n) :
    crankResidueCount M n r = 0 := by
  classical
  unfold crankResidueCount
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_zero]
  ext lam
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact False.elim (hnot (by simpa [h] using crankResidue_mem_support M lam))
  · intro h
    cases h

/-- If a residue does not occur among partitions of `n`, the corresponding
fiber-series coefficient is zero. -/
theorem coeff_crankResidueFiberSeries_eq_zero_of_not_mem_support
    (R : Type*) [Field R] {M n : Nat} {r : ZMod M}
    (hnot : r ∉ crankResidueSupport M n) :
    (crankResidueFiberSeries R M r).coeff n = 0 := by
  rw [coeff_crankResidueFiberSeries,
    crankResidueCount_eq_zero_of_not_mem_support hnot]
  norm_num

/-! ## Elementary support and count facts -/

/-- The residue count is the cardinality of the corresponding filter on
partitions. -/
theorem crankResidueCount_eq_card_filter (M n : Nat) (r : ZMod M) :
    crankResidueCount M n r =
      ((Finset.univ : Finset (Nat.Partition n)).filter
        (fun lam => crankResidue M lam = r)).card := by
  classical
  unfold crankResidueCount
  rw [Fintype.card_subtype]

/-- A residue occurs in the support iff its fiber count is positive. -/
theorem crankResidueCount_pos_iff_mem_support
    {M n : Nat} {r : ZMod M} :
    0 < crankResidueCount M n r ↔ r ∈ crankResidueSupport M n := by
  classical
  rw [crankResidueCount_eq_card_filter, Finset.card_pos]
  constructor
  · rintro ⟨lam, hlam⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam
    simpa [hlam] using crankResidue_mem_support M lam
  · intro hr
    simp only [crankResidueSupport, Finset.mem_image, Finset.mem_univ, true_and] at hr
    rcases hr with ⟨lam, hlam⟩
    exact ⟨lam, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlam⟩

/-- If a residue occurs in the support, its fiber count is positive. -/
theorem crankResidueCount_pos_of_mem_support
    {M n : Nat} {r : ZMod M} (hr : r ∈ crankResidueSupport M n) :
    0 < crankResidueCount M n r :=
  (crankResidueCount_pos_iff_mem_support).2 hr

/-- Vanishing of a residue count is equivalent to absence from the finite
support. -/
theorem crankResidueCount_eq_zero_iff_not_mem_support
    {M n : Nat} {r : ZMod M} :
    crankResidueCount M n r = 0 ↔ r ∉ crankResidueSupport M n := by
  rw [← crankResidueCount_pos_iff_mem_support]
  omega

/-- A residue has nonzero fiber count iff it occurs in the support. -/
theorem crankResidueCount_ne_zero_iff_mem_support
    {M n : Nat} {r : ZMod M} :
    crankResidueCount M n r ≠ 0 ↔ r ∈ crankResidueSupport M n := by
  constructor
  · intro h
    exact (crankResidueCount_pos_iff_mem_support).1 (Nat.pos_of_ne_zero h)
  · intro hr
    exact Nat.ne_of_gt ((crankResidueCount_pos_iff_mem_support).2 hr)

/-- Nonzero count gives membership in the finite support. -/
theorem crankResidue_mem_support_of_count_ne_zero
    {M n : Nat} {r : ZMod M} (h : crankResidueCount M n r ≠ 0) :
    r ∈ crankResidueSupport M n :=
  crankResidueCount_ne_zero_iff_mem_support.1 h

/-- Zero count gives absence from the finite support. -/
theorem crankResidue_not_mem_support_of_count_eq_zero
    {M n : Nat} {r : ZMod M} (h : crankResidueCount M n r = 0) :
    r ∉ crankResidueSupport M n :=
  crankResidueCount_eq_zero_iff_not_mem_support.1 h

/-- Over `ℚ`, a single-residue fiber coefficient is nonzero exactly when that
residue occurs in the support. -/
theorem coeff_crankResidueFiberSeries_rat_ne_zero_iff_mem_support
    {M n : Nat} {r : ZMod M} :
    (crankResidueFiberSeries ℚ M r).coeff n ≠ 0 ↔
      r ∈ crankResidueSupport M n := by
  rw [coeff_crankResidueFiberSeries, ← crankResidueCount_ne_zero_iff_mem_support]
  norm_num

/-- Over `ℚ`, vanishing of a single-residue fiber coefficient is equivalent to
absence from the support. -/
theorem coeff_crankResidueFiberSeries_rat_eq_zero_iff_not_mem_support
    {M n : Nat} {r : ZMod M} :
    (crankResidueFiberSeries ℚ M r).coeff n = 0 ↔
      r ∉ crankResidueSupport M n := by
  constructor
  · intro h
    rw [coeff_crankResidueFiberSeries] at h
    have hnat : crankResidueCount M n r = 0 := by
      exact_mod_cast h
    exact crankResidueCount_eq_zero_iff_not_mem_support.1 hnat
  · intro hnot
    rw [coeff_crankResidueFiberSeries,
      crankResidueCount_eq_zero_of_not_mem_support hnot]
    norm_num

/-- Every single residue count is bounded by the total partition count. -/
theorem crankResidueCount_le_partition_card (M n : Nat) (r : ZMod M) :
    crankResidueCount M n r ≤ Fintype.card (Nat.Partition n) := by
  classical
  rw [crankResidueCount_eq_card_filter]
  exact Finset.card_filter_le _ _

/-- Every single residue count is bounded by this repository's
`partitionCount`. -/
theorem crankResidueCount_le_partitionCount (M n : Nat) (r : ZMod M) :
    crankResidueCount M n r ≤ QseriesFormalization.Ch01.partitionCount n := by
  rw [QseriesFormalization.Ch01.partitionCount]
  exact crankResidueCount_le_partition_card M n r

/-- The number of occurring residues is bounded by the number of partitions. -/
theorem card_crankResidueSupport_le_partition_card (M n : Nat) :
    (crankResidueSupport M n).card ≤ Fintype.card (Nat.Partition n) := by
  classical
  unfold crankResidueSupport
  change
    ((Finset.univ : Finset (Nat.Partition n)).image
        (fun lam => crankResidue M lam)).card ≤
      (Finset.univ : Finset (Nat.Partition n)).card
  exact Finset.card_image_le

/-- The number of occurring residues is bounded by `partitionCount n`. -/
theorem card_crankResidueSupport_le_partitionCount (M n : Nat) :
    (crankResidueSupport M n).card ≤ QseriesFormalization.Ch01.partitionCount n := by
  rw [QseriesFormalization.Ch01.partitionCount]
  exact card_crankResidueSupport_le_partition_card M n

/-- The number of occurring residues is bounded by the size of the residue
ring. -/
theorem card_crankResidueSupport_le_residue_card
    (M n : Nat) [Fintype (ZMod M)] :
    (crankResidueSupport M n).card ≤ Fintype.card (ZMod M) := by
  classical
  simpa using Finset.card_le_univ (s := crankResidueSupport M n)

/-- At modulus `5`, at most five crank residues occur in any degree. -/
theorem card_crankResidueSupport_mod_five_le_five (n : Nat) :
    (crankResidueSupport 5 n).card ≤ 5 := by
  simpa using card_crankResidueSupport_le_residue_card 5 n

/-- The residue support is nonempty exactly when there is at least one
partition of `n`. -/
theorem crankResidueSupport_nonempty_iff_partition_card_pos (M n : Nat) :
    (crankResidueSupport M n).Nonempty ↔
      0 < Fintype.card (Nat.Partition n) := by
  classical
  constructor
  · rintro ⟨r, hr⟩
    simp only [crankResidueSupport, Finset.mem_image, Finset.mem_univ, true_and] at hr
    rcases hr with ⟨lam, _hlam⟩
    rw [Fintype.card, Finset.card_pos]
    exact ⟨lam, Finset.mem_univ lam⟩
  · intro h
    rw [Fintype.card, Finset.card_pos] at h
    rcases h with ⟨lam, _hlam⟩
    exact ⟨crankResidue M lam, crankResidue_mem_support M lam⟩

/-- The residue support is empty exactly when there is no partition of `n`. -/
theorem crankResidueSupport_eq_empty_iff_partition_card_eq_zero (M n : Nat) :
    crankResidueSupport M n = ∅ ↔
      Fintype.card (Nat.Partition n) = 0 := by
  classical
  constructor
  · intro h
    apply Nat.eq_zero_of_not_pos
    intro hpos
    rcases (crankResidueSupport_nonempty_iff_partition_card_pos M n).2 hpos with
      ⟨r, hr⟩
    simp [h] at hr
  · intro hcard
    ext r
    constructor
    · intro hr
      have hpos := (crankResidueSupport_nonempty_iff_partition_card_pos M n).1
        ⟨r, hr⟩
      omega
    · intro hr
      simp at hr

/-- Cardinal-zero form of `crankResidueSupport_eq_empty_iff_partition_card_eq_zero`. -/
theorem card_crankResidueSupport_eq_zero_iff_partition_card_eq_zero (M n : Nat) :
    (crankResidueSupport M n).card = 0 ↔
      Fintype.card (Nat.Partition n) = 0 := by
  rw [Finset.card_eq_zero, crankResidueSupport_eq_empty_iff_partition_card_eq_zero]

/-- The support is empty iff every residue fiber has count zero. -/
theorem crankResidueSupport_eq_empty_iff_forall_count_eq_zero (M n : Nat) :
    crankResidueSupport M n = ∅ ↔
      ∀ r : ZMod M, crankResidueCount M n r = 0 := by
  classical
  constructor
  · intro hs r
    apply crankResidueCount_eq_zero_of_not_mem_support
    intro hr
    simp [hs] at hr
  · intro h
    ext r
    constructor
    · intro hr
      exact False.elim ((crankResidueCount_ne_zero_iff_mem_support.2 hr) (h r))
    · intro hr
      simp at hr

/-- There is a positive residue fiber exactly when there is at least one
partition of `n`. -/
theorem exists_crankResidueCount_pos_iff_partition_card_pos (M n : Nat) :
    (∃ r : ZMod M, 0 < crankResidueCount M n r) ↔
      0 < Fintype.card (Nat.Partition n) := by
  constructor
  · rintro ⟨r, hr⟩
    exact (crankResidueSupport_nonempty_iff_partition_card_pos M n).1
      ⟨r, (crankResidueCount_pos_iff_mem_support).1 hr⟩
  · intro h
    rcases (crankResidueSupport_nonempty_iff_partition_card_pos M n).2 h with ⟨r, hr⟩
    exact ⟨r, crankResidueCount_pos_of_mem_support hr⟩

/-- There is a nonzero residue fiber exactly when there is at least one
partition of `n`. -/
theorem exists_crankResidueCount_ne_zero_iff_partition_card_pos (M n : Nat) :
    (∃ r : ZMod M, crankResidueCount M n r ≠ 0) ↔
      0 < Fintype.card (Nat.Partition n) := by
  constructor
  · rintro ⟨r, hr⟩
    exact (exists_crankResidueCount_pos_iff_partition_card_pos M n).1
      ⟨r, Nat.pos_of_ne_zero hr⟩
  · intro h
    rcases (exists_crankResidueCount_pos_iff_partition_card_pos M n).2 h with
      ⟨r, hr⟩
    exact ⟨r, Nat.ne_of_gt hr⟩

/-- All residue fibers vanish exactly when there is no partition of `n`. -/
theorem forall_crankResidueCount_eq_zero_iff_partition_card_eq_zero (M n : Nat) :
    (∀ r : ZMod M, crankResidueCount M n r = 0) ↔
      Fintype.card (Nat.Partition n) = 0 := by
  rw [← crankResidueSupport_eq_empty_iff_forall_count_eq_zero,
    crankResidueSupport_eq_empty_iff_partition_card_eq_zero]

/-- If there are no partitions of `n`, then every residue fiber has count
zero. -/
theorem crankResidueCount_eq_zero_of_partition_card_eq_zero
    (M n : Nat) (hcard : Fintype.card (Nat.Partition n) = 0) (r : ZMod M) :
    crankResidueCount M n r = 0 :=
  (forall_crankResidueCount_eq_zero_iff_partition_card_eq_zero M n).2 hcard r

/-- If the degree-`n` support is empty, then every residue-weighted crank
series has zero degree-`n` coefficient. -/
theorem coeff_crankResidueSeriesEval_eq_zero_of_support_eq_empty
    (R : Type*) [Field R] (M : Nat) (w : ZMod M → R) (n : Nat)
    (hs : crankResidueSupport M n = ∅) :
    (crankResidueSeriesEval R M w).coeff n = 0 := by
  rw [coeff_crankResidueSeriesEval_eq_residue_sum, hs]
  simp

/-- If there are no partitions of `n`, then every residue-weighted crank
series has zero degree-`n` coefficient. -/
theorem coeff_crankResidueSeriesEval_eq_zero_of_partition_card_eq_zero
    (R : Type*) [Field R] (M : Nat) (w : ZMod M → R) (n : Nat)
    (hcard : Fintype.card (Nat.Partition n) = 0) :
    (crankResidueSeriesEval R M w).coeff n = 0 :=
  coeff_crankResidueSeriesEval_eq_zero_of_support_eq_empty R M w n
    ((crankResidueSupport_eq_empty_iff_partition_card_eq_zero M n).2 hcard)

/-- If there are no partitions of `n`, then every single-residue fiber
coefficient is zero. -/
theorem coeff_crankResidueFiberSeries_eq_zero_of_partition_card_eq_zero
    (R : Type*) [Field R] {M n : Nat}
    (hcard : Fintype.card (Nat.Partition n) = 0) (r : ZMod M) :
    (crankResidueFiberSeries R M r).coeff n = 0 := by
  rw [coeff_crankResidueFiberSeries,
    crankResidueCount_eq_zero_of_partition_card_eq_zero M n hcard r]
  norm_num

/-- If all partitions of `n` have the same crank residue `r`, then the support
is contained in the singleton `{r}`. -/
theorem crankResidueSupport_subset_singleton_of_forall_crankResidue_eq
    {M n : Nat} {r : ZMod M}
    (h : ∀ lam : Nat.Partition n, crankResidue M lam = r) :
    crankResidueSupport M n ⊆ {r} := by
  classical
  intro s hs
  simp only [crankResidueSupport, Finset.mem_image, Finset.mem_univ, true_and] at hs
  rcases hs with ⟨lam, hlam⟩
  simpa [← hlam] using h lam

/-- If all partitions of `n` have crank residue `r`, then the `r`-fiber has the
full partition cardinality. -/
theorem crankResidueCount_eq_partition_card_of_forall_crankResidue_eq
    {M n : Nat} {r : ZMod M}
    (h : ∀ lam : Nat.Partition n, crankResidue M lam = r) :
    crankResidueCount M n r = Fintype.card (Nat.Partition n) := by
  classical
  rw [crankResidueCount_eq_card_filter]
  congr 1
  ext lam
  simp [h lam]

/-- The same full-fiber statement, using this repository's `partitionCount`. -/
theorem crankResidueCount_eq_partitionCount_of_forall_crankResidue_eq
    {M n : Nat} {r : ZMod M}
    (h : ∀ lam : Nat.Partition n, crankResidue M lam = r) :
    crankResidueCount M n r = QseriesFormalization.Ch01.partitionCount n := by
  rw [crankResidueCount_eq_partition_card_of_forall_crankResidue_eq h]
  rfl

/-- If no partition of `n` has crank residue `r`, then the `r`-fiber is empty. -/
theorem crankResidueCount_eq_zero_of_forall_crankResidue_ne
    {M n : Nat} {r : ZMod M}
    (h : ∀ lam : Nat.Partition n, crankResidue M lam ≠ r) :
    crankResidueCount M n r = 0 := by
  classical
  rw [crankResidueCount_eq_card_filter, Finset.card_eq_zero]
  ext lam
  simp [h lam]

/-- If all partitions have residue `r`, then every different residue has zero
fiber count. -/
theorem crankResidueCount_eq_zero_of_forall_crankResidue_eq_of_ne
    {M n : Nat} {r s : ZMod M}
    (h : ∀ lam : Nat.Partition n, crankResidue M lam = r) (hs : s ≠ r) :
    crankResidueCount M n s = 0 :=
  crankResidueCount_eq_zero_of_forall_crankResidue_ne
    (fun lam => by rw [h lam]; exact hs.symm)

/-- If the support is contained in `{r}`, every partition of `n` has crank
residue `r`. -/
theorem forall_crankResidue_eq_of_support_subset_singleton
    {M n : Nat} {r : ZMod M} (hsub : crankResidueSupport M n ⊆ {r}) :
    ∀ lam : Nat.Partition n, crankResidue M lam = r := by
  intro lam
  have hmem := hsub (crankResidue_mem_support M lam)
  simpa using hmem

/-- If the support is contained in `{r}`, then the `r`-fiber has the full
partition cardinality. -/
theorem crankResidueCount_eq_partition_card_of_support_subset_singleton
    {M n : Nat} {r : ZMod M} (hsub : crankResidueSupport M n ⊆ {r}) :
    crankResidueCount M n r = Fintype.card (Nat.Partition n) :=
  crankResidueCount_eq_partition_card_of_forall_crankResidue_eq
    (forall_crankResidue_eq_of_support_subset_singleton hsub)

/-- The same support-subset full-fiber statement, using `partitionCount`. -/
theorem crankResidueCount_eq_partitionCount_of_support_subset_singleton
    {M n : Nat} {r : ZMod M} (hsub : crankResidueSupport M n ⊆ {r}) :
    crankResidueCount M n r = QseriesFormalization.Ch01.partitionCount n :=
  crankResidueCount_eq_partitionCount_of_forall_crankResidue_eq
    (forall_crankResidue_eq_of_support_subset_singleton hsub)

/-- If the support is contained in `{r}`, every different residue has zero
fiber count. -/
theorem crankResidueCount_eq_zero_of_support_subset_singleton_of_ne
    {M n : Nat} {r s : ZMod M}
    (hsub : crankResidueSupport M n ⊆ {r}) (hs : s ≠ r) :
    crankResidueCount M n s = 0 :=
  crankResidueCount_eq_zero_of_forall_crankResidue_eq_of_ne
    (forall_crankResidue_eq_of_support_subset_singleton hsub) hs

/-- If the support is exactly `{r}`, then the `r`-fiber has the full partition
count. -/
theorem crankResidueCount_eq_partitionCount_of_support_eq_singleton
    {M n : Nat} {r : ZMod M} (h : crankResidueSupport M n = {r}) :
    crankResidueCount M n r = QseriesFormalization.Ch01.partitionCount n :=
  crankResidueCount_eq_partitionCount_of_support_subset_singleton (by
    rw [h])

/-- If the support is exactly `{r}`, every different residue has zero count. -/
theorem crankResidueCount_eq_zero_of_support_eq_singleton_of_ne
    {M n : Nat} {r s : ZMod M}
    (h : crankResidueSupport M n = {r}) (hs : s ≠ r) :
    crankResidueCount M n s = 0 :=
  crankResidueCount_eq_zero_of_support_subset_singleton_of_ne (by rw [h]) hs

/-- If the support has cardinality one and contains `r`, then it is exactly
`{r}`. -/
theorem crankResidueSupport_eq_singleton_of_card_eq_one_of_mem
    {M n : Nat} {r : ZMod M}
    (hcard : (crankResidueSupport M n).card = 1)
    (hr : r ∈ crankResidueSupport M n) :
    crankResidueSupport M n = {r} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨hr, ?_⟩
  intro s hs
  exact (Finset.card_le_one.1 (by omega) s hs r hr)

/-- If exactly one residue occurs and it is `r`, then the `r`-fiber has the
full partition count. -/
theorem crankResidueCount_eq_partitionCount_of_support_card_eq_one_of_mem
    {M n : Nat} {r : ZMod M}
    (hcard : (crankResidueSupport M n).card = 1)
    (hr : r ∈ crankResidueSupport M n) :
    crankResidueCount M n r = QseriesFormalization.Ch01.partitionCount n :=
  crankResidueCount_eq_partitionCount_of_support_eq_singleton
    (crankResidueSupport_eq_singleton_of_card_eq_one_of_mem hcard hr)

/-- If exactly one residue occurs and it is `r`, every different residue has
zero count. -/
theorem crankResidueCount_eq_zero_of_support_card_eq_one_of_mem_of_ne
    {M n : Nat} {r s : ZMod M}
    (hcard : (crankResidueSupport M n).card = 1)
    (hr : r ∈ crankResidueSupport M n) (hs : s ≠ r) :
    crankResidueCount M n s = 0 :=
  crankResidueCount_eq_zero_of_support_eq_singleton_of_ne
    (crankResidueSupport_eq_singleton_of_card_eq_one_of_mem hcard hr) hs

/-- If exactly one residue occurs, then there is at least one partition of
`n`. -/
theorem partitionCount_pos_of_support_card_eq_one
    {M n : Nat} (hcard : (crankResidueSupport M n).card = 1) :
    0 < QseriesFormalization.Ch01.partitionCount n := by
  have hpos : 0 < (crankResidueSupport M n).card := by omega
  rcases Finset.card_pos.1 hpos with ⟨r, hr⟩
  rw [QseriesFormalization.Ch01.partitionCount]
  exact (crankResidueSupport_nonempty_iff_partition_card_pos M n).1 ⟨r, hr⟩

/-- If exactly one residue occurs, it is the unique residue with positive
fiber count. -/
theorem exists_unique_crankResidueCount_pos_of_support_card_eq_one
    {M n : Nat} (hcard : (crankResidueSupport M n).card = 1) :
    ∃! r : ZMod M, 0 < crankResidueCount M n r := by
  rcases Finset.card_eq_one.1 hcard with ⟨r, hr⟩
  refine ⟨r, ?_, ?_⟩
  · exact crankResidueCount_pos_of_mem_support (by rw [hr]; simp)
  · intro s hs
    have hmem : s ∈ crankResidueSupport M n :=
      (crankResidueCount_pos_iff_mem_support).1 hs
    simpa [hr] using hmem

/-- The support has cardinality at most one iff positive residue fibers are
subsingleton. -/
theorem card_crankResidueSupport_le_one_iff_count_pos_subsingleton
    (M n : Nat) :
    (crankResidueSupport M n).card ≤ 1 ↔
      ∀ r s : ZMod M,
        0 < crankResidueCount M n r →
        0 < crankResidueCount M n s → r = s := by
  constructor
  · intro hcard r s hr hs
    exact Finset.card_le_one.1 hcard r
      ((crankResidueCount_pos_iff_mem_support).1 hr) s
      ((crankResidueCount_pos_iff_mem_support).1 hs)
  · intro h
    exact Finset.card_le_one.2 (fun r hr s hs =>
      h r s ((crankResidueCount_pos_iff_mem_support).2 hr)
        ((crankResidueCount_pos_iff_mem_support).2 hs))

/-- The support has cardinality one iff there is a unique residue with positive
fiber count. -/
theorem card_crankResidueSupport_eq_one_iff_exists_unique_count_pos
    (M n : Nat) :
    (crankResidueSupport M n).card = 1 ↔
      ∃! r : ZMod M, 0 < crankResidueCount M n r := by
  constructor
  · exact exists_unique_crankResidueCount_pos_of_support_card_eq_one
  · rintro ⟨r, hrpos, huniq⟩
    rw [Finset.card_eq_one]
    refine ⟨r, ?_⟩
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨(crankResidueCount_pos_iff_mem_support).1 hrpos, ?_⟩
    intro s hs
    exact huniq s ((crankResidueCount_pos_iff_mem_support).2 hs)

/-- The support has cardinality one iff there is a unique nonzero residue
fiber. -/
theorem card_crankResidueSupport_eq_one_iff_exists_unique_count_ne_zero
    (M n : Nat) :
    (crankResidueSupport M n).card = 1 ↔
      ∃! r : ZMod M, crankResidueCount M n r ≠ 0 := by
  rw [card_crankResidueSupport_eq_one_iff_exists_unique_count_pos]
  constructor
  · rintro ⟨r, hrpos, huniq⟩
    refine ⟨r, Nat.ne_of_gt hrpos, ?_⟩
    intro s hs
    exact huniq s (Nat.pos_of_ne_zero hs)
  · rintro ⟨r, hrne, huniq⟩
    refine ⟨r, Nat.pos_of_ne_zero hrne, ?_⟩
    intro s hs
    exact huniq s (Nat.ne_of_gt hs)

/-- If every residue different from `r` has zero count, then the support is
contained in `{r}`. -/
theorem crankResidueSupport_subset_singleton_of_count_eq_zero_of_ne
    {M n : Nat} {r : ZMod M}
    (hzero : ∀ s : ZMod M, s ≠ r → crankResidueCount M n s = 0) :
    crankResidueSupport M n ⊆ {r} := by
  intro s hs
  by_cases hsr : s = r
  · simp [hsr]
  · exact False.elim ((crankResidueCount_ne_zero_iff_mem_support.2 hs)
      (hzero s hsr))

/-- If every residue different from `r` has zero count, then at most one
residue occurs. -/
theorem card_crankResidueSupport_le_one_of_count_eq_zero_of_ne
    {M n : Nat} {r : ZMod M}
    (hzero : ∀ s : ZMod M, s ≠ r → crankResidueCount M n s = 0) :
    (crankResidueSupport M n).card ≤ 1 := by
  have hsub := crankResidueSupport_subset_singleton_of_count_eq_zero_of_ne
    (M := M) (n := n) (r := r) hzero
  exact (Finset.card_le_card hsub).trans (by simp)

/-- If every residue different from `r` has zero count and at least one
partition exists, then the support is exactly `{r}`. -/
theorem crankResidueSupport_eq_singleton_of_partition_card_pos_of_count_eq_zero_of_ne
    {M n : Nat} {r : ZMod M}
    (hpos : 0 < Fintype.card (Nat.Partition n))
    (hzero : ∀ s : ZMod M, s ≠ r → crankResidueCount M n s = 0) :
    crankResidueSupport M n = {r} := by
  classical
  have hsub := crankResidueSupport_subset_singleton_of_count_eq_zero_of_ne
    (M := M) (n := n) (r := r) hzero
  rcases (crankResidueSupport_nonempty_iff_partition_card_pos M n).2 hpos with
    ⟨s, hs⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨?_, ?_⟩
  · have hsr : s = r := by simpa using hsub hs
    simpa [hsr] using hs
  · intro t ht
    simpa using hsub ht

/-- Under the same one-residue support hypothesis, the surviving residue has
full `partitionCount`. -/
theorem crankResidueCount_eq_partitionCount_of_partition_card_pos_of_count_eq_zero_of_ne
    {M n : Nat} {r : ZMod M}
    (hpos : 0 < Fintype.card (Nat.Partition n))
    (hzero : ∀ s : ZMod M, s ≠ r → crankResidueCount M n s = 0) :
    crankResidueCount M n r = QseriesFormalization.Ch01.partitionCount n :=
  crankResidueCount_eq_partitionCount_of_support_eq_singleton
    (crankResidueSupport_eq_singleton_of_partition_card_pos_of_count_eq_zero_of_ne
      hpos hzero)

/-- Coefficient version of
`crankResidueCount_eq_partitionCount_of_partition_card_pos_of_count_eq_zero_of_ne`. -/
theorem coeff_crankResidueFiberSeries_eq_partitionCount_of_partition_card_pos_of_count_eq_zero_of_ne
    (R : Type*) [Field R] {M n : Nat} {r : ZMod M}
    (hpos : 0 < Fintype.card (Nat.Partition n))
    (hzero : ∀ s : ZMod M, s ≠ r → crankResidueCount M n s = 0) :
    (crankResidueFiberSeries R M r).coeff n =
      (QseriesFormalization.Ch01.partitionCount n : R) := by
  rw [coeff_crankResidueFiberSeries,
    crankResidueCount_eq_partitionCount_of_partition_card_pos_of_count_eq_zero_of_ne
      hpos hzero]

/-- If in every degree all residue fibers except `r` vanish and a partition
exists, then the `r`-fiber series is the ordinary partition generating
function. -/
theorem crankResidueFiberSeries_eq_partitionGenFun_of_count_eq_zero_of_ne
    (R : Type*) [Field R] {M : Nat} {r : ZMod M}
    (hpos : ∀ n : Nat, 0 < Fintype.card (Nat.Partition n))
    (hzero : ∀ n (s : ZMod M), s ≠ r → crankResidueCount M n s = 0) :
    crankResidueFiberSeries R M r =
      QseriesFormalization.PartIV.Ch19.partitionGenFun R := by
  ext n
  rw [coeff_crankResidueFiberSeries_eq_partitionCount_of_partition_card_pos_of_count_eq_zero_of_ne
    R (hpos n) (hzero n), QseriesFormalization.PartIV.Ch19.coeff_partitionGenFun]
  rfl

/-- If a residue fiber vanishes in every degree, then its fiber series is zero. -/
theorem crankResidueFiberSeries_eq_zero_of_count_eq_zero_all_degrees
    (R : Type*) [Field R] {M : Nat} {s : ZMod M}
    (hzero : ∀ n : Nat, crankResidueCount M n s = 0) :
    crankResidueFiberSeries R M s = 0 := by
  ext n
  rw [coeff_crankResidueFiberSeries, hzero n]
  norm_num

/-- If in every degree all residue fibers except `r` vanish and a partition
exists, then every different fiber series is zero. -/
theorem crankResidueFiberSeries_eq_zero_of_count_eq_zero_of_ne_all_degrees
    (R : Type*) [Field R] {M : Nat} {r s : ZMod M}
    (hzero : ∀ n (t : ZMod M), t ≠ r → crankResidueCount M n t = 0)
    (hs : s ≠ r) :
    crankResidueFiberSeries R M s = 0 :=
  crankResidueFiberSeries_eq_zero_of_count_eq_zero_all_degrees R
    (fun n => hzero n s hs)

/-- Under a one-surviving-residue hypothesis in every degree, a residue-weighted
crank series collapses to the surviving weight times the partition generating
function. -/
theorem crankResidueSeriesEval_eq_smul_partitionGenFun_of_count_eq_zero_of_ne
    (R : Type*) [Field R] {M : Nat} {r : ZMod M} (w : ZMod M → R)
    (hpos : ∀ n : Nat, 0 < Fintype.card (Nat.Partition n))
    (hzero : ∀ n (s : ZMod M), s ≠ r → crankResidueCount M n s = 0) :
    crankResidueSeriesEval R M w =
      w r • QseriesFormalization.PartIV.Ch19.partitionGenFun R := by
  ext n
  rw [coeff_crankResidueSeriesEval_eq_residue_sum]
  have hsupport :
      crankResidueSupport M n = {r} :=
    crankResidueSupport_eq_singleton_of_partition_card_pos_of_count_eq_zero_of_ne
      (hpos n) (hzero n)
  rw [hsupport]
  rw [Finset.sum_singleton, PowerSeries.coeff_smul,
    QseriesFormalization.PartIV.Ch19.coeff_partitionGenFun]
  rw [crankResidueCount_eq_partitionCount_of_support_eq_singleton hsupport]
  rw [QseriesFormalization.Ch01.partitionCount]
  simp [smul_eq_mul, mul_comm]

/-- If the support is exactly `{r}`, then the `r`-fiber count is positive. -/
theorem crankResidueCount_pos_of_support_eq_singleton
    {M n : Nat} {r : ZMod M} (h : crankResidueSupport M n = {r}) :
    0 < crankResidueCount M n r :=
  crankResidueCount_pos_of_mem_support (by rw [h]; simp)

/-- If the support is exactly a singleton, then there is at least one partition
of `n`. -/
theorem partition_card_pos_of_support_eq_singleton
    {M n : Nat} {r : ZMod M} (h : crankResidueSupport M n = {r}) :
    0 < Fintype.card (Nat.Partition n) :=
  (crankResidueSupport_nonempty_iff_partition_card_pos M n).1
    ⟨r, by rw [h]; simp⟩

/-- The same singleton-support positivity, stated with `partitionCount`. -/
theorem partitionCount_pos_of_support_eq_singleton
    {M n : Nat} {r : ZMod M} (h : crankResidueSupport M n = {r}) :
    0 < QseriesFormalization.Ch01.partitionCount n := by
  rw [QseriesFormalization.Ch01.partitionCount]
  exact partition_card_pos_of_support_eq_singleton h

/-- Over `ℚ`, if the support is exactly `{r}`, then the `r`-fiber coefficient
is nonzero. -/
theorem coeff_crankResidueFiberSeries_rat_ne_zero_of_support_eq_singleton
    {M n : Nat} {r : ZMod M} (h : crankResidueSupport M n = {r}) :
    (crankResidueFiberSeries ℚ M r).coeff n ≠ 0 :=
  (coeff_crankResidueFiberSeries_rat_ne_zero_iff_mem_support).2 (by rw [h]; simp)

/-- Coefficient form: if the degree-`n` support is contained in `{r}`, the
`r`-fiber coefficient is the partition count. -/
theorem coeff_crankResidueFiberSeries_eq_partitionCount_of_support_subset_singleton
    (R : Type*) [Field R] {M n : Nat} {r : ZMod M}
    (hsub : crankResidueSupport M n ⊆ {r}) :
    (crankResidueFiberSeries R M r).coeff n =
      (QseriesFormalization.Ch01.partitionCount n : R) := by
  rw [coeff_crankResidueFiberSeries,
    crankResidueCount_eq_partitionCount_of_support_subset_singleton hsub]

/-- Coefficient form: if the degree-`n` support is contained in `{r}`, every
different residue has zero fiber coefficient. -/
theorem coeff_crankResidueFiberSeries_eq_zero_of_support_subset_singleton_of_ne
    (R : Type*) [Field R] {M n : Nat} {r s : ZMod M}
    (hsub : crankResidueSupport M n ⊆ {r}) (hs : s ≠ r) :
    (crankResidueFiberSeries R M s).coeff n = 0 := by
  rw [coeff_crankResidueFiberSeries,
    crankResidueCount_eq_zero_of_support_subset_singleton_of_ne hsub hs]
  norm_num

/-- If every degree has support contained in `{r}`, the `r`-fiber series is the
ordinary partition generating function. -/
theorem crankResidueFiberSeries_eq_partitionGenFun_of_support_subset_singleton
    (R : Type*) [Field R] {M : Nat} {r : ZMod M}
    (hsub : ∀ n : Nat, crankResidueSupport M n ⊆ {r}) :
    crankResidueFiberSeries R M r =
      QseriesFormalization.PartIV.Ch19.partitionGenFun R := by
  ext n
  rw [coeff_crankResidueFiberSeries_eq_partitionCount_of_support_subset_singleton
    R (hsub n), QseriesFormalization.PartIV.Ch19.coeff_partitionGenFun]
  rfl

/-- If every degree has support contained in `{r}`, each different residue
fiber series is zero. -/
theorem crankResidueFiberSeries_eq_zero_of_support_subset_singleton_of_ne
    (R : Type*) [Field R] {M : Nat} {r s : ZMod M}
    (hsub : ∀ n : Nat, crankResidueSupport M n ⊆ {r}) (hs : s ≠ r) :
    crankResidueFiberSeries R M s = 0 := by
  ext n
  exact coeff_crankResidueFiberSeries_eq_zero_of_support_subset_singleton_of_ne
    R (hsub n) hs

/-- Summing over all residues recovers the number of partitions of `n`, when
the residue ring is finite. -/
theorem sum_univ_crankResidueCount_eq_partition_card
    (M n : Nat) [Fintype (ZMod M)] :
    ∑ r : ZMod M, crankResidueCount M n r =
      Fintype.card (Nat.Partition n) := by
  classical
  calc
    ∑ r : ZMod M, crankResidueCount M n r =
        ∑ r ∈ crankResidueSupport M n, crankResidueCount M n r := by
          symm
          apply Finset.sum_subset
          · intro r _hr
            exact Finset.mem_univ r
          · intro r _hruniv hnot
            exact crankResidueCount_eq_zero_of_not_mem_support hnot
    _ = Fintype.card (Nat.Partition n) :=
        sum_crankResidueCount_eq_partition_card M n

/-- The same all-residue identity, stated with this repository's
`partitionCount`. -/
theorem sum_univ_crankResidueCount_eq_partitionCount
    (M n : Nat) [Fintype (ZMod M)] :
    ∑ r : ZMod M, crankResidueCount M n r =
      QseriesFormalization.Ch01.partitionCount n := by
  rw [sum_univ_crankResidueCount_eq_partition_card]
  rfl

/-- All-residue crank counts modulo `5` recover the partition count. -/
theorem sum_univ_crankResidueCount_mod_five_eq_partitionCount (n : Nat) :
    ∑ r : ZMod 5, crankResidueCount 5 n r =
      QseriesFormalization.Ch01.partitionCount n :=
  sum_univ_crankResidueCount_eq_partitionCount 5 n

/-! ## Linearity in the residue weight -/

/-- The residue-weighted crank series is additive in the residue weight. -/
theorem crankResidueSeriesEval_add
    (R : Type*) [Field R] (M : Nat) (w v : ZMod M → R) :
    crankResidueSeriesEval R M (fun r => w r + v r) =
      crankResidueSeriesEval R M w + crankResidueSeriesEval R M v := by
  ext n
  simp [coeff_crankResidueSeriesEval, Finset.sum_add_distrib]

/-- The residue-weighted crank series for the zero weight is zero. -/
theorem crankResidueSeriesEval_zero
    (R : Type*) [Field R] (M : Nat) :
    crankResidueSeriesEval R M (fun _ => 0) = 0 := by
  ext n
  simp [coeff_crankResidueSeriesEval]

/-- The residue-weighted crank series is compatible with negating the weight. -/
theorem crankResidueSeriesEval_neg
    (R : Type*) [Field R] (M : Nat) (w : ZMod M → R) :
    crankResidueSeriesEval R M (fun r => -w r) =
      -crankResidueSeriesEval R M w := by
  ext n
  simp [coeff_crankResidueSeriesEval]

/-- The residue-weighted crank series is subtractive in the residue weight. -/
theorem crankResidueSeriesEval_sub
    (R : Type*) [Field R] (M : Nat) (w v : ZMod M → R) :
    crankResidueSeriesEval R M (fun r => w r - v r) =
      crankResidueSeriesEval R M w - crankResidueSeriesEval R M v := by
  ext n
  simp [coeff_crankResidueSeriesEval, Finset.sum_sub_distrib]

/-- The residue-weighted crank series is compatible with scalar multiplication
of the residue weight. -/
theorem crankResidueSeriesEval_smul
    (R : Type*) [Field R] (M : Nat) (c : R) (w : ZMod M → R) :
    crankResidueSeriesEval R M (fun r => c * w r) =
      c • crankResidueSeriesEval R M w := by
  ext n
  rw [coeff_crankResidueSeriesEval, PowerSeries.coeff_smul,
    coeff_crankResidueSeriesEval]
  simp [smul_eq_mul, Finset.mul_sum]

/-! ## Constant residue weights -/

/-- If every residue has the same weight `c`, the coefficient is `c` times the
partition count. -/
theorem coeff_crankResidueSeriesEval_const
    (R : Type*) [Field R] (M n : Nat) (c : R) :
    (crankResidueSeriesEval R M (fun _ => c)).coeff n =
      (QseriesFormalization.Ch01.partitionCount n : R) * c := by
  rw [coeff_crankResidueSeriesEval]
  change (∑ _lam : Nat.Partition n, c) =
    (Fintype.card (Nat.Partition n) : R) * c
  simp

/-- The constant-weight crank series is the corresponding scalar multiple of
the ordinary partition generating function. -/
theorem crankResidueSeriesEval_const_eq_smul_partitionGenFun
    (R : Type*) [Field R] (M : Nat) (c : R) :
    crankResidueSeriesEval R M (fun _ => c) =
      c • QseriesFormalization.PartIV.Ch19.partitionGenFun R := by
  ext n
  rw [coeff_crankResidueSeriesEval_const, PowerSeries.coeff_smul,
    QseriesFormalization.PartIV.Ch19.coeff_partitionGenFun]
  rw [QseriesFormalization.Ch01.partitionCount]
  simp [smul_eq_mul, mul_comm]

/-- Modulus-`5` specialization of the constant-weight crank series. -/
theorem crankResidueSeriesEval_mod_five_const_eq_smul_partitionGenFun
    (R : Type*) [Field R] (c : R) :
    crankResidueSeriesEval R 5 (fun _ => c) =
      c • QseriesFormalization.PartIV.Ch19.partitionGenFun R :=
  crankResidueSeriesEval_const_eq_smul_partitionGenFun R 5 c

/-- Summing the all-residue counts with a constant coefficient gives the
constant multiple of the partition count. -/
theorem sum_univ_crankResidueCount_const_eq_partitionCount_mul
    (R : Type*) [Field R] (M n : Nat) [Fintype (ZMod M)] (c : R) :
    ∑ r : ZMod M, (crankResidueCount M n r : R) * c =
      (QseriesFormalization.Ch01.partitionCount n : R) * c := by
  rw [← Finset.sum_mul]
  have hnat :
      ∑ r : ZMod M, crankResidueCount M n r =
        QseriesFormalization.Ch01.partitionCount n :=
    sum_univ_crankResidueCount_eq_partitionCount M n
  rw [← Nat.cast_sum]
  rw [hnat]

/-! ## Decomposition into single-residue fibers -/

/-- The indicator weight for one residue is exactly the corresponding
single-residue fiber series. -/
theorem crankResidueSeriesEval_indicator_eq_fiberSeries
    (R : Type*) [Field R] (M : Nat) (r : ZMod M) :
    crankResidueSeriesEval R M (fun s => if s = r then 1 else 0) =
      crankResidueFiberSeries R M r :=
  rfl

/-- Coefficient form of `crankResidueSeriesEval_indicator_eq_fiberSeries`. -/
theorem coeff_crankResidueSeriesEval_indicator
    (R : Type*) [Field R] (M : Nat) (r : ZMod M) (n : Nat) :
    (crankResidueSeriesEval R M (fun s => if s = r then 1 else 0)).coeff n =
      (crankResidueCount M n r : R) := by
  rw [crankResidueSeriesEval_indicator_eq_fiberSeries,
    coeff_crankResidueFiberSeries]

/-- A scaled indicator residue weight gives the scalar multiple of the
single-residue fiber series. -/
theorem crankResidueSeriesEval_scaled_indicator_eq_smul_fiberSeries
    (R : Type*) [Field R] (M : Nat) (r : ZMod M) (c : R) :
    crankResidueSeriesEval R M (fun s => if s = r then c else 0) =
      c • crankResidueFiberSeries R M r := by
  have hweight :
      (fun s : ZMod M => if s = r then c else 0) =
        (fun s : ZMod M => c * (if s = r then (1 : R) else 0)) := by
    ext s
    by_cases hs : s = r <;> simp [hs]
  rw [hweight, crankResidueSeriesEval_smul,
    crankResidueSeriesEval_indicator_eq_fiberSeries]

/-- Coefficient form of a scaled single-residue indicator weight. -/
theorem coeff_crankResidueSeriesEval_scaled_indicator
    (R : Type*) [Field R] (M : Nat) (r : ZMod M) (c : R) (n : Nat) :
    (crankResidueSeriesEval R M (fun s => if s = r then c else 0)).coeff n =
      (crankResidueCount M n r : R) * c := by
  rw [crankResidueSeriesEval_scaled_indicator_eq_smul_fiberSeries,
    PowerSeries.coeff_smul, coeff_crankResidueFiberSeries]
  simp [smul_eq_mul, mul_comm]

/-- Modulus-`5` specialization of the scaled indicator residue weight. -/
theorem crankResidueSeriesEval_mod_five_scaled_indicator_eq_smul_fiberSeries
    (R : Type*) [Field R] (r : ZMod 5) (c : R) :
    crankResidueSeriesEval R 5 (fun s => if s = r then c else 0) =
      c • crankResidueFiberSeries R 5 r :=
  crankResidueSeriesEval_scaled_indicator_eq_smul_fiberSeries R 5 r c

/-- Coefficient form of the residue decomposition when summing over all
residues instead of only the finite support. -/
theorem coeff_crankResidueSeriesEval_eq_univ_residue_sum
    (R : Type*) [Field R] (M : Nat) [Fintype (ZMod M)]
    (w : ZMod M → R) (n : Nat) :
    (crankResidueSeriesEval R M w).coeff n =
      ∑ r : ZMod M, (crankResidueCount M n r : R) * w r := by
  classical
  rw [coeff_crankResidueSeriesEval_eq_residue_sum]
  apply Finset.sum_subset
  · intro r _hr
    exact Finset.mem_univ r
  · intro r _hruniv hnot
    rw [crankResidueCount_eq_zero_of_not_mem_support hnot]
    simp

/-- Coefficient decomposition over all residues, expressed using
single-residue fiber coefficients. -/
theorem coeff_crankResidueSeriesEval_eq_univ_weighted_fiber_coeff
    (R : Type*) [Field R] (M : Nat) [Fintype (ZMod M)]
    (w : ZMod M → R) (n : Nat) :
    (crankResidueSeriesEval R M w).coeff n =
      ∑ r : ZMod M, w r * (crankResidueFiberSeries R M r).coeff n := by
  rw [coeff_crankResidueSeriesEval_eq_univ_residue_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [coeff_crankResidueFiberSeries]
  ring

/-- Degree-wise fiber decomposition over all residues. -/
theorem sum_univ_coeff_crankResidueFiberSeries_eq_partitionCount
    (R : Type*) [Field R] (M n : Nat) [Fintype (ZMod M)] :
    ∑ r : ZMod M, (crankResidueFiberSeries R M r).coeff n =
      (QseriesFormalization.Ch01.partitionCount n : R) := by
  calc
    ∑ r : ZMod M, (crankResidueFiberSeries R M r).coeff n =
        ∑ r : ZMod M, (crankResidueCount M n r : R) := by
          apply Finset.sum_congr rfl
          intro r _hr
          rw [coeff_crankResidueFiberSeries]
    _ = (QseriesFormalization.Ch01.partitionCount n : R) := by
          have hnat :
              ∑ r : ZMod M, crankResidueCount M n r =
                QseriesFormalization.Ch01.partitionCount n :=
            sum_univ_crankResidueCount_eq_partitionCount M n
          rw [← Nat.cast_sum]
          rw [hnat]

/-- Modulus-`5` specialization of the degree-wise fiber decomposition. -/
theorem sum_univ_coeff_crankResidueFiberSeries_mod_five_eq_partitionCount
    (R : Type*) [Field R] (n : Nat) :
    ∑ r : ZMod 5, (crankResidueFiberSeries R 5 r).coeff n =
      (QseriesFormalization.Ch01.partitionCount n : R) :=
  sum_univ_coeff_crankResidueFiberSeries_eq_partitionCount R 5 n

/-- A residue-weighted crank series is the corresponding linear combination of
the single-residue fiber series. -/
theorem crankResidueSeriesEval_eq_sum_weighted_fiberSeries
    (R : Type*) [Field R] (M : Nat) [Fintype (ZMod M)] (w : ZMod M → R) :
    crankResidueSeriesEval R M w =
      ∑ r : ZMod M, w r • crankResidueFiberSeries R M r := by
  classical
  ext n
  rw [coeff_crankResidueSeriesEval_eq_univ_residue_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [PowerSeries.coeff_smul, coeff_crankResidueFiberSeries]
  simp [smul_eq_mul, mul_comm]

/-- The same linear-combination decomposition at the classical modulus `5`. -/
theorem crankResidueSeriesEval_mod_five_eq_sum_weighted_fiberSeries
    (R : Type*) [Field R] (w : ZMod 5 → R) :
    crankResidueSeriesEval R 5 w =
      ∑ r : ZMod 5, w r • crankResidueFiberSeries R 5 r :=
  crankResidueSeriesEval_eq_sum_weighted_fiberSeries R 5 w

/-- Summing all residue-fiber series recovers the ordinary partition generating
function, for any modulus whose residue ring is finite. -/
theorem sum_crankResidueFiberSeries_eq_partitionGenFun
    (R : Type*) [Field R] (M : Nat) [Fintype (ZMod M)] :
    (∑ r : ZMod M, crankResidueFiberSeries R M r) =
      QseriesFormalization.PartIV.Ch19.partitionGenFun R := by
  classical
  ext n
  rw [map_sum]
  calc
    (∑ r : ZMod M, (crankResidueFiberSeries R M r).coeff n)
        = ∑ r : ZMod M, (crankResidueCount M n r : R) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [coeff_crankResidueFiberSeries]
    _ = ∑ r ∈ crankResidueSupport M n, (crankResidueCount M n r : R) := by
            symm
            apply Finset.sum_subset
            · intro r hr
              exact Finset.mem_univ r
            · intro r _hruniv hnot
              rw [crankResidueCount_eq_zero_of_not_mem_support hnot]
              norm_num
    _ = (QseriesFormalization.Ch01.partitionCount n : R) := by
            have hnat := congrArg (fun z : Nat => (z : R))
              (sum_crankResidueCount_eq_partitionCount M n)
            simpa using hnat
    _ = (QseriesFormalization.PartIV.Ch19.partitionGenFun R).coeff n := by
            rw [QseriesFormalization.PartIV.Ch19.coeff_partitionGenFun]
            rfl

/-- Coefficient form of the all-residue fiber-series decomposition. -/
theorem coeff_sum_crankResidueFiberSeries_eq_partitionCount
    (R : Type*) [Field R] (M : Nat) [Fintype (ZMod M)] (n : Nat) :
    ((∑ r : ZMod M, crankResidueFiberSeries R M r) : R⟦X⟧).coeff n =
      (QseriesFormalization.Ch01.partitionCount n : R) := by
  rw [sum_crankResidueFiberSeries_eq_partitionGenFun,
    QseriesFormalization.PartIV.Ch19.coeff_partitionGenFun]
  rfl

/-- Coefficient form of the classical modulus-`5` fiber decomposition. -/
theorem coeff_sum_crankResidueFiberSeries_mod_five_eq_partitionCount
    (R : Type*) [Field R] (n : Nat) :
    ((∑ r : ZMod 5, crankResidueFiberSeries R 5 r) : R⟦X⟧).coeff n =
      (QseriesFormalization.Ch01.partitionCount n : R) :=
  coeff_sum_crankResidueFiberSeries_eq_partitionCount R 5 n

/-- The fiber decomposition at the classical modulus `5`. -/
theorem sum_crankResidueFiberSeries_mod_five_eq_partitionGenFun
    (R : Type*) [Field R] :
    (∑ r : ZMod 5, crankResidueFiberSeries R 5 r) =
      QseriesFormalization.PartIV.Ch19.partitionGenFun R :=
  sum_crankResidueFiberSeries_eq_partitionGenFun R 5

end

end Ch14Residue
end Pending
end QseriesFormalization
