import QseriesFormalization.Basic
import QseriesFormalization.Chapter05

namespace QseriesFormalization
namespace PartIV
namespace Ch18

section HookLengths

/-- Ferrers cells reused from Chapter 5, with rows and columns zero-indexed. -/
abbrev FerrersCell (lam : List Nat) (r c : Nat) : Prop :=
  PartI.Ch05.FerrersCell lam r c

/-- Number of cells to the right of `(r,c)` in a Ferrers row. -/
def armLength (lam : List Nat) (r c : Nat) : Nat :=
  lam.getD r 0 - (c + 1)

/-- Number of lower rows whose Ferrers diagram contains column `c`. -/
def legLength (lam : List Nat) (r c : Nat) : Nat :=
  ((lam.drop (r + 1)).filter (fun rowLength => c < rowLength)).length

/-- Hook length of a Ferrers cell: arm plus leg plus the cell itself. -/
def hookLength (lam : List Nat) (r c : Nat) : Nat :=
  armLength lam r c + legLength lam r c + 1

/-- At a Ferrers cell, the arm length plus the cell itself is the remaining
row length from column `c`. -/
theorem armLength_add_one_of_FerrersCell {lam : List Nat} {r c : Nat}
    (hcell : FerrersCell lam r c) :
    armLength lam r c + 1 = lam.getD r 0 - c := by
  unfold armLength
  unfold FerrersCell PartI.Ch05.FerrersCell at hcell
  omega

/-- At a Ferrers cell, the arm length is strictly shorter than the row length. -/
theorem armLength_lt_rowLength_of_FerrersCell {lam : List Nat} {r c : Nat}
    (hcell : FerrersCell lam r c) :
    armLength lam r c < lam.getD r 0 := by
  have h := armLength_add_one_of_FerrersCell hcell
  unfold FerrersCell PartI.Ch05.FerrersCell at hcell
  omega

/-- At a Ferrers cell, hook length can be written as remaining row length plus
leg length. -/
theorem hookLength_eq_row_sub_col_add_leg_of_FerrersCell {lam : List Nat} {r c : Nat}
    (hcell : FerrersCell lam r c) :
    hookLength lam r c = (lam.getD r 0 - c) + legLength lam r c := by
  unfold hookLength
  rw [← armLength_add_one_of_FerrersCell hcell]
  omega

/-- A Ferrers hook always contains the whole arm plus the distinguished cell. -/
theorem armLength_lt_hookLength (lam : List Nat) (r c : Nat) :
    armLength lam r c < hookLength lam r c := by
  unfold hookLength
  omega

/-- A Ferrers hook always contains the whole leg plus the distinguished cell. -/
theorem legLength_lt_hookLength (lam : List Nat) (r c : Nat) :
    legLength lam r c < hookLength lam r c := by
  unfold hookLength
  omega

/-- Hook lengths are always positive in this finite Ferrers model. -/
theorem hookLength_pos (lam : List Nat) (r c : Nat) :
    0 < hookLength lam r c := by
  unfold hookLength
  omega

/-- Hook lengths are never zero. -/
theorem hookLength_ne_zero (lam : List Nat) (r c : Nat) :
    hookLength lam r c ≠ 0 :=
  Nat.ne_of_gt (hookLength_pos lam r c)

/-- The hook-divisibility obstruction to being a `t`-core. -/
def HasHookDivisibleBy (t : Nat) (lam : List Nat) : Prop :=
  ∃ r c, FerrersCell lam r c ∧ t ∣ hookLength lam r c

/-- Hook-length definition of a `t`-core partition. -/
def IsTCoreByHooks (t : Nat) (lam : List Nat) : Prop :=
  ¬ HasHookDivisibleBy t lam

/-- Package one Ferrers cell and divisibility proof into the hook obstruction. -/
theorem hasHookDivisibleBy_of_cell {t : Nat} {lam : List Nat} {r c : Nat}
    (hcell : FerrersCell lam r c) (hdiv : t ∣ hookLength lam r c) :
    HasHookDivisibleBy t lam :=
  ⟨r, c, hcell, hdiv⟩

/-- Package a Ferrers cell whose hook length is displayed as `t * k` into
the hook-divisibility obstruction. -/
theorem hasHookDivisibleBy_of_hookLength_eq_mul {t : Nat} {lam : List Nat} {r c k : Nat}
    (hcell : FerrersCell lam r c) (hhook : hookLength lam r c = t * k) :
    HasHookDivisibleBy t lam :=
  hasHookDivisibleBy_of_cell hcell ⟨k, hhook⟩

/-- Hook-divisibility can equivalently be displayed by naming the multiplier
of the modulus. -/
theorem hasHookDivisibleBy_iff_exists_hookLength_eq_mul (t : Nat) (lam : List Nat) :
    HasHookDivisibleBy t lam ↔
      ∃ r c k, FerrersCell lam r c ∧ hookLength lam r c = t * k := by
  constructor
  · intro h
    rcases h with ⟨r, c, hcell, hdiv⟩
    rcases hdiv with ⟨k, hk⟩
    exact ⟨r, c, k, hcell, hk⟩
  · rintro ⟨r, c, k, hcell, hk⟩
    exact hasHookDivisibleBy_of_cell hcell ⟨k, hk⟩

/-- Every Ferrers cell supplies an obstruction for the modulus equal to its own
hook length. -/
theorem hasHookDivisibleBy_hookLength_of_cell {lam : List Nat} {r c : Nat}
    (hcell : FerrersCell lam r c) :
    HasHookDivisibleBy (hookLength lam r c) lam :=
  hasHookDivisibleBy_of_cell hcell (dvd_refl _)

/-- A hook-length preserving map on Ferrers cells carries hook-divisibility
obstructions from one partition to another. -/
theorem HasHookDivisibleBy.map_hookLength {t : Nat} {lam mu : List Nat}
    (hmap : ∀ ⦃r c : Nat⦄, FerrersCell lam r c →
      ∃ r' c', FerrersCell mu r' c' ∧ hookLength mu r' c' = hookLength lam r c)
    (h : HasHookDivisibleBy t lam) :
    HasHookDivisibleBy t mu := by
  rcases h with ⟨r, c, hcell, hdiv⟩
  rcases hmap hcell with ⟨r', c', hcell', hhook⟩
  exact ⟨r', c', hcell', by rwa [hhook]⟩

/-- If hook lengths of Ferrers cells are represented in both directions, then
hook-divisibility obstructions are equivalent. -/
theorem hasHookDivisibleBy_iff_of_hookLength_maps {t : Nat} {lam mu : List Nat}
    (hmap_lm : ∀ ⦃r c : Nat⦄, FerrersCell lam r c →
      ∃ r' c', FerrersCell mu r' c' ∧ hookLength mu r' c' = hookLength lam r c)
    (hmap_ml : ∀ ⦃r c : Nat⦄, FerrersCell mu r c →
      ∃ r' c', FerrersCell lam r' c' ∧ hookLength lam r' c' = hookLength mu r c) :
    HasHookDivisibleBy t lam ↔ HasHookDivisibleBy t mu := by
  constructor
  · exact HasHookDivisibleBy.map_hookLength hmap_lm
  · exact HasHookDivisibleBy.map_hookLength hmap_ml

/-- A hook-length preserving representation of cells in both directions
preserves the hook-length `t`-core predicate. -/
theorem isTCoreByHooks_iff_of_hookLength_maps {t : Nat} {lam mu : List Nat}
    (hmap_lm : ∀ ⦃r c : Nat⦄, FerrersCell lam r c →
      ∃ r' c', FerrersCell mu r' c' ∧ hookLength mu r' c' = hookLength lam r c)
    (hmap_ml : ∀ ⦃r c : Nat⦄, FerrersCell mu r c →
      ∃ r' c', FerrersCell lam r' c' ∧ hookLength lam r' c' = hookLength mu r c) :
    IsTCoreByHooks t lam ↔ IsTCoreByHooks t mu := by
  unfold IsTCoreByHooks
  rw [hasHookDivisibleBy_iff_of_hookLength_maps hmap_lm hmap_ml]

/-- A conjugation-specific packaging lemma: once hook lengths are shown to
match across transposed Ferrers cells, hook-divisibility obstructions are
preserved by Ferrers conjugation. -/
theorem hasHookDivisibleBy_FerrersConjugatePartition_iff_of_hookLength_eq
    {t : Nat} {lam : List Nat} (hpart : IsPartition lam)
    (hforward : ∀ ⦃r c : Nat⦄, FerrersCell lam r c →
      hookLength (PartI.Ch05.FerrersConjugatePartition lam) c r = hookLength lam r c)
    (hback : ∀ ⦃r c : Nat⦄, FerrersCell (PartI.Ch05.FerrersConjugatePartition lam) r c →
      hookLength lam c r = hookLength (PartI.Ch05.FerrersConjugatePartition lam) r c) :
    HasHookDivisibleBy t lam ↔
      HasHookDivisibleBy t (PartI.Ch05.FerrersConjugatePartition lam) := by
  apply hasHookDivisibleBy_iff_of_hookLength_maps
  · intro r c hcell
    exact ⟨c, r, (PartI.Ch05.FerrersCell_FerrersConjugatePartition_iff hpart).2 hcell,
      hforward hcell⟩
  · intro r c hcell
    exact ⟨c, r, (PartI.Ch05.FerrersCell_FerrersConjugatePartition_iff hpart).1 hcell,
      hback hcell⟩

/-- The corresponding t-core packaging lemma for Ferrers conjugation. -/
theorem isTCoreByHooks_FerrersConjugatePartition_iff_of_hookLength_eq
    {t : Nat} {lam : List Nat} (hpart : IsPartition lam)
    (hforward : ∀ ⦃r c : Nat⦄, FerrersCell lam r c →
      hookLength (PartI.Ch05.FerrersConjugatePartition lam) c r = hookLength lam r c)
    (hback : ∀ ⦃r c : Nat⦄, FerrersCell (PartI.Ch05.FerrersConjugatePartition lam) r c →
      hookLength lam c r = hookLength (PartI.Ch05.FerrersConjugatePartition lam) r c) :
    IsTCoreByHooks t lam ↔
      IsTCoreByHooks t (PartI.Ch05.FerrersConjugatePartition lam) := by
  unfold IsTCoreByHooks
  rw [hasHookDivisibleBy_FerrersConjugatePartition_iff_of_hookLength_eq
    hpart hforward hback]

/-- Ferrers columns of a cons list split into the optional new top cell and
the shifted old column. -/
theorem FerrersColumnCells_cons (n : Nat) (tail : List Nat) (c : Nat) :
    PartI.Ch05.FerrersColumnCells (n :: tail) c =
      (if c < n then ({0} : Finset Nat) else ∅) ∪
        (PartI.Ch05.FerrersColumnCells tail c).image Nat.succ := by
  ext r
  cases r with
  | zero =>
      by_cases hc : c < n <;> simp [PartI.Ch05.FerrersColumnCells, hc]
  | succ r =>
      by_cases hc : c < n <;> simp [PartI.Ch05.FerrersColumnCells, hc]

/-- Cardinal form of `FerrersColumnCells_cons`. -/
theorem FerrersColumnCells_card_cons (n : Nat) (tail : List Nat) (c : Nat) :
    (PartI.Ch05.FerrersColumnCells (n :: tail) c).card =
      (if c < n then 1 else 0) + (PartI.Ch05.FerrersColumnCells tail c).card := by
  rw [FerrersColumnCells_cons]
  have hinj : Function.Injective Nat.succ := by
    intro a b h
    exact Nat.succ.inj h
  by_cases hc : c < n
  · simp [hc]
    rw [Finset.card_image_of_injective _ hinj]
    omega
  · simp [hc]
    rw [Finset.card_image_of_injective _ hinj]

/-- Filtering a list of row lengths by a fixed column threshold counts exactly
the Ferrers column cells in that column. -/
theorem filter_length_eq_FerrersColumnCells_card (lam : List Nat) (c : Nat) :
    (lam.filter (fun rowLength => c < rowLength)).length =
      (PartI.Ch05.FerrersColumnCells lam c).card := by
  induction lam with
  | nil =>
      simp [PartI.Ch05.FerrersColumnCells]
  | cons n tail ih =>
      rw [FerrersColumnCells_card_cons]
      by_cases hc : c < n
      · simp [hc, ih]
        omega
      · simp [hc, ih]

/-- The leg below `(r,c)` is the column height remaining after dropping the
rows through `r`. -/
theorem legLength_eq_FerrersColumnCells_drop_card (lam : List Nat) (r c : Nat) :
    legLength lam r c =
      (PartI.Ch05.FerrersColumnCells (lam.drop (r + 1)) c).card := by
  unfold legLength
  rw [filter_length_eq_FerrersColumnCells_card]

/-- In a partition, the dropped-column height below a Ferrers cell is the
original column height minus the rows through that cell. -/
theorem FerrersColumnCells_drop_card_of_FerrersCell {lam : List Nat}
    (hpart : IsPartition lam) {r c : Nat} (hcell : FerrersCell lam r c) :
    (PartI.Ch05.FerrersColumnCells (lam.drop (r + 1)) c).card =
      (PartI.Ch05.FerrersColumnCells lam c).card - (r + 1) := by
  have hcol := PartI.Ch05.FerrersColumnCells_eq_range_card hpart c
  have hrmem : r ∈ PartI.Ch05.FerrersColumnCells lam c := by
    rw [PartI.Ch05.mem_FerrersColumnCells_iff]
    exact hcell
  have hrcol : r < (PartI.Ch05.FerrersColumnCells lam c).card := by
    rwa [hcol, Finset.mem_range] at hrmem
  have hdrop_eq : PartI.Ch05.FerrersColumnCells (lam.drop (r + 1)) c =
      Finset.range ((PartI.Ch05.FerrersColumnCells lam c).card - (r + 1)) := by
    ext s
    rw [PartI.Ch05.mem_FerrersColumnCells_iff, Finset.mem_range]
    constructor
    · intro hs
      have hslen : r + 1 + s < lam.length := by
        rw [PartI.Ch05.FerrersCell, List.length_drop] at hs
        omega
      have hscell : PartI.Ch05.FerrersCell lam (r + 1 + s) c := by
        refine ⟨hslen, ?_⟩
        have hsdrop_len := hs.1
        have hsdrop_col := hs.2
        rw [List.getD_eq_getElem (l := lam.drop (r + 1)) (d := 0) hsdrop_len,
          List.getElem_drop] at hsdrop_col
        simpa [List.getD_eq_getElem?_getD, hslen] using hsdrop_col
      have hmem : r + 1 + s ∈ PartI.Ch05.FerrersColumnCells lam c := by
        rwa [PartI.Ch05.mem_FerrersColumnCells_iff]
      rw [hcol, Finset.mem_range] at hmem
      exact Nat.lt_sub_iff_add_lt'.2 hmem
    · intro hs
      have hmem : r + 1 + s ∈ PartI.Ch05.FerrersColumnCells lam c := by
        rw [hcol, Finset.mem_range]
        omega
      rw [PartI.Ch05.mem_FerrersColumnCells_iff] at hmem
      refine ⟨?_, ?_⟩
      · rw [List.length_drop]
        exact Nat.lt_sub_iff_add_lt'.2 hmem.1
      · have hsdrop_len : s < (lam.drop (r + 1)).length := by
          rw [List.length_drop]
          exact Nat.lt_sub_iff_add_lt'.2 hmem.1
        rw [List.getD_eq_getElem (l := lam.drop (r + 1)) (d := 0) hsdrop_len,
          List.getElem_drop]
        simpa [List.getD_eq_getElem?_getD, hmem.1] using hmem.2
  rw [hdrop_eq]
  simp

/-- In a partition, the leg below `(r,c)` is column height minus the rows
through `r`. -/
theorem legLength_eq_column_card_sub_succ_of_FerrersCell {lam : List Nat}
    (hpart : IsPartition lam) {r c : Nat} (hcell : FerrersCell lam r c) :
    legLength lam r c = (PartI.Ch05.FerrersColumnCells lam c).card - (r + 1) := by
  rw [legLength_eq_FerrersColumnCells_drop_card,
    FerrersColumnCells_drop_card_of_FerrersCell hpart hcell]

/-- The `r`-th original row length is the height of column `r` in the
Ferrers conjugate. -/
theorem FerrersColumnCells_FerrersConjugatePartition_card_eq_getD {lam : List Nat}
    (hpart : IsPartition lam) {r : Nat} (hr : r < lam.length) :
    (PartI.Ch05.FerrersColumnCells (PartI.Ch05.FerrersConjugatePartition lam) r).card =
      lam.getD r 0 := by
  have hcol_eq :
      PartI.Ch05.FerrersColumnCells (PartI.Ch05.FerrersConjugatePartition lam) r =
        Finset.range (lam.getD r 0) := by
    ext c
    rw [PartI.Ch05.mem_FerrersColumnCells_iff, Finset.mem_range]
    constructor
    · intro hc
      exact ((PartI.Ch05.FerrersCell_FerrersConjugatePartition_iff hpart).1 hc).2
    · intro hc
      exact (PartI.Ch05.FerrersCell_FerrersConjugatePartition_iff hpart).2 ⟨hr, hc⟩
  rw [hcol_eq]
  simp

/-- Ferrers conjugation preserves hook length at transposed cells, for every
cell of every partition. -/
theorem hookLength_FerrersConjugatePartition_cell {lam : List Nat}
    (hpart : IsPartition lam) {r c : Nat} (hcell : FerrersCell lam r c) :
    FerrersCell (PartI.Ch05.FerrersConjugatePartition lam) c r ∧
      hookLength (PartI.Ch05.FerrersConjugatePartition lam) c r = hookLength lam r c := by
  have hcell' : FerrersCell (PartI.Ch05.FerrersConjugatePartition lam) c r :=
    (PartI.Ch05.FerrersCell_FerrersConjugatePartition_iff hpart).2 hcell
  refine ⟨hcell', ?_⟩
  have hcfirst : c < lam.getD 0 0 :=
    Nat.lt_of_lt_of_le hcell.2 (PartI.Ch05.IsPartition.getD_le_first hpart hcell.1)
  have hrcol : r < (PartI.Ch05.FerrersColumnCells lam c).card := by
    have hmem : r ∈ PartI.Ch05.FerrersColumnCells lam c := by
      rw [PartI.Ch05.mem_FerrersColumnCells_iff]
      exact hcell
    rwa [PartI.Ch05.FerrersColumnCells_eq_range_card hpart c, Finset.mem_range] at hmem
  rw [hookLength_eq_row_sub_col_add_leg_of_FerrersCell hcell',
    hookLength_eq_row_sub_col_add_leg_of_FerrersCell hcell,
    PartI.Ch05.FerrersConjugatePartition_getD_of_lt (lam := lam) hcfirst,
    legLength_eq_column_card_sub_succ_of_FerrersCell hpart hcell,
    legLength_eq_column_card_sub_succ_of_FerrersCell
      (PartI.Ch05.IsPartition_FerrersConjugatePartition lam) hcell',
    FerrersColumnCells_FerrersConjugatePartition_card_eq_getD hpart hcell.1]
  have hrow : c < lam.getD r 0 := hcell.2
  have hA : (PartI.Ch05.FerrersColumnCells lam c).card - r =
      ((PartI.Ch05.FerrersColumnCells lam c).card - (r + 1)) + 1 := by
    omega
  have hB : lam.getD r 0 - c = lam.getD r 0 - (c + 1) + 1 := by
    omega
  rw [hA, hB]
  omega

/-- Hook-divisibility obstructions are invariant under Ferrers conjugation. -/
theorem hasHookDivisibleBy_FerrersConjugatePartition_iff
    {t : Nat} {lam : List Nat} (hpart : IsPartition lam) :
    HasHookDivisibleBy t lam ↔
      HasHookDivisibleBy t (PartI.Ch05.FerrersConjugatePartition lam) := by
  apply hasHookDivisibleBy_FerrersConjugatePartition_iff_of_hookLength_eq hpart
  · intro r c hcell
    exact (hookLength_FerrersConjugatePartition_cell hpart hcell).2
  · intro r c hcell
    have hcell_orig : FerrersCell lam c r :=
      (PartI.Ch05.FerrersCell_FerrersConjugatePartition_iff hpart).1 hcell
    exact (hookLength_FerrersConjugatePartition_cell hpart hcell_orig).2.symm

/-- The hook-length `t`-core predicate is invariant under Ferrers conjugation. -/
theorem isTCoreByHooks_FerrersConjugatePartition_iff
    {t : Nat} {lam : List Nat} (hpart : IsPartition lam) :
    IsTCoreByHooks t lam ↔
      IsTCoreByHooks t (PartI.Ch05.FerrersConjugatePartition lam) := by
  unfold IsTCoreByHooks
  rw [hasHookDivisibleBy_FerrersConjugatePartition_iff hpart]

/-- A partition cannot be a core for the hook length of one of its own cells. -/
theorem not_isTCoreByHooks_hookLength_of_cell {lam : List Nat} {r c : Nat}
    (hcell : FerrersCell lam r c) :
    ¬ IsTCoreByHooks (hookLength lam r c) lam := by
  intro hcore
  exact hcore (hasHookDivisibleBy_hookLength_of_cell hcell)

/-- A displayed hook length `t * k` immediately rules out being a `t`-core. -/
theorem not_isTCoreByHooks_of_hookLength_eq_mul {t : Nat} {lam : List Nat}
    {r c k : Nat} (hcell : FerrersCell lam r c)
    (hhook : hookLength lam r c = t * k) :
    ¬ IsTCoreByHooks t lam := by
  intro hcore
  exact hcore (hasHookDivisibleBy_of_hookLength_eq_mul hcell hhook)

/-- If `lam` is a `t`-core, no cell of `lam` has hook length exactly `t`. -/
theorem hookLength_ne_of_isTCoreByHooks {t : Nat} {lam : List Nat}
    (hcore : IsTCoreByHooks t lam) {r c : Nat} (hcell : FerrersCell lam r c) :
    hookLength lam r c ≠ t := by
  intro h
  apply hcore
  exact hasHookDivisibleBy_of_cell hcell (by rw [h])

/-- A `t`-core has no Ferrers cell whose hook length is divisible by `t`. -/
theorem not_dvd_hookLength_of_isTCoreByHooks {t : Nat} {lam : List Nat}
    (hcore : IsTCoreByHooks t lam) {r c : Nat} (hcell : FerrersCell lam r c) :
    ¬ t ∣ hookLength lam r c := by
  intro hdiv
  exact hcore (hasHookDivisibleBy_of_cell hcell hdiv)

/-- A `t`-core has no cell whose hook length is any displayed multiple of `t`. -/
theorem hookLength_ne_mul_of_isTCoreByHooks {t : Nat} {lam : List Nat}
    (hcore : IsTCoreByHooks t lam) {r c k : Nat} (hcell : FerrersCell lam r c) :
    hookLength lam r c ≠ t * k := by
  intro hmul
  exact (not_dvd_hookLength_of_isTCoreByHooks hcore hcell) ⟨k, hmul⟩

/-- Hook-divisibility obstructions are downward closed under divisibility of
the modulus. -/
theorem hasHookDivisibleBy_of_dvd {t u : Nat} {lam : List Nat}
    (htu : t ∣ u) (h : HasHookDivisibleBy u lam) :
    HasHookDivisibleBy t lam := by
  rcases h with ⟨r, c, hcell, hdiv⟩
  exact ⟨r, c, hcell, dvd_trans htu hdiv⟩

/-- A hook divisible by `lcm t u` is in particular divisible by `t`. -/
theorem hasHookDivisibleBy_left_of_lcm {t u : Nat} {lam : List Nat}
    (h : HasHookDivisibleBy (Nat.lcm t u) lam) :
    HasHookDivisibleBy t lam :=
  hasHookDivisibleBy_of_dvd (dvd_lcm_left t u) h

/-- A hook divisible by `lcm t u` is in particular divisible by `u`. -/
theorem hasHookDivisibleBy_right_of_lcm {t u : Nat} {lam : List Nat}
    (h : HasHookDivisibleBy (Nat.lcm t u) lam) :
    HasHookDivisibleBy u lam :=
  hasHookDivisibleBy_of_dvd (dvd_lcm_right t u) h

/-- Package both projections of an `lcm t u` hook obstruction. -/
theorem hasHookDivisibleBy_pair_of_lcm {t u : Nat} {lam : List Nat}
    (h : HasHookDivisibleBy (Nat.lcm t u) lam) :
    HasHookDivisibleBy t lam ∧ HasHookDivisibleBy u lam :=
  ⟨hasHookDivisibleBy_left_of_lcm h, hasHookDivisibleBy_right_of_lcm h⟩

/-- Any `t` hook obstruction is also a `gcd t u` hook obstruction. -/
theorem hasHookDivisibleBy_gcd_of_left {t u : Nat} {lam : List Nat}
    (h : HasHookDivisibleBy t lam) :
    HasHookDivisibleBy (Nat.gcd t u) lam :=
  hasHookDivisibleBy_of_dvd (Nat.gcd_dvd_left t u) h

/-- Any `u` hook obstruction is also a `gcd t u` hook obstruction. -/
theorem hasHookDivisibleBy_gcd_of_right {t u : Nat} {lam : List Nat}
    (h : HasHookDivisibleBy u lam) :
    HasHookDivisibleBy (Nat.gcd t u) lam :=
  hasHookDivisibleBy_of_dvd (Nat.gcd_dvd_right t u) h

/-- If a partition has no hook length divisible by `t`, then it has no hook
length divisible by any multiple of `t`. -/
theorem IsTCoreByHooks.of_dvd {t u : Nat} {lam : List Nat}
    (hcore : IsTCoreByHooks t lam) (htu : t ∣ u) :
    IsTCoreByHooks u lam := by
  intro hu
  exact hcore (hasHookDivisibleBy_of_dvd htu hu)

/-- Being a `t`-core implies being an `lcm t u`-core: any hook divisible by
the lcm is in particular divisible by `t`. -/
theorem IsTCoreByHooks.lcm_left {t u : Nat} {lam : List Nat}
    (hcore : IsTCoreByHooks t lam) :
    IsTCoreByHooks (Nat.lcm t u) lam :=
  IsTCoreByHooks.of_dvd hcore (dvd_lcm_left t u)

/-- Being a `u`-core implies being an `lcm t u`-core. -/
theorem IsTCoreByHooks.lcm_right {t u : Nat} {lam : List Nat}
    (hcore : IsTCoreByHooks u lam) :
    IsTCoreByHooks (Nat.lcm t u) lam :=
  IsTCoreByHooks.of_dvd hcore (dvd_lcm_right t u)

/-- Being a `gcd t u`-core implies being a `t`-core. -/
theorem IsTCoreByHooks.gcd_left {t u : Nat} {lam : List Nat}
    (hcore : IsTCoreByHooks (Nat.gcd t u) lam) :
    IsTCoreByHooks t lam :=
  IsTCoreByHooks.of_dvd hcore (Nat.gcd_dvd_left t u)

/-- Being a `gcd t u`-core implies being a `u`-core. -/
theorem IsTCoreByHooks.gcd_right {t u : Nat} {lam : List Nat}
    (hcore : IsTCoreByHooks (Nat.gcd t u) lam) :
    IsTCoreByHooks u lam :=
  IsTCoreByHooks.of_dvd hcore (Nat.gcd_dvd_right t u)

/-- Package the two consequences of being a `gcd t u`-core. -/
theorem IsTCoreByHooks.gcd_pair {t u : Nat} {lam : List Nat}
    (hcore : IsTCoreByHooks (Nat.gcd t u) lam) :
    IsTCoreByHooks t lam ∧ IsTCoreByHooks u lam :=
  ⟨IsTCoreByHooks.gcd_left hcore, IsTCoreByHooks.gcd_right hcore⟩

/-- Contrapositive monotonicity: if `t ∣ u` and a partition is not a
`u`-core, then it is not a `t`-core. -/
theorem not_isTCoreByHooks_of_dvd_not_isTCoreByHooks {t u : Nat} {lam : List Nat}
    (htu : t ∣ u) (hnot : ¬ IsTCoreByHooks u lam) :
    ¬ IsTCoreByHooks t lam := by
  intro hcore
  exact hnot (IsTCoreByHooks.of_dvd hcore htu)

/-- If a partition is not an `lcm t u`-core, then it is not a `t`-core. -/
theorem not_isTCoreByHooks_left_of_not_lcm {t u : Nat} {lam : List Nat}
    (hnot : ¬ IsTCoreByHooks (Nat.lcm t u) lam) :
    ¬ IsTCoreByHooks t lam :=
  not_isTCoreByHooks_of_dvd_not_isTCoreByHooks (dvd_lcm_left t u) hnot

/-- If a partition is not an `lcm t u`-core, then it is not a `u`-core. -/
theorem not_isTCoreByHooks_right_of_not_lcm {t u : Nat} {lam : List Nat}
    (hnot : ¬ IsTCoreByHooks (Nat.lcm t u) lam) :
    ¬ IsTCoreByHooks u lam :=
  not_isTCoreByHooks_of_dvd_not_isTCoreByHooks (dvd_lcm_right t u) hnot

/-- If a partition is not a `t`-core, then it is not a `gcd t u`-core. -/
theorem not_isTCoreByHooks_gcd_of_not_left {t u : Nat} {lam : List Nat}
    (hnot : ¬ IsTCoreByHooks t lam) :
    ¬ IsTCoreByHooks (Nat.gcd t u) lam :=
  not_isTCoreByHooks_of_dvd_not_isTCoreByHooks (Nat.gcd_dvd_left t u) hnot

/-- If a partition is not a `u`-core, then it is not a `gcd t u`-core. -/
theorem not_isTCoreByHooks_gcd_of_not_right {t u : Nat} {lam : List Nat}
    (hnot : ¬ IsTCoreByHooks u lam) :
    ¬ IsTCoreByHooks (Nat.gcd t u) lam :=
  not_isTCoreByHooks_of_dvd_not_isTCoreByHooks (Nat.gcd_dvd_right t u) hnot

/-- A hook obstruction immediately rules out being a `t`-core. -/
theorem not_isTCoreByHooks_of_hasHook {t : Nat} {lam : List Nat}
    (h : HasHookDivisibleBy t lam) :
    ¬ IsTCoreByHooks t lam := by
  intro hcore
  exact hcore h

/-- Negating the hook-core predicate is exactly exhibiting a hook obstruction. -/
theorem not_isTCoreByHooks_iff_hasHookDivisibleBy (t : Nat) (lam : List Nat) :
    ¬ IsTCoreByHooks t lam ↔ HasHookDivisibleBy t lam := by
  unfold IsTCoreByHooks
  tauto

/-- Zero cannot divide any hook length, since hook lengths are positive. -/
theorem not_zero_dvd_hookLength (lam : List Nat) (r c : Nat) :
    ¬ 0 ∣ hookLength lam r c := by
  intro hdiv
  rcases hdiv with ⟨k, hk⟩
  apply hookLength_ne_zero lam r c
  simpa using hk

/-- In the raw divisibility predicate, no partition has a hook length divisible
by zero. -/
theorem not_hasHookDivisibleBy_zero (lam : List Nat) :
    ¬ HasHookDivisibleBy 0 lam := by
  intro h
  rcases h with ⟨r, c, _hcell, hdiv⟩
  exact not_zero_dvd_hookLength lam r c hdiv

/-- The hook-divisibility definition makes every partition a `0`-core
vacuously. Meaningful t-core applications use positive `t`; this lemma records
the boundary behavior of the formal predicate. -/
theorem zeroCoreByHooks (lam : List Nat) :
    IsTCoreByHooks 0 lam :=
  not_hasHookDivisibleBy_zero lam

/-- A partition is `t`-core exactly when none of its Ferrers hook lengths is
divisible by `t`. This packages the hook-length characterization used in
Chan Chapter 18. -/
theorem tCore_hookLength_characterization (t : Nat) (lam : List Nat) :
    IsTCoreByHooks t lam ↔
      ∀ r c, FerrersCell lam r c → ¬ t ∣ hookLength lam r c := by
  unfold IsTCoreByHooks HasHookDivisibleBy
  constructor
  · intro h r c hcell hdiv
    exact h ⟨r, c, hcell, hdiv⟩
  · intro h hdiv
    rcases hdiv with ⟨r, c, hcell, hhook⟩
    exact h r c hcell hhook

/-- Equivalently, a `t`-core has no hook length equal to any displayed
multiple `t * k`. This form avoids repeatedly unpacking divisibility in
finite hook-length arguments. -/
theorem tCore_hookLength_ne_mul_characterization (t : Nat) (lam : List Nat) :
    IsTCoreByHooks t lam ↔
      ∀ r c k, FerrersCell lam r c → hookLength lam r c ≠ t * k := by
  rw [tCore_hookLength_characterization]
  constructor
  · intro h r c k hcell heq
    exact h r c hcell ⟨k, heq⟩
  · intro h r c hcell hdiv
    rcases hdiv with ⟨k, hk⟩
    exact h r c k hcell hk

/-- A positive natural number strictly below `t` is not divisible by `t`. -/
theorem not_dvd_of_pos_lt {t n : Nat} (hn : 0 < n) (hnt : n < t) :
    ¬ t ∣ n := by
  intro hdiv
  have hle : t ≤ n := Nat.le_of_dvd hn hdiv
  omega

/-- If every Ferrers hook length is strictly below `t`, there is no
hook-divisibility obstruction by `t`. -/
theorem not_hasHookDivisibleBy_of_hookLength_lt {t : Nat} {lam : List Nat}
    (hbound : ∀ r c, FerrersCell lam r c → hookLength lam r c < t) :
    ¬ HasHookDivisibleBy t lam := by
  intro h
  rcases h with ⟨r, c, hcell, hdiv⟩
  exact not_dvd_of_pos_lt (hookLength_pos lam r c) (hbound r c hcell) hdiv

/-- A partition is a `t`-core if all of its hook lengths are strictly below
`t`. This is a convenient finite sufficient criterion for small examples. -/
theorem isTCoreByHooks_of_hookLength_lt {t : Nat} {lam : List Nat}
    (hbound : ∀ r c, FerrersCell lam r c → hookLength lam r c < t) :
    IsTCoreByHooks t lam := by
  rw [tCore_hookLength_characterization]
  intro r c hcell hdiv
  exact not_dvd_of_pos_lt (hookLength_pos lam r c) (hbound r c hcell) hdiv

/-- If all Ferrers hook lengths are bounded by `B < t`, there is no
hook-divisibility obstruction by `t`. -/
theorem not_hasHookDivisibleBy_of_hookLength_le_bound {t B : Nat} {lam : List Nat}
    (hB : B < t)
    (hbound : ∀ r c, FerrersCell lam r c → hookLength lam r c ≤ B) :
    ¬ HasHookDivisibleBy t lam := by
  apply not_hasHookDivisibleBy_of_hookLength_lt
  intro r c hcell
  exact Nat.lt_of_le_of_lt (hbound r c hcell) hB

/-- A partition is a `t`-core if all hook lengths are bounded above by some
`B < t`. -/
theorem isTCoreByHooks_of_hookLength_le_bound {t B : Nat} {lam : List Nat}
    (hB : B < t)
    (hbound : ∀ r c, FerrersCell lam r c → hookLength lam r c ≤ B) :
    IsTCoreByHooks t lam := by
  rw [tCore_hookLength_characterization]
  intro r c hcell hdiv
  exact not_dvd_of_pos_lt (hookLength_pos lam r c)
    (Nat.lt_of_le_of_lt (hbound r c hcell) hB) hdiv

/-- A cell-free Ferrers diagram is a `t`-core for every modulus. -/
theorem isTCoreByHooks_of_no_FerrersCell {t : Nat} {lam : List Nat}
    (hcellless : ∀ r c, ¬ FerrersCell lam r c) :
    IsTCoreByHooks t lam := by
  rw [tCore_hookLength_characterization]
  intro r c hcell _hdiv
  exact hcellless r c hcell

/-- The empty partition is a `t`-core for every `t`: it has no Ferrers cells
and hence no hook-length obstruction. -/
theorem nilCoreByHooks (t : Nat) :
    IsTCoreByHooks t [] := by
  rw [tCore_hookLength_characterization]
  intro r c hcell _hdiv
  simp [FerrersCell, PartI.Ch05.FerrersCell] at hcell

/-- In the hook-length characterization, `1`-cores are exactly partitions with
no Ferrers cells. This isolates the boundary case where every hook length is
divisible by `1`. -/
theorem oneCoreByHooks_iff_no_FerrersCell (lam : List Nat) :
    IsTCoreByHooks 1 lam ↔ ∀ r c, ¬ FerrersCell lam r c := by
  rw [tCore_hookLength_characterization]
  constructor
  · intro h r c hcell
    exact h r c hcell (Nat.one_dvd _)
  · intro h r c hcell _hdiv
    exact h r c hcell

/-- For list partitions with positive displayed parts, being a `1`-core is
equivalent to being the empty partition. -/
theorem oneCoreByHooks_iff_eq_nil_of_positive {lam : List Nat}
    (hpos : PartI.Ch05.PositiveParts lam) :
    IsTCoreByHooks 1 lam ↔ lam = [] := by
  constructor
  · intro hcore
    cases lam with
    | nil =>
        rfl
    | cons n tail =>
        have hn : 0 < n := hpos n (by simp)
        have hcell : FerrersCell (n :: tail) 0 0 := by
          exact ⟨by simp, by simpa [FerrersCell, PartI.Ch05.FerrersCell] using hn⟩
        exact False.elim (hcore (hasHookDivisibleBy_of_cell hcell (Nat.one_dvd _)))
  · intro hnil
    rw [hnil]
    exact nilCoreByHooks 1

/-- For `t = 1`, hook-divisibility obstructions are exactly Ferrers cells:
every positive hook length is divisible by `1`. -/
theorem hasHookDivisibleBy_one_iff_exists_FerrersCell (lam : List Nat) :
    HasHookDivisibleBy 1 lam ↔ ∃ r c, FerrersCell lam r c := by
  constructor
  · intro h
    rcases h with ⟨r, c, hcell, _hdiv⟩
    exact ⟨r, c, hcell⟩
  · rintro ⟨r, c, hcell⟩
    exact hasHookDivisibleBy_of_cell hcell (Nat.one_dvd _)

/-- Any Ferrers cell obstructs being a `1`-core. -/
theorem not_oneCoreByHooks_of_FerrersCell {lam : List Nat} {r c : Nat}
    (hcell : FerrersCell lam r c) :
    ¬ IsTCoreByHooks 1 lam :=
  not_isTCoreByHooks_of_hasHook (hasHookDivisibleBy_of_cell hcell (Nat.one_dvd _))

/-- A positive first row gives the top-left Ferrers cell. -/
theorem FerrersCell_cons_zero_zero {n : Nat} {tail : List Nat} (hn : 0 < n) :
    FerrersCell (n :: tail) 0 0 := by
  exact ⟨by simp, by simpa [FerrersCell, PartI.Ch05.FerrersCell] using hn⟩

/-- Any list-partition with positive first part is not a `1`-core in the
hook-length sense. -/
theorem not_oneCoreByHooks_cons_pos {n : Nat} {tail : List Nat} (hn : 0 < n) :
    ¬ IsTCoreByHooks 1 (n :: tail) :=
  not_oneCoreByHooks_of_FerrersCell (FerrersCell_cons_zero_zero (tail := tail) hn)

/-- Failing to be a `1`-core is exactly having at least one Ferrers cell. -/
theorem not_oneCoreByHooks_iff_exists_FerrersCell (lam : List Nat) :
    ¬ IsTCoreByHooks 1 lam ↔ ∃ r c, FerrersCell lam r c := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    rw [oneCoreByHooks_iff_no_FerrersCell]
    intro r c hcell
    exact hnone ⟨r, c, hcell⟩
  · rintro ⟨r, c, hcell⟩
    exact not_oneCoreByHooks_of_FerrersCell hcell

/-- The number of staircase rows whose length is greater than a fixed column
index `c`. This is the row-count input for general staircase hook lengths. -/
theorem filter_staircasePartition_length (n c : Nat) :
    ((PartI.Ch05.staircasePartition n).filter (fun rowLength => c < rowLength)).length =
      n - c := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      by_cases hc : c < n + 1
      · simp [PartI.Ch05.staircasePartition, hc, ih]
        omega
      · simp [PartI.Ch05.staircasePartition, hc, ih]
        omega

/-- In a staircase partition, the leg below `(r,c)` has the expected
triangular length. -/
theorem legLength_staircasePartition (n r c : Nat)
    (hcell : FerrersCell (PartI.Ch05.staircasePartition n) r c) :
    legLength (PartI.Ch05.staircasePartition n) r c = n - c - (r + 1) := by
  induction n generalizing r c with
  | zero =>
      simp [FerrersCell, PartI.Ch05.FerrersCell] at hcell
  | succ n ih =>
      cases r with
      | zero =>
          simp [legLength, PartI.Ch05.staircasePartition, filter_staircasePartition_length]
          rw [FerrersCell, PartI.Ch05.FerrersCell, PartI.Ch05.staircasePartition_length,
            PartI.Ch05.staircasePartition_getD_of_lt hcell.1] at hcell
          omega
      | succ r =>
          have htail : FerrersCell (PartI.Ch05.staircasePartition n) r c := by
            simpa [FerrersCell, PartI.Ch05.FerrersCell, PartI.Ch05.staircasePartition] using hcell
          have ih' := ih r c htail
          simp [legLength, PartI.Ch05.staircasePartition] at ih' ⊢
          rw [ih']
          have hc : c < n - r := by
            rw [FerrersCell, PartI.Ch05.FerrersCell, PartI.Ch05.staircasePartition_length,
              PartI.Ch05.staircasePartition_getD_of_lt htail.1] at htail
            exact htail.2
          omega

/-- General hook-length formula for staircase Ferrers diagrams. -/
theorem hookLength_staircasePartition (n r c : Nat)
    (hcell : FerrersCell (PartI.Ch05.staircasePartition n) r c) :
    hookLength (PartI.Ch05.staircasePartition n) r c = 2 * (n - r - c) - 1 := by
  rw [hookLength_eq_row_sub_col_add_leg_of_FerrersCell hcell,
    legLength_staircasePartition n r c hcell]
  have hrn : r < n := by simpa [PartI.Ch05.staircasePartition_length] using hcell.1
  have hrow := PartI.Ch05.staircasePartition_getD_of_lt (n := n) (r := r) hrn
  rw [hrow]
  rw [FerrersCell, PartI.Ch05.FerrersCell, PartI.Ch05.staircasePartition_length,
    PartI.Ch05.staircasePartition_getD_of_lt hrn] at hcell
  omega

/-- Staircase Ferrers diagrams preserve hook lengths under transposition of a
cell. This is the general version of the `[3,2,1]` transpose check. -/
theorem hookLength_staircasePartition_transpose_cell (n r c : Nat)
    (hcell : FerrersCell (PartI.Ch05.staircasePartition n) r c) :
    FerrersCell (PartI.Ch05.staircasePartition n) c r ∧
      hookLength (PartI.Ch05.staircasePartition n) c r =
        hookLength (PartI.Ch05.staircasePartition n) r c := by
  have hcell' : FerrersCell (PartI.Ch05.staircasePartition n) c r := by
    rw [FerrersCell, PartI.Ch05.FerrersCell, PartI.Ch05.staircasePartition_length,
      PartI.Ch05.staircasePartition_getD_of_lt]
    · rw [FerrersCell, PartI.Ch05.FerrersCell, PartI.Ch05.staircasePartition_length,
        PartI.Ch05.staircasePartition_getD_of_lt hcell.1] at hcell
      constructor <;> omega
    · rw [FerrersCell, PartI.Ch05.FerrersCell, PartI.Ch05.staircasePartition_length,
        PartI.Ch05.staircasePartition_getD_of_lt hcell.1] at hcell
      omega
  refine ⟨hcell', ?_⟩
  rw [hookLength_staircasePartition n c r hcell',
    hookLength_staircasePartition n r c hcell]
  omega

/-- Every hook in the staircase partition of height `n` has length less than
`2 * n`. -/
theorem hookLength_staircasePartition_lt_two_mul (n r c : Nat)
    (hcell : FerrersCell (PartI.Ch05.staircasePartition n) r c) :
    hookLength (PartI.Ch05.staircasePartition n) r c < 2 * n := by
  rw [hookLength_staircasePartition n r c hcell]
  rw [FerrersCell, PartI.Ch05.FerrersCell, PartI.Ch05.staircasePartition_length,
    PartI.Ch05.staircasePartition_getD_of_lt hcell.1] at hcell
  omega

/-- Equivalently, every staircase hook length is at most `2n - 1`. -/
theorem hookLength_staircasePartition_le_two_mul_sub_one (n r c : Nat)
    (hcell : FerrersCell (PartI.Ch05.staircasePartition n) r c) :
    hookLength (PartI.Ch05.staircasePartition n) r c ≤ 2 * n - 1 := by
  have hlt := hookLength_staircasePartition_lt_two_mul n r c hcell
  have hn : 0 < n := by
    have hrn : r < n := by
      simpa [PartI.Ch05.staircasePartition_length] using hcell.1
    omega
  omega

/-- Every hook length in a staircase partition is odd; in particular it is not
divisible by `2`. -/
theorem not_two_dvd_hookLength_staircasePartition (n r c : Nat)
    (hcell : FerrersCell (PartI.Ch05.staircasePartition n) r c) :
    ¬ 2 ∣ hookLength (PartI.Ch05.staircasePartition n) r c := by
  have hcell_orig := hcell
  have hpos : 0 < n - r - c := by
    rw [FerrersCell, PartI.Ch05.FerrersCell, PartI.Ch05.staircasePartition_length,
      PartI.Ch05.staircasePartition_getD_of_lt hcell.1] at hcell
    omega
  rw [hookLength_staircasePartition n r c hcell_orig]
  intro hdiv
  rcases hdiv with ⟨k, hk⟩
  omega

/-- Every staircase partition is a `2`-core in the hook-length sense. -/
theorem isTCoreByHooks_two_staircasePartition (n : Nat) :
    IsTCoreByHooks 2 (PartI.Ch05.staircasePartition n) := by
  rw [tCore_hookLength_characterization]
  intro r c hcell hdiv
  exact not_two_dvd_hookLength_staircasePartition n r c hcell hdiv

/-- More generally, every staircase partition is a `t`-core whenever `t` is
even, since all staircase hooks are odd. -/
theorem isTCoreByHooks_staircasePartition_of_two_dvd {n t : Nat} (ht : 2 ∣ t) :
    IsTCoreByHooks t (PartI.Ch05.staircasePartition n) := by
  rw [tCore_hookLength_characterization]
  intro r c hcell hdiv
  exact not_two_dvd_hookLength_staircasePartition n r c hcell (dvd_trans ht hdiv)

/-- A staircase partition of height `n` is automatically a `t`-core by hooks
whenever `t ≥ 2n`, because all its hook lengths are smaller than `t`. -/
theorem isTCoreByHooks_staircasePartition_of_two_mul_le {n t : Nat} (ht : 2 * n ≤ t) :
    IsTCoreByHooks t (PartI.Ch05.staircasePartition n) := by
  apply isTCoreByHooks_of_hookLength_lt
  intro r c hcell
  exact Nat.lt_of_lt_of_le (hookLength_staircasePartition_lt_two_mul n r c hcell) ht

/-- The upper-left cell exists in every positive-height staircase. -/
theorem FerrersCell_staircasePartition_zero_zero {n : Nat} (hn : 0 < n) :
    FerrersCell (PartI.Ch05.staircasePartition n) 0 0 := by
  rw [FerrersCell, PartI.Ch05.FerrersCell, PartI.Ch05.staircasePartition_length,
    PartI.Ch05.staircasePartition_getD_of_lt hn]
  constructor <;> omega

/-- The largest hook in the staircase of positive height `n` is the upper-left
hook of length `2n - 1`. -/
theorem hookLength_staircasePartition_zero_zero {n : Nat} (hn : 0 < n) :
    hookLength (PartI.Ch05.staircasePartition n) 0 0 = 2 * n - 1 := by
  have hcell := FerrersCell_staircasePartition_zero_zero hn
  rw [hookLength_staircasePartition n 0 0 hcell]
  omega

/-- The top row of a staircase contains a cell whose hook length is
`2k + 1`, for every `k < n`. -/
theorem FerrersCell_staircasePartition_zero_sub_succ {n k : Nat} (hk : k < n) :
    FerrersCell (PartI.Ch05.staircasePartition n) 0 (n - (k + 1)) := by
  have hn : 0 < n := by omega
  rw [FerrersCell, PartI.Ch05.FerrersCell, PartI.Ch05.staircasePartition_length,
    PartI.Ch05.staircasePartition_getD_of_lt hn]
  constructor <;> omega

/-- The staircase hook lengths realize every positive odd number up to
`2n - 1` along the first row. -/
theorem hookLength_staircasePartition_zero_sub_succ {n k : Nat} (hk : k < n) :
    hookLength (PartI.Ch05.staircasePartition n) 0 (n - (k + 1)) = 2 * k + 1 := by
  have hcell := FerrersCell_staircasePartition_zero_sub_succ (n := n) (k := k) hk
  rw [hookLength_staircasePartition n 0 (n - (k + 1)) hcell]
  omega

/-- Every positive odd number `2k+1` with `k < n` is itself a staircase hook,
so it supplies a hook-divisibility obstruction. -/
theorem hasHookDivisibleBy_odd_staircasePartition_of_lt {n k : Nat} (hk : k < n) :
    HasHookDivisibleBy (2 * k + 1) (PartI.Ch05.staircasePartition n) := by
  rw [← hookLength_staircasePartition_zero_sub_succ (n := n) (k := k) hk]
  exact hasHookDivisibleBy_hookLength_of_cell
    (FerrersCell_staircasePartition_zero_sub_succ (n := n) (k := k) hk)

/-- Consequently, a staircase of height `n` is not a `(2k+1)`-core when
`k < n`. -/
theorem not_isTCoreByHooks_odd_staircasePartition_of_lt {n k : Nat} (hk : k < n) :
    ¬ IsTCoreByHooks (2 * k + 1) (PartI.Ch05.staircasePartition n) :=
  not_isTCoreByHooks_of_hasHook
    (hasHookDivisibleBy_odd_staircasePartition_of_lt (n := n) (k := k) hk)

/-- For odd moduli written as `2k+1`, the staircase core condition is exactly
the absence of the corresponding first-row hook. -/
theorem isTCoreByHooks_odd_staircasePartition_iff_le (n k : Nat) :
    IsTCoreByHooks (2 * k + 1) (PartI.Ch05.staircasePartition n) ↔ n ≤ k := by
  constructor
  · intro hcore
    by_contra hnot
    have hk : k < n := Nat.lt_of_not_ge hnot
    exact not_isTCoreByHooks_odd_staircasePartition_of_lt (n := n) (k := k) hk hcore
  · intro hle
    apply isTCoreByHooks_staircasePartition_of_two_mul_le
    omega

/-- Complete hook-length criterion for staircase partitions: a staircase of
height `n` is a `t`-core exactly when `t` is even or no hook can reach `t`. -/
theorem isTCoreByHooks_staircasePartition_iff (n t : Nat) :
    IsTCoreByHooks t (PartI.Ch05.staircasePartition n) ↔ 2 ∣ t ∨ 2 * n ≤ t := by
  constructor
  · intro hcore
    by_cases ht_even : 2 ∣ t
    · exact Or.inl ht_even
    · right
      by_contra hnot
      have htlt : t < 2 * n := Nat.lt_of_not_ge hnot
      let k := t / 2
      have hmod : t % 2 = 1 := (Nat.two_dvd_ne_zero).1 ht_even
      have ht_eq : t = 2 * k + 1 := by
        have h := Nat.div_add_mod t 2
        rw [hmod] at h
        omega
      have hk : k < n := by
        omega
      have hcore_odd :
          IsTCoreByHooks (2 * k + 1) (PartI.Ch05.staircasePartition n) := by
        simpa [ht_eq] using hcore
      exact not_isTCoreByHooks_odd_staircasePartition_of_lt
        (n := n) (k := k) hk hcore_odd
  · rintro (ht_even | hge)
    · exact isTCoreByHooks_staircasePartition_of_two_dvd ht_even
    · exact isTCoreByHooks_staircasePartition_of_two_mul_le hge

/-- Exact hook-length spectrum of a staircase, ignoring multiplicities: a
number appears as a hook length iff it is odd and below `2n`. -/
theorem exists_FerrersCell_hookLength_staircasePartition_iff (n t : Nat) :
    (∃ r c, FerrersCell (PartI.Ch05.staircasePartition n) r c ∧
      hookLength (PartI.Ch05.staircasePartition n) r c = t) ↔
      ¬ 2 ∣ t ∧ t < 2 * n := by
  constructor
  · rintro ⟨r, c, hcell, hhook⟩
    constructor
    · intro ht
      exact not_two_dvd_hookLength_staircasePartition n r c hcell (by rwa [hhook])
    · rw [← hhook]
      exact hookLength_staircasePartition_lt_two_mul n r c hcell
  · rintro ⟨htodd, hlt⟩
    let k := t / 2
    have hmod : t % 2 = 1 := (Nat.two_dvd_ne_zero).1 htodd
    have ht_eq : t = 2 * k + 1 := by
      have h := Nat.div_add_mod t 2
      rw [hmod] at h
      omega
    have hk : k < n := by
      omega
    exact ⟨0, n - (k + 1), FerrersCell_staircasePartition_zero_sub_succ (n := n) hk,
      by rw [hookLength_staircasePartition_zero_sub_succ (n := n) (k := k) hk, ht_eq]⟩

/-- Cells in a staircase whose hook length is exactly `t`. -/
def StaircaseHookCellsOfLength (n t : Nat) : Finset (Nat × Nat) :=
  (PartI.Ch05.FerrersDiagramCells (PartI.Ch05.staircasePartition n)).filter
    (fun cell => hookLength (PartI.Ch05.staircasePartition n) cell.1 cell.2 = t)

/-- Membership in `StaircaseHookCellsOfLength` is exactly the Ferrers-cell
predicate together with the requested hook length. -/
theorem mem_StaircaseHookCellsOfLength_iff {n t : Nat} {cell : Nat × Nat} :
    cell ∈ StaircaseHookCellsOfLength n t ↔
      FerrersCell (PartI.Ch05.staircasePartition n) cell.1 cell.2 ∧
        hookLength (PartI.Ch05.staircasePartition n) cell.1 cell.2 = t := by
  unfold StaircaseHookCellsOfLength
  rw [Finset.mem_filter, PartI.Ch05.mem_FerrersDiagramCells_iff]

/-- The cells with staircase hook length `2k+1` lie on one antidiagonal. -/
theorem StaircaseHookCellsOfLength_odd_eq_antidiagonal {n k : Nat} (hk : k < n) :
    StaircaseHookCellsOfLength n (2 * k + 1) =
      Finset.antidiagonal (n - (k + 1)) := by
  ext cell
  rw [mem_StaircaseHookCellsOfLength_iff, Finset.mem_antidiagonal]
  constructor
  · rintro ⟨hcell, hhook⟩
    have hformula := hookLength_staircasePartition n cell.1 cell.2 hcell
    have hsum_lt : cell.1 + cell.2 < n := by
      rw [FerrersCell, PartI.Ch05.FerrersCell, PartI.Ch05.staircasePartition_length,
        PartI.Ch05.staircasePartition_getD_of_lt hcell.1] at hcell
      omega
    rw [hformula] at hhook
    omega
  · intro hsum
    have hcell : FerrersCell (PartI.Ch05.staircasePartition n) cell.1 cell.2 := by
      rw [FerrersCell, PartI.Ch05.FerrersCell, PartI.Ch05.staircasePartition_length,
        PartI.Ch05.staircasePartition_getD_of_lt]
      · constructor <;> omega
      · omega
    refine ⟨hcell, ?_⟩
    rw [hookLength_staircasePartition n cell.1 cell.2 hcell]
    omega

/-- The hook length `2k+1` occurs in the staircase of height `n` with
multiplicity `n-k`. -/
theorem StaircaseHookCellsOfLength_odd_card {n k : Nat} (hk : k < n) :
    (StaircaseHookCellsOfLength n (2 * k + 1)).card = n - k := by
  rw [StaircaseHookCellsOfLength_odd_eq_antidiagonal (n := n) (k := k) hk,
    Finset.Nat.card_antidiagonal]
  omega

/-- A hook-length layer in a staircase is empty exactly for even lengths or
lengths beyond the largest possible hook. -/
theorem StaircaseHookCellsOfLength_eq_empty_iff (n t : Nat) :
    StaircaseHookCellsOfLength n t = ∅ ↔ 2 ∣ t ∨ 2 * n ≤ t := by
  constructor
  · intro hempty
    by_contra hnot
    have hoddlt : ¬ 2 ∣ t ∧ t < 2 * n := by
      constructor
      · intro ht
        exact hnot (Or.inl ht)
      · exact Nat.lt_of_not_ge (by intro hge; exact hnot (Or.inr hge))
    rcases (exists_FerrersCell_hookLength_staircasePartition_iff n t).2 hoddlt with
      ⟨r, c, hcell, hhook⟩
    have hmem : (r, c) ∈ StaircaseHookCellsOfLength n t := by
      rw [mem_StaircaseHookCellsOfLength_iff]
      exact ⟨hcell, hhook⟩
    rw [hempty] at hmem
    simp at hmem
  · intro hcrit
    ext cell
    rw [mem_StaircaseHookCellsOfLength_iff]
    constructor
    · rintro ⟨hcell, hhook⟩
      have hoddlt := (exists_FerrersCell_hookLength_staircasePartition_iff n t).1
        ⟨cell.1, cell.2, hcell, hhook⟩
      rcases hcrit with ht_even | hge
      · exact False.elim (hoddlt.1 ht_even)
      · omega
    · intro hfalse
      simp at hfalse

/-- Cardinal form of `StaircaseHookCellsOfLength_eq_empty_iff`. -/
theorem StaircaseHookCellsOfLength_card_eq_zero_iff (n t : Nat) :
    (StaircaseHookCellsOfLength n t).card = 0 ↔ 2 ∣ t ∨ 2 * n ≤ t := by
  rw [← StaircaseHookCellsOfLength_eq_empty_iff n t, Finset.card_eq_zero]

/-- Unconditional multiplicity of the odd hook length `2k+1` in a staircase:
it occurs `n-k` times, with the natural subtraction giving zero past the top
hook. -/
theorem StaircaseHookCellsOfLength_odd_card_eq_sub (n k : Nat) :
    (StaircaseHookCellsOfLength n (2 * k + 1)).card = n - k := by
  by_cases hk : k < n
  · exact StaircaseHookCellsOfLength_odd_card (n := n) (k := k) hk
  · have hzero :
        (StaircaseHookCellsOfLength n (2 * k + 1)).card = 0 := by
      rw [StaircaseHookCellsOfLength_card_eq_zero_iff]
      exact Or.inr (by omega)
    rw [hzero]
    omega

/-- Even hook-length layers are empty in staircase partitions. -/
theorem StaircaseHookCellsOfLength_even_eq_empty (n k : Nat) :
    StaircaseHookCellsOfLength n (2 * k) = ∅ := by
  rw [StaircaseHookCellsOfLength_eq_empty_iff]
  exact Or.inl ⟨k, rfl⟩

/-- Even hook lengths occur with multiplicity zero in staircase partitions. -/
theorem StaircaseHookCellsOfLength_even_card (n k : Nat) :
    (StaircaseHookCellsOfLength n (2 * k)).card = 0 := by
  rw [StaircaseHookCellsOfLength_card_eq_zero_iff]
  exact Or.inl ⟨k, rfl⟩

/-- Unified cardinal formula for staircase hook-length layers. Odd hook length
`t` occurs `n - t/2` times; even hook lengths occur zero times. -/
theorem StaircaseHookCellsOfLength_card_eq_if (n t : Nat) :
    (StaircaseHookCellsOfLength n t).card =
      if 2 ∣ t then 0 else n - t / 2 := by
  by_cases ht : 2 ∣ t
  · have hzero : (StaircaseHookCellsOfLength n t).card = 0 := by
      rw [StaircaseHookCellsOfLength_card_eq_zero_iff]
      exact Or.inl ht
    simp [ht, hzero]
  · let k := t / 2
    have hmod : t % 2 = 1 := (Nat.two_dvd_ne_zero).1 ht
    have ht_eq : t = 2 * k + 1 := by
      have h := Nat.div_add_mod t 2
      rw [hmod] at h
      omega
    have hhalf : (2 * k + 1) / 2 = k := by
      rw [show 2 * k + 1 = 1 + 2 * k by omega]
      rw [Nat.add_mul_div_left 1 k (by decide : 0 < 2)]
      norm_num
    have hodd : ¬ 2 ∣ 2 * k + 1 := by
      simpa [← ht_eq] using ht
    rw [ht_eq]
    simp [hodd, hhalf, StaircaseHookCellsOfLength_odd_card_eq_sub]

/-- Odd staircase hook layers have the cardinal predicted by half the hook
length, with natural subtraction making the out-of-range case zero. -/
theorem StaircaseHookCellsOfLength_card_eq_sub_div_two_of_odd {n t : Nat}
    (ht : ¬ 2 ∣ t) :
    (StaircaseHookCellsOfLength n t).card = n - t / 2 := by
  rw [StaircaseHookCellsOfLength_card_eq_if]
  simp [ht]

/-- For an odd hook length below the staircase bound, the whole layer is the
corresponding antidiagonal. -/
theorem StaircaseHookCellsOfLength_eq_antidiagonal_of_odd_lt {n t : Nat}
    (ht : ¬ 2 ∣ t) (hlt : t < 2 * n) :
    StaircaseHookCellsOfLength n t =
      Finset.antidiagonal (n - (t / 2 + 1)) := by
  let k := t / 2
  have hmod : t % 2 = 1 := (Nat.two_dvd_ne_zero).1 ht
  have ht_eq : t = 2 * k + 1 := by
    have h := Nat.div_add_mod t 2
    rw [hmod] at h
    omega
  have hk : k < n := by
    omega
  have hhalf : (2 * k + 1) / 2 = k := by
    rw [show 2 * k + 1 = 1 + 2 * k by omega]
    rw [Nat.add_mul_div_left 1 k (by decide : 0 < 2)]
    norm_num
  rw [ht_eq]
  rw [hhalf]
  exact StaircaseHookCellsOfLength_odd_eq_antidiagonal (n := n) (k := k) hk

/-- Summing the descending natural numbers `n, n-1, ..., 1` gives the
triangular number. -/
theorem sum_range_sub_eq_triangular (n : Nat) :
    (Finset.range n).sum (fun k => n - k) = triangular n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hcongr : (Finset.range n).sum (fun k => n + 1 - k) =
          (Finset.range n).sum (fun k => (n - k) + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        omega
      rw [hcongr, Finset.sum_add_distrib]
      simp [ih, triangular_succ]
      omega

/-- Summing the multiplicities of all odd hook lengths in the staircase
recovers the triangular number of cells. -/
theorem sum_StaircaseHookCellsOfLength_odd_cards (n : Nat) :
    (Finset.range n).sum
        (fun k => (StaircaseHookCellsOfLength n (2 * k + 1)).card) =
      triangular n := by
  simp [StaircaseHookCellsOfLength_odd_card_eq_sub, sum_range_sub_eq_triangular]

/-- The odd hook-layer multiplicities add up to the weight of the staircase
partition. -/
theorem sum_StaircaseHookCellsOfLength_odd_cards_eq_weight (n : Nat) :
    (Finset.range n).sum
        (fun k => (StaircaseHookCellsOfLength n (2 * k + 1)).card) =
      partitionWeight (PartI.Ch05.staircasePartition n) := by
  rw [sum_StaircaseHookCellsOfLength_odd_cards,
    PartI.Ch05.partitionWeight_staircasePartition]

/-- A hook-length layer in a staircase is nonempty exactly for odd lengths
below the largest hook bound. -/
theorem StaircaseHookCellsOfLength_nonempty_iff (n t : Nat) :
    (StaircaseHookCellsOfLength n t).Nonempty ↔ ¬ 2 ∣ t ∧ t < 2 * n := by
  constructor
  · rintro ⟨cell, hmem⟩
    rw [mem_StaircaseHookCellsOfLength_iff] at hmem
    exact (exists_FerrersCell_hookLength_staircasePartition_iff n t).1
      ⟨cell.1, cell.2, hmem.1, hmem.2⟩
  · intro hoddlt
    rcases (exists_FerrersCell_hookLength_staircasePartition_iff n t).2 hoddlt with
      ⟨r, c, hcell, hhook⟩
    refine ⟨(r, c), ?_⟩
    rw [mem_StaircaseHookCellsOfLength_iff]
    exact ⟨hcell, hhook⟩

/-- Cardinal-positive form of `StaircaseHookCellsOfLength_nonempty_iff`. -/
theorem StaircaseHookCellsOfLength_card_pos_iff (n t : Nat) :
    0 < (StaircaseHookCellsOfLength n t).card ↔ ¬ 2 ∣ t ∧ t < 2 * n := by
  rw [Finset.card_pos, StaircaseHookCellsOfLength_nonempty_iff]

/-- Dual obstruction form of the complete staircase criterion. A staircase has
a hook divisible by `t` exactly when `t` is odd and below the largest hook
bound `2n`. -/
theorem hasHookDivisibleBy_staircasePartition_iff (n t : Nat) :
    HasHookDivisibleBy t (PartI.Ch05.staircasePartition n) ↔
      ¬ 2 ∣ t ∧ t < 2 * n := by
  constructor
  · intro hhook
    have hnotcore :
        ¬ IsTCoreByHooks t (PartI.Ch05.staircasePartition n) :=
      not_isTCoreByHooks_of_hasHook hhook
    have hnotcrit : ¬ (2 ∣ t ∨ 2 * n ≤ t) := by
      intro hcrit
      exact hnotcore ((isTCoreByHooks_staircasePartition_iff n t).2 hcrit)
    constructor
    · intro ht
      exact hnotcrit (Or.inl ht)
    · exact Nat.lt_of_not_ge (by intro hge; exact hnotcrit (Or.inr hge))
  · rintro ⟨htodd, hlt⟩
    have hnotcore :
        ¬ IsTCoreByHooks t (PartI.Ch05.staircasePartition n) := by
      intro hcore
      have hcrit := (isTCoreByHooks_staircasePartition_iff n t).1 hcore
      rcases hcrit with ht_even | hge
      · exact htodd ht_even
      · omega
    exact (not_isTCoreByHooks_iff_hasHookDivisibleBy t
      (PartI.Ch05.staircasePartition n)).1 hnotcore

/-- The positive-height staircase has a hook divisible by `2n - 1`, namely its
upper-left hook. -/
theorem hasHookDivisibleBy_two_mul_sub_one_staircasePartition {n : Nat} (hn : 0 < n) :
    HasHookDivisibleBy (2 * n - 1) (PartI.Ch05.staircasePartition n) := by
  rw [← hookLength_staircasePartition_zero_zero hn]
  exact hasHookDivisibleBy_hookLength_of_cell (FerrersCell_staircasePartition_zero_zero hn)

/-- Any divisor of the top-left staircase hook gives a hook obstruction. -/
theorem hasHookDivisibleBy_staircasePartition_of_dvd_two_mul_sub_one
    {n t : Nat} (hn : 0 < n) (hdiv : t ∣ 2 * n - 1) :
    HasHookDivisibleBy t (PartI.Ch05.staircasePartition n) :=
  hasHookDivisibleBy_of_dvd hdiv (hasHookDivisibleBy_two_mul_sub_one_staircasePartition hn)

/-- The bound `t ≥ 2n` for staircases is sharp in the hook model: a
positive-height staircase is not a `(2n - 1)`-core. -/
theorem not_isTCoreByHooks_two_mul_sub_one_staircasePartition {n : Nat} (hn : 0 < n) :
    ¬ IsTCoreByHooks (2 * n - 1) (PartI.Ch05.staircasePartition n) :=
  not_isTCoreByHooks_of_hasHook (hasHookDivisibleBy_two_mul_sub_one_staircasePartition hn)

/-- Any divisor of `2n - 1` rules out the corresponding t-core property for a
positive-height staircase. -/
theorem not_isTCoreByHooks_staircasePartition_of_dvd_two_mul_sub_one
    {n t : Nat} (hn : 0 < n) (hdiv : t ∣ 2 * n - 1) :
    ¬ IsTCoreByHooks t (PartI.Ch05.staircasePartition n) :=
  not_isTCoreByHooks_of_hasHook
    (hasHookDivisibleBy_staircasePartition_of_dvd_two_mul_sub_one hn hdiv)

@[simp] theorem hookLength_nil (r c : Nat) :
    hookLength [] r c = 1 := by
  simp [hookLength, armLength, legLength]

theorem hookLength_three_two_one_zero_zero :
    hookLength [3, 2, 1] 0 0 = 5 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_three_two_one_zero_one :
    hookLength [3, 2, 1] 0 1 = 3 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_three_two_one_zero_two :
    hookLength [3, 2, 1] 0 2 = 1 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_three_two_one_one_zero :
    hookLength [3, 2, 1] 1 0 = 3 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_three_two_one_one_one :
    hookLength [3, 2, 1] 1 1 = 1 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_three_two_one_two_zero :
    hookLength [3, 2, 1] 2 0 = 1 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_four_two_zero_zero :
    hookLength [4, 2] 0 0 = 5 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_four_two_zero_one :
    hookLength [4, 2] 0 1 = 4 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_four_two_zero_two :
    hookLength [4, 2] 0 2 = 2 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_four_two_zero_three :
    hookLength [4, 2] 0 3 = 1 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_four_two_one_zero :
    hookLength [4, 2] 1 0 = 2 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_four_two_one_one :
    hookLength [4, 2] 1 1 = 1 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_two_two_one_one_zero_zero :
    hookLength [2, 2, 1, 1] 0 0 = 5 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_two_two_one_one_zero_one :
    hookLength [2, 2, 1, 1] 0 1 = 2 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_two_two_one_one_one_zero :
    hookLength [2, 2, 1, 1] 1 0 = 4 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_two_two_one_one_one_one :
    hookLength [2, 2, 1, 1] 1 1 = 1 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_two_two_one_one_two_zero :
    hookLength [2, 2, 1, 1] 2 0 = 2 := by
  norm_num [hookLength, armLength, legLength]

theorem hookLength_two_two_one_one_three_zero :
    hookLength [2, 2, 1, 1] 3 0 = 1 := by
  norm_num [hookLength, armLength, legLength]

/-- The partition `[3,2,1]` has a hook length divisible by `3`. -/
theorem hasHookDivisibleBy_three_three_two_one :
    HasHookDivisibleBy 3 [3, 2, 1] := by
  refine ⟨0, 1, ?_, ?_⟩
  · exact ⟨by norm_num, by norm_num [FerrersCell, PartI.Ch05.FerrersCell]⟩
  · rw [hookLength_three_two_one_zero_one]

/-- The partition `[3,2,1]` has a hook length divisible by `5`. -/
theorem hasHookDivisibleBy_five_three_two_one :
    HasHookDivisibleBy 5 [3, 2, 1] := by
  refine ⟨0, 0, ?_, ?_⟩
  · exact ⟨by norm_num, by norm_num [FerrersCell, PartI.Ch05.FerrersCell]⟩
  · rw [hookLength_three_two_one_zero_zero]

/-- The nonempty partition `[3,2,1]` has a hook length divisible by `1`. -/
theorem hasHookDivisibleBy_one_three_two_one :
    HasHookDivisibleBy 1 [3, 2, 1] := by
  exact hasHookDivisibleBy_of_dvd (Nat.one_dvd 5) hasHookDivisibleBy_five_three_two_one

/-- The partition `[4,2]` has a hook length divisible by `2`. -/
theorem hasHookDivisibleBy_two_four_two :
    HasHookDivisibleBy 2 [4, 2] := by
  refine ⟨0, 1, ?_, ?_⟩
  · exact ⟨by norm_num, by norm_num [FerrersCell, PartI.Ch05.FerrersCell]⟩
  · rw [hookLength_four_two_zero_one]
    norm_num

/-- The partition `[4,2]` has a hook length divisible by `4`. -/
theorem hasHookDivisibleBy_four_four_two :
    HasHookDivisibleBy 4 [4, 2] := by
  refine ⟨0, 1, ?_, ?_⟩
  · exact ⟨by norm_num, by norm_num [FerrersCell, PartI.Ch05.FerrersCell]⟩
  · rw [hookLength_four_two_zero_one]

/-- The partition `[4,2]` has a hook length divisible by `5`. -/
theorem hasHookDivisibleBy_five_four_two :
    HasHookDivisibleBy 5 [4, 2] := by
  refine ⟨0, 0, ?_, ?_⟩
  · exact ⟨by norm_num, by norm_num [FerrersCell, PartI.Ch05.FerrersCell]⟩
  · rw [hookLength_four_two_zero_zero]

/-- The nonempty partition `[4,2]` has a hook length divisible by `1`. -/
theorem hasHookDivisibleBy_one_four_two :
    HasHookDivisibleBy 1 [4, 2] := by
  exact hasHookDivisibleBy_of_dvd (Nat.one_dvd 5) hasHookDivisibleBy_five_four_two

/-- The conjugate partition `[2,2,1,1]` of `[4,2]` has a hook length
divisible by `2`. -/
theorem hasHookDivisibleBy_two_two_one_one :
    HasHookDivisibleBy 2 [2, 2, 1, 1] := by
  refine ⟨0, 1, ?_, ?_⟩
  · exact ⟨by norm_num, by norm_num [FerrersCell, PartI.Ch05.FerrersCell]⟩
  · rw [hookLength_two_two_one_one_zero_one]

/-- The conjugate partition `[2,2,1,1]` of `[4,2]` has a hook length
divisible by `4`. -/
theorem hasHookDivisibleBy_four_two_two_one_one :
    HasHookDivisibleBy 4 [2, 2, 1, 1] := by
  refine ⟨1, 0, ?_, ?_⟩
  · exact ⟨by norm_num, by norm_num [FerrersCell, PartI.Ch05.FerrersCell]⟩
  · rw [hookLength_two_two_one_one_one_zero]

/-- The conjugate partition `[2,2,1,1]` of `[4,2]` has a hook length
divisible by `5`. -/
theorem hasHookDivisibleBy_five_two_two_one_one :
    HasHookDivisibleBy 5 [2, 2, 1, 1] := by
  refine ⟨0, 0, ?_, ?_⟩
  · exact ⟨by norm_num, by norm_num [FerrersCell, PartI.Ch05.FerrersCell]⟩
  · rw [hookLength_two_two_one_one_zero_zero]

/-- The nonempty conjugate partition `[2,2,1,1]` has a hook length divisible
by `1`. -/
theorem hasHookDivisibleBy_one_two_two_one_one :
    HasHookDivisibleBy 1 [2, 2, 1, 1] := by
  exact hasHookDivisibleBy_of_dvd (Nat.one_dvd 5) hasHookDivisibleBy_five_two_two_one_one

/-- Hence `[4,2]` is not a `2`-core in the hook-length sense. -/
theorem not_twoCoreByHooks_four_two :
    ¬ IsTCoreByHooks 2 [4, 2] :=
  not_isTCoreByHooks_of_hasHook hasHookDivisibleBy_two_four_two

/-- Hence `[4,2]` is not a `4`-core in the hook-length sense. -/
theorem not_fourCoreByHooks_four_two :
    ¬ IsTCoreByHooks 4 [4, 2] :=
  not_isTCoreByHooks_of_hasHook hasHookDivisibleBy_four_four_two

/-- Hence `[4,2]` is not a `5`-core in the hook-length sense. -/
theorem not_fiveCoreByHooks_four_two :
    ¬ IsTCoreByHooks 5 [4, 2] :=
  not_isTCoreByHooks_of_hasHook hasHookDivisibleBy_five_four_two

/-- Hence `[4,2]` is not a `1`-core in the hook-length sense. -/
theorem not_oneCoreByHooks_four_two :
    ¬ IsTCoreByHooks 1 [4, 2] :=
  not_isTCoreByHooks_of_hasHook hasHookDivisibleBy_one_four_two

/-- Hence the conjugate `[2,2,1,1]` is not a `2`-core. -/
theorem not_twoCoreByHooks_two_two_one_one :
    ¬ IsTCoreByHooks 2 [2, 2, 1, 1] :=
  not_isTCoreByHooks_of_hasHook hasHookDivisibleBy_two_two_one_one

/-- Hence the conjugate `[2,2,1,1]` is not a `4`-core. -/
theorem not_fourCoreByHooks_two_two_one_one :
    ¬ IsTCoreByHooks 4 [2, 2, 1, 1] :=
  not_isTCoreByHooks_of_hasHook hasHookDivisibleBy_four_two_two_one_one

/-- Hence the conjugate `[2,2,1,1]` is not a `5`-core. -/
theorem not_fiveCoreByHooks_two_two_one_one :
    ¬ IsTCoreByHooks 5 [2, 2, 1, 1] :=
  not_isTCoreByHooks_of_hasHook hasHookDivisibleBy_five_two_two_one_one

/-- Hence the conjugate `[2,2,1,1]` is not a `1`-core. -/
theorem not_oneCoreByHooks_two_two_one_one :
    ¬ IsTCoreByHooks 1 [2, 2, 1, 1] :=
  not_isTCoreByHooks_of_hasHook hasHookDivisibleBy_one_two_two_one_one

/-- Every hook cell of `[4,2]` has the same hook length at the transposed cell
of its Ferrers conjugate `[2,2,1,1]`. -/
theorem hookLength_four_two_conjugate_cell {r c : Nat}
    (hcell : FerrersCell [4, 2] r c) :
    FerrersCell [2, 2, 1, 1] c r ∧
      hookLength [2, 2, 1, 1] c r = hookLength [4, 2] r c := by
  rcases hcell with ⟨hr, hc⟩
  norm_num [FerrersCell, PartI.Ch05.FerrersCell] at hr hc
  interval_cases r
  · norm_num at hc
    interval_cases c <;> norm_num [FerrersCell, PartI.Ch05.FerrersCell,
      hookLength, armLength, legLength]
  · norm_num at hc
    interval_cases c <;> norm_num [FerrersCell, PartI.Ch05.FerrersCell,
      hookLength, armLength, legLength]

/-- Every hook cell of `[2,2,1,1]` has the same hook length at the transposed
cell of its Ferrers conjugate `[4,2]`. -/
theorem hookLength_two_two_one_one_conjugate_cell {r c : Nat}
    (hcell : FerrersCell [2, 2, 1, 1] r c) :
    FerrersCell [4, 2] c r ∧
      hookLength [4, 2] c r = hookLength [2, 2, 1, 1] r c := by
  rcases hcell with ⟨hr, hc⟩
  norm_num [FerrersCell, PartI.Ch05.FerrersCell] at hr hc
  interval_cases r
  · norm_num at hc
    interval_cases c <;> norm_num [FerrersCell, PartI.Ch05.FerrersCell,
      hookLength, armLength, legLength]
  · norm_num at hc
    interval_cases c <;> norm_num [FerrersCell, PartI.Ch05.FerrersCell,
      hookLength, armLength, legLength]
  · norm_num at hc
    have hc0 : c = 0 := by omega
    subst c
    norm_num [FerrersCell, PartI.Ch05.FerrersCell, hookLength, armLength, legLength]
  · norm_num at hc
    have hc0 : c = 0 := by omega
    subst c
    norm_num [FerrersCell, PartI.Ch05.FerrersCell, hookLength, armLength, legLength]

/-- Hook obstructions are preserved between `[4,2]` and its conjugate
`[2,2,1,1]`. -/
theorem hasHookDivisibleBy_four_two_conjugate_iff (t : Nat) :
    HasHookDivisibleBy t [4, 2] ↔ HasHookDivisibleBy t [2, 2, 1, 1] := by
  apply hasHookDivisibleBy_iff_of_hookLength_maps
  · intro r c hcell
    exact ⟨c, r, (hookLength_four_two_conjugate_cell hcell).1,
      (hookLength_four_two_conjugate_cell hcell).2⟩
  · intro r c hcell
    exact ⟨c, r, (hookLength_two_two_one_one_conjugate_cell hcell).1,
      (hookLength_two_two_one_one_conjugate_cell hcell).2⟩

/-- The hook-length `t`-core predicate agrees on `[4,2]` and its Ferrers
conjugate `[2,2,1,1]`. -/
theorem isTCoreByHooks_four_two_conjugate_iff (t : Nat) :
    IsTCoreByHooks t [4, 2] ↔ IsTCoreByHooks t [2, 2, 1, 1] := by
  apply isTCoreByHooks_iff_of_hookLength_maps
  · intro r c hcell
    exact ⟨c, r, (hookLength_four_two_conjugate_cell hcell).1,
      (hookLength_four_two_conjugate_cell hcell).2⟩
  · intro r c hcell
    exact ⟨c, r, (hookLength_two_two_one_one_conjugate_cell hcell).1,
      (hookLength_two_two_one_one_conjugate_cell hcell).2⟩

/-- The self-conjugate staircase `[3,2,1]` preserves hook lengths under
transposition of Ferrers cells. -/
theorem hookLength_three_two_one_transpose_cell {r c : Nat}
    (hcell : FerrersCell [3, 2, 1] r c) :
    FerrersCell [3, 2, 1] c r ∧
      hookLength [3, 2, 1] c r = hookLength [3, 2, 1] r c := by
  rcases hcell with ⟨hr, hc⟩
  norm_num [FerrersCell, PartI.Ch05.FerrersCell] at hr hc
  interval_cases r
  · norm_num at hc
    interval_cases c <;> norm_num [FerrersCell, PartI.Ch05.FerrersCell,
      hookLength, armLength, legLength]
  · norm_num at hc
    interval_cases c <;> norm_num [FerrersCell, PartI.Ch05.FerrersCell,
      hookLength, armLength, legLength]
  · norm_num at hc
    have hc0 : c = 0 := by omega
    subst c
    norm_num [FerrersCell, PartI.Ch05.FerrersCell, hookLength, armLength, legLength]

/-- Hook obstructions are invariant under transposition for the self-conjugate
staircase `[3,2,1]`. -/
theorem hasHookDivisibleBy_three_two_one_transpose_iff (t : Nat) :
    HasHookDivisibleBy t [3, 2, 1] ↔ HasHookDivisibleBy t [3, 2, 1] := by
  apply hasHookDivisibleBy_iff_of_hookLength_maps
  · intro r c hcell
    exact ⟨c, r, (hookLength_three_two_one_transpose_cell hcell).1,
      (hookLength_three_two_one_transpose_cell hcell).2⟩
  · intro r c hcell
    exact ⟨c, r, (hookLength_three_two_one_transpose_cell hcell).1,
      (hookLength_three_two_one_transpose_cell hcell).2⟩

/-- Hence `[3,2,1]` is not a `3`-core in the hook-length sense. -/
theorem not_threeCoreByHooks_three_two_one :
    ¬ IsTCoreByHooks 3 [3, 2, 1] := by
  intro h
  exact h hasHookDivisibleBy_three_three_two_one

/-- Hence `[3,2,1]` is not a `5`-core in the hook-length sense. -/
theorem not_fiveCoreByHooks_three_two_one :
    ¬ IsTCoreByHooks 5 [3, 2, 1] :=
  not_isTCoreByHooks_of_hasHook hasHookDivisibleBy_five_three_two_one

/-- Hence `[3,2,1]` is not a `1`-core in the hook-length sense. -/
theorem not_oneCoreByHooks_three_two_one :
    ¬ IsTCoreByHooks 1 [3, 2, 1] :=
  not_isTCoreByHooks_of_hasHook hasHookDivisibleBy_one_three_two_one

/-- Every hook length in `[3,2,1]` is below `6`; its largest hook is the
top-left hook of length `5`. -/
theorem hookLength_lt_six_three_two_one {r c : Nat}
    (hcell : FerrersCell [3, 2, 1] r c) :
    hookLength [3, 2, 1] r c < 6 := by
  rcases hcell with ⟨hr, hc⟩
  norm_num [FerrersCell, PartI.Ch05.FerrersCell] at hr hc
  interval_cases r
  · norm_num at hc
    interval_cases c
    · rw [hookLength_three_two_one_zero_zero]
      norm_num
    · rw [hookLength_three_two_one_zero_one]
      norm_num
    · rw [hookLength_three_two_one_zero_two]
      norm_num
  · norm_num at hc
    interval_cases c
    · rw [hookLength_three_two_one_one_zero]
      norm_num
    · rw [hookLength_three_two_one_one_one]
      norm_num
  · norm_num at hc
    have hc0 : c = 0 := by omega
    subst c
    rw [hookLength_three_two_one_two_zero]
    norm_num

/-- The partition `[3,2,1]` is a `t`-core for every `t ≥ 6`, since all its
hook lengths are strictly below `6`. -/
theorem isTCoreByHooks_three_two_one_of_six_le {t : Nat} (ht : 6 ≤ t) :
    IsTCoreByHooks t [3, 2, 1] := by
  apply isTCoreByHooks_of_hookLength_lt
  intro r c hcell
  have hlt : hookLength [3, 2, 1] r c < 6 :=
    hookLength_lt_six_three_two_one hcell
  omega

/-- The partition `[3,2,1]` is a positive example of a `6`-core in the
hook-length sense. -/
theorem isSixCoreByHooks_three_two_one :
    IsTCoreByHooks 6 [3, 2, 1] :=
  isTCoreByHooks_three_two_one_of_six_le le_rfl

/-- The same partition is also a `7`-core. -/
theorem isSevenCoreByHooks_three_two_one :
    IsTCoreByHooks 7 [3, 2, 1] :=
  isTCoreByHooks_three_two_one_of_six_le (by norm_num)

/-- Every hook length in `[4,2]` is below `6`; the largest hook has length
`5`. -/
theorem hookLength_lt_six_four_two {r c : Nat}
    (hcell : FerrersCell [4, 2] r c) :
    hookLength [4, 2] r c < 6 := by
  rcases hcell with ⟨hr, hc⟩
  norm_num [FerrersCell, PartI.Ch05.FerrersCell] at hr hc
  interval_cases r
  · norm_num at hc
    interval_cases c
    · rw [hookLength_four_two_zero_zero]
      norm_num
    · rw [hookLength_four_two_zero_one]
      norm_num
    · rw [hookLength_four_two_zero_two]
      norm_num
    · rw [hookLength_four_two_zero_three]
      norm_num
  · norm_num at hc
    interval_cases c
    · rw [hookLength_four_two_one_zero]
      norm_num
    · rw [hookLength_four_two_one_one]
      norm_num

/-- The partition `[4,2]` is a `t`-core for every `t ≥ 6`. -/
theorem isTCoreByHooks_four_two_of_six_le {t : Nat} (ht : 6 ≤ t) :
    IsTCoreByHooks t [4, 2] := by
  apply isTCoreByHooks_of_hookLength_lt
  intro r c hcell
  have hlt : hookLength [4, 2] r c < 6 := hookLength_lt_six_four_two hcell
  omega

/-- The partition `[4,2]` is a `6`-core. -/
theorem isSixCoreByHooks_four_two :
    IsTCoreByHooks 6 [4, 2] :=
  isTCoreByHooks_four_two_of_six_le le_rfl

/-- The partition `[4,2]` is also a `7`-core. -/
theorem isSevenCoreByHooks_four_two :
    IsTCoreByHooks 7 [4, 2] :=
  isTCoreByHooks_four_two_of_six_le (by norm_num)

/-- The conjugate `[2,2,1,1]` is a `t`-core for every `t ≥ 6`, by hook-length
preservation under conjugation. -/
theorem isTCoreByHooks_two_two_one_one_of_six_le {t : Nat} (ht : 6 ≤ t) :
    IsTCoreByHooks t [2, 2, 1, 1] :=
  (isTCoreByHooks_four_two_conjugate_iff t).1 (isTCoreByHooks_four_two_of_six_le ht)

/-- The conjugate `[2,2,1,1]` is a `6`-core. -/
theorem isSixCoreByHooks_two_two_one_one :
    IsTCoreByHooks 6 [2, 2, 1, 1] :=
  isTCoreByHooks_two_two_one_one_of_six_le le_rfl

/-- The conjugate `[2,2,1,1]` is also a `7`-core. -/
theorem isSevenCoreByHooks_two_two_one_one :
    IsTCoreByHooks 7 [2, 2, 1, 1] :=
  isTCoreByHooks_two_two_one_one_of_six_le (by norm_num)

end HookLengths

section Field

variable {R : Type*} [Field R]

/-- Truncated t-core generating function numerator: `∏_{n=1}^N (1 - q^{tn})^t`. -/
noncomputable def tCoreNumeratorTrunc (t : Nat) (q : R) : Nat → R
  | 0 => 1
  | Nat.succ n => tCoreNumeratorTrunc t q n * (1 - q ^ (t * (n + 1))) ^ t

/-- Truncated t-core generating function denominator: `∏_{n=1}^N (1 - q^n)`. -/
noncomputable def tCoreDenominatorTrunc (q : R) (N : Nat) : R :=
  qPochhammer q N

/-- Truncated t-core ratio. -/
noncomputable def tCoreRatioTrunc (t : Nat) (q : R) (N : Nat) : R :=
  tCoreNumeratorTrunc t q N / tCoreDenominatorTrunc q N

@[simp] theorem tCoreNumeratorTrunc_zero (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 0 = 1 := rfl

/-- Recursion: `tCoreNumeratorTrunc t q (N+1) =
tCoreNumeratorTrunc t q N · (1 − q^(t(N+1)))^t`. -/
theorem tCoreNumeratorTrunc_succ (t : Nat) (q : R) (N : Nat) :
    tCoreNumeratorTrunc t q (N + 1) =
      tCoreNumeratorTrunc t q N * (1 - q ^ (t * (N + 1))) ^ t := rfl

/-- Recursion: `tCoreDenominatorTrunc q (N+1) =
tCoreDenominatorTrunc q N · (1 − q^(N+1))`. -/
theorem tCoreDenominatorTrunc_succ (q : R) (N : Nat) :
    tCoreDenominatorTrunc q (N + 1) =
      tCoreDenominatorTrunc q N * (1 - q ^ (N + 1)) := by
  simp [tCoreDenominatorTrunc, qPochhammer_succ]

theorem tCoreNumeratorTrunc_one (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 1 = (1 - q^t)^t := by
  simp [tCoreNumeratorTrunc]

theorem tCoreNumeratorTrunc_two (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 2 = (1 - q^t)^t * (1 - q^(2*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreNumeratorTrunc_three (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 3 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreNumeratorTrunc_four (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 4 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t * (1 - q^(4*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreNumeratorTrunc_five (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 5 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t * (1 - q^(4*t))^t * (1 - q^(5*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

@[simp] theorem tCoreDenominatorTrunc_zero (q : R) :
    tCoreDenominatorTrunc q 0 = 1 := rfl

theorem tCoreDenominatorTrunc_one (q : R) :
    tCoreDenominatorTrunc q 1 = 1 - q := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreDenominatorTrunc_two (q : R) :
    tCoreDenominatorTrunc q 2 = (1 - q) * (1 - q ^ 2) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreDenominatorTrunc_three (q : R) :
    tCoreDenominatorTrunc q 3 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreNumeratorTrunc_six (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 6 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreRatioTrunc_zero (t : Nat) (q : R) :
    tCoreRatioTrunc t q 0 = 1 := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc]

theorem tCoreDenominatorTrunc_four (q : R) :
    tCoreDenominatorTrunc q 4 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreDenominatorTrunc_five (q : R) :
    tCoreDenominatorTrunc q 5 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreDenominatorTrunc_six (q : R) :
    tCoreDenominatorTrunc q 6 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreNumeratorTrunc_seven (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 7 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t * (1 - q^(7*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreNumeratorTrunc_eight (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 8 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_seven (q : R) :
    tCoreDenominatorTrunc q 7 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreDenominatorTrunc_eight (q : R) :
    tCoreDenominatorTrunc q 8 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_one (t : Nat) (q : R) :
    tCoreRatioTrunc t q 1 = (1 - q^t)^t / (1 - q) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_two (t : Nat) (q : R) :
    tCoreRatioTrunc t q 2 =
      ((1 - q^t)^t * (1 - q^(2*t))^t) / ((1 - q) * (1 - q ^ 2)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreRatioTrunc_three (t : Nat) (q : R) :
    tCoreRatioTrunc t q 3 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreDenominatorTrunc_nine (q : R) :
    tCoreDenominatorTrunc q 9 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreDenominatorTrunc_ten (q : R) :
    tCoreDenominatorTrunc q 10 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreNumeratorTrunc_nine (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 9 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreNumeratorTrunc_ten (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 10 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t * (1 - q^(10*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreRatioTrunc_four (t : Nat) (q : R) :
    tCoreRatioTrunc t q 4 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t * (1 - q^(4*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreRatioTrunc_five (t : Nat) (q : R) :
    tCoreRatioTrunc t q 5 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t * (1 - q^(4*t))^t * (1 - q^(5*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreRatioTrunc_six (t : Nat) (q : R) :
    tCoreRatioTrunc t q 6 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreRatioTrunc_seven (t : Nat) (q : R) :
    tCoreRatioTrunc t q 7 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t * (1 - q^(7*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreRatioTrunc_eight (t : Nat) (q : R) :
    tCoreRatioTrunc t q 8 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreRatioTrunc_nine (t : Nat) (q : R) :
    tCoreRatioTrunc t q 9 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreRatioTrunc_ten (t : Nat) (q : R) :
    tCoreRatioTrunc t q 10 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t * (1 - q^(10*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_eleven (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 11 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
      (1 - q^(10*t))^t * (1 - q^(11*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreNumeratorTrunc_twelve (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 12 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
      (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_eleven (q : R) :
    tCoreDenominatorTrunc q 11 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreDenominatorTrunc_twelve (q : R) :
    tCoreDenominatorTrunc q 12 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_eleven (t : Nat) (q : R) :
    tCoreRatioTrunc t q 11 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
       (1 - q^(10*t))^t * (1 - q^(11*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
       (1 - q ^ 11)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreRatioTrunc_twelve (t : Nat) (q : R) :
    tCoreRatioTrunc t q 12 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
       (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
       (1 - q ^ 11) * (1 - q ^ 12)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_thirteen (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 13 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
      (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t * (1 - q^(13*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreNumeratorTrunc_fourteen (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 14 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
      (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
      (1 - q^(13*t))^t * (1 - q^(14*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreNumeratorTrunc_fifteen (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 15 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
      (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
      (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_thirteen (q : R) :
    tCoreDenominatorTrunc q 13 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreDenominatorTrunc_fourteen (q : R) :
    tCoreDenominatorTrunc q 14 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreDenominatorTrunc_fifteen (q : R) :
    tCoreDenominatorTrunc q 15 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_thirteen (t : Nat) (q : R) :
    tCoreRatioTrunc t q 13 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
       (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t * (1 - q^(13*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
       (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreRatioTrunc_fourteen (t : Nat) (q : R) :
    tCoreRatioTrunc t q 14 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
       (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
       (1 - q^(13*t))^t * (1 - q^(14*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
       (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreRatioTrunc_fifteen (t : Nat) (q : R) :
    tCoreRatioTrunc t q 15 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
       (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
       (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
       (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_sixteen (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 16 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
      (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
      (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t * (1 - q^(16*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreNumeratorTrunc_seventeen (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 17 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
      (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
      (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
      (1 - q^(16*t))^t * (1 - q^(17*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreNumeratorTrunc_eighteen (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 18 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
      (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
      (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
      (1 - q^(16*t))^t * (1 - q^(17*t))^t * (1 - q^(18*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_sixteen (q : R) :
    tCoreDenominatorTrunc q 16 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreDenominatorTrunc_seventeen (q : R) :
    tCoreDenominatorTrunc q 17 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreDenominatorTrunc_eighteen (q : R) :
    tCoreDenominatorTrunc q 18 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_sixteen (t : Nat) (q : R) :
    tCoreRatioTrunc t q 16 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
       (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
       (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t * (1 - q^(16*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
       (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
       (1 - q ^ 16)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreRatioTrunc_seventeen (t : Nat) (q : R) :
    tCoreRatioTrunc t q 17 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
       (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
       (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
       (1 - q^(16*t))^t * (1 - q^(17*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
       (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
       (1 - q ^ 16) * (1 - q ^ 17)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreRatioTrunc_eighteen (t : Nat) (q : R) :
    tCoreRatioTrunc t q 18 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
       (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
       (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
       (1 - q^(16*t))^t * (1 - q^(17*t))^t * (1 - q^(18*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
       (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
       (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_nineteen (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 19 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
      (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
      (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
      (1 - q^(16*t))^t * (1 - q^(17*t))^t * (1 - q^(18*t))^t *
      (1 - q^(19*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_nineteen (q : R) :
    tCoreDenominatorTrunc q 19 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_nineteen (t : Nat) (q : R) :
    tCoreRatioTrunc t q 19 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
       (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
       (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
       (1 - q^(16*t))^t * (1 - q^(17*t))^t * (1 - q^(18*t))^t *
       (1 - q^(19*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
       (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
       (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_twenty (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 20 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
      (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
      (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
      (1 - q^(16*t))^t * (1 - q^(17*t))^t * (1 - q^(18*t))^t *
      (1 - q^(19*t))^t * (1 - q^(20*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_twenty (q : R) :
    tCoreDenominatorTrunc q 20 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_twenty (t : Nat) (q : R) :
    tCoreRatioTrunc t q 20 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
       (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
       (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
       (1 - q^(16*t))^t * (1 - q^(17*t))^t * (1 - q^(18*t))^t *
       (1 - q^(19*t))^t * (1 - q^(20*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
       (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
       (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_twentyone (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 21 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
      (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
      (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
      (1 - q^(16*t))^t * (1 - q^(17*t))^t * (1 - q^(18*t))^t *
      (1 - q^(19*t))^t * (1 - q^(20*t))^t * (1 - q^(21*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_twentyone (q : R) :
    tCoreDenominatorTrunc q 21 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_twentyone (t : Nat) (q : R) :
    tCoreRatioTrunc t q 21 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
       (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
       (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
       (1 - q^(16*t))^t * (1 - q^(17*t))^t * (1 - q^(18*t))^t *
       (1 - q^(19*t))^t * (1 - q^(20*t))^t * (1 - q^(21*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
       (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
       (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
       (1 - q ^ 21)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_twentytwo (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 22 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
      (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
      (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
      (1 - q^(16*t))^t * (1 - q^(17*t))^t * (1 - q^(18*t))^t *
      (1 - q^(19*t))^t * (1 - q^(20*t))^t * (1 - q^(21*t))^t *
      (1 - q^(22*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_twentytwo (q : R) :
    tCoreDenominatorTrunc q 22 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_twentytwo (t : Nat) (q : R) :
    tCoreRatioTrunc t q 22 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
       (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
       (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
       (1 - q^(16*t))^t * (1 - q^(17*t))^t * (1 - q^(18*t))^t *
       (1 - q^(19*t))^t * (1 - q^(20*t))^t * (1 - q^(21*t))^t *
       (1 - q^(22*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
       (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
       (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
       (1 - q ^ 21) * (1 - q ^ 22)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_twentythree (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 23 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
      (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
      (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
      (1 - q^(16*t))^t * (1 - q^(17*t))^t * (1 - q^(18*t))^t *
      (1 - q^(19*t))^t * (1 - q^(20*t))^t * (1 - q^(21*t))^t *
      (1 - q^(22*t))^t * (1 - q^(23*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_twentythree (q : R) :
    tCoreDenominatorTrunc q 23 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_twentythree (t : Nat) (q : R) :
    tCoreRatioTrunc t q 23 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
       (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
       (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
       (1 - q^(16*t))^t * (1 - q^(17*t))^t * (1 - q^(18*t))^t *
       (1 - q^(19*t))^t * (1 - q^(20*t))^t * (1 - q^(21*t))^t *
       (1 - q^(22*t))^t * (1 - q^(23*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
       (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
       (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
       (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_twentyfour (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 24 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
      (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
      (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
      (1 - q^(16*t))^t * (1 - q^(17*t))^t * (1 - q^(18*t))^t *
      (1 - q^(19*t))^t * (1 - q^(20*t))^t * (1 - q^(21*t))^t *
      (1 - q^(22*t))^t * (1 - q^(23*t))^t * (1 - q^(24*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_twentyfour (q : R) :
    tCoreDenominatorTrunc q 24 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_twentyfour (t : Nat) (q : R) :
    tCoreRatioTrunc t q 24 =
      ((1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
       (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
       (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t *
       (1 - q^(10*t))^t * (1 - q^(11*t))^t * (1 - q^(12*t))^t *
       (1 - q^(13*t))^t * (1 - q^(14*t))^t * (1 - q^(15*t))^t *
       (1 - q^(16*t))^t * (1 - q^(17*t))^t * (1 - q^(18*t))^t *
       (1 - q^(19*t))^t * (1 - q^(20*t))^t * (1 - q^(21*t))^t *
       (1 - q^(22*t))^t * (1 - q^(23*t))^t * (1 - q^(24*t))^t) /
      ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
       (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
       (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
       (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
       (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_twentyfive (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 25 =
      (1 - q^(1*t))^t *
      (1 - q^(2*t))^t *
      (1 - q^(3*t))^t *
      (1 - q^(4*t))^t *
      (1 - q^(5*t))^t *
      (1 - q^(6*t))^t *
      (1 - q^(7*t))^t *
      (1 - q^(8*t))^t *
      (1 - q^(9*t))^t *
      (1 - q^(10*t))^t *
      (1 - q^(11*t))^t *
      (1 - q^(12*t))^t *
      (1 - q^(13*t))^t *
      (1 - q^(14*t))^t *
      (1 - q^(15*t))^t *
      (1 - q^(16*t))^t *
      (1 - q^(17*t))^t *
      (1 - q^(18*t))^t *
      (1 - q^(19*t))^t *
      (1 - q^(20*t))^t *
      (1 - q^(21*t))^t *
      (1 - q^(22*t))^t *
      (1 - q^(23*t))^t *
      (1 - q^(24*t))^t *
      (1 - q^(25*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_twentyfive (q : R) :
    tCoreDenominatorTrunc q 25 =
      (1 - q ^ 1) *
      (1 - q ^ 2) *
      (1 - q ^ 3) *
      (1 - q ^ 4) *
      (1 - q ^ 5) *
      (1 - q ^ 6) *
      (1 - q ^ 7) *
      (1 - q ^ 8) *
      (1 - q ^ 9) *
      (1 - q ^ 10) *
      (1 - q ^ 11) *
      (1 - q ^ 12) *
      (1 - q ^ 13) *
      (1 - q ^ 14) *
      (1 - q ^ 15) *
      (1 - q ^ 16) *
      (1 - q ^ 17) *
      (1 - q ^ 18) *
      (1 - q ^ 19) *
      (1 - q ^ 20) *
      (1 - q ^ 21) *
      (1 - q ^ 22) *
      (1 - q ^ 23) *
      (1 - q ^ 24) *
      (1 - q ^ 25) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_twentyfive (t : Nat) (q : R) :
    tCoreRatioTrunc t q 25 =
      ((1 - q^(1*t))^t *
      (1 - q^(2*t))^t *
      (1 - q^(3*t))^t *
      (1 - q^(4*t))^t *
      (1 - q^(5*t))^t *
      (1 - q^(6*t))^t *
      (1 - q^(7*t))^t *
      (1 - q^(8*t))^t *
      (1 - q^(9*t))^t *
      (1 - q^(10*t))^t *
      (1 - q^(11*t))^t *
      (1 - q^(12*t))^t *
      (1 - q^(13*t))^t *
      (1 - q^(14*t))^t *
      (1 - q^(15*t))^t *
      (1 - q^(16*t))^t *
      (1 - q^(17*t))^t *
      (1 - q^(18*t))^t *
      (1 - q^(19*t))^t *
      (1 - q^(20*t))^t *
      (1 - q^(21*t))^t *
      (1 - q^(22*t))^t *
      (1 - q^(23*t))^t *
      (1 - q^(24*t))^t *
      (1 - q^(25*t))^t) /
      ((1 - q ^ 1) *
      (1 - q ^ 2) *
      (1 - q ^ 3) *
      (1 - q ^ 4) *
      (1 - q ^ 5) *
      (1 - q ^ 6) *
      (1 - q ^ 7) *
      (1 - q ^ 8) *
      (1 - q ^ 9) *
      (1 - q ^ 10) *
      (1 - q ^ 11) *
      (1 - q ^ 12) *
      (1 - q ^ 13) *
      (1 - q ^ 14) *
      (1 - q ^ 15) *
      (1 - q ^ 16) *
      (1 - q ^ 17) *
      (1 - q ^ 18) *
      (1 - q ^ 19) *
      (1 - q ^ 20) *
      (1 - q ^ 21) *
      (1 - q ^ 22) *
      (1 - q ^ 23) *
      (1 - q ^ 24) *
      (1 - q ^ 25)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_twentysix (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 26 =
      (1 - q^(1*t))^t *
      (1 - q^(2*t))^t *
      (1 - q^(3*t))^t *
      (1 - q^(4*t))^t *
      (1 - q^(5*t))^t *
      (1 - q^(6*t))^t *
      (1 - q^(7*t))^t *
      (1 - q^(8*t))^t *
      (1 - q^(9*t))^t *
      (1 - q^(10*t))^t *
      (1 - q^(11*t))^t *
      (1 - q^(12*t))^t *
      (1 - q^(13*t))^t *
      (1 - q^(14*t))^t *
      (1 - q^(15*t))^t *
      (1 - q^(16*t))^t *
      (1 - q^(17*t))^t *
      (1 - q^(18*t))^t *
      (1 - q^(19*t))^t *
      (1 - q^(20*t))^t *
      (1 - q^(21*t))^t *
      (1 - q^(22*t))^t *
      (1 - q^(23*t))^t *
      (1 - q^(24*t))^t *
      (1 - q^(25*t))^t *
      (1 - q^(26*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_twentysix (q : R) :
    tCoreDenominatorTrunc q 26 =
      (1 - q ^ 1) *
      (1 - q ^ 2) *
      (1 - q ^ 3) *
      (1 - q ^ 4) *
      (1 - q ^ 5) *
      (1 - q ^ 6) *
      (1 - q ^ 7) *
      (1 - q ^ 8) *
      (1 - q ^ 9) *
      (1 - q ^ 10) *
      (1 - q ^ 11) *
      (1 - q ^ 12) *
      (1 - q ^ 13) *
      (1 - q ^ 14) *
      (1 - q ^ 15) *
      (1 - q ^ 16) *
      (1 - q ^ 17) *
      (1 - q ^ 18) *
      (1 - q ^ 19) *
      (1 - q ^ 20) *
      (1 - q ^ 21) *
      (1 - q ^ 22) *
      (1 - q ^ 23) *
      (1 - q ^ 24) *
      (1 - q ^ 25) *
      (1 - q ^ 26) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_twentysix (t : Nat) (q : R) :
    tCoreRatioTrunc t q 26 =
      ((1 - q^(1*t))^t *
      (1 - q^(2*t))^t *
      (1 - q^(3*t))^t *
      (1 - q^(4*t))^t *
      (1 - q^(5*t))^t *
      (1 - q^(6*t))^t *
      (1 - q^(7*t))^t *
      (1 - q^(8*t))^t *
      (1 - q^(9*t))^t *
      (1 - q^(10*t))^t *
      (1 - q^(11*t))^t *
      (1 - q^(12*t))^t *
      (1 - q^(13*t))^t *
      (1 - q^(14*t))^t *
      (1 - q^(15*t))^t *
      (1 - q^(16*t))^t *
      (1 - q^(17*t))^t *
      (1 - q^(18*t))^t *
      (1 - q^(19*t))^t *
      (1 - q^(20*t))^t *
      (1 - q^(21*t))^t *
      (1 - q^(22*t))^t *
      (1 - q^(23*t))^t *
      (1 - q^(24*t))^t *
      (1 - q^(25*t))^t *
      (1 - q^(26*t))^t) /
      ((1 - q ^ 1) *
      (1 - q ^ 2) *
      (1 - q ^ 3) *
      (1 - q ^ 4) *
      (1 - q ^ 5) *
      (1 - q ^ 6) *
      (1 - q ^ 7) *
      (1 - q ^ 8) *
      (1 - q ^ 9) *
      (1 - q ^ 10) *
      (1 - q ^ 11) *
      (1 - q ^ 12) *
      (1 - q ^ 13) *
      (1 - q ^ 14) *
      (1 - q ^ 15) *
      (1 - q ^ 16) *
      (1 - q ^ 17) *
      (1 - q ^ 18) *
      (1 - q ^ 19) *
      (1 - q ^ 20) *
      (1 - q ^ 21) *
      (1 - q ^ 22) *
      (1 - q ^ 23) *
      (1 - q ^ 24) *
      (1 - q ^ 25) *
      (1 - q ^ 26)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_twentyseven (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 27 =
      (1 - q^(1*t))^t *
      (1 - q^(2*t))^t *
      (1 - q^(3*t))^t *
      (1 - q^(4*t))^t *
      (1 - q^(5*t))^t *
      (1 - q^(6*t))^t *
      (1 - q^(7*t))^t *
      (1 - q^(8*t))^t *
      (1 - q^(9*t))^t *
      (1 - q^(10*t))^t *
      (1 - q^(11*t))^t *
      (1 - q^(12*t))^t *
      (1 - q^(13*t))^t *
      (1 - q^(14*t))^t *
      (1 - q^(15*t))^t *
      (1 - q^(16*t))^t *
      (1 - q^(17*t))^t *
      (1 - q^(18*t))^t *
      (1 - q^(19*t))^t *
      (1 - q^(20*t))^t *
      (1 - q^(21*t))^t *
      (1 - q^(22*t))^t *
      (1 - q^(23*t))^t *
      (1 - q^(24*t))^t *
      (1 - q^(25*t))^t *
      (1 - q^(26*t))^t *
      (1 - q^(27*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_twentyseven (q : R) :
    tCoreDenominatorTrunc q 27 =
      (1 - q ^ 1) *
      (1 - q ^ 2) *
      (1 - q ^ 3) *
      (1 - q ^ 4) *
      (1 - q ^ 5) *
      (1 - q ^ 6) *
      (1 - q ^ 7) *
      (1 - q ^ 8) *
      (1 - q ^ 9) *
      (1 - q ^ 10) *
      (1 - q ^ 11) *
      (1 - q ^ 12) *
      (1 - q ^ 13) *
      (1 - q ^ 14) *
      (1 - q ^ 15) *
      (1 - q ^ 16) *
      (1 - q ^ 17) *
      (1 - q ^ 18) *
      (1 - q ^ 19) *
      (1 - q ^ 20) *
      (1 - q ^ 21) *
      (1 - q ^ 22) *
      (1 - q ^ 23) *
      (1 - q ^ 24) *
      (1 - q ^ 25) *
      (1 - q ^ 26) *
      (1 - q ^ 27) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_twentyseven (t : Nat) (q : R) :
    tCoreRatioTrunc t q 27 =
      ((1 - q^(1*t))^t *
      (1 - q^(2*t))^t *
      (1 - q^(3*t))^t *
      (1 - q^(4*t))^t *
      (1 - q^(5*t))^t *
      (1 - q^(6*t))^t *
      (1 - q^(7*t))^t *
      (1 - q^(8*t))^t *
      (1 - q^(9*t))^t *
      (1 - q^(10*t))^t *
      (1 - q^(11*t))^t *
      (1 - q^(12*t))^t *
      (1 - q^(13*t))^t *
      (1 - q^(14*t))^t *
      (1 - q^(15*t))^t *
      (1 - q^(16*t))^t *
      (1 - q^(17*t))^t *
      (1 - q^(18*t))^t *
      (1 - q^(19*t))^t *
      (1 - q^(20*t))^t *
      (1 - q^(21*t))^t *
      (1 - q^(22*t))^t *
      (1 - q^(23*t))^t *
      (1 - q^(24*t))^t *
      (1 - q^(25*t))^t *
      (1 - q^(26*t))^t *
      (1 - q^(27*t))^t) /
      ((1 - q ^ 1) *
      (1 - q ^ 2) *
      (1 - q ^ 3) *
      (1 - q ^ 4) *
      (1 - q ^ 5) *
      (1 - q ^ 6) *
      (1 - q ^ 7) *
      (1 - q ^ 8) *
      (1 - q ^ 9) *
      (1 - q ^ 10) *
      (1 - q ^ 11) *
      (1 - q ^ 12) *
      (1 - q ^ 13) *
      (1 - q ^ 14) *
      (1 - q ^ 15) *
      (1 - q ^ 16) *
      (1 - q ^ 17) *
      (1 - q ^ 18) *
      (1 - q ^ 19) *
      (1 - q ^ 20) *
      (1 - q ^ 21) *
      (1 - q ^ 22) *
      (1 - q ^ 23) *
      (1 - q ^ 24) *
      (1 - q ^ 25) *
      (1 - q ^ 26) *
      (1 - q ^ 27)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_twentyeight (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 28 =
      (1 - q^(1*t))^t *
      (1 - q^(2*t))^t *
      (1 - q^(3*t))^t *
      (1 - q^(4*t))^t *
      (1 - q^(5*t))^t *
      (1 - q^(6*t))^t *
      (1 - q^(7*t))^t *
      (1 - q^(8*t))^t *
      (1 - q^(9*t))^t *
      (1 - q^(10*t))^t *
      (1 - q^(11*t))^t *
      (1 - q^(12*t))^t *
      (1 - q^(13*t))^t *
      (1 - q^(14*t))^t *
      (1 - q^(15*t))^t *
      (1 - q^(16*t))^t *
      (1 - q^(17*t))^t *
      (1 - q^(18*t))^t *
      (1 - q^(19*t))^t *
      (1 - q^(20*t))^t *
      (1 - q^(21*t))^t *
      (1 - q^(22*t))^t *
      (1 - q^(23*t))^t *
      (1 - q^(24*t))^t *
      (1 - q^(25*t))^t *
      (1 - q^(26*t))^t *
      (1 - q^(27*t))^t *
      (1 - q^(28*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_twentyeight (q : R) :
    tCoreDenominatorTrunc q 28 =
      (1 - q ^ 1) *
      (1 - q ^ 2) *
      (1 - q ^ 3) *
      (1 - q ^ 4) *
      (1 - q ^ 5) *
      (1 - q ^ 6) *
      (1 - q ^ 7) *
      (1 - q ^ 8) *
      (1 - q ^ 9) *
      (1 - q ^ 10) *
      (1 - q ^ 11) *
      (1 - q ^ 12) *
      (1 - q ^ 13) *
      (1 - q ^ 14) *
      (1 - q ^ 15) *
      (1 - q ^ 16) *
      (1 - q ^ 17) *
      (1 - q ^ 18) *
      (1 - q ^ 19) *
      (1 - q ^ 20) *
      (1 - q ^ 21) *
      (1 - q ^ 22) *
      (1 - q ^ 23) *
      (1 - q ^ 24) *
      (1 - q ^ 25) *
      (1 - q ^ 26) *
      (1 - q ^ 27) *
      (1 - q ^ 28) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_twentyeight (t : Nat) (q : R) :
    tCoreRatioTrunc t q 28 =
      ((1 - q^(1*t))^t *
      (1 - q^(2*t))^t *
      (1 - q^(3*t))^t *
      (1 - q^(4*t))^t *
      (1 - q^(5*t))^t *
      (1 - q^(6*t))^t *
      (1 - q^(7*t))^t *
      (1 - q^(8*t))^t *
      (1 - q^(9*t))^t *
      (1 - q^(10*t))^t *
      (1 - q^(11*t))^t *
      (1 - q^(12*t))^t *
      (1 - q^(13*t))^t *
      (1 - q^(14*t))^t *
      (1 - q^(15*t))^t *
      (1 - q^(16*t))^t *
      (1 - q^(17*t))^t *
      (1 - q^(18*t))^t *
      (1 - q^(19*t))^t *
      (1 - q^(20*t))^t *
      (1 - q^(21*t))^t *
      (1 - q^(22*t))^t *
      (1 - q^(23*t))^t *
      (1 - q^(24*t))^t *
      (1 - q^(25*t))^t *
      (1 - q^(26*t))^t *
      (1 - q^(27*t))^t *
      (1 - q^(28*t))^t) /
      ((1 - q ^ 1) *
      (1 - q ^ 2) *
      (1 - q ^ 3) *
      (1 - q ^ 4) *
      (1 - q ^ 5) *
      (1 - q ^ 6) *
      (1 - q ^ 7) *
      (1 - q ^ 8) *
      (1 - q ^ 9) *
      (1 - q ^ 10) *
      (1 - q ^ 11) *
      (1 - q ^ 12) *
      (1 - q ^ 13) *
      (1 - q ^ 14) *
      (1 - q ^ 15) *
      (1 - q ^ 16) *
      (1 - q ^ 17) *
      (1 - q ^ 18) *
      (1 - q ^ 19) *
      (1 - q ^ 20) *
      (1 - q ^ 21) *
      (1 - q ^ 22) *
      (1 - q ^ 23) *
      (1 - q ^ 24) *
      (1 - q ^ 25) *
      (1 - q ^ 26) *
      (1 - q ^ 27) *
      (1 - q ^ 28)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_twentynine (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 29 =
      (1 - q^(1*t))^t *
      (1 - q^(2*t))^t *
      (1 - q^(3*t))^t *
      (1 - q^(4*t))^t *
      (1 - q^(5*t))^t *
      (1 - q^(6*t))^t *
      (1 - q^(7*t))^t *
      (1 - q^(8*t))^t *
      (1 - q^(9*t))^t *
      (1 - q^(10*t))^t *
      (1 - q^(11*t))^t *
      (1 - q^(12*t))^t *
      (1 - q^(13*t))^t *
      (1 - q^(14*t))^t *
      (1 - q^(15*t))^t *
      (1 - q^(16*t))^t *
      (1 - q^(17*t))^t *
      (1 - q^(18*t))^t *
      (1 - q^(19*t))^t *
      (1 - q^(20*t))^t *
      (1 - q^(21*t))^t *
      (1 - q^(22*t))^t *
      (1 - q^(23*t))^t *
      (1 - q^(24*t))^t *
      (1 - q^(25*t))^t *
      (1 - q^(26*t))^t *
      (1 - q^(27*t))^t *
      (1 - q^(28*t))^t *
      (1 - q^(29*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_twentynine (q : R) :
    tCoreDenominatorTrunc q 29 =
      (1 - q ^ 1) *
      (1 - q ^ 2) *
      (1 - q ^ 3) *
      (1 - q ^ 4) *
      (1 - q ^ 5) *
      (1 - q ^ 6) *
      (1 - q ^ 7) *
      (1 - q ^ 8) *
      (1 - q ^ 9) *
      (1 - q ^ 10) *
      (1 - q ^ 11) *
      (1 - q ^ 12) *
      (1 - q ^ 13) *
      (1 - q ^ 14) *
      (1 - q ^ 15) *
      (1 - q ^ 16) *
      (1 - q ^ 17) *
      (1 - q ^ 18) *
      (1 - q ^ 19) *
      (1 - q ^ 20) *
      (1 - q ^ 21) *
      (1 - q ^ 22) *
      (1 - q ^ 23) *
      (1 - q ^ 24) *
      (1 - q ^ 25) *
      (1 - q ^ 26) *
      (1 - q ^ 27) *
      (1 - q ^ 28) *
      (1 - q ^ 29) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_twentynine (t : Nat) (q : R) :
    tCoreRatioTrunc t q 29 =
      ((1 - q^(1*t))^t *
      (1 - q^(2*t))^t *
      (1 - q^(3*t))^t *
      (1 - q^(4*t))^t *
      (1 - q^(5*t))^t *
      (1 - q^(6*t))^t *
      (1 - q^(7*t))^t *
      (1 - q^(8*t))^t *
      (1 - q^(9*t))^t *
      (1 - q^(10*t))^t *
      (1 - q^(11*t))^t *
      (1 - q^(12*t))^t *
      (1 - q^(13*t))^t *
      (1 - q^(14*t))^t *
      (1 - q^(15*t))^t *
      (1 - q^(16*t))^t *
      (1 - q^(17*t))^t *
      (1 - q^(18*t))^t *
      (1 - q^(19*t))^t *
      (1 - q^(20*t))^t *
      (1 - q^(21*t))^t *
      (1 - q^(22*t))^t *
      (1 - q^(23*t))^t *
      (1 - q^(24*t))^t *
      (1 - q^(25*t))^t *
      (1 - q^(26*t))^t *
      (1 - q^(27*t))^t *
      (1 - q^(28*t))^t *
      (1 - q^(29*t))^t) /
      ((1 - q ^ 1) *
      (1 - q ^ 2) *
      (1 - q ^ 3) *
      (1 - q ^ 4) *
      (1 - q ^ 5) *
      (1 - q ^ 6) *
      (1 - q ^ 7) *
      (1 - q ^ 8) *
      (1 - q ^ 9) *
      (1 - q ^ 10) *
      (1 - q ^ 11) *
      (1 - q ^ 12) *
      (1 - q ^ 13) *
      (1 - q ^ 14) *
      (1 - q ^ 15) *
      (1 - q ^ 16) *
      (1 - q ^ 17) *
      (1 - q ^ 18) *
      (1 - q ^ 19) *
      (1 - q ^ 20) *
      (1 - q ^ 21) *
      (1 - q ^ 22) *
      (1 - q ^ 23) *
      (1 - q ^ 24) *
      (1 - q ^ 25) *
      (1 - q ^ 26) *
      (1 - q ^ 27) *
      (1 - q ^ 28) *
      (1 - q ^ 29)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

theorem tCoreNumeratorTrunc_thirty (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 30 =
      (1 - q^(1*t))^t *
      (1 - q^(2*t))^t *
      (1 - q^(3*t))^t *
      (1 - q^(4*t))^t *
      (1 - q^(5*t))^t *
      (1 - q^(6*t))^t *
      (1 - q^(7*t))^t *
      (1 - q^(8*t))^t *
      (1 - q^(9*t))^t *
      (1 - q^(10*t))^t *
      (1 - q^(11*t))^t *
      (1 - q^(12*t))^t *
      (1 - q^(13*t))^t *
      (1 - q^(14*t))^t *
      (1 - q^(15*t))^t *
      (1 - q^(16*t))^t *
      (1 - q^(17*t))^t *
      (1 - q^(18*t))^t *
      (1 - q^(19*t))^t *
      (1 - q^(20*t))^t *
      (1 - q^(21*t))^t *
      (1 - q^(22*t))^t *
      (1 - q^(23*t))^t *
      (1 - q^(24*t))^t *
      (1 - q^(25*t))^t *
      (1 - q^(26*t))^t *
      (1 - q^(27*t))^t *
      (1 - q^(28*t))^t *
      (1 - q^(29*t))^t *
      (1 - q^(30*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_thirty (q : R) :
    tCoreDenominatorTrunc q 30 =
      (1 - q ^ 1) *
      (1 - q ^ 2) *
      (1 - q ^ 3) *
      (1 - q ^ 4) *
      (1 - q ^ 5) *
      (1 - q ^ 6) *
      (1 - q ^ 7) *
      (1 - q ^ 8) *
      (1 - q ^ 9) *
      (1 - q ^ 10) *
      (1 - q ^ 11) *
      (1 - q ^ 12) *
      (1 - q ^ 13) *
      (1 - q ^ 14) *
      (1 - q ^ 15) *
      (1 - q ^ 16) *
      (1 - q ^ 17) *
      (1 - q ^ 18) *
      (1 - q ^ 19) *
      (1 - q ^ 20) *
      (1 - q ^ 21) *
      (1 - q ^ 22) *
      (1 - q ^ 23) *
      (1 - q ^ 24) *
      (1 - q ^ 25) *
      (1 - q ^ 26) *
      (1 - q ^ 27) *
      (1 - q ^ 28) *
      (1 - q ^ 29) *
      (1 - q ^ 30) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_thirty (t : Nat) (q : R) :
    tCoreRatioTrunc t q 30 =
      ((1 - q^(1*t))^t *
      (1 - q^(2*t))^t *
      (1 - q^(3*t))^t *
      (1 - q^(4*t))^t *
      (1 - q^(5*t))^t *
      (1 - q^(6*t))^t *
      (1 - q^(7*t))^t *
      (1 - q^(8*t))^t *
      (1 - q^(9*t))^t *
      (1 - q^(10*t))^t *
      (1 - q^(11*t))^t *
      (1 - q^(12*t))^t *
      (1 - q^(13*t))^t *
      (1 - q^(14*t))^t *
      (1 - q^(15*t))^t *
      (1 - q^(16*t))^t *
      (1 - q^(17*t))^t *
      (1 - q^(18*t))^t *
      (1 - q^(19*t))^t *
      (1 - q^(20*t))^t *
      (1 - q^(21*t))^t *
      (1 - q^(22*t))^t *
      (1 - q^(23*t))^t *
      (1 - q^(24*t))^t *
      (1 - q^(25*t))^t *
      (1 - q^(26*t))^t *
      (1 - q^(27*t))^t *
      (1 - q^(28*t))^t *
      (1 - q^(29*t))^t *
      (1 - q^(30*t))^t) /
      ((1 - q ^ 1) *
      (1 - q ^ 2) *
      (1 - q ^ 3) *
      (1 - q ^ 4) *
      (1 - q ^ 5) *
      (1 - q ^ 6) *
      (1 - q ^ 7) *
      (1 - q ^ 8) *
      (1 - q ^ 9) *
      (1 - q ^ 10) *
      (1 - q ^ 11) *
      (1 - q ^ 12) *
      (1 - q ^ 13) *
      (1 - q ^ 14) *
      (1 - q ^ 15) *
      (1 - q ^ 16) *
      (1 - q ^ 17) *
      (1 - q ^ 18) *
      (1 - q ^ 19) *
      (1 - q ^ 20) *
      (1 - q ^ 21) *
      (1 - q ^ 22) *
      (1 - q ^ 23) *
      (1 - q ^ 24) *
      (1 - q ^ 25) *
      (1 - q ^ 26) *
      (1 - q ^ 27) *
      (1 - q ^ 28) *
      (1 - q ^ 29) *
      (1 - q ^ 30)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer, Nat.mul_comm]

-- Specialized 2-core numerator: ∏_{k=1}^N (1 - q^{2k})^2
theorem twoCoreNumerator_one (q : R) :
    tCoreNumeratorTrunc 2 q 1 = (1 - q ^ 2) ^ 2 := by
  simp [tCoreNumeratorTrunc]

theorem twoCoreNumerator_two (q : R) :
    tCoreNumeratorTrunc 2 q 2 = (1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 := by
  simp [tCoreNumeratorTrunc]

theorem twoCoreNumerator_three (q : R) :
    tCoreNumeratorTrunc 2 q 3 = (1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 := by
  simp [tCoreNumeratorTrunc]

theorem twoCoreNumerator_four (q : R) :
    tCoreNumeratorTrunc 2 q 4 = (1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 := by
  simp [tCoreNumeratorTrunc]

theorem twoCoreNumerator_five (q : R) :
    tCoreNumeratorTrunc 2 q 5 = (1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 := by
  simp [tCoreNumeratorTrunc]

theorem twoCoreNumerator_six (q : R) :
    tCoreNumeratorTrunc 2 q 6 = (1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2 := by
  simp [tCoreNumeratorTrunc]

theorem twoCoreNumerator_seven (q : R) :
    tCoreNumeratorTrunc 2 q 7 = (1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2 * (1 - q ^ 14) ^ 2 := by
  simp [tCoreNumeratorTrunc]

theorem twoCoreNumerator_eight (q : R) :
    tCoreNumeratorTrunc 2 q 8 = (1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2 * (1 - q ^ 14) ^ 2 * (1 - q ^ 16) ^ 2 := by
  simp [tCoreNumeratorTrunc]

theorem twoCoreNumerator_nine (q : R) :
    tCoreNumeratorTrunc 2 q 9 = (1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2 * (1 - q ^ 14) ^ 2 * (1 - q ^ 16) ^ 2 * (1 - q ^ 18) ^ 2 := by
  simp [tCoreNumeratorTrunc]

theorem twoCoreNumerator_ten (q : R) :
    tCoreNumeratorTrunc 2 q 10 = (1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2 * (1 - q ^ 14) ^ 2 * (1 - q ^ 16) ^ 2 * (1 - q ^ 18) ^ 2 * (1 - q ^ 20) ^ 2 := by
  simp [tCoreNumeratorTrunc]

theorem twoCoreNumerator_eleven (q : R) :
    tCoreNumeratorTrunc 2 q 11 = (1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2 * (1 - q ^ 14) ^ 2 * (1 - q ^ 16) ^ 2 * (1 - q ^ 18) ^ 2 * (1 - q ^ 20) ^ 2 * (1 - q ^ 22) ^ 2 := by
  simp [tCoreNumeratorTrunc]

theorem twoCoreNumerator_twelve (q : R) :
    tCoreNumeratorTrunc 2 q 12 = (1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2 * (1 - q ^ 14) ^ 2 * (1 - q ^ 16) ^ 2 * (1 - q ^ 18) ^ 2 * (1 - q ^ 20) ^ 2 * (1 - q ^ 22) ^ 2 * (1 - q ^ 24) ^ 2 := by
  simp [tCoreNumeratorTrunc]

theorem twoCoreNumerator_thirteen (q : R) :
    tCoreNumeratorTrunc 2 q 13 = (1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2 * (1 - q ^ 14) ^ 2 * (1 - q ^ 16) ^ 2 * (1 - q ^ 18) ^ 2 * (1 - q ^ 20) ^ 2 * (1 - q ^ 22) ^ 2 * (1 - q ^ 24) ^ 2 * (1 - q ^ 26) ^ 2 := by
  simp [tCoreNumeratorTrunc]

theorem twoCoreNumerator_fourteen (q : R) :
    tCoreNumeratorTrunc 2 q 14 = (1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2 * (1 - q ^ 14) ^ 2 * (1 - q ^ 16) ^ 2 * (1 - q ^ 18) ^ 2 * (1 - q ^ 20) ^ 2 * (1 - q ^ 22) ^ 2 * (1 - q ^ 24) ^ 2 * (1 - q ^ 26) ^ 2 * (1 - q ^ 28) ^ 2 := by
  simp [tCoreNumeratorTrunc]

theorem twoCoreNumerator_fifteen (q : R) :
    tCoreNumeratorTrunc 2 q 15 = (1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2 * (1 - q ^ 14) ^ 2 * (1 - q ^ 16) ^ 2 * (1 - q ^ 18) ^ 2 * (1 - q ^ 20) ^ 2 * (1 - q ^ 22) ^ 2 * (1 - q ^ 24) ^ 2 * (1 - q ^ 26) ^ 2 * (1 - q ^ 28) ^ 2 * (1 - q ^ 30) ^ 2 := by
  simp [tCoreNumeratorTrunc]

-- Specialized 3-core numerator: ∏_{k=1}^N (1 - q^{3k})^3
theorem threeCoreNumerator_one (q : R) :
    tCoreNumeratorTrunc 3 q 1 = (1 - q ^ 3) ^ 3 := by
  simp [tCoreNumeratorTrunc]

theorem threeCoreNumerator_two (q : R) :
    tCoreNumeratorTrunc 3 q 2 = (1 - q ^ 3) ^ 3 * (1 - q ^ 6) ^ 3 := by
  simp [tCoreNumeratorTrunc]

theorem threeCoreNumerator_three (q : R) :
    tCoreNumeratorTrunc 3 q 3 = (1 - q ^ 3) ^ 3 * (1 - q ^ 6) ^ 3 * (1 - q ^ 9) ^ 3 := by
  simp [tCoreNumeratorTrunc]

theorem threeCoreNumerator_four (q : R) :
    tCoreNumeratorTrunc 3 q 4 = (1 - q ^ 3) ^ 3 * (1 - q ^ 6) ^ 3 * (1 - q ^ 9) ^ 3 * (1 - q ^ 12) ^ 3 := by
  simp [tCoreNumeratorTrunc]

theorem threeCoreNumerator_five (q : R) :
    tCoreNumeratorTrunc 3 q 5 = (1 - q ^ 3) ^ 3 * (1 - q ^ 6) ^ 3 * (1 - q ^ 9) ^ 3 * (1 - q ^ 12) ^ 3 * (1 - q ^ 15) ^ 3 := by
  simp [tCoreNumeratorTrunc]

theorem threeCoreNumerator_six (q : R) :
    tCoreNumeratorTrunc 3 q 6 = (1 - q ^ 3) ^ 3 * (1 - q ^ 6) ^ 3 * (1 - q ^ 9) ^ 3 * (1 - q ^ 12) ^ 3 * (1 - q ^ 15) ^ 3 * (1 - q ^ 18) ^ 3 := by
  simp [tCoreNumeratorTrunc]

theorem threeCoreNumerator_seven (q : R) :
    tCoreNumeratorTrunc 3 q 7 = (1 - q ^ 3) ^ 3 * (1 - q ^ 6) ^ 3 * (1 - q ^ 9) ^ 3 * (1 - q ^ 12) ^ 3 * (1 - q ^ 15) ^ 3 * (1 - q ^ 18) ^ 3 * (1 - q ^ 21) ^ 3 := by
  simp [tCoreNumeratorTrunc]

theorem threeCoreNumerator_eight (q : R) :
    tCoreNumeratorTrunc 3 q 8 = (1 - q ^ 3) ^ 3 * (1 - q ^ 6) ^ 3 * (1 - q ^ 9) ^ 3 * (1 - q ^ 12) ^ 3 * (1 - q ^ 15) ^ 3 * (1 - q ^ 18) ^ 3 * (1 - q ^ 21) ^ 3 * (1 - q ^ 24) ^ 3 := by
  simp [tCoreNumeratorTrunc]

theorem threeCoreNumerator_nine (q : R) :
    tCoreNumeratorTrunc 3 q 9 = (1 - q ^ 3) ^ 3 * (1 - q ^ 6) ^ 3 * (1 - q ^ 9) ^ 3 * (1 - q ^ 12) ^ 3 * (1 - q ^ 15) ^ 3 * (1 - q ^ 18) ^ 3 * (1 - q ^ 21) ^ 3 * (1 - q ^ 24) ^ 3 * (1 - q ^ 27) ^ 3 := by
  simp [tCoreNumeratorTrunc]

theorem threeCoreNumerator_ten (q : R) :
    tCoreNumeratorTrunc 3 q 10 = (1 - q ^ 3) ^ 3 * (1 - q ^ 6) ^ 3 * (1 - q ^ 9) ^ 3 * (1 - q ^ 12) ^ 3 * (1 - q ^ 15) ^ 3 * (1 - q ^ 18) ^ 3 * (1 - q ^ 21) ^ 3 * (1 - q ^ 24) ^ 3 * (1 - q ^ 27) ^ 3 * (1 - q ^ 30) ^ 3 := by
  simp [tCoreNumeratorTrunc]

-- Specialized 5-core numerator: ∏_{k=1}^N (1 - q^{5k})^5
theorem fiveCoreNumerator_one (q : R) :
    tCoreNumeratorTrunc 5 q 1 = (1 - q ^ 5) ^ 5 := by
  simp [tCoreNumeratorTrunc]

theorem fiveCoreNumerator_two (q : R) :
    tCoreNumeratorTrunc 5 q 2 = (1 - q ^ 5) ^ 5 * (1 - q ^ 10) ^ 5 := by
  simp [tCoreNumeratorTrunc]

theorem fiveCoreNumerator_three (q : R) :
    tCoreNumeratorTrunc 5 q 3 = (1 - q ^ 5) ^ 5 * (1 - q ^ 10) ^ 5 * (1 - q ^ 15) ^ 5 := by
  simp [tCoreNumeratorTrunc]

theorem fiveCoreNumerator_four (q : R) :
    tCoreNumeratorTrunc 5 q 4 = (1 - q ^ 5) ^ 5 * (1 - q ^ 10) ^ 5 * (1 - q ^ 15) ^ 5 * (1 - q ^ 20) ^ 5 := by
  simp [tCoreNumeratorTrunc]

theorem fiveCoreNumerator_five (q : R) :
    tCoreNumeratorTrunc 5 q 5 = (1 - q ^ 5) ^ 5 * (1 - q ^ 10) ^ 5 * (1 - q ^ 15) ^ 5 * (1 - q ^ 20) ^ 5 * (1 - q ^ 25) ^ 5 := by
  simp [tCoreNumeratorTrunc]

theorem fiveCoreNumerator_six (q : R) :
    tCoreNumeratorTrunc 5 q 6 = (1 - q ^ 5) ^ 5 * (1 - q ^ 10) ^ 5 * (1 - q ^ 15) ^ 5 * (1 - q ^ 20) ^ 5 * (1 - q ^ 25) ^ 5 * (1 - q ^ 30) ^ 5 := by
  simp [tCoreNumeratorTrunc]

theorem fiveCoreNumerator_seven (q : R) :
    tCoreNumeratorTrunc 5 q 7 = (1 - q ^ 5) ^ 5 * (1 - q ^ 10) ^ 5 * (1 - q ^ 15) ^ 5 * (1 - q ^ 20) ^ 5 * (1 - q ^ 25) ^ 5 * (1 - q ^ 30) ^ 5 * (1 - q ^ 35) ^ 5 := by
  simp [tCoreNumeratorTrunc]

-- Specialized 2-core ratio: ∏(1-q^{2k})^2 / ∏(1-q^k)
theorem twoCoreRatio_one (q : R) :
    tCoreRatioTrunc 2 q 1 = ((1 - q ^ 2) ^ 2) / ((1 - q)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer]

theorem twoCoreRatio_two (q : R) :
    tCoreRatioTrunc 2 q 2 = ((1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2) / ((1 - q) * (1 - q ^ 2)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer]

theorem twoCoreRatio_three (q : R) :
    tCoreRatioTrunc 2 q 3 = ((1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer]

theorem twoCoreRatio_four (q : R) :
    tCoreRatioTrunc 2 q 4 = ((1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer]

theorem twoCoreRatio_five (q : R) :
    tCoreRatioTrunc 2 q 5 = ((1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer]

theorem twoCoreRatio_six (q : R) :
    tCoreRatioTrunc 2 q 6 = ((1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer]

theorem twoCoreRatio_seven (q : R) :
    tCoreRatioTrunc 2 q 7 = ((1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2 * (1 - q ^ 14) ^ 2) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer]

theorem twoCoreRatio_eight (q : R) :
    tCoreRatioTrunc 2 q 8 = ((1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2 * (1 - q ^ 14) ^ 2 * (1 - q ^ 16) ^ 2) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer]

theorem twoCoreRatio_nine (q : R) :
    tCoreRatioTrunc 2 q 9 = ((1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2 * (1 - q ^ 14) ^ 2 * (1 - q ^ 16) ^ 2 * (1 - q ^ 18) ^ 2) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer]

theorem twoCoreRatio_ten (q : R) :
    tCoreRatioTrunc 2 q 10 = ((1 - q ^ 2) ^ 2 * (1 - q ^ 4) ^ 2 * (1 - q ^ 6) ^ 2 * (1 - q ^ 8) ^ 2 * (1 - q ^ 10) ^ 2 * (1 - q ^ 12) ^ 2 * (1 - q ^ 14) ^ 2 * (1 - q ^ 16) ^ 2 * (1 - q ^ 18) ^ 2 * (1 - q ^ 20) ^ 2) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10)) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer]



-- 7-core numerator
theorem sevenCoreNumerator_one (q : R) :
    tCoreNumeratorTrunc 7 q 1 = (1 - q ^ 7) ^ 7 := by
  simp [tCoreNumeratorTrunc]

theorem sevenCoreNumerator_two (q : R) :
    tCoreNumeratorTrunc 7 q 2 = (1 - q ^ 7) ^ 7 * (1 - q ^ 14) ^ 7 := by
  simp [tCoreNumeratorTrunc]

theorem sevenCoreNumerator_three (q : R) :
    tCoreNumeratorTrunc 7 q 3 = (1 - q ^ 7) ^ 7 * (1 - q ^ 14) ^ 7 * (1 - q ^ 21) ^ 7 := by
  simp [tCoreNumeratorTrunc]

theorem sevenCoreNumerator_four (q : R) :
    tCoreNumeratorTrunc 7 q 4 = (1 - q ^ 7) ^ 7 * (1 - q ^ 14) ^ 7 * (1 - q ^ 21) ^ 7 * (1 - q ^ 28) ^ 7 := by
  simp [tCoreNumeratorTrunc]

theorem sevenCoreNumerator_five (q : R) :
    tCoreNumeratorTrunc 7 q 5 = (1 - q ^ 7) ^ 7 * (1 - q ^ 14) ^ 7 * (1 - q ^ 21) ^ 7 * (1 - q ^ 28) ^ 7 * (1 - q ^ 35) ^ 7 := by
  simp [tCoreNumeratorTrunc]

-- 3-core numerator N=11-15
theorem threeCoreNumerator_eleven (q : R) :
    tCoreNumeratorTrunc 3 q 11 = (1 - q ^ 3) ^ 3 * (1 - q ^ 6) ^ 3 * (1 - q ^ 9) ^ 3 * (1 - q ^ 12) ^ 3 * (1 - q ^ 15) ^ 3 * (1 - q ^ 18) ^ 3 * (1 - q ^ 21) ^ 3 * (1 - q ^ 24) ^ 3 * (1 - q ^ 27) ^ 3 * (1 - q ^ 30) ^ 3 * (1 - q ^ 33) ^ 3 := by
  simp [tCoreNumeratorTrunc]

theorem threeCoreNumerator_twelve (q : R) :
    tCoreNumeratorTrunc 3 q 12 = (1 - q ^ 3) ^ 3 * (1 - q ^ 6) ^ 3 * (1 - q ^ 9) ^ 3 * (1 - q ^ 12) ^ 3 * (1 - q ^ 15) ^ 3 * (1 - q ^ 18) ^ 3 * (1 - q ^ 21) ^ 3 * (1 - q ^ 24) ^ 3 * (1 - q ^ 27) ^ 3 * (1 - q ^ 30) ^ 3 * (1 - q ^ 33) ^ 3 * (1 - q ^ 36) ^ 3 := by
  simp [tCoreNumeratorTrunc]

theorem threeCoreNumerator_thirteen (q : R) :
    tCoreNumeratorTrunc 3 q 13 = (1 - q ^ 3) ^ 3 * (1 - q ^ 6) ^ 3 * (1 - q ^ 9) ^ 3 * (1 - q ^ 12) ^ 3 * (1 - q ^ 15) ^ 3 * (1 - q ^ 18) ^ 3 * (1 - q ^ 21) ^ 3 * (1 - q ^ 24) ^ 3 * (1 - q ^ 27) ^ 3 * (1 - q ^ 30) ^ 3 * (1 - q ^ 33) ^ 3 * (1 - q ^ 36) ^ 3 * (1 - q ^ 39) ^ 3 := by
  simp [tCoreNumeratorTrunc]

theorem threeCoreNumerator_fourteen (q : R) :
    tCoreNumeratorTrunc 3 q 14 = (1 - q ^ 3) ^ 3 * (1 - q ^ 6) ^ 3 * (1 - q ^ 9) ^ 3 * (1 - q ^ 12) ^ 3 * (1 - q ^ 15) ^ 3 * (1 - q ^ 18) ^ 3 * (1 - q ^ 21) ^ 3 * (1 - q ^ 24) ^ 3 * (1 - q ^ 27) ^ 3 * (1 - q ^ 30) ^ 3 * (1 - q ^ 33) ^ 3 * (1 - q ^ 36) ^ 3 * (1 - q ^ 39) ^ 3 * (1 - q ^ 42) ^ 3 := by
  simp [tCoreNumeratorTrunc]

theorem threeCoreNumerator_fifteen (q : R) :
    tCoreNumeratorTrunc 3 q 15 = (1 - q ^ 3) ^ 3 * (1 - q ^ 6) ^ 3 * (1 - q ^ 9) ^ 3 * (1 - q ^ 12) ^ 3 * (1 - q ^ 15) ^ 3 * (1 - q ^ 18) ^ 3 * (1 - q ^ 21) ^ 3 * (1 - q ^ 24) ^ 3 * (1 - q ^ 27) ^ 3 * (1 - q ^ 30) ^ 3 * (1 - q ^ 33) ^ 3 * (1 - q ^ 36) ^ 3 * (1 - q ^ 39) ^ 3 * (1 - q ^ 42) ^ 3 * (1 - q ^ 45) ^ 3 := by
  simp [tCoreNumeratorTrunc]

end Field
end Ch18
end PartIV
end QseriesFormalization
