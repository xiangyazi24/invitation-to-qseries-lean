# Batch 48: Chapter 5 Ferrers column double-counting wrappers

Added exercise wrappers for the following theorems from `Chapter05.lean` into `Exercises.lean`:

- `exercise5_mem_FerrersDiagramCellsByColumnsUpTo_iff`
- `exercise5_FerrersDiagramCellsByColumnsUpTo_eq_of_bound`
- `exercise5_FerrersDiagramCellsByColumnsUpTo_card`
- `exercise5_FerrersDiagramCells_card_eq_sum_column_cards_of_bound`
- `exercise5_FerrersColumnHeightsUpTo_length`
- `exercise5_partitionWeight_FerrersColumnHeightsUpTo`

## Verification Results

- `lake build QseriesFormalization.Exercises` completed successfully.
- `rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean QseriesFormalization/Chapter05.lean` returned no matches.

## Changes in QseriesFormalization/Exercises.lean

```lean
/-- Exercise (Chapter 5 style): membership in the column-grouped Ferrers diagram with a bound. -/
theorem exercise5_mem_FerrersDiagramCellsByColumnsUpTo_iff {lam : List Nat} {N r c : Nat} :
    (r, c) ∈ PartI.Ch05.FerrersDiagramCellsByColumnsUpTo lam N ↔ PartI.Ch05.FerrersCell lam r c ∧ c < N :=
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

/-- Exercise (Chapter 5 style): the weight of the truncated column-height list is the sum of its heights. -/
theorem exercise5_partitionWeight_FerrersColumnHeightsUpTo (lam : List Nat) (N : Nat) :
    partitionWeight (PartI.Ch05.FerrersColumnHeightsUpTo lam N) =
      (Finset.range N).sum (fun c => (PartI.Ch05.FerrersColumnCells lam c).card) :=
  PartI.Ch05.partitionWeight_FerrersColumnHeightsUpTo lam N
```
