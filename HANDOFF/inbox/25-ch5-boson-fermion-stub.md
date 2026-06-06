# Task 25: Ch5 — Boson-Fermion correspondence stub (Part I)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Chan Ch 5 (Borcherd's combinatorial proof of JTP). Levels are
`i ∈ ℤ + 1/2` (which we model as `ℤ` with offset, or as a two-sided
sequence). An admissible state differs from the vacuum by finitely
many levels. Charge `Q(S)` and energy `H(S)` are integers/rationals.

Full formalization is heavy combinatorics — this task is just to
land a **structural scaffold** so the namespace exists.

## Goal

Replace `QseriesFormalization/Chapter05.lean` (currently a stub) with:

```lean
import QseriesFormalization.Basic

namespace QseriesFormalization
namespace PartI
namespace Ch05

/-- An admissible "fermion sea" configuration, modelled as the finset
of levels (offset from ℤ+1/2 to ℤ for Lean simplicity) that DIFFER
from the vacuum state. Vacuum has all i ≤ -1 occupied; an admissible
state has finitely many levels added (i ≥ 0 occupied) or removed
(i ≤ -1 vacated). -/
structure AdmissibleState where
  /-- Levels added (i ≥ 0 occupied beyond vacuum). -/
  added : Finset Nat
  /-- Levels removed (i ≤ -1 vacated below vacuum, encoded as Nat for the
  reflection k = -1 - i ≥ 0). -/
  removed : Finset Nat

/-- The vacuum state: nothing added, nothing removed. -/
def vacuum : AdmissibleState := ⟨∅, ∅⟩

/-- Charge `Q(S) := added.card - removed.card`. -/
def charge (S : AdmissibleState) : Int :=
  (S.added.card : Int) - S.removed.card

/-- Energy `H(S) := ∑_{i ∈ added} (i + 1) + ∑_{k ∈ removed} (k + 1)`.
(Using offset `+1` so that the lowest added level i=0 contributes 1, etc.) -/
def energy (S : AdmissibleState) : Nat :=
  S.added.sum (· + 1) + S.removed.sum (· + 1)

/-- Vacuum has charge 0 and energy 0. -/
@[simp] theorem charge_vacuum : charge vacuum = 0 := by simp [charge, vacuum]
@[simp] theorem energy_vacuum : energy vacuum = 0 := by simp [energy, vacuum]

end Ch05
end PartI
end QseriesFormalization
```

## Constraints

- **No `axiom`, no `sorry`, no `native_decide`.**
- `lake build` clean.
- Touch only `Chapter05.lean`.

## Deliverable

1. Modified `Chapter05.lean`.
2. Reply file with status, lake build final line.
