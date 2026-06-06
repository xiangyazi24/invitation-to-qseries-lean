# Task 46: Ch5 — charge / energy further properties

## Goal

In `Chapter05.lean` (current state has AdmissibleState, vacuum,
charge, energy, charge_vacuum, energy_vacuum):

Add these:

```lean
/-- Adding a single empty level k (i ≥ 0 occupied) gives charge +1. -/
theorem charge_add_single (k : Nat) :
    charge ⟨{k}, ∅⟩ = 1 := by
  simp [charge]

/-- Removing a single level vacates: charge -1. -/
theorem charge_remove_single (k : Nat) :
    charge ⟨∅, {k}⟩ = -1 := by
  simp [charge]

/-- Energy of single added level k = k+1. -/
theorem energy_add_single (k : Nat) :
    energy ⟨{k}, ∅⟩ = k + 1 := by
  simp [energy]

/-- Energy of single removed level k = k+1. -/
theorem energy_remove_single (k : Nat) :
    energy ⟨∅, {k}⟩ = k + 1 := by
  simp [energy]
```

Touch only `Chapter05.lean`. No axiom/sorry/native_decide. lake build clean.

## Deliverable

Modified file + reply.
