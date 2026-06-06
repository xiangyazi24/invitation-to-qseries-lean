# Batch 29: Ch05 — Ferrers diagram foundation lemmas

## Context

We are formalizing Chan's *An Invitation to q-Series* in Lean 4.
Current priority is theory infrastructure, not extending truncation tables.

`QseriesFormalization/Chapter05.lean` currently has:

- `AdmissibleState`
- `vacuum`
- `charge`
- `energy`
- small charge/energy lemmas

The Franklin involution work needs a lightweight Ferrers diagram interface
before the actual involution proof.

## Goal

Touch only `QseriesFormalization/Chapter05.lean`.

Add a small Ferrers diagram foundation using the existing list-based partition
representation from `Basic.lean`:

```lean
def FerrersCell (λ : List Nat) (r c : Nat) : Prop :=
  r < λ.length ∧ c < λ.getD r 0
```

Then prove small, useful lemmas/examples:

```lean
theorem FerrersCell_nil (r c : Nat) :
    FerrersCell [] r c ↔ False := by ...

theorem FerrersCell_row_bound {λ : List Nat} {r c : Nat}
    (h : FerrersCell λ r c) : r < λ.length := h.1

theorem FerrersCell_col_bound {λ : List Nat} {r c : Nat}
    (h : FerrersCell λ r c) : c < λ.getD r 0 := h.2

theorem FerrersCell_singleton {n r c : Nat} :
    FerrersCell [n] r c ↔ r = 0 ∧ c < n := by ...

theorem FerrersCell_three_two_one_zero_zero :
    FerrersCell [3, 2, 1] 0 0 := by ...

theorem FerrersCell_three_two_one_one_one :
    FerrersCell [3, 2, 1] 1 1 := by ...

theorem not_FerrersCell_three_two_one_two_one :
    ¬ FerrersCell [3, 2, 1] 2 1 := by ...
```

If these exact names conflict, use nearby names and report the final names.

## Constraints

- No `sorry`, no `axiom`, no `native_decide`.
- Do not touch any other file.
- Build only this chapter:

```bash
lake build QseriesFormalization.Chapter05
```

Also run:

```bash
rg -n "sorry|axiom|native_decide" QseriesFormalization/Chapter05.lean
```

Expected result for the `rg` command: no matches.

## Report

Write a short reply under `HANDOFF/outbox/batch29-ch05-ferrers-foundation-reply.md`
with:

- declarations added
- build result
- any exact theorem-name changes
