# Batch 52: Exercise wrapper for Ch09 Bailey coefficient identity

## Context

Work in `~/.openclaw/workspace/projects/Q-series-and-Chan-s-work`.

`QseriesFormalization/Chapter09.lean` now contains:

```lean
theorem BaileyTransform_one_alpha_zero_coefficient_identity
    (a q ρ₁ ρ₂ : R) (hρ : ρ₁ * ρ₂ ≠ 0) :
    (1 - a * q) * (1 - a * q / (ρ₁ * ρ₂)) +
        (1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) =
      (1 - a * q / ρ₁) * (1 - a * q / ρ₂)
```

## Task

Add a thin exercise wrapper in `QseriesFormalization/Exercises.lean`, near the other Chapter 9 wrappers.

Use a name matching the local style, for example:

```lean
theorem exercise9_BaileyTransform_one_alpha_zero_coefficient_identity ...
```

The proof should just call the Ch09 theorem.

## Constraints

- Touch only `QseriesFormalization/Exercises.lean`.
- No `sorry`, no `axiom`, no `native_decide`.
- Build only:

```bash
lake build QseriesFormalization.Exercises
```

- Write results to:

```text
HANDOFF/outbox/batch52-exercises-ch09-bailey-coeff-wrapper-reply.md
```
