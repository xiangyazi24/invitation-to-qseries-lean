# Chapter 5 Franklin involution — closing strategy

**Source**: ChatGPT consultation 2026-05-14 (task `4a8a28d7`).

## Diagnosis

From CHECKPOINT, the active-domain Franklin bijection is essentially proved.
The MISSING piece is the **global packaging theorem**:

```lean
IsStrictPartition λ →
¬ IsPentagonalFixedShape λ →
∃! μ, IsFranklinMovePair λ μ
```

plus the symmetric/involutive consequences. This is NOT another local Franklin
move lemma — it's the global wrapper assembling local branch analysis.

## Recommended next theorems (in order)

### 1. Active-domain wrapper

```lean
theorem franklin_nonfixed_active
    (hstrict : IsStrictPartition λ)
    (hnfixed : ¬ IsPentagonalFixedShape λ) :
    FranklinActiveDomain λ := by
  -- use four-way split + fixed-shape exclusion (already in CHECKPOINT)
```

### 2. Unique target

```lean
theorem franklin_nonfixed_unique_target
    (hstrict : IsStrictPartition λ)
    (hnfixed : ¬ IsPentagonalFixedShape λ) :
    ∃! μ, IsFranklinMovePair λ μ := by
  exact active_domain_unique_target ...
```

### 3. Weight & sign

```lean
theorem franklin_nonfixed_weight_sign_reverse
    (hpair : IsFranklinMovePair λ μ) :
    weight μ = weight λ ∧ sign μ = - sign λ := by
  exact ⟨franklin_weight_preserving hpair, franklin_sign_reversing hpair⟩
```

### 4. Complement structure theorem (the GLOBAL closure)

```lean
theorem strict_partition_inactive_iff_fixed
    (hstrict : IsStrictPartition λ) :
    ¬ FranklinActiveDomain λ ↔ IsPentagonalFixedShape λ
```

This assembles all local branch analysis into a global statement.

### 5. Alternating-sum assembly (Boson-Fermion)

```lean
theorem franklin_cancel_nonfixed_weight_fiber (N : ℕ) :
    (strictPartitionsOfWeight N).sum
      (fun λ => if IsPentagonalFixedShape λ then sign λ else 0)
    =
    (strictPartitionsOfWeight N).sum sign
```

Pair nonfixed terms by Franklin involution.

## Scope notes

- **Don't handle non-strict partitions inside Franklin.** Exclude at the
  statement boundary via `λ ∈ strictPartitionsOfWeight N`. The fermionic
  side is strict/distinct partitions only.
- The Boson-Fermion correspondence statement is the alternating-sum
  formula at the end of Ch5.

## Assignment

Per existing CHECKPOINT, Codex is working on Ch5. This doc gives the next
3-5 theorem shapes for them to target.
