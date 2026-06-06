# Batch 24: Ch09 — BaileyBeta for rrAlpha at N=1

## Context
Chapter09.lean (316 lines) has:
- `BaileyTerm a q α n k` — the k-th summand
- `BaileyBeta a q α n` — β_n = natSum(BaileyTerm) over k=0..n
- `rrAlpha a q n` = (-1)^n * q^{n(n-1)/2} * (1 - a*q^{2n}) / (1 - a)
- `rrAlpha_zero` : rrAlpha a q 0 = 1
- `rrAlpha_one` : rrAlpha a q 1 = -(1 - a*q^2)/(1 - a)
- `BaileyBeta_rrAlpha_zero` : BaileyBeta a q (rrAlpha a q) 0 = 1
- All within `section Field` / `variable {R : Type*} [Field R]`
- Uses `qPochhammer` from Basic.lean and `qPoch` from Basic.lean

## Goal: Verify BaileyBeta_rrAlpha for N=1

### Task 1: BaileyBeta_rrAlpha_one

Compute BaileyBeta a q (rrAlpha a q) 1, which expands as:

β_1 = ∑_{k=0}^{1} α_k / ((q;q)_{1-k} · (aq;q)_{1+k})
    = α_0 / ((q;q)_1 · (aq;q)_1) + α_1 / ((q;q)_0 · (aq;q)_2)
    = 1/((1-q)(1-aq)) + (-(1-aq^2)/(1-a)) / (1 · (1-aq)(1-aq^2))
    = 1/((1-q)(1-aq)) + (-1)/((1-a)(1-aq))
    = 1/((1-aq)) · (1/(1-q) - 1/(1-a))
    = 1/((1-aq)) · (a-q)/((1-q)(1-a))

Actually β_1 = (a-q)/((1-q)(1-a)(1-aq)) but check the sign carefully.

The target value for a Bailey pair relative to a should be:
β_1 = 1 / ((q;q)_1 · (aq;q)_1) = 1 / ((1-q)(1-aq))

Wait — for the UNIT Bailey pair (α_0 = 1, α_n = 0 for n ≥ 1), β_n = 1/((q;q)_n · (aq;q)_n).
But for the RR seed, β_0 = 1, and β_n for n ≥ 1 is NOT simply 1/((q;q)_n · (aq;q)_n).

So the correct theorem is just to compute the explicit value:

```lean
theorem BaileyBeta_rrAlpha_one (a q : R) (ha : 1 - a ≠ 0)
    (hq : 1 - q ≠ 0) (haq : 1 - a * q ≠ 0) (haq2 : 1 - a * q ^ 2 ≠ 0) :
    BaileyBeta a q (rrAlpha a q) 1 =
      (1 / ((1 - q) * (1 - a * q)) +
       (-(1 - a * q ^ 2) / (1 - a)) / ((1 - a * q) * (1 - a * q ^ 2))) := by
  simp [BaileyBeta, natSum, BaileyTerm, rrAlpha, qPochhammer, qPoch]
```

Hmm, this might be hard to state cleanly. A more practical approach:

```lean
/-- BaileyBeta at N=1 expands to a two-term sum. -/
theorem BaileyBeta_rrAlpha_one_expand (a q : R) (ha : 1 - a ≠ 0) :
    BaileyBeta a q (rrAlpha a q) 1 =
      BaileyTerm a q (rrAlpha a q) 1 0 + BaileyTerm a q (rrAlpha a q) 1 1 := by
  simp [BaileyBeta, natSum]

/-- The k=0 term of BaileyBeta at N=1. -/
theorem BaileyTerm_rrAlpha_one_zero (a q : R) (ha : 1 - a ≠ 0) :
    BaileyTerm a q (rrAlpha a q) 1 0 =
      1 / ((1 - q) * (1 - a * q)) := by
  simp [BaileyTerm, rrAlpha, qPochhammer, qPoch]
  field_simp
  ring

/-- The k=1 term of BaileyBeta at N=1. -/
theorem BaileyTerm_rrAlpha_one_one (a q : R) (ha : 1 - a ≠ 0) :
    BaileyTerm a q (rrAlpha a q) 1 1 =
      -(1 - a * q ^ 2) / ((1 - a) * (1 - a * q) * (1 - a * q ^ 2)) := by
  simp [BaileyTerm, rrAlpha, qPochhammer, qPoch]
  field_simp
  ring
```

### Proof Strategy
1. `simp [BaileyBeta, natSum]` to expand the sum
2. `simp [BaileyTerm, rrAlpha, qPochhammer, qPoch]` to expand each term
3. `field_simp` to clear denominators
4. `ring` to verify polynomial identity

### Task 2: BaileyTransformAlpha applied to rrAlpha at N=1

```lean
theorem BaileyTransformAlpha_rrAlpha_one (a q ρ₁ ρ₂ : R) (ha : 1 - a ≠ 0) :
    BaileyTransformAlpha a q ρ₁ ρ₂ (rrAlpha a q) 1 =
      (1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
      ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) *
      (-(1 - a * q ^ 2) / (1 - a)) := by
  rw [BaileyTransformAlpha_one, rrAlpha_one]
```

## File: QseriesFormalization/Chapter09.lean
Insert before `end Field` at line 312.

## Constraints
- No sorry, no axiom, no native_decide
- `lake build QseriesFormalization.Chapter09` must pass
- If `field_simp; ring` fails, try `simp [BaileyTerm, rrAlpha, qPochhammer, qPoch]; field_simp` and simplify step by step
- The `ha : 1 - a ≠ 0` hypothesis may need to be used via `exact ha` or `field_simp [ha]`

## Build command
```
lake build QseriesFormalization.Chapter09
```
