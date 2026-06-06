# Batch 27: Ch09 — BaileyBeta for rrAlpha at N=2

## Context
Chapter09.lean now has (345 lines):
- `BaileyTerm a q α n k`, `BaileyBeta a q α n`
- `rrAlpha a q n` = (-1)^n * q^{n(n-1)/2} * (1 - a*q^{2n}) / (1 - a)
- `rrAlpha_zero`, `rrAlpha_one`
- `BaileyBeta_rrAlpha_zero` : β_0 = 1
- `BaileyBeta_rrAlpha_one_expand` : β_1 = term_0 + term_1
- `BaileyTerm_rrAlpha_one_zero`, `BaileyTerm_rrAlpha_one_one`
- `BaileyTransformAlpha_zero/one`, `BaileyTransformAlpha_rrAlpha_zero/one`
- All within `section Field` / `variable {R : Type*} [Field R]`

## Goal: Extend rrAlpha and BaileyBeta to N=2

### Task 1: rrAlpha_two
```lean
theorem rrAlpha_two (a q : R) :
    rrAlpha a q 2 = q * (1 - a * q ^ 4) / (1 - a) := by
  unfold rrAlpha
  norm_num [triangularNum]  -- or simp + ring
```

Note: triangularNum is NOT used. rrAlpha uses `n * (n - 1) / 2`. For n=2: `2 * (2-1) / 2 = 1`.
So rrAlpha a q 2 = (-1)^2 * q^1 * (1 - a*q^4) / (1-a) = q*(1-a*q^4)/(1-a).

### Task 2: BaileyBeta_rrAlpha_two_expand
```lean
theorem BaileyBeta_rrAlpha_two_expand (a q : R) :
    BaileyBeta a q (rrAlpha a q) 2 =
      BaileyTerm a q (rrAlpha a q) 2 0 +
      BaileyTerm a q (rrAlpha a q) 2 1 +
      BaileyTerm a q (rrAlpha a q) 2 2 := by
  simp [BaileyBeta, natSum]
```

### Task 3: Each BaileyTerm at N=2

BaileyTerm a q α 2 k = α_k / ((q;q)_{2-k} · (aq;q)_{2+k}).

k=0: α_0 / ((q;q)_2 · (aq;q)_2) = 1 / ((1-q)(1-q^2) · (1-aq)(1-aq^2))
k=1: α_1 / ((q;q)_1 · (aq;q)_3) = (-(1-aq^2)/(1-a)) / ((1-q) · (1-aq)(1-aq^2)(1-aq^3))
k=2: α_2 / ((q;q)_0 · (aq;q)_4) = (q(1-aq^4)/(1-a)) / ((1-aq)(1-aq^2)(1-aq^3)(1-aq^4))

```lean
theorem BaileyTerm_rrAlpha_two_zero (a q : R) (ha : 1 - a ≠ 0) :
    BaileyTerm a q (rrAlpha a q) 2 0 =
      1 / ((1 - q) * (1 - q ^ 2) * ((1 - a * q) * (1 - a * q ^ 2))) := by
  simp only [BaileyTerm, rrAlpha_zero a q ha]
  simp [qPochhammer, qPoch]

theorem BaileyTerm_rrAlpha_two_one (a q : R) (ha : 1 - a ≠ 0) :
    BaileyTerm a q (rrAlpha a q) 2 1 =
      -(1 - a * q ^ 2) / ((1 - a) * ((1 - q) * ((1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3)))) := by
  simp only [BaileyTerm, rrAlpha_one]
  simp [qPochhammer, qPoch]
  field_simp

theorem BaileyTerm_rrAlpha_two_two (a q : R) (ha : 1 - a ≠ 0) :
    BaileyTerm a q (rrAlpha a q) 2 2 =
      q * (1 - a * q ^ 4) / ((1 - a) * ((1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4))) := by
  simp only [BaileyTerm, rrAlpha_two]
  simp [qPochhammer, qPoch]
  field_simp
```

## Proof strategy
- `simp [BaileyBeta, natSum]` for sum expansion
- `simp [BaileyTerm, rrAlpha_zero/one/two, qPochhammer, qPoch]` for term evaluation
- `field_simp` + optional `ring` for denominator clearing
- If `field_simp` alone doesn't close it, try `field_simp; ring`

## File: QseriesFormalization/Chapter09.lean
Insert before `end Field` (currently at line 341).

## Constraints
- No sorry, no axiom, no native_decide
- `lake build QseriesFormalization.Chapter09` must pass
- The RHS expressions may need adjustment — the exact form depends on how `simp` normalizes the products. If the stated RHS doesn't match, adjust it to match what `simp` produces.
- For rrAlpha_two: `(-1)^2 = 1`, `2*(2-1)/2 = 1` in Nat, so the result is `q^1 * (1-a*q^4)/(1-a)`.

## Build command
```
lake build QseriesFormalization.Chapter09
```
