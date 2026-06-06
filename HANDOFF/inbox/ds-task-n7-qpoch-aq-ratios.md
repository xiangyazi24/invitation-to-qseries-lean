# DS Task: N=7 qPoch (a*q) ratio helpers for Ch09 Bailey lemma

You are generating Lean 4 / Mathlib v4.27.0 code. Output ONLY Lean code (no
markdown fences, no commentary). The code will be appended to
`QseriesFormalization/Chapter09.lean`. The code must build with
`lake build QseriesFormalization.Chapter09` with no warnings.

## Context

Existing Ch09 helpers compute qPoch (a*q) q n / qPoch (a*q) q k as products of
(1 - a*q^j) factors. The N=6 series (already in the file) follows the template:

```lean
/-- The ratio `(aq;q)_6 / (aq;q)_1`. -/
theorem BaileyTransform_six_qpoch_aq_six_over_one
    (a q : R) (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPoch (a * q) q 6 / qPoch (a * q) q 1 =
      (1 - a * q ^ 2) * (1 - a * q ^ 3) *
        (1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) := by
  rw [show qPoch (a * q) q 6 =
      qPoch (a * q) q 1 * (1 - (a * q) * q ^ 1) *
        (1 - (a * q) * q ^ 2) * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) * (1 - (a * q) * q ^ 5) by rfl]
  simp only [pow_one]
  field_simp [hA1]
```

The denominator `qPoch (a * q) q n / qPoch (a * q) q k` for `k < n` simplifies
to the product of `(1 - a * q^(k+1)) * (1 - a * q^(k+2)) * ... * (1 - a * q^n)`.

## Task

Write the seven theorems for the n=7 case. Names follow exact pattern:

  BaileyTransform_seven_qpoch_aq_seven_over_one
  BaileyTransform_seven_qpoch_aq_seven_over_two
  BaileyTransform_seven_qpoch_aq_seven_over_three
  BaileyTransform_seven_qpoch_aq_seven_over_four
  BaileyTransform_seven_qpoch_aq_seven_over_five
  BaileyTransform_seven_qpoch_aq_seven_over_six
  (six total — k = 1..6)

For each `over_k`:
- Hypothesis: `(hAk : qPoch (a * q) q k ≠ 0)`
- Statement: `qPoch (a * q) q 7 / qPoch (a * q) q k = ∏_{j=k+1}^{7} (1 - a * q ^ j)`
- Proof: same template as `BaileyTransform_six_qpoch_aq_six_over_one`,
  but the `show` must rewrite `qPoch (a * q) q 7` as
  `qPoch (a * q) q k * (1 - (a*q) * q^k) * (1 - (a*q) * q^(k+1)) * ... * (1 - (a*q) * q^6)`
  by `rfl`. The factors cover indices k through 6 (6 - k + 1 = 7 - k factors total).
  Then `simp only [pow_one]` plus `field_simp [hAk]`.

## Constraints

- Each theorem is in the same `section Field` / `variable {R : Type*} [Field R]`
  scope as the existing N=6 helpers, so just write theorems (no namespace, no
  variable declarations).
- No `sorry`, no `axiom`.
- The doc comments should follow the same `/-- The ratio `(aq;q)_7 / (aq;q)_k`. -/`
  format.

## Output

Just the six theorems, one after another, exactly the format of the N=6 example.
No surrounding text, no markdown fences, no closing comments.
