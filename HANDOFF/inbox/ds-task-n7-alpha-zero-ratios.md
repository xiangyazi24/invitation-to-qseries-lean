# DS Task: 6 alpha_zero scalar-ratio lemmas for n=7 (Ch09 Bailey)

You are generating Lean 4 / Mathlib v4.27.0 code. Output ONLY Lean code (no
markdown fences, no commentary).

## Context

The n=7 alpha_zero common-denominator identity factors into 6 scalar-ratio
lemmas, each combining a qPochhammer ratio with a qPoch (a*q) ratio via
`BaileyTransform_ratio_mul`. Existing n=6 template (already in Chapter09.lean):

```lean
theorem BaileyTransform_six_alpha_zero_first_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 6 /
        (qPochhammer q 5 * qPochhammer q 1 * qPoch (a * q) q 1) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) *
        ((1 - a * q ^ 2) * (1 - a * q ^ 3) *
          (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6)) := by
  have hQ5Q1 : qPochhammer q 5 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ5 hQ1
  have hQ := BaileyTransform_six_qpochhammer_six_over_five_one q hQ1 hQ5
  have hA := BaileyTransform_six_qpoch_aq_six_over_one a q hA1
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 5 * qPochhammer q 1)
      (qPoch (a * q) q 6) (qPoch (a * q) q 1)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5)
      ((1 - a * q ^ 2) * (1 - a * q ^ 3) *
        (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6))
      hQ5Q1 hA1 hQ hA
```

The 7 cross-pairs at n=7 are (k, 7-k) for k=1..6, giving 6 ratio lemmas.

## Already-built n=7 helpers you can call

qPochhammer ratios (each takes hQ1 and the relevant qPochhammer hypothesis):

  BaileyTransform_seven_qpochhammer_seven_over_six_one  → q-binomial [7,1]
    = 1 + q + q² + q³ + q⁴ + q⁵ + q⁶
  BaileyTransform_seven_qpochhammer_seven_over_one_six  (commuted)
  BaileyTransform_seven_qpochhammer_seven_over_five_two → [7,2]
    = (1 + q + q² + q³ + q⁴ + q⁵ + q⁶) * (1 + q² + q⁴)
  BaileyTransform_seven_qpochhammer_seven_over_two_five (commuted)
  BaileyTransform_seven_qpochhammer_seven_over_four_three → [7,3] (not factor)
    = 1 + q + 2*q² + 3*q³ + 4*q⁴ + 4*q⁵ + 5*q⁶ + 4*q⁷ + 4*q⁸ + 3*q⁹ + 2*q¹⁰ + q¹¹ + q¹²
  BaileyTransform_seven_qpochhammer_seven_over_three_four (commuted)

qPoch (a*q) ratios (each takes the relevant qPoch (a*q) ≠ 0 hypothesis):

  BaileyTransform_seven_qpoch_aq_seven_over_one
    = (1 - a*q²)(1 - a*q³)(1 - a*q⁴)(1 - a*q⁵)(1 - a*q⁶)(1 - a*q⁷)
  BaileyTransform_seven_qpoch_aq_seven_over_two
    = (1 - a*q³)(1 - a*q⁴)(1 - a*q⁵)(1 - a*q⁶)(1 - a*q⁷)
  BaileyTransform_seven_qpoch_aq_seven_over_three
    = (1 - a*q⁴)(1 - a*q⁵)(1 - a*q⁶)(1 - a*q⁷)
  BaileyTransform_seven_qpoch_aq_seven_over_four
    = (1 - a*q⁵)(1 - a*q⁶)(1 - a*q⁷)
  BaileyTransform_seven_qpoch_aq_seven_over_five
    = (1 - a*q⁶)(1 - a*q⁷)
  BaileyTransform_seven_qpoch_aq_seven_over_six
    = (1 - a*q⁷)

## Generic combining theorem (already in file)

```lean
theorem BaileyTransform_ratio_mul (Q D Q' D' P P' : R)
    (hD : D ≠ 0) (hD' : D' ≠ 0)
    (hQ : Q / D = P) (hQ' : Q' / D' = P') :
    Q * Q' / (D * D') = P * P'
```

Returns the product `Q * Q' / (D * D') = P * P'` given individual ratios.

## Task: Write 6 theorems

Names follow the n=6 pattern with "_seven_" prefix:

  BaileyTransform_seven_alpha_zero_first_ratio  (k=1, pair (6, 1))
  BaileyTransform_seven_alpha_zero_second_ratio (k=2, pair (5, 2))
  BaileyTransform_seven_alpha_zero_third_ratio  (k=3, pair (4, 3))
  BaileyTransform_seven_alpha_zero_fourth_ratio (k=4, pair (3, 4))
  BaileyTransform_seven_alpha_zero_fifth_ratio  (k=5, pair (2, 5))
  BaileyTransform_seven_alpha_zero_sixth_ratio  (k=6, pair (1, 6))

For each `k` in {1..6}, the lemma:

  qPochhammer q 7 * qPoch (a * q) q 7 /
      (qPochhammer q (7 - k) * qPochhammer q k * qPoch (a * q) q k) =
    (q-binomial [7, k]_q) *
      (qPoch (a * q) q 7 / qPoch (a * q) q k expanded as product)

Hypotheses: as needed for the qPochhammer ratio (hQ1, possibly hQ2 / hQ3 / hQ4 / hQ5 / hQ6 / hQ(7-k)) plus hAk for qPoch (a*q) q k.

Pattern of body (mirroring n=6 first_ratio):

  have hQ_combo : qPochhammer q (7-k) * qPochhammer q k ≠ 0 :=
    mul_ne_zero h(7-k) hk
  have hQ := BaileyTransform_seven_qpochhammer_seven_over_(7-k)_(k) q ...
  have hA := BaileyTransform_seven_qpoch_aq_seven_over_(k) a q hAk
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 7)
      (qPochhammer q (7-k) * qPochhammer q k)
      (qPoch (a * q) q 7) (qPoch (a * q) q k)
      <q-binomial [7,k] polynomial>
      <(1 - a*q^(k+1)) * ... * (1 - a*q^7)>
      hQ_combo hAk hQ hA

For pair (3, 4) (third_ratio, k=3) and (4, 3) (fourth_ratio, k=4):
- third_ratio uses seven_qpochhammer_seven_over_four_three
- fourth_ratio uses seven_qpochhammer_seven_over_three_four

The [7,3]_q polynomial goes verbatim (it does not factor).

## Constraints

- No `sorry`, no `axiom`.
- No surrounding markdown.
- Same `section Field` / `variable {R : Type*} [Field R]` scope assumed.
- Match the doc-comment style:
  `/-- The k-th scalar ratio in the `n = 7`, α₀ common-denominator calculation. -/`

## Output

Just the six theorems, one after another. No surrounding text.
