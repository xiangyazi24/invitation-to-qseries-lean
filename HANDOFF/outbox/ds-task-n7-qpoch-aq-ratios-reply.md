/-- The ratio `(aq;q)_7 / (aq;q)_1`. -/
theorem BaileyTransform_seven_qpoch_aq_seven_over_one
    (a q : R) (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 1 =
      (1 - a * q ^ 2) * (1 - a * q ^ 3) *
        (1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) * (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 1 * (1 - (a * q) * q ^ 1) *
        (1 - (a * q) * q ^ 2) * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) by rfl]
  simp only [pow_one]
  field_simp [hA1]

/-- The ratio `(aq;q)_7 / (aq;q)_2`. -/
theorem BaileyTransform_seven_qpoch_aq_seven_over_two
    (a q : R) (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 2 =
      (1 - a * q ^ 3) * (1 - a * q ^ 4) *
        (1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 2 * (1 - (a * q) * q ^ 2) *
        (1 - (a * q) * q ^ 3) * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) * (1 - (a * q) * q ^ 6) by rfl]
  simp only [pow_one]
  field_simp [hA2]

/-- The ratio `(aq;q)_7 / (aq;q)_3`. -/
theorem BaileyTransform_seven_qpoch_aq_seven_over_three
    (a q : R) (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 3 =
      (1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) * (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 3 * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) by rfl]
  simp only [pow_one]
  field_simp [hA3]

/-- The ratio `(aq;q)_7 / (aq;q)_4`. -/
theorem BaileyTransform_seven_qpoch_aq_seven_over_four
    (a q : R) (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 4 =
      (1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 4 * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) * (1 - (a * q) * q ^ 6) by rfl]
  simp only [pow_one]
  field_simp [hA4]

/-- The ratio `(aq;q)_7 / (aq;q)_5`. -/
theorem BaileyTransform_seven_qpoch_aq_seven_over_five
    (a q : R) (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 5 =
      (1 - a * q ^ 6) * (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 5 * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) by rfl]
  simp only [pow_one]
  field_simp [hA5]

/-- The ratio `(aq;q)_7 / (aq;q)_6`. -/
theorem BaileyTransform_seven_qpoch_aq_seven_over_six
    (a q : R) (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 6 =
      (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 6 * (1 - (a * q) * q ^ 6) by rfl]
  simp only [pow_one]
  field_simp [hA6]
