import QseriesFormalization.Chapter09

open QseriesFormalization QseriesFormalization.PartII.Ch09 QseriesFormalization.PartI.Ch03 Finset

section Field
variable {R : Type*} [Field R]

private lemma shift_term_eq (x q : R) (N k : Nat) (hk : k ≤ N) :
    x ^ (k + 1) * q ^ ((k + 1) * (k + 1)) * (q ^ (N - k) * gaussianBinom q N k) /
      qPoch (x * q) q (k + 1) =
    x * q ^ (N + 1) / (1 - x * q) *
      ((x * q) ^ k * q ^ (k * k) * gaussianBinom q N k / qPoch (x * q ^ 2) q k) := by
  rw [qPoch_xq_succ_shift]
  -- Both sides have denominator (1-xq) * qPoch(xq²;q)_k
  -- RHS: (a/b) * (c/d) = a*c / (b*d)
  rw [div_mul_eq_mul_div, div_div]
  -- Now both are .../((1-xq) * qPoch(xq²;q)_k)
  -- Show numerators are equal
  congr 1
  -- x^{k+1} q^{(k+1)²} (q^{N-k} [N;k]) = x q^{N+1} (xq)^k q^{k²} [N;k]
  rw [mul_pow, ← pow_add q ((k + 1) * (k + 1)) (N - k)]
  have hexp : (k + 1) * (k + 1) + (N - k) = k * k + k + (N + 1) := by omega
  rw [hexp]; ring

private lemma s1_last_zero (x q : R) (N : Nat) :
    x ^ (N + 1) * q ^ ((N + 1) * (N + 1)) * gaussianBinom q N (N + 1) /
      qPoch (x * q) q (N + 1) = 0 := by
  have : gaussianBinom q N (N + 1) = 0 := gaussianBinom_eq_zero_of_lt q (by omega)
  simp [this]

private lemma qPoch_xqq_eq (x q : R) (k : Nat) :
    qPoch (x * q * q) q k = qPoch (x * q ^ 2) q k := by
  congr 1; ring

set_option maxHeartbeats 1600000 in
theorem lemma91Base_recurrence_proof (x q : R) (N : Nat)
    (hxq : (1 : R) - x * q ≠ 0) :
    lemma91Base x q (N + 1) =
      lemma91Base x q N +
        x * q ^ (N + 1) / (1 - x * q) * lemma91Base (x * q) q N := by
  simp only [lemma91Base]
  simp_rw [qPoch_xqq_eq]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.zero_mul, one_mul, gaussianBinom_zero_right, qPoch_zero, div_one]
  have hgb : ∀ k ∈ Finset.range (N + 1),
      x ^ (k + 1) * q ^ ((k + 1) * (k + 1)) * gaussianBinom q (N + 1) (k + 1) /
        qPoch (x * q) q (k + 1) =
      x ^ (k + 1) * q ^ ((k + 1) * (k + 1)) * gaussianBinom q N (k + 1) /
        qPoch (x * q) q (k + 1) +
      x * q ^ (N + 1) / (1 - x * q) *
        ((x * q) ^ k * q ^ (k * k) * gaussianBinom q N k / qPoch (x * q ^ 2) q k) := by
    intro k hk
    have hk_le : k ≤ N := by simp [mem_range] at hk; omega
    show x ^ (k + 1) * q ^ ((k + 1) * (k + 1)) *
        (gaussianBinom q N (k + 1) + q ^ (N - k) * gaussianBinom q N k) /
        qPoch (x * q) q (k + 1) = _
    rw [mul_add, add_div]; congr 1
    exact shift_term_eq x q N k hk_le
  rw [sum_congr rfl hgb, sum_add_distrib, ← mul_sum]
  -- State: (S1 + factor*G) + 1 = base + factor*G
  -- Rearrange: (S1 + F*G) + 1 → (1 + S1) + F*G
  conv_lhs => rw [show ∀ (a b c : R), (a + b) + c = (c + a) + b from by intro a b c; abel]
  -- (1 + S1) + factor*G = base + factor*G
  congr 1
  -- 1 + S1 = base
  rw [sum_range_succ, s1_last_zero, add_zero]
  rw [sum_range_succ']
  simp only [pow_zero, Nat.zero_mul, one_mul, gaussianBinom_zero_right, qPoch_zero, div_one]
  simp_rw [show ∀ n : Nat, 1 + n = n + 1 from fun n => Nat.add_comm 1 n]
  abel

end Field
