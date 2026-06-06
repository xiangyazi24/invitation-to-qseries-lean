import QseriesFormalization.Chapter17_Mod5ResidueAnalysis
import QseriesFormalization.Chapter19

/-!
# Chapter 17 — Per-term mod-5 residue obstruction (helpers)

Helpers for closing the Finset.sum convolution sorry in
`Pending/Chapter17_Ramanujan5Conditional.lean`.

Strategy: when `jacobiTripleSign n ≠ 0`, the `List.find?` in its
definition returned `some k`, giving us `k ≤ n` with `n = k(k+1)/2`.
Similarly for `pentagonalSign`.

These extraction lemmas are the bridge from the existential structure
of `jacobiTripleSign` / `pentagonalSign` (defined via `find?`) to
explicit triangular / pentagonal indices, which the residue analysis
of `Chapter17_Mod5ResidueAnalysis` can then dispatch.
-/

namespace QseriesFormalization
namespace PartIV
namespace Ch17

open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartI.Ch04Franklin

/-- When `jacobiTripleSign n ≠ 0`, we can extract a witness `k ≤ n`
with `n = k * (k + 1) / 2` and the sign formula. -/
theorem jacobiTripleSign_ne_zero_extract (n : Nat) (h : jacobiTripleSign n ≠ 0) :
    ∃ k, k ≤ n ∧ n = k * (k + 1) / 2 ∧
      jacobiTripleSign n = (-1 : Int) ^ k * (2 * k + 1) := by
  unfold jacobiTripleSign at h ⊢
  generalize h_find :
    (List.range (n + 1)).find? (fun k => n = k * (k + 1) / 2) = res
  rcases res with _ | k
  · rw [h_find] at h; simp at h
  · refine ⟨k, ?_, ?_, rfl⟩
    · have hk_range : k ∈ List.range (n + 1) := List.mem_of_find?_eq_some h_find
      exact Nat.lt_succ_iff.mp (List.mem_range.mp hk_range)
    · have hk_pred := List.find?_some h_find
      simpa using hk_pred

/-- When `pentagonalSign n ≠ 0`, we can extract a witness `k ≤ n` such
that `n` equals either the "minus side" `k(3k-1)/2` or the "plus side"
`k(3k+1)/2` pentagonal number, and `pentagonalSign n = (-1)^k`. -/
theorem pentagonalSign_ne_zero_extract (n : Nat) (h : pentagonalSign n ≠ 0) :
    ∃ k, k ≤ n ∧
      (n = k * (3 * k - 1) / 2 ∨ (0 < k ∧ n = k * (3 * k + 1) / 2)) ∧
      pentagonalSign n = (-1 : Int) ^ k := by
  unfold pentagonalSign at h ⊢
  generalize h_find1 :
    (List.range (n + 1)).find? (fun k => n = k * (3 * k - 1) / 2) = res1
  rcases res1 with _ | k1
  · -- First find? returned none; check second find?.
    rw [h_find1] at h
    simp only at h
    generalize h_find2 :
      (List.range (n + 1)).find? (fun k => 0 < k ∧ n = k * (3 * k + 1) / 2) = res2
    rcases res2 with _ | k2
    · rw [h_find2] at h; simp at h
    · refine ⟨k2, ?_, Or.inr ?_, ?_⟩
      · have hk_range : k2 ∈ List.range (n + 1) :=
          List.mem_of_find?_eq_some h_find2
        exact Nat.lt_succ_iff.mp (List.mem_range.mp hk_range)
      · have hk_pred := List.find?_some h_find2
        simpa using hk_pred
      · rfl
  · refine ⟨k1, ?_, Or.inl ?_, ?_⟩
    · have hk_range : k1 ∈ List.range (n + 1) :=
        List.mem_of_find?_eq_some h_find1
      exact Nat.lt_succ_iff.mp (List.mem_range.mp hk_range)
    · have hk_pred := List.find?_some h_find1
      simpa using hk_pred
    · rfl

/-! ## Cast-to-ZMod-5 helpers for triangular and pentagonal residues -/

/-- Cast of triangular `k(k+1)/2` to `ZMod 5` equals `triangularMod5 (k : ZMod 5)`. -/
theorem triangular_cast_eq_triangularMod5 (k : Nat) :
    ((k * (k + 1) / 2 : ℕ) : ZMod 5) = triangularMod5 (k : ZMod 5) := by
  have heven : 2 ∣ k * (k + 1) := by
    rcases Nat.even_or_odd k with he | ho
    · exact Dvd.dvd.mul_right he.two_dvd _
    · rcases ho with ⟨m, hm⟩
      refine Dvd.dvd.mul_left ?_ k
      exact ⟨m + 1, by omega⟩
  obtain ⟨q, hq⟩ := heven
  have h_div : k * (k + 1) / 2 = q := by
    rw [hq]; exact Nat.mul_div_cancel_left q (by omega)
  rw [h_div]
  -- We have hq : k * (k + 1) = 2 * q.  Cast to ZMod 5 and use that 6 = 1
  -- to extract q = 3 * k * (k+1) = triangularMod5 k.
  have h_cast : ((k : ZMod 5)) * ((k : ZMod 5) + 1) = 2 * (q : ZMod 5) := by
    have : ((k * (k + 1) : ℕ) : ZMod 5) = ((2 * q : ℕ) : ZMod 5) := by rw [hq]
    push_cast at this
    convert this using 1
  unfold triangularMod5
  calc (q : ZMod 5)
      = 6 * (q : ZMod 5) := by
        rw [show (6 : ZMod 5) = 1 from by decide]; ring
    _ = 3 * (2 * (q : ZMod 5)) := by ring
    _ = 3 * ((k : ZMod 5) * ((k : ZMod 5) + 1)) := by rw [← h_cast]
    _ = 3 * (k : ZMod 5) * ((k : ZMod 5) + 1) := by ring

/-- "Minus side" pentagonal residue helper in ZMod 5:
`pentagonalMod5Minus k := 3 * k * (3 * k + 4)` — equivalent to
`3 * k * (3 * k − 1)` in ZMod 5 since `−1 = 4` mod 5. -/
def pentagonalMod5Minus (k : ZMod 5) : ZMod 5 := 3 * k * (3 * k + 4)

/-- Range of `pentagonalMod5Minus`: also `{0, 1, 2}` (same as plus side). -/
theorem pentagonalMod5Minus_range : ∀ k : ZMod 5,
    pentagonalMod5Minus k = 0 ∨ pentagonalMod5Minus k = 1 ∨
    pentagonalMod5Minus k = 2 := by decide

/-- **Triangular + minus-side pentagonal ≠ 4 in ZMod 5** (the residue
obstruction for the "minus side" pentagonal). -/
theorem triangular_plus_pentagonalMinus_ne_four
    (k j : ZMod 5) (hk : (2 * k + 1 : ZMod 5) ≠ 0) :
    triangularMod5 k + pentagonalMod5Minus j ≠ 4 := by
  rcases triangular_when_jacobi_nonzero k hk with htri | htri <;>
  rcases pentagonalMod5Minus_range j with hp | hp | hp <;>
  rw [htri, hp] <;> decide

/-- Cast of pentagonal "plus side" `k(3k+1)/2` to ZMod 5 equals
`pentagonalMod5 (k : ZMod 5)`. -/
theorem pentagonal_plus_cast_eq_pentagonalMod5 (k : Nat) :
    ((k * (3 * k + 1) / 2 : ℕ) : ZMod 5) = pentagonalMod5 (k : ZMod 5) := by
  have heven : 2 ∣ k * (3 * k + 1) := by
    rcases Nat.even_or_odd k with he | ⟨m, hm⟩
    · exact Dvd.dvd.mul_right he.two_dvd _
    · -- k = 2m + 1, so 3k + 1 = 6m + 4 = 2(3m + 2), even.
      refine Dvd.dvd.mul_left ?_ k
      exact ⟨3 * m + 2, by omega⟩
  obtain ⟨q, hq⟩ := heven
  have h_div : k * (3 * k + 1) / 2 = q := by
    rw [hq]; exact Nat.mul_div_cancel_left q (by omega)
  rw [h_div]
  have h_cast : ((k : ZMod 5)) * (3 * (k : ZMod 5) + 1) = 2 * (q : ZMod 5) := by
    have : ((k * (3 * k + 1) : ℕ) : ZMod 5) = ((2 * q : ℕ) : ZMod 5) := by rw [hq]
    push_cast at this
    convert this using 1
  unfold pentagonalMod5
  calc (q : ZMod 5)
      = 6 * (q : ZMod 5) := by
        rw [show (6 : ZMod 5) = 1 from by decide]; ring
    _ = 3 * (2 * (q : ZMod 5)) := by ring
    _ = 3 * ((k : ZMod 5) * (3 * (k : ZMod 5) + 1)) := by rw [← h_cast]
    _ = 3 * (k : ZMod 5) * (3 * (k : ZMod 5) + 1) := by ring

/-- Cast of pentagonal "minus side" `k(3k-1)/2` to ZMod 5 equals
`pentagonalMod5Minus (k : ZMod 5)`, when `k ≥ 1` (so the Nat
subtraction `3*k - 1` is honest). -/
theorem pentagonal_minus_cast_eq_pentagonalMod5Minus (k : Nat) (hk : 0 < k) :
    ((k * (3 * k - 1) / 2 : ℕ) : ZMod 5) = pentagonalMod5Minus (k : ZMod 5) := by
  have heven : 2 ∣ k * (3 * k - 1) := by
    rcases Nat.even_or_odd k with he | ⟨m, hm⟩
    · exact Dvd.dvd.mul_right he.two_dvd _
    · refine Dvd.dvd.mul_left ?_ k
      exact ⟨3 * m + 1, by omega⟩
  obtain ⟨q, hq⟩ := heven
  have h_div : k * (3 * k - 1) / 2 = q := by
    rw [hq]; exact Nat.mul_div_cancel_left q (by omega)
  rw [h_div]
  -- Reduce the Nat subtraction cast.
  have h_sub_cast : ((3 * k - 1 : ℕ) : ZMod 5) = 3 * (k : ZMod 5) + 4 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 3 * k)]
    push_cast
    have h41 : (4 : ZMod 5) = -1 + 5 := by decide
    have h50 : (5 : ZMod 5) = 0 := by decide
    rw [h41, h50]
    ring
  have h_cast_eq : (k : ZMod 5) * (3 * (k : ZMod 5) + 4) = 2 * (q : ZMod 5) := by
    have h1 : ((k * (3 * k - 1) : ℕ) : ZMod 5) = ((2 * q : ℕ) : ZMod 5) := by rw [hq]
    -- Decompose the LHS cast: (k * (3*k - 1) : ZMod 5) = (k : ZMod 5) * ((3*k - 1 : ℕ) : ZMod 5)
    rw [show ((k * (3 * k - 1) : ℕ) : ZMod 5) =
        (k : ZMod 5) * ((3 * k - 1 : ℕ) : ZMod 5) from by push_cast; ring] at h1
    rw [h_sub_cast] at h1
    push_cast at h1
    exact h1
  unfold pentagonalMod5Minus
  calc (q : ZMod 5)
      = 6 * (q : ZMod 5) := by rw [show (6 : ZMod 5) = 1 from by decide]; ring
    _ = 3 * (2 * (q : ZMod 5)) := by ring
    _ = 3 * ((k : ZMod 5) * (3 * (k : ZMod 5) + 4)) := by rw [← h_cast_eq]
    _ = 3 * (k : ZMod 5) * (3 * (k : ZMod 5) + 4) := by ring

/-- **Per-term residue obstruction**: for all natural numbers `i, j, m` with
`i + j = 5*m + 4`, the product `jacobiTripleSign(i) · pentagonalSign(j)` is
zero in `ZMod 5`.

This is the key per-term lemma that closes the Finset.sum convolution sorry
in `Pending/Chapter17_Ramanujan5Conditional.lean`. -/
theorem jacobiPentagonal_per_term_zero_mod_5
    (i j m : Nat) (h_sum : i + j = 5 * m + 4) :
    ((jacobiTripleSign i : ℤ) : ZMod 5) *
      ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign j : ℤ) : ZMod 5) = 0 := by
  -- Case 1: jacobiTripleSign i = 0.
  by_cases h_jac_zero : jacobiTripleSign i = 0
  · rw [h_jac_zero]; simp
  -- Case 2: pentagonalSign j = 0.
  by_cases h_pent_zero : QseriesFormalization.PartI.Ch04Franklin.pentagonalSign j = 0
  · rw [h_pent_zero]; simp
  -- Case 3: both nonzero.  Extract k, l witnesses.
  obtain ⟨k, hk_le, hk_eq, hk_sign⟩ :=
    jacobiTripleSign_ne_zero_extract i h_jac_zero
  obtain ⟨l, hl_le, hl_side, hl_sign⟩ :=
    pentagonalSign_ne_zero_extract j h_pent_zero
  -- Now `hk_sign : jacobiTripleSign i = (-1)^k * (2*k+1)`,
  --     `hl_sign : pentagonalSign j = (-1)^l`,
  --     `hk_eq : i = k * (k+1) / 2`,
  --     `hl_side : j = l*(3l-1)/2 ∨ (0 < l ∧ j = l*(3l+1)/2)`.
  -- Substitute the sign formulas.
  rw [hk_sign]
  -- Goal: ((-1)^k * (2*k+1) : ZMod 5) * (pentagonalSign j : ZMod 5) = 0
  -- Case split on whether (2*k+1) = 0 in ZMod 5.
  by_cases h2k1 : ((2 * (k : ZMod 5) + 1 : ZMod 5)) = 0
  · -- (2k+1) = 0 mod 5: jacobiTripleSign factor is zero, term is zero.
    have h_fact_zero : (((-1 : ℤ) ^ k * (2 * (k : ℤ) + 1) : ℤ) : ZMod 5) = 0 := by
      push_cast
      rw [h2k1]
      ring
    rw [h_fact_zero]
    simp
  -- (2k+1) ≠ 0 mod 5.  Apply residue obstruction.
  exfalso
  -- Compute (i : ZMod 5) using triangular cast.
  have h_i_mod : (i : ZMod 5) = triangularMod5 (k : ZMod 5) := by
    rw [hk_eq, triangular_cast_eq_triangularMod5]
  -- Compute (j : ZMod 5) using minus or plus pentagonal cast.
  have h_sum_mod5 : (i : ZMod 5) + (j : ZMod 5) = 4 := by
    have : ((i + j : ℕ) : ZMod 5) = ((5 * m + 4 : ℕ) : ZMod 5) := by rw [h_sum]
    push_cast at this
    have h5 : (5 : ZMod 5) = 0 := by decide
    rw [show (5 * (m : ZMod 5) + 4 : ZMod 5) = (5 : ZMod 5) * (m : ZMod 5) + 4 from rfl, h5,
        zero_mul, zero_add] at this
    exact this
  rcases hl_side with hl_minus | ⟨hl_pos, hl_plus⟩
  · -- minus side: j = l * (3l - 1) / 2.  Handle l = 0 separately.
    rcases Nat.eq_zero_or_pos l with rfl | hl_pos
    · -- l = 0: j = 0 * (3*0 - 1) / 2 = 0.  Then i = 5m+4, and i must be triangular T_k.
      -- T_k = 5m + 4.  Mod 5: T_k ≡ 4.  But triangularMod5(k mod 5) ∈ {0,1,3} or {0,1} (when 2k+1≢0).
      -- So no such k.  Apply residue obstruction at l = 0 (pentagonalMod5Minus 0 = 0).
      simp only [Nat.zero_mul, Nat.zero_div] at hl_minus
      have h_j_zero : (j : ZMod 5) = 0 := by rw [hl_minus]; simp
      rw [h_j_zero, add_zero] at h_sum_mod5
      -- h_sum_mod5 : (i : ZMod 5) = 4
      -- h_i_mod : (i : ZMod 5) = triangularMod5 (k : ZMod 5)
      -- So triangularMod5 (k : ZMod 5) = 4.  But range is {0, 1, 3} or {0, 1} when 2k+1 ≢ 0.
      rw [h_i_mod] at h_sum_mod5
      rcases triangular_when_jacobi_nonzero (k : ZMod 5) h2k1 with hkv | hkv <;>
        rw [hkv] at h_sum_mod5 <;> exact absurd h_sum_mod5 (by decide)
    · -- l ≥ 1: use minus cast lemma.
      have h_j_mod : (j : ZMod 5) = pentagonalMod5Minus (l : ZMod 5) := by
        rw [hl_minus, pentagonal_minus_cast_eq_pentagonalMod5Minus l hl_pos]
      rw [h_i_mod, h_j_mod] at h_sum_mod5
      exact triangular_plus_pentagonalMinus_ne_four (k : ZMod 5) (l : ZMod 5) h2k1 h_sum_mod5
  · -- plus side: 0 < l ∧ j = l * (3l + 1) / 2.
    have h_j_mod : (j : ZMod 5) = pentagonalMod5 (l : ZMod 5) := by
      rw [hl_plus, pentagonal_plus_cast_eq_pentagonalMod5]
    rw [h_i_mod, h_j_mod] at h_sum_mod5
    exact triangular_plus_pentagonal_ne_four (k : ZMod 5) (l : ZMod 5) h2k1 h_sum_mod5

end Ch17
end PartIV
end QseriesFormalization
