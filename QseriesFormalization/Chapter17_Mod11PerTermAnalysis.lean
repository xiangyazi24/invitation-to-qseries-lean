import QseriesFormalization.Chapter19_JacobiTripleSignChar

/-!
# Chapter 17 — Mod-11 per-term residue analysis

For Ramanujan's third congruence `∀ n, 11 ∣ p(11n + 6)`.

**Note**: unlike mod 5 / mod 7, a single per-term zero on convolution
`coeff (qPoch^k) (11n+6) ≠ 0` analysis does NOT close mod 11 — that would
require pentagonal-residue cancellation, but the relevant residue set
{0,1,3,6,10} can sum to 6 mod 11 in several ways.  So this file only
collects the basic mod-11 residue classification of `jacobiTripleSign`,
to be consumed by the Hirschhorn §3.5 J_i-decomposition.
-/

namespace QseriesFormalization
namespace PartIV
namespace Ch17

open QseriesFormalization.PartIV.Ch19

/-- **Triangular residues mod 11**: `T_n mod 11 ∈ {0, 1, 3, 4, 6, 10}`. -/
theorem triangular_mod_11_in (n : ℕ) :
    (((n * (n + 1) / 2 : ℕ) : ZMod 11)) = 0 ∨
    (((n * (n + 1) / 2 : ℕ) : ZMod 11)) = 1 ∨
    (((n * (n + 1) / 2 : ℕ) : ZMod 11)) = 3 ∨
    (((n * (n + 1) / 2 : ℕ) : ZMod 11)) = 4 ∨
    (((n * (n + 1) / 2 : ℕ) : ZMod 11)) = 6 ∨
    (((n * (n + 1) / 2 : ℕ) : ZMod 11)) = 10 := by
  have h2T : 2 * (n * (n + 1) / 2) = n * (n + 1) := two_mul_triangular n
  have h_cast : (2 : ZMod 11) * ((n * (n + 1) / 2 : ℕ) : ZMod 11) =
                ((n : ZMod 11)) * ((n : ZMod 11) + 1) := by
    have h1 : ((2 * (n * (n + 1) / 2) : ℕ) : ZMod 11) =
              ((n * (n + 1) : ℕ) : ZMod 11) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 11) h2T
    push_cast at h1
    exact h1
  have hT_eq : ((n * (n + 1) / 2 : ℕ) : ZMod 11) =
      6 * (((n : ZMod 11)) * ((n : ZMod 11) + 1)) := by
    -- 6 * 2 = 12 ≡ 1 (mod 11)
    have h2_inv : (6 : ZMod 11) * 2 = 1 := by decide
    calc ((n * (n + 1) / 2 : ℕ) : ZMod 11)
        = 1 * ((n * (n + 1) / 2 : ℕ) : ZMod 11) := (one_mul _).symm
      _ = (6 * 2) * ((n * (n + 1) / 2 : ℕ) : ZMod 11) := by rw [h2_inv]
      _ = 6 * (2 * ((n * (n + 1) / 2 : ℕ) : ZMod 11)) := by ring
      _ = 6 * ((n : ZMod 11) * ((n : ZMod 11) + 1)) := by rw [h_cast]
  rw [hT_eq]
  obtain ⟨k, hk⟩ : ∃ k : ZMod 11, (n : ZMod 11) = k := ⟨(n : ZMod 11), rfl⟩
  rw [hk]
  fin_cases k <;> decide

/-- If `n = k*(k+1)/2` (triangular) and `n mod 11 = 4`, then `k mod 11 = 5`. -/
theorem triangular_index_mod_11_eq_5_of_n_mod_11_eq_4 (n k : ℕ)
    (heq : n = k * (k + 1) / 2) (hn : (n : ZMod 11) = 4) :
    (k : ZMod 11) = 5 := by
  have h2T : 2 * (k * (k + 1) / 2) = k * (k + 1) := two_mul_triangular k
  have h_cast : (2 : ZMod 11) * ((k * (k + 1) / 2 : ℕ) : ZMod 11) =
                ((k : ZMod 11)) * ((k : ZMod 11) + 1) := by
    have h1 : ((2 * (k * (k + 1) / 2) : ℕ) : ZMod 11) =
              ((k * (k + 1) : ℕ) : ZMod 11) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 11) h2T
    push_cast at h1
    exact h1
  rw [← heq] at h_cast
  rw [hn] at h_cast
  -- h_cast : (2 : ZMod 11) * 4 = k * (k + 1), so k * (k + 1) = 8
  have h_kk1 : ((k : ZMod 11)) * ((k : ZMod 11) + 1) = 8 := by
    rw [← h_cast]; decide
  -- Only k ≡ 5 mod 11 satisfies k(k+1) ≡ 8 (mod 11)
  have h_check : ∀ k' : ZMod 11, k' * (k' + 1) = 8 → k' = 5 := by decide
  exact h_check (k : ZMod 11) h_kk1

/-- If `(jacobiTripleSign n : ZMod 11) ≠ 0`, then `(n : ZMod 11) ∈ {0, 1, 3, 6, 10}`. -/
theorem jacobiTripleSign_nonzero_mod_11_residue (n : ℕ)
    (h : ((jacobiTripleSign n : ℤ) : ZMod 11) ≠ 0) :
    (n : ZMod 11) = 0 ∨ (n : ZMod 11) = 1 ∨ (n : ZMod 11) = 3 ∨
    (n : ZMod 11) = 6 ∨ (n : ZMod 11) = 10 := by
  by_cases h_tri : ∃ k ≤ n, n = k * (k + 1) / 2
  · obtain ⟨k, _hkle, hk_eq⟩ := h_tri
    have h_T := triangular_mod_11_in k
    rw [← hk_eq] at h_T
    rcases h_T with h0 | h1 | h3 | h4 | h6 | h10
    · left; exact h0
    · right; left; exact h1
    · right; right; left; exact h3
    · -- (n : ZMod 11) = 4 forces k mod 11 = 5, then 2k+1 ≡ 0 mod 11
      exfalso
      apply h
      rw [hk_eq, jacobiTripleSign_triangular]
      have hk5 : (k : ZMod 11) = 5 :=
        triangular_index_mod_11_eq_5_of_n_mod_11_eq_4 n k hk_eq h4
      have h_2k1 : ((2 * (k : ZMod 11) + 1)) = 0 := by rw [hk5]; decide
      push_cast
      rw [h_2k1]; ring
    · right; right; right; left; exact h6
    · right; right; right; right; exact h10
  · exfalso
    apply h
    push_neg at h_tri
    rw [jacobiTripleSign_of_not_triangular n h_tri]
    simp

end Ch17
end PartIV
end QseriesFormalization
