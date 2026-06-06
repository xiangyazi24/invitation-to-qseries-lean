import QseriesFormalization.Chapter19_JacobiTripleSignChar

/-!
# Chapter 17 — Mod-7 per-term residue analysis for Ramanujan's 2nd congruence

For `i + j = 7n + 5`, `(jts i : ZMod 7) * (jts j : ZMod 7) = 0`.

Proof structure (analog of `Chapter17_PerTermAnalysis` for mod 5):
  - Triangular numbers mod 7 are in {0, 1, 3, 6}.
  - For `(jts i : ZMod 7) ≠ 0`: i is triangular AND its index is ≢ 3 mod 7,
    forcing `(i : ZMod 7) ∈ {0, 1, 3}`.
  - For pairs in `{0,1,3} × {0,1,3}`, the sum mod 7 ∈ {0,1,2,3,4,6} — never 5.
  - Hence convolution at 7n+5 is identically zero in ZMod 7.

This is the building block for `∀ n, 7 ∣ p(7n + 5)` via:
  `(qPochInfPS ZMod 7)^6 = (jacobiThetaPS ZMod 7)^2` (B2 squared) +
  `((jacobiThetaPS ZMod 7)^2).coeff (7n+5) = 0` (this analysis) +
  `ramanujan_from_pochInf_vanishes 7`.
-/

namespace QseriesFormalization
namespace PartIV
namespace Ch17

open QseriesFormalization.PartIV.Ch19

/-- **Triangular residues mod 7**: `T_n mod 7 ∈ {0, 1, 3, 6}`. -/
theorem triangular_mod_7_in (n : ℕ) :
    (((n * (n + 1) / 2 : ℕ) : ZMod 7)) = 0 ∨
    (((n * (n + 1) / 2 : ℕ) : ZMod 7)) = 1 ∨
    (((n * (n + 1) / 2 : ℕ) : ZMod 7)) = 3 ∨
    (((n * (n + 1) / 2 : ℕ) : ZMod 7)) = 6 := by
  have h2T : 2 * (n * (n + 1) / 2) = n * (n + 1) := two_mul_triangular n
  have h_cast : (2 : ZMod 7) * ((n * (n + 1) / 2 : ℕ) : ZMod 7) =
                ((n : ZMod 7)) * ((n : ZMod 7) + 1) := by
    have h1 : ((2 * (n * (n + 1) / 2) : ℕ) : ZMod 7) =
              ((n * (n + 1) : ℕ) : ZMod 7) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 7) h2T
    push_cast at h1
    exact h1
  have hT_eq : ((n * (n + 1) / 2 : ℕ) : ZMod 7) =
      4 * (((n : ZMod 7)) * ((n : ZMod 7) + 1)) := by
    have h2_inv : (4 : ZMod 7) * 2 = 1 := by decide
    calc ((n * (n + 1) / 2 : ℕ) : ZMod 7)
        = 1 * ((n * (n + 1) / 2 : ℕ) : ZMod 7) := (one_mul _).symm
      _ = (4 * 2) * ((n * (n + 1) / 2 : ℕ) : ZMod 7) := by rw [h2_inv]
      _ = 4 * (2 * ((n * (n + 1) / 2 : ℕ) : ZMod 7)) := by ring
      _ = 4 * ((n : ZMod 7) * ((n : ZMod 7) + 1)) := by rw [h_cast]
  rw [hT_eq]
  obtain ⟨k, hk⟩ : ∃ k : ZMod 7, (n : ZMod 7) = k := ⟨(n : ZMod 7), rfl⟩
  rw [hk]
  fin_cases k <;> decide

/-- **Non-triangular residues mod 7**: if `n mod 7 ∈ {2, 4, 5}`, then `n` is not triangular. -/
theorem not_triangular_of_mod_7_in_245 (n : ℕ)
    (h : (n : ZMod 7) = 2 ∨ (n : ZMod 7) = 4 ∨ (n : ZMod 7) = 5) :
    ∀ k ≤ n, n ≠ k * (k + 1) / 2 := by
  intro k _ heq
  have h_tri := triangular_mod_7_in k
  rw [← heq] at h_tri
  rcases h with h2 | h4 | h5
  all_goals (rcases h_tri with h | h | h | h) <;>
    first
    | (rw [h2] at h; exact absurd h (by decide))
    | (rw [h4] at h; exact absurd h (by decide))
    | (rw [h5] at h; exact absurd h (by decide))

/-- If `n = k*(k+1)/2` (triangular) and `n mod 7 = 6`, then `k mod 7 = 3`. -/
theorem triangular_index_mod_7_eq_3_of_n_mod_7_eq_6 (n k : ℕ)
    (heq : n = k * (k + 1) / 2) (hn : (n : ZMod 7) = 6) :
    (k : ZMod 7) = 3 := by
  have h2T : 2 * (k * (k + 1) / 2) = k * (k + 1) := two_mul_triangular k
  have h_cast : (2 : ZMod 7) * ((k * (k + 1) / 2 : ℕ) : ZMod 7) =
                ((k : ZMod 7)) * ((k : ZMod 7) + 1) := by
    have h1 : ((2 * (k * (k + 1) / 2) : ℕ) : ZMod 7) =
              ((k * (k + 1) : ℕ) : ZMod 7) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 7) h2T
    push_cast at h1
    exact h1
  rw [← heq] at h_cast
  rw [hn] at h_cast
  have h_kk1 : ((k : ZMod 7)) * ((k : ZMod 7) + 1) = 5 := by
    rw [← h_cast]; decide
  -- Show (k : ZMod 7) = 3 by checking all 7 residues.
  have h_check : ∀ k' : ZMod 7, k' * (k' + 1) = 5 → k' = 3 := by decide
  exact h_check (k : ZMod 7) h_kk1

/-- If `(jacobiTripleSign n : ZMod 7) ≠ 0`, then `(n : ZMod 7) ∈ {0, 1, 3}`. -/
theorem jacobiTripleSign_nonzero_mod_7_residue (n : ℕ)
    (h : ((jacobiTripleSign n : ℤ) : ZMod 7) ≠ 0) :
    (n : ZMod 7) = 0 ∨ (n : ZMod 7) = 1 ∨ (n : ZMod 7) = 3 := by
  -- Case split: n triangular or not, and n mod 7.
  by_cases h_tri : ∃ k ≤ n, n = k * (k + 1) / 2
  · obtain ⟨k, _hkle, hk_eq⟩ := h_tri
    -- (n : ZMod 7) = (T_k : ZMod 7) ∈ {0, 1, 3, 6}.
    have h_T := triangular_mod_7_in k
    rw [← hk_eq] at h_T
    rcases h_T with h0 | h1 | h3 | h6
    · left; exact h0
    · right; left; exact h1
    · right; right; exact h3
    · -- (n : ZMod 7) = 6.  Then k mod 7 = 3, so jts ≡ 0 mod 7.  Contradicts h.
      exfalso
      apply h
      rw [hk_eq, jacobiTripleSign_triangular]
      have hk3 : (k : ZMod 7) = 3 :=
        triangular_index_mod_7_eq_3_of_n_mod_7_eq_6 n k hk_eq h6
      have h_2k1 : ((2 * (k : ZMod 7) + 1)) = 0 := by rw [hk3]; decide
      push_cast
      rw [h_2k1]; ring
  · -- n not triangular.  jts(n) = 0 in ℤ.  Contradicts h.
    exfalso
    apply h
    push_neg at h_tri
    rw [jacobiTripleSign_of_not_triangular n h_tri]
    simp

/-- **Per-term mod-7 zero**: for `i + j = 7n + 5`,
`(jts i : ZMod 7) * (jts j : ZMod 7) = 0`. -/
theorem jacobiTripleSign_squared_per_term_zero_mod_7 (i j n : ℕ)
    (h_sum : i + j = 7 * n + 5) :
    ((jacobiTripleSign i : ℤ) : ZMod 7) *
      ((jacobiTripleSign j : ℤ) : ZMod 7) = 0 := by
  -- By contrapositive: assume both factors nonzero, derive contradiction.
  by_contra h_ne
  push_neg at h_ne
  have h_i_ne : ((jacobiTripleSign i : ℤ) : ZMod 7) ≠ 0 := by
    intro h0; apply h_ne; rw [h0]; ring
  have h_j_ne : ((jacobiTripleSign j : ℤ) : ZMod 7) ≠ 0 := by
    intro h0; apply h_ne; rw [h0]; ring
  have h_i_res := jacobiTripleSign_nonzero_mod_7_residue i h_i_ne
  have h_j_res := jacobiTripleSign_nonzero_mod_7_residue j h_j_ne
  -- (i + j : ZMod 7) = 5
  have h_sum_mod7 : (i : ZMod 7) + (j : ZMod 7) = 5 := by
    have : ((i + j : ℕ) : ZMod 7) = ((7 * n + 5 : ℕ) : ZMod 7) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 7) h_sum
    push_cast at this
    have h7 : ((7 : ℕ) : ZMod 7) = 0 := by decide
    have : (i : ZMod 7) + (j : ZMod 7) = 7 * (n : ZMod 7) + 5 := this
    rw [show ((7 : ZMod 7) * (n : ZMod 7) = 0) from by
      rw [show (7 : ZMod 7) = 0 from by decide]; ring] at this
    rw [zero_add] at this
    exact this
  -- Now (i, j) residues ∈ {0,1,3} × {0,1,3}, sum should be 5: impossible.
  rcases h_i_res with hi | hi | hi <;>
    rcases h_j_res with hj | hj | hj <;>
      (rw [hi, hj] at h_sum_mod7; exact absurd h_sum_mod7 (by decide))


end Ch17
end PartIV
end QseriesFormalization
