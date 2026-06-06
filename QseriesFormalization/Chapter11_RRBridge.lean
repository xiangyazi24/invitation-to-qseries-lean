import QseriesFormalization.Chapter11
import QseriesFormalization.Chapter04

/-!
# Chapter 11 — Rogers-Ramanujan G/H ↔ Chapter 4 mod-5 bridge

`Chapter11.lean` is a ~60k-line file of mechanical G_trunc/H_trunc N=0..5000
truncations. To avoid recompiling that monster for every new R-R lemma, this
module isolates the bridge from `G_trunc`/`H_trunc` to Chapter 4's
`rrMod5Factor` machinery. (Same pattern as `Chapter04_T43.lean`.)
-/

namespace QseriesFormalization
namespace PartIII
namespace Ch11

open Filter Topology

/-- The G_trunc reciprocal-product factor for index n equals
`PartI.Ch04.rrMod5Factor q 1 n · PartI.Ch04.rrMod5Factor q 4 n`. -/
theorem G_trunc_factor_eq_rrMod5 (q : ℂ) (n : ℕ) :
    (1 - q ^ (5 * (n + 1) - 4)) * (1 - q ^ (5 * (n + 1) - 1)) =
      PartI.Ch04.rrMod5Factor q 1 n * PartI.Ch04.rrMod5Factor q 4 n := by
  simp only [PartI.Ch04.rrMod5Factor]
  rw [show 5 * (n + 1) - 4 = 1 + 5 * n from by omega,
      show 5 * (n + 1) - 1 = 4 + 5 * n from by omega]

/-- The H_trunc reciprocal-product factor for index n equals
`PartI.Ch04.rrMod5Factor q 2 n · PartI.Ch04.rrMod5Factor q 3 n`. -/
theorem H_trunc_factor_eq_rrMod5 (q : ℂ) (n : ℕ) :
    (1 - q ^ (5 * (n + 1) - 3)) * (1 - q ^ (5 * (n + 1) - 2)) =
      PartI.Ch04.rrMod5Factor q 2 n * PartI.Ch04.rrMod5Factor q 3 n := by
  simp only [PartI.Ch04.rrMod5Factor]
  rw [show 5 * (n + 1) - 3 = 2 + 5 * n from by omega,
      show 5 * (n + 1) - 2 = 3 + 5 * n from by omega]

/-- `G_trunc q N` times the partial mod-5 product (residues 1,4) is 1,
provided no factor vanishes (true for ‖q‖ < 1). -/
theorem G_trunc_mul_partial_eq_one (q : ℂ) (hq : ‖q‖ < 1) (N : ℕ) :
    G_trunc q N *
      ∏ n ∈ Finset.range N,
        (PartI.Ch04.rrMod5Factor q 1 n * PartI.Ch04.rrMod5Factor q 4 n) = 1 := by
  induction N with
  | zero => simp [G_trunc]
  | succ N ih =>
    rw [G_trunc_succ, Finset.prod_range_succ]
    have hfac := G_trunc_factor_eq_rrMod5 q N
    have h1ne := PartI.Ch04.rrMod5Factor_ne_zero q hq 1 (by norm_num) N
    have h4ne := PartI.Ch04.rrMod5Factor_ne_zero q hq 4 (by norm_num) N
    have hfac_ne :
        PartI.Ch04.rrMod5Factor q 1 N * PartI.Ch04.rrMod5Factor q 4 N ≠ 0 :=
      mul_ne_zero h1ne h4ne
    rw [← hfac]
    have hfac_ne' : (1 - q ^ (5 * (N + 1) - 4)) * (1 - q ^ (5 * (N + 1) - 1)) ≠ 0 := by
      rw [hfac]; exact hfac_ne
    set D : ℂ := (1 - q ^ (5 * (N + 1) - 4)) * (1 - q ^ (5 * (N + 1) - 1)) with hD
    set P : ℂ := ∏ n ∈ Finset.range N,
      (PartI.Ch04.rrMod5Factor q 1 n * PartI.Ch04.rrMod5Factor q 4 n) with hP
    -- Goal: G_trunc q N / D * (P * D) = 1.
    rw [show G_trunc q N / D * (P * D) = (G_trunc q N * P) * (D / D) from by ring]
    rw [div_self hfac_ne', mul_one]
    exact ih

end Ch11
end PartIII
end QseriesFormalization
