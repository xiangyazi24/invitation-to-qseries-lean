import QseriesFormalization.Chapter20
import QseriesFormalization.Pending.Chapter17_Ramanujan5Conditional
import QseriesFormalization.Pending.Chapter17_Ramanujan7
import QseriesFormalization.Pending.Chapter17_Hirschhorn_Mod11

/-!
# Chapter 20 -- Ono-style partition congruence target

This file records the exact formal target for Chan Theorem 20.1 and proves the
unconditional part currently reachable from the repository: the classical
Ramanujan congruences modulo 5, 7, and 11 already imply infinitely many
arithmetic-progression congruences, by refinement of the progression.

The full Ono theorem for every prime `m >= 5` is not proved here.  Chan's sketch
uses half-integral-weight modular forms, Hecke operators, the Shimura
correspondence, and Serre's density theorem; those ingredients are not present
in Mathlib in the required form.
-/

namespace QseriesFormalization
namespace PartIV
namespace Ch20

open QseriesFormalization.Ch01 (partitionCount)

/-- A single arithmetic-progression congruence refines to infinitely many:
replace `n` by `(C+1)*n` to get step `A*(C+1)` above any requested bound `C`. -/
theorem infinitelyManyPartitionAPCongruences_of_base {m A B : Nat}
    (hA : 0 < A)
    (h : ∀ n : Nat, ((partitionCount (A * n + B) : Nat) : ZMod m) = 0) :
    InfinitelyManyPartitionAPCongruences m := by
  intro C
  refine ⟨A * (C + 1), B, ?_, ?_⟩
  · exact le_trans (Nat.le_succ C) (by
      simpa [one_mul] using Nat.mul_le_mul_right (C + 1) (show 1 ≤ A from hA))
  · constructor
    · exact Nat.mul_pos hA (Nat.succ_pos C)
    · intro n
      have hn := h ((C + 1) * n)
      convert hn using 2
      ring_nf

/-- Ono-style infinite family obtained from Ramanujan's congruence
`5 | p(5*n+4)`. -/
theorem theorem20_1_mod_5 :
    InfinitelyManyPartitionAPCongruences 5 := by
  refine infinitelyManyPartitionAPCongruences_of_base
    (m := 5) (A := 5) (B := 4) (by decide) ?_
  intro n
  exact (ZMod.natCast_eq_zero_iff _ 5).mpr
    (QseriesFormalization.PartIV.Ch17.ramanujan_5_dvd_p_5n_plus_4 n)

/-- Ono-style infinite family obtained from Ramanujan's congruence
`7 | p(7*n+5)`. -/
theorem theorem20_1_mod_7 :
    InfinitelyManyPartitionAPCongruences 7 := by
  refine infinitelyManyPartitionAPCongruences_of_base
    (m := 7) (A := 7) (B := 5) (by decide) ?_
  intro n
  exact (ZMod.natCast_eq_zero_iff _ 7).mpr
    (QseriesFormalization.Pending.Ch17p7.ramanujan_7_dvd_p_7n_plus_5 n)

/-- Ono-style infinite family obtained from Ramanujan's congruence
`11 | p(11*n+6)`. -/
theorem theorem20_1_mod_11 :
    InfinitelyManyPartitionAPCongruences 11 := by
  refine infinitelyManyPartitionAPCongruences_of_base
    (m := 11) (A := 11) (B := 6) (by decide) ?_
  intro n
  exact (ZMod.natCast_eq_zero_iff _ 11).mpr
    (QseriesFormalization.Pending.Hirschhorn11.ramanujan_11_dvd_p_11n_plus_6 n)

/-- The currently closed prime cases of Chan Theorem 20.1 in this repository:
`m = 5, 7, 11`. -/
theorem theorem20_1_for_ramanujan_primes (m : Nat)
    (hm : m = 5 ∨ m = 7 ∨ m = 11) :
    InfinitelyManyPartitionAPCongruences m := by
  rcases hm with h5 | h7 | h11
  · subst m
    exact theorem20_1_mod_5
  · subst m
    exact theorem20_1_mod_7
  · subst m
    exact theorem20_1_mod_11

end Ch20
end PartIV
end QseriesFormalization
