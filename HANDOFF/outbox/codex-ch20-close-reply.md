# Chan Chapter 20 / Ono Theorem 20.1 close attempt

## Result

Full Ono Theorem 20.1 is still not closed unconditionally in Lean.

I added the formal target statement and closed the strongest unconditional
piece currently reachable from this repository: the already-proved Ramanujan
congruences mod 5, 7, and 11 imply infinitely many arithmetic-progression
partition congruences by progression refinement.

New file:

- `QseriesFormalization/Chapter20_Ono.lean`

New declarations:

- `PartitionAPCongruence m A B`
- `InfinitelyManyPartitionAPCongruences m`
- `onoTheorem20_1Statement`
- `infinitelyManyPartitionAPCongruences_of_base`
- `theorem20_1_mod_5`
- `theorem20_1_mod_7`
- `theorem20_1_mod_11`
- `theorem20_1_for_ramanujan_primes`

I also imported `QseriesFormalization.Chapter20_Ono` from
`QseriesFormalization.lean`.

## What the new theorems prove

`PartitionAPCongruence m A B` means:

```lean
0 < A ∧ ∀ n, ((partitionCount (A * n + B) : Nat) : ZMod m) = 0
```

`InfinitelyManyPartitionAPCongruences m` is the unbounded-step formulation:

```lean
∀ C, ∃ A B, C ≤ A ∧ PartitionAPCongruence m A B
```

The key generic lemma is:

```lean
infinitelyManyPartitionAPCongruences_of_base
```

Given one AP congruence `p(A*n+B)=0 mod m`, it proves infinitely many refined
congruences by replacing `n` with `(C+1)*n`, giving step `A*(C+1)`.

Instantiated cases:

- mod 5 from `PartIV.Ch17.ramanujan_5_dvd_p_5n_plus_4`
- mod 7 from `Pending.Ch17p7.ramanujan_7_dvd_p_7n_plus_5`
- mod 11 from `Pending.Hirschhorn11.ramanujan_11_dvd_p_11n_plus_6`

This is a real infinite-family result, but it is not the full Ono theorem:
it only covers `m = 5, 7, 11`, and the infinite families are refinements of the
classical Ramanujan APs.

## Irreducible gap for full Theorem 20.1

The missing proof is not a Lean tactic gap in the new file.  Chan's route needs
modular-form infrastructure not present in Mathlib at the required level:

- half-integral weight modular forms on congruence subgroups with characters;
- q-expansion API for those forms;
- `U_t` and `V_t` operators preserving the relevant spaces;
- half-integral weight Hecke operators `T(l^2)`;
- eta-quotient modularity/cusp criteria sufficient for the `f_m` construction;
- Shimura correspondence;
- Serre density theorem in the modular-form/coefficient-mod-`m` form used by
  Ono.

Without those, an unconditional proof for all prime `m >= 5` would either be
an axiom/sorry wrapper or a new large upstream modular-forms development.

## Verification

Commands run:

```bash
lake env lean QseriesFormalization/Chapter20_Ono.lean
lake build QseriesFormalization.Chapter20_Ono
lake build QseriesFormalization.Chapter20_TauValues QseriesFormalization.Chapter20_TauMult QseriesFormalization.Chapter20_TauExtend
lake env lean QseriesFormalization.lean
lake build
rg -n "sorry|admit|axiom|native_decide" QseriesFormalization/Chapter20_Ono.lean QseriesFormalization/Chapter20.lean QseriesFormalization/Chapter20_TauValues.lean QseriesFormalization/Chapter20_TauMult.lean QseriesFormalization/Chapter20_TauExtend.lean
```

Results:

- `lake env lean QseriesFormalization/Chapter20_Ono.lean`: passed.
- `lake build QseriesFormalization.Chapter20_Ono`: passed.
- `lake env lean QseriesFormalization.lean`: passed.
- `lake build`: passed, `Build completed successfully (8013 jobs)`.
- forbidden-token scan: no matches.
- `#print axioms` for the new theorems reports only the standard clean-3
  axioms: `[propext, Classical.choice, Quot.sound]`.

Note: `lake build QseriesFormalization.Chapter20_Ono` had to rebuild the
already-dirty `Chapter20.lean`; that succeeded but took about 1298 seconds.
