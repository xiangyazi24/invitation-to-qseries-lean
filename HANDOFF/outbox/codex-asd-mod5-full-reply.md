# codex-asd-mod5-full reply

Created `QseriesFormalization/Pending/Chapter17_ASD_Mod5_Full.lean`.

Main contents:
- Reuses `Pending.Chapter17_ASD_Mod5`'s `section5`, `A`, and
  `qPochInfPS_cube_decompose_mod_5`.
- Proves a generic extraction lemma:
  `section_kr R p r (f * expand p g) = section_kr R p r f * g`.
- Proves the denominator-cleared Hirschhorn §3.6 identity over `ZMod 5`:
  `P5 * D5^2 = S5^3`, where
  `P5 = partitionGenFun (ZMod 5)`,
  `D5 = expand 5 (qPochInfPS (ZMod 5))`, and
  `S5 = A 0 + A 1`.
- Expands the ASD numerator
  `S5^3 = N0 + N1 + N2 + N3`, with
  `N0 = (A 0)^3`,
  `N1 = 3*(A 0)^2*A 1`,
  `N2 = 3*A 0*(A 1)^2`,
  `N3 = (A 1)^3`.
- Extracts all five residue classes:
  - denominator-cleared forms
    `section_kr 5 j P5 * Q5^2 = section_kr 5 j Nj` for `j=0..3`;
  - `section_kr 5 4 P5 * Q5^2 = 0`;
  - divided forms using `P5^2 = 1 / Q5^2`, including
    `section_kr 5 4 P5 = 0`.
- Includes the existing `p(5n+4) ≡ 0 (mod 5)` restatement as a sanity check.

Stretch not done:
- I did not identify `A 0` and `A 1` with the eta-products in Hirschhorn
  (3.6.5); the file delivers the section-component form requested as the
  reachable core.

Verification:
- `lake env lean QseriesFormalization/Pending/Chapter17_ASD_Mod5_Full.lean`
  succeeds.
- `rg -n "sorry|admit|axiom|sorryAx" QseriesFormalization/Pending/Chapter17_ASD_Mod5_Full.lean`
  returns no matches.
- Scratch-copy `#print axioms` for
  `partitionGenFun_mul_D5_sq_eq_S5_cube`,
  `partition_section_0_eq_over_Q5_sq`,
  `partition_section_4_eq_zero`, and
  `partition_5n_plus_4_eq_zero_mod_5` reports only
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

No existing Lean source files, import aggregators, or owned files from other
agents were edited.
