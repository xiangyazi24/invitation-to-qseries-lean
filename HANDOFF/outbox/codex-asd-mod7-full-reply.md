# codex-asd-mod7-full reply

Created `QseriesFormalization/Pending/Chapter17_ASD_Mod7_Full.lean`.

Main contents:
- Imports `QseriesFormalization.Pending.Chapter17_ASD_Mod7` and
  `QseriesFormalization.Chapter19_Section5`.
- Reuses `section7`, `ASD7`, `isRes7_ASD7`, and
  `qPochInfPS_cube_decompose_mod_7`.
- Proves the generic extraction lemma
  `section_kr R p r (f * expand p g) = section_kr R p r f * g`.
- Proves the denominator-cleared Hirschhorn §3.7 identity over `ZMod 7`:
  `P7 * D7 = S7^2`, where
  `P7 = partitionGenFun (ZMod 7)`,
  `D7 = expand 7 (qPochInfPS (ZMod 7))`, and
  `S7 = ASD7 0 + ASD7 1 + ASD7 3`.
- Expands the ASD numerator
  `S7^2 = N0 + N1 + N2 + N3 + N4 + N6`, with residue supports
  `0, 1, 2, 3, 4, 6`.
- Extracts all seven residue classes:
  - denominator-cleared forms
    `section_kr 7 j P7 * Q7 = section_kr 7 j Nj` for
    `j = 0,1,2,3,4,6`;
  - `section_kr 7 5 P7 * Q7 = 0`;
  - divided forms using `Q7 * P7 = 1`, including
    `partition_section_5_eq_zero`.
- Includes coefficient form:
  `partition_7n_plus_5_eq_zero_mod_7`.

Stretch not done:
- I did not identify the section components with eta-products; the file
  delivers the requested section-component form.

Verification:
- `lake env lean QseriesFormalization/Pending/Chapter17_ASD_Mod7_Full.lean`
  succeeds.
- `rg -n "sorry|admit|axiom|sorryAx" QseriesFormalization/Pending/Chapter17_ASD_Mod7_Full.lean`
  returns no matches.
- `#print axioms` via stdin for
  `partitionGenFun_mul_D7_eq_S7_sq`,
  `partition_section_5_eq_zero`, and
  `partition_7n_plus_5_eq_zero_mod_7` reports only
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

No existing Lean source files or import aggregators were edited.
