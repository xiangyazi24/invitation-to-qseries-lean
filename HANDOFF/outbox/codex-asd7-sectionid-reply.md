# codex-asd7-sectionid reply

Created `QseriesFormalization/Pending/ASD_Mod7_EtaQuotient.lean`.

Closed with 0 sorry/admit/axiom in the new file:

- `asd7HProductPS_eq_asd7HSeriesPS_zmod7`
- `asd7JProductPS_eq_asd7JSeriesPS_zmod7`
- `asd7KProductPS_eq_asd7KSeriesPS_zmod7`
- `ASD7_0_eq_asd7HSeriesPS_zmod7`
- `ASD7_0_eq_asd7HProductPS_zmod7`
- `ASD7_1_eq_asd7JShiftedSeriesPS_zmod7`
- `ASD7_1_eq_asd7JShiftedProductPS_zmod7`
- `ASD7_3_eq_asd7KShiftedSeriesPS_zmod7`
- `ASD7_3_eq_asd7KShiftedProductPS_zmod7`
- unconditional eta-product section congruences:
  `partition_section_0_eq_eta_product`,
  `partition_section_1_eq_eta_product`,
  `partition_section_2_eq_eta_product`,
  `partition_section_3_eq_eta_product`,
  `partition_section_4_eq_eta_product`,
  `partition_section_5_eq_zero_eta_product`,
  `partition_section_6_eq_eta_product`.

Notes:

- `asd7JShiftedProductPS = -3 * X * asd7JProductPS (ZMod 7)`.
- `asd7KShiftedProductPS = 5 * X^3 * asd7KProductPS (ZMod 7)`.
- The coefficient matching mirrors `Pending.ASD_EtaProducts`: triangular
  residue splits `0={0,6}`, `1={1,5}`, `3={2,4}` are matched to
  theta exponents `c=1,3,5`, with scalars `1`, `-3`, and `5`.

Verification:

- `lake env lean QseriesFormalization/Pending/ASD_Mod7_EtaQuotient.lean`
  succeeds.
- `lake build QseriesFormalization.Pending.ASD_Mod7_EtaQuotient` succeeds.
- `rg -n "sorry|admit|axiom|sorryAx" QseriesFormalization/Pending/ASD_Mod7_EtaQuotient.lean`
  returns no matches.
- `#print axioms` for the three ASD7 identifications and all seven
  `partition_section_*` eta-product theorems reports only
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

No existing Lean source file or import aggregator was edited.
