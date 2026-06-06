# codex-asd5-etaquotient reply

Status: partial, 0-sorry.

Touched:
- `QseriesFormalization/Pending/ASD_EtaProducts.lean`

Closed:
- Added integral and mod-5 versions of the two mod-5 JTP product identities:
  - `pentagonalProduct014PS_eq_pentagonal014SeriesPS_int`
  - `pentagonalProduct023PS_eq_pentagonal023SeriesPS_int`
  - `pentagonalProduct014PS_eq_pentagonal014SeriesPS_zmod5`
  - `pentagonalProduct023PS_eq_pentagonal023SeriesPS_zmod5`
- Lifted the F/G eta-product identities to `ZMod 5`:
  - `asd5FProductPS_eq_asd5FSeriesPS_zmod5`
  - `asd5GProductPS_eq_asd5GSeriesPS_zmod5`
- Added the shifted product name for Hirschhorn's `-3qG(q^5)` term:
  - `asd5GShiftedProductPS`
- Added conditional section-to-eta bridge lemmas showing that, once the two
  remaining component identifications are supplied,
  `A 0 = asd5FProductPS (ZMod 5)` and
  `A 1 = asd5GShiftedProductPS`, the existing ASD section congruences rewrite
  to eta-product form:
  - `partition_section_0_eq_eta_product_of_A0`
  - `partition_section_1_eq_eta_product_of_A0_A1`
  - `partition_section_2_eq_eta_product_of_A0_A1`
  - `partition_section_3_eq_eta_product_of_A1`
- Re-exported the clean divided `5n+4` vanishing in this file:
  - `partition_section_4_eq_zero_eta_product`

Not closed:
- The unconditional coefficient-level identifications
  `A 0 = F(q^5)` and `A 1 = -3qG(q^5)` over `ZMod 5`.
- Consequently the unconditional eta-quotient forms for `j = 0,1,2,3` are
  still conditional on those two identifications.

Validation:
- `lake env lean QseriesFormalization/Pending/ASD_EtaProducts.lean`
- `rg -n "\bsorry\b|\badmit\b|\baxiom\b|sorryAx|native_decide" QseriesFormalization/Pending/ASD_EtaProducts.lean`
  returned no matches.
