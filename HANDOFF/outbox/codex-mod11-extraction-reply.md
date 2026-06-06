Closed the mod-11 residue-extraction gap in
`QseriesFormalization/Pending/Chapter17_Hirschhorn_Mod11.lean`.

What changed:
- Added residue-support infrastructure (`IsRes`) for `section11`, including
  add/mul/pow support lemmas and a canonical `JTerm` monomial normal form.
- Proved the explicit degree-4 extractions
  `section11 r (JSum^4) = R_r` for `r = 3,6,8,9,10`.
- Proved the explicit degree-7 extraction
  `section11 6 (JSum^7) = P`.
- Converted the existing `(qPoch)^12` off-pentagonal coefficient vanishing into
  `R_r = 0`, then used
  `HirschhornComb.hirschhorn_P_eq_combination` to prove `P = 0`.
- Replaced the theorem
  `coeff_qPochInfPS_pow_twentyone_at_11n_plus_6_eq_zero`
  with a real proof.

Validation:
- `~/.elan/bin/lake env lean QseriesFormalization/Pending/Chapter17_Hirschhorn_Mod11.lean`
  exits successfully.
- `rg -n "sorry|admit|axiom" QseriesFormalization/Pending/Chapter17_Hirschhorn_Mod11.lean`
  returns no matches.
