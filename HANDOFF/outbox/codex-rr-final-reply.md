Status: Rogers-Ramanujan formal G/H assembly closed; full Chan 11.1 still blocked by a missing CF-limit-to-ratio theorem.

Implemented:

- Added `QseriesFormalization/Pending/RR_FinalAssembly.lean`.
- Extended `QseriesFormalization/Pending/RR_TaylorBridge.lean` with the H-side Taylor bridge:
  - `analyticAt_rrJInf_q_zero`
  - `hasFPowerSeriesAt_rrJTerm_q`
  - `rrJInf_q_taylorCoeff_eq_rrHPS_coeff`
  - `exists_rrJInf_q_taylor_coeffs_agree`
- Proved in `RR_FinalAssembly`:
  - `rogers_ramanujan_G_complex_formal`
  - `rogersRamanujan_G_formal :
      rrGPS * qPochInfPS ℚ = pentagonal023SeriesPS ℚ`
  - `rogers_ramanujan_H_complex_formal`
  - `rogersRamanujan_H_formal :
      rrHPS * qPochInfPS ℚ = pentagonal014SeriesPS ℚ`
  - `rogersRamanujan_ratio_formal :
      rrHPS * rrGPS⁻¹ = Ch13RRCF.rrcf_r`
  - conditional final bridge:
    `chan_theorem_11_1_of_rrcf_via_CF_eq_ratio`, which turns a future proof
    `rrcf_r_via_CF = rrHPS * rrGPS⁻¹` into
    `Ch13RRCF.rrcf_r = rrcf_r_via_CF`.

Validation:

```bash
lake build QseriesFormalization.Pending.RR_TaylorBridge
lake env lean QseriesFormalization/Pending/RR_FinalAssembly.lean
rg -n "sorry|axiom|admit" \
  QseriesFormalization/Pending/RR_FinalAssembly.lean \
  QseriesFormalization/Pending/RR_TaylorBridge.lean
```

The single-file check passes with no warnings. The `rg` check returns no
matches in the touched files.

I did not add an unconditional theorem `rrcf_r = rrcf_r_via_CF`. The repo
does not currently contain the claimed CF convergence theorem identifying
`rrcf_r_via_CF` with `rrHPS * rrGPS⁻¹`; `Chapter11_Thm111.lean` explicitly
states that the full equality remains open and only proves coefficient
matches through degree 20. The formal RR product identities now close the
product/ratio side; the remaining missing piece is exactly the CF-limit
identification.
