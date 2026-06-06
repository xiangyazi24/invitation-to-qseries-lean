Final Ch20 verification/documentation pass completed.

Verification:

- `lake build QseriesFormalization` completed successfully.
- Lake reported: `Build completed successfully (8011 jobs).`
- `rg -n "sorry|admit|axiom" QseriesFormalization/Chapter20.lean`
  returned no matches.

Documentation updated:

- `UNDERSTANDING.md`
  - Updated global status to 17/20 PASS, with AUX now Ch10, Ch15, Ch20.
  - Recorded the latest full-build result:
    `lake build QseriesFormalization`, 8011 jobs, 2026-06-01.
  - Added the Ch20 theorem list after tau consolidation.
- `HANDOFF.md`
  - Updated date/state.
  - Recorded the successful full-build check.
  - Added the current Ch20 theorem list.

Ch20 theorem list now recorded:

- `ramanujanTau_zero` through `ramanujanTau_fifty`.
- `ramanujanTau_mul_of_coprime_mul_le_50`.
- `ramanujanTau_hecke_prime_power_le_50`.
- `ramanujanTau_log_derivative_recurrence`.
- `ramanujanTau_mod_two_eq_one_iff_odd_square`.
- `ramanujanTau_odd_iff_odd_square_param`.
- `ramanujanTau_odd_iff_odd_square`.
- `sigma11`.
- `ramanujanTau_congr_sigma11_mod_691_through_fifty`.
