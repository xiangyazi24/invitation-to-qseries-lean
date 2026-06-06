# Batch 6 Reply

Tasks 97-101 are present and verified in the target chapters.

- Task 97: `ramanujanMockF_trunc_four` is in `QseriesFormalization/Chapter10.lean`.
  - Verified: `lake build QseriesFormalization.Chapter10`
- Task 98: `tCoreNumeratorTrunc_two` and `tCoreNumeratorTrunc_three` are in `QseriesFormalization/Chapter18.lean`.
  - Verified: `lake build QseriesFormalization.Chapter18`
- Task 99: `etaPolyPart_three` and `discriminantPolyPart_three` are in `QseriesFormalization/Chapter20.lean`.
  - Verified: `lake build QseriesFormalization.Chapter20`
- Task 100: `BaileyBeta_trivial_two` is in `QseriesFormalization/Chapter09.lean`.
  - Verified: `lake build QseriesFormalization.Chapter09`
- Task 101: `α_pow_seven` and `β_pow_six` are in `QseriesFormalization/Chapter11.lean`.
  - Verified: `lake build QseriesFormalization.Chapter11`

Also checked the five target chapter files for `sorry`, `axiom`, and `native_decide`; none occur in those files.

Full `lake build` was started after the single-chapter checks. It replayed through the project and reported existing warnings in `Chapter02` (`sorry`) and `Chapter13` (unused simp argument), then remained running for an extended period without producing a Lean error. The single-chapter builds for all batch targets completed successfully.
