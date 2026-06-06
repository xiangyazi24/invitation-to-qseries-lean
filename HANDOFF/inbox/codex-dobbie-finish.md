# Task: FINISH Ch15 — assemble the recurrence + induction, with clean-3 axioms

You have already committed (good): `string_scalar_identity`, `fiveStringHSum_recurrence`,
`fiveStringASum_recurrence`, `gaussK_pi5_conj_pair_recurrence`, `fiveStringEndpointScalar_recurrence`,
`normShellHSumByNorm_five_filter_decomp`, and the conditional closer
`pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_apSigma_residual_recurrence` (line ~6103),
plus abstract recurrence→zero lemmas. ONE sorry remains at line ~6143 (the `5∣4*N+1` branch of
`pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff`).

## Finish it
1. Assemble the UNCONDITIONAL recurrence `S(5M) = -6·S(M) - 25·S(M/5)` for both shell sums
   (K = pentagonal selected, H = Jacobi) from your committed `fiveStringHSum_recurrence`,
   `gaussK_pi5_conj_pair_recurrence`, `normShellHSumByNorm_five_filter_decomp`, and
   `fiveStringEndpointScalar_recurrence`. (Verified numerically: holds for both sides, M<400.)
2. Close the `5∣4N+1` branch by strong induction on the 5-adic valuation k of M=4N+1
   (M = 5^k·M₀, 5∤M₀):
   - **Base k=0 (5∤M)**: use `pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_t0`. (ALGEBRAIC — NOT native_decide.)
   - **Step**: both K and H satisfy the same recurrence with equal S(M), S(M/5) by IH ⟹ equal at 5M.
   Then feed into `..._of_apSigma_residual_recurrence` (or directly) to kill the sorry.

## HARD REQUIREMENT: clean-3 axioms
The final `pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff` MUST satisfy
`#print axioms pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff = [propext, Classical.choice, Quot.sound]`.
- It must NOT depend on `pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_le_fifty` or ANY lemma
  proved by `native_decide` (those inject `Lean.ofReduceBool`/`trustCompiler` and FAIL the audit).
- The recurrence base case is the algebraic `5∤M` branch — do NOT bottom out the induction on a
  finite `native_decide` range. If you need small-case checks, use `decide`/`rfl`/explicit `omega`, never `native_decide`.
- After closing, RUN `#print axioms` (via a scratch import) and paste the result in your reply.
  If it shows `ofReduceBool`, find the native_decide dependency and replace it with `decide`/explicit, then re-verify.

## Discipline
STRICT 0 sorry / 0 axiom / 0 native_decide IN THE DEPENDENCY CHAIN of the final theorem. Self-verify
`lake env lean QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean`. Edit only that file.
Commit when the sorry is gone AND #print axioms is clean-3. Write HANDOFF/outbox/codex-dobbie-finish-reply.md
with the final #print axioms output.
