# Task: close the last Ch15 sorry (RR-Wronskian = jacobiTheta²), or report the exact blocker

## The ONLY goal
Close the single remaining `sorry` in
`QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean`,
in theorem `pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff` (the `5 ∣ 4*N+1` branch;
the `t=0` / `4N+1 ≢ 0 mod 5` branch `..._of_t0` is already proved).
This is the ONLY blocker for Chan §15 / Theorem 11.7 (the Rogers–Ramanujan continued
fraction differential equation). Closing it unconditionally finishes Ch15.

STRICT acceptance: NO `sorry`, NO `axiom`, NO `native_decide` in any committed proof.
(You may use `native_decide`/`decide` only as a throwaway numeric sanity check; never commit it.)
Self-verify with: `export PATH=$HOME/.elan/bin:$PATH && lake env lean QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean`.
One file, one writer: edit ONLY `Chapter15_WronskianIndependent.lean` (you may add new helper
defs/lemmas in it). Do NOT touch `QseriesFormalization.lean` or `Audit.lean`.

## KEY NEW RESOURCE you likely have not used
The formal-power-series Jacobi identity is ALREADY PROVED, over any commutative ring R:
  `(qPochInfPS R)^3 = jacobiThetaPS R`
in `QseriesFormalization/Pending/Chapter19_B2_FromCubeConvolution.lean` (theorem near line 95;
also in `Chapter06_Macdonald_A1.lean`). Import it.

Consequence (prove this small bridge first):
  `(jacobiThetaPS ℚ)^2 = (qPochInfPS ℚ)^6`,  hence
  `jacobiThetaSquareCoeff N = ((qPochInfPS ℚ)^6).coeff N`   for every N
(using the already-proved `jacobiThetaSquareCoeff N = ((jacobiThetaPS ℚ)^2).coeff N`).

So the target `pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N` is EQUIVALENT to the
SERIES identity:
  `pentagonalWronskian (series) = (qPochInfPS ℚ)^6`,
where (at pentagonal level)
  `pentagonalWronskian = pentagonal014SeriesPS·pentagonal023SeriesPS
        + 5·(pentagonal023SeriesPS·thetaOp pentagonal014SeriesPS
             − pentagonal014SeriesPS·thetaOp pentagonal023SeriesPS)`.

## Math design (from an expert q-series proof reviewer)
Let A = f(−X,−X⁴), B = f(−X²,−X³) be the two Rogers–Ramanujan theta series; by JTP these
are the pentagonal products, and AB = (X;X)_∞·(X⁵;X⁵)_∞. The clean identity is the WRONSKIAN
  AB + 5(B·θA − A·θB) = P⁶,  P = (X;X)_∞,  θ = X·d/dX,
which is exactly Jacobi's Θ² = P⁶ since Θ = P³ (the proved Jacobi identity above).
The whole Ch15 differential-equation identity `apSigmaLambertFactor · expand5(qPoch) = qPoch^5`
then follows from this Wronskian by: `L·AB = AB + 5(BθA − AθB)` (because
`L = 1 + 5·θlog(A/B)`), giving `L·P·P₅ = P⁶`, then cancel the unit P.

## Two attack angles (try ANGLE A first — it may bypass the stuck coefficient grouping)

ANGLE A — series-level, using the now-available Jacobi identity:
  1. Prove `(jacobiThetaPS ℚ)^2 = (qPochInfPS ℚ)^6` from the imported formal Jacobi identity.
  2. Try to prove the SERIES identity
       `pentagonalWronskian = (qPochInfPS ℚ)^6`
     directly, using the existing infrastructure in this file:
       - `etaQuotientProductSide_mul_expandFive_eq_qPoch_pow_five` and the eta-product splits,
       - the proved `thetaLog_P014_eq_neg_apSigmas`, `thetaLog_P023_eq_neg_apSigmas`,
       - `wronskian_at_pentagonal_level_of_apSigma_mul_expandFive` (note: this currently goes
         apSigma ⇒ Wronskian; you want an INDEPENDENT proof of Wronskian = P⁶ so the implication
         can be reversed without circularity),
       - any theta bilinear / addition identity available in Mathlib or Chapter04_T43.
     If you find a clean series proof, it closes the goal without the 5-string coefficient grouping.

ANGLE B — finish the existing coefficient route:
  Close the `5 ∣ 4N+1` branch of `pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff` by the
  "group each non-endpoint 5-string" argument, mirroring how the `_of_t0` branch handled the
  other residue case. The expanded forms `pentagonalWronskianCoeffExpanded`,
  `jacobiThetaSquareCoeffExpanded`, `fullNormShellHQuarterSum` are already set up.

## If you cannot close it
Do NOT fake it. Report in `HANDOFF/outbox/codex-ch15-wronskian-jacobi-reply.md`:
- exactly which sub-lemma blocks, with the precise goal state;
- whether ANGLE A reduces to a clean missing theta identity (name it);
- whether ANGLE B's 5-string grouping needs a finite bound (Sturm/valence) Mathlib lacks.
This honest blocker report is itself a valuable deliverable.

## On success
Report the final `#print axioms` of `pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff`
(must be only `propext, Classical.choice, Quot.sound`), and confirm
`lake env lean QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean` passes.
Then commit with a clear message.
