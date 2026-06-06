# codex ch15 wronskian jacobi reply

Result: not closed; no commit made.

I tried ANGLE A first.  The Jacobi bridge itself is already available in this
file via
`QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_six_eq_jacobiThetaPS_pow_two`,
and the local coefficient bridge is already present as
`coeff_jacobiThetaPS_sq`.

The exact remaining ANGLE A blocker is the independent series identity

```lean
pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
  5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
       pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ)) =
  (qPochInfPS ℚ) ^ 6
```

With this theorem, the blocked branch would close by coefficient extraction:

```lean
have hcoeff := congrArg (fun f : ℚ⟦X⟧ => f.coeff N) hw
change
  (pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
      5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
           pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ))).coeff N =
    ((qPochInfPS ℚ) ^ 6).coeff N at hcoeff
rw [coeff_pentagonal_wronskian_lhs] at hcoeff
rw [qPochInfPS_pow_six_eq_jacobiThetaPS_pow_two] at hcoeff
rw [coeff_jacobiThetaPS_sq] at hcoeff
exact hcoeff
```

But the only existing unconditional routes in the file reduce this to the
already-isolated AP-sigma eta identity

```lean
apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5
```

or equivalently the all-degree residual

```lean
∀ n : ℕ, apSigmaLambertThetaResidualZ n = 0
```

Those are exactly the missing Chan/quintuple-product arithmetic input, so using
them here would be circular.

ANGLE B status: the file has local 5-string algebra, including
`fiveStringHSum_eq_fiveStringC_mul`,
`unitConjOrbitK_pi5_add_piBar5`, endpoint/interior vanishing lemmas, and the
closed `t=0` shell identity.  What is missing is the global finite-shell
decomposition/reindexing that partitions `fullNormShell N` for
`5 ∣ 4*N+1` into primitive 5-strings and proves the K/H string sums cover the
full shell without overlap.  I did not find such a lemma or a Sturm/valence
theorem in the available imports.

Precise current Lean branch goal at the remaining `sorry`:

```lean
N : ℕ
h5N : ¬(4 * (N : ℤ) + 1) % 5 ≠ 0
⊢ pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N
```

I made one local compile fix in
`QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean` inside
`unitConjOrbitK_pi5_add_piBar5`, replacing a failed `simp` with explicit
rewrites of the two zero terms.

Verification run:

```bash
export PATH=$HOME/.elan/bin:$PATH && lake env lean QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean
```

Result: exit code 0, with the expected warning:

```text
QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean:5514:8:
warning: declaration uses 'sorry'
```

I did not run `#print axioms` because the main theorem is still closed by
`sorry`.
