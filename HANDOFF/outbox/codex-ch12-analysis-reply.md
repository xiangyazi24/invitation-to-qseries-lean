# Chan Theorem 11.4 feasibility analysis

## Conclusion

I do not think Chan Theorem 11.4 is currently closeable in Lean from the
available files.

Mathematically, Theorem 11.2 is not needed once Theorem 11.3 is available in
the analytic form used by Chan.  Chan's Section 12.3 proof of Theorem 11.4 is:

1. Use Theorem 11.3 to get
   \[
   \frac1{R(q)} - 1 - R(q)
     =
   \frac{f(-q^{1/5})}{q^{1/5} f(-q^5)}.
   \]
2. Put \(q = e^{2\pi i\tau}\), rewrite the right side as
   \[
   \frac{\eta(\tau/5)}{\eta(5\tau)}.
   \]
3. Put \(\tau=i\), so \(q=e^{-2\pi}\), and use the eta transformation
   formula
   \[
   \eta(-1/z)=\sqrt{z/i}\,\eta(z)
   \]
   with \(z=5i\), giving
   \[
   \frac{\eta(i/5)}{\eta(5i)}=\sqrt 5.
   \]
4. Hence, for \(x=R(e^{-2\pi})\),
   \[
   \frac1x - 1 - x = \sqrt 5,
   \]
   and the positive root is
   \[
   x = \sqrt{\frac{5+\sqrt5}{2}}-\frac{1+\sqrt5}{2}.
   \]

The problem is that the current Lean inputs do not yet provide the analytic
objects and bridges needed to instantiate this argument.

## Current Lean inputs

### `Pending/Chapter12_SpecialValue.lean`

This file defines the real target value

```lean
ramanujanRRCFSpecialValue : ℝ :=
  Real.sqrt ((5 + Real.sqrt 5) / 2) - (1 + Real.sqrt 5) / 2
```

and proves elementary positivity/algebra support.  It does not define an
analytic scalar \(R(q)\), nor does it state an equality
\(R(e^{-2\pi}) =\) this value.  The file header explicitly says that this
special-value equality remains open and requires analytic RRCF convergence and
modular theory.

### `Pending/Chan_Theorem_11_1.lean`

The available Theorem 11.1 is a formal-power-series result.  The exported
statement is

```lean
QseriesFormalization.Pending.chan_theorem_11_1 :
  Ch13RRCF.rrcf_r = Ch11RRCFConvergent.rrcf_r_via_CF
```

and the stronger ratio statement inside the file is

```lean
rrcf_r_via_CF_eq_rrHPS_mul_rrGPS_inv :
  rrcf_r_via_CF = rrHPS * rrGPS⁻¹
```

This is the formal identity corresponding to \(r(q)=H(q)/G(q)\), not an
analytic theorem evaluating a complex function at \(q=e^{-2\pi}\).

### `Pending/Chapter13_Thm113.lean`

The available Theorem 11.3 is also formal.  The final theorem is

```lean
QseriesFormalization.Pending.Ch13Thm113.chan_theorem_11_3_formal_ps
```

It proves a cleared formal-power-series identity over `ℚ`:

```lean
(PowerSeries.expand 5 (pentagonal023SeriesPS ℚ)) ^ 2
  - X * PowerSeries.expand 5 (pentagonal023SeriesPS ℚ)
      * PowerSeries.expand 5 (pentagonal014SeriesPS ℚ)
  - X ^ 2 * (PowerSeries.expand 5 (pentagonal014SeriesPS ℚ)) ^ 2
  =
qPochInfPS ℚ * PowerSeries.expand 5 (qPochInfPS ℚ)
```

This is the formal, denominator-cleared version behind

\[
\frac1{R(q)} - 1 - R(q)
  =
\frac{f(-q^{1/5})}{q^{1/5}f(-q^5)}.
\]

It does not currently expose the analytic scalar identity at a complex \(q\).

### `Pending/Chapter13_RRCF_RForm.lean`

This file defines

```lean
rrcf_r : PowerSeries ℚ :=
  pentagonal014SeriesPS ℚ * (pentagonal023SeriesPS ℚ)⁻¹

rrcf_v : PowerSeries ℚ := X * PowerSeries.expand 5 rrcf_r
```

The comments explain that `rrcf_v` is the fractional-power-free version of
\(R(q^5)=q r(q^5)\).  This is useful formal infrastructure, but still not an
analytic evaluation theorem.

## Mathlib eta transformation check

Mathlib has a true Dedekind eta definition:

```lean
ModularForm.eta : ℂ → ℂ
```

in

```text
Mathlib/NumberTheory/ModularForms/DedekindEta.lean
```

It also has basic analytic facts such as:

```lean
ModularForm.eta_ne_zero
ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
```

However, I did not find the Dedekind eta modular transformation theorem

```text
eta (-1 / τ) = sqrt (-I * τ) * eta τ
```

or an equivalent slash-action statement for eta.  I checked the relevant
Mathlib modular forms / theta / upper half-plane files and queried Lean.  The
available nearby theorem is the Jacobi theta S-transform:

```lean
jacobiTheta_S_smul :
  ∀ τ : UpperHalfPlane,
    jacobiTheta ↑(ModularGroup.S • τ)
      = (-Complex.I * ↑τ) ^ (1 / 2) * jacobiTheta ↑τ
```

So Mathlib appears to contain the theta transformation machinery, but not the
Dedekind eta transformation formula needed by Chan's Section 12.3 proof.

## Can Theorem 11.4 be proved without Theorem 11.2?

Mathematically: yes, if Theorem 11.3 is already available analytically.  The
Section 12.3 proof uses only Theorem 11.3, the eta rewrite, the eta
S-transform, and quadratic algebra.  Theorem 11.2 is only part of Chan's route
to Theorem 11.3.

In the current Lean development: not yet.  The available Theorem 11.3 is a
formal-power-series theorem, not the analytic identity needed at
\(q=e^{-2\pi}\).  Therefore Theorem 11.2 can be bypassed conceptually, but this
does not close Theorem 11.4 with the current API.

## Missing prerequisites for a Lean proof

To close Theorem 11.4, the project likely needs the following intermediate
results.

1. An analytic RRCF function \(R(q)\), or a theorem identifying the existing
   formal `rrcf_v` / `rrcf_r` with the analytic continued fraction or product
   for real \(0<q<1\).

2. A specialization/evaluation bridge from
   `chan_theorem_11_3_formal_ps` to the analytic identity
   \[
   \frac1{R(q)} - 1 - R(q)
     =
   \frac{f(-q^{1/5})}{q^{1/5} f(-q^5)}
   \]
   at least for \(q=e^{-2\pi}\).

3. A bridge from the \(f(-q)\) product to Mathlib's `ModularForm.eta`,
   including the exact \(q^{1/24}\) normalization cancellation:
   \[
   \frac{f(-q^{1/5})}{q^{1/5}f(-q^5)}
     =
   \frac{\eta(\tau/5)}{\eta(5\tau)}
   \quad(q=e^{2\pi i\tau}).
   \]

4. The eta S-transform, or at least the specialized value
   \[
   \frac{\eta(i/5)}{\eta(5i)}=\sqrt5.
   \]
   Current Mathlib does not appear to provide this directly.

5. Positivity/nonzero facts for \(R(e^{-2\pi})\), so the quadratic equation
   selects Chan's positive root rather than the other root.

## Practical route

The shortest route is probably not to formalize all of Theorem 11.2.  Instead,
build a narrow analytic bridge for the already-proved formal Theorem 11.3 and
prove the specialized eta/theta evaluation needed at \(\tau=i\).

Even the specialized route is nontrivial: the eta transformation theorem is not
currently in Mathlib, and the formal-to-analytic bridge for `rrcf_v` and the
Euler products is not exposed by the existing files.  Therefore I did not write
Lean code for Theorem 11.4.
