# Ch13 Theorem 11.5 analysis

## Bottom line

The shortest path to `chan_theorem_11_5` is Watson's proof, not the Gugg proof.

With Theorem 11.1 now proved as

`Ch13RRCF.rrcf_r = Ch11RRCFConvergent.rrcf_r_via_CF`,

the formal `rrcf_r` in Chapter 13 is now known to be the continued-fraction
object Chan calls `R(q)/q^(1/5)`.  For the current Lean statement itself,
however, Theorem 11.1 is mostly a bridge theorem: `chan_theorem_11_5` is already
stated purely in the product-form `rrcf_r`.

The remaining mathematical work is:

1. package a formal version of Theorem 11.3 at `q -> q^5`;
2. package Eq. 12.37 and its `q -> q^5` expansion;
3. add the missing Watson polynomial/algebra branch step.

Theorem 11.2 is not needed on this route.

## Current Lean state

`Pending/Chapter13_DeepIdentity.lean`

The target is exactly the denominator-cleared Chan identity:

`rrcf_r^5 * B(rrcf_v) = expand5(rrcf_r) * A(rrcf_v)`,

where

- `rrcf_v = X * expand5(rrcf_r)`;
- `A(v) = 1 - 2v + 4v^2 - 3v^3 + v^4`;
- `B(v) = 1 + 3v + 4v^2 + 2v^3 + v^4`.

This is Chan's

`u^5 = v * A(v) / B(v)`

after writing `u = R(q) = q^(1/5) rrcf_r`, so
`u^5 = X * rrcf_r^5`, and `v = R(q^5) = X * expand5(rrcf_r)`.
The current Lean theorem has cancelled the common factor `X`.

`Pending/Chapter13_RRCF_RForm.lean`

The definitions and unit infrastructure are in place:

- `rrcf_r = pentagonal014SeriesPS Q * (pentagonal023SeriesPS Q)^-1`;
- `rrcf_v = X * expand5(rrcf_r)`;
- denominator unit lemmas for the two polynomial denominators;
- multiplication lemmas connecting `rrcf_r` and `rrcf_v` back to the
  pentagonal numerator/denominator series.

`Pending/Chapter13_Watson_Algebraic.lean`

This has the polynomial names and some elementary facts for `A` and `B`, but it
does not yet contain the two Watson identities actually needed for assembly:

- `(1 - v - v^2) * A(v) * B(v) = 1 - 11 v^5 - v^10`;
- `B(v)^2 - 11 v A(v) B(v) - v^2 A(v)^2 = (1 - v - v^2)^5`.

Both are pure `ring`-level identities.

`Pending/Chapter13_CoeffVerification.lean`

This verifies the identity through degree 10.  It is useful as a regression
check, but it is not a route to the full theorem.

`Pending/RR_FinalAssembly.lean` and `Pending/Chan_Theorem_11_1.lean`

The Rogers-Ramanujan ratio bridge is complete:

- `rrHPS * rrGPS^-1 = Ch13RRCF.rrcf_r`;
- `Ch13RRCF.rrcf_r = Ch11RRCFConvergent.rrcf_r_via_CF`.

No further RR ratio work is needed for Theorem 11.5.

## PDF dependency check

Chapter 13 gives two proofs.

Gugg proof:

- uses Theorem 11.2;
- introduces products `A^j_{s,t}` and `B^j_{s,t}`;
- needs Theorem 13.1, equations (13.6)--(13.14);
- uses roots of unity, fractional powers, and square roots through
  Theorem 11.2.

Watson proof:

- uses Theorem 11.3 with `q -> q^5`, equation (13.18);
- uses Eq. 12.37, equation (13.19), and the same equation with `q -> q^5`,
  equation (13.20);
- then finishes by polynomial algebra in `v`.

Therefore the Watson proof has the smaller Lean surface.

## Prerequisites

### Theorem 11.2

Needed for shortest path: no.

Theorem 11.2 is only needed for the Gugg proof.  It is not currently present in
the Lean files I checked.  Existing `RamanujanQuinticJTP` infrastructure has
some related JTP/product identities over `C`, but Theorem 11.2 itself would
need new infrastructure for:

- `J(x; q^(1/5))`;
- the alpha/beta quadratic constants in Chan's statement;
- square roots;
- fractional-power bookkeeping;
- the product identity used in Chapter 12 to derive Theorem 11.3.

This is not the shortest route to `chan_theorem_11_5`.

### Theorem 11.3

Needed for shortest path: yes, but only its `q -> q^5` formal version.

The useful cleared form is the identity

`G5^2 - X*G5*H5 - X^2*H5^2 = E * E5`,

where

- `H5 = expand5(pentagonal014SeriesPS Q)`;
- `G5 = expand5(pentagonal023SeriesPS Q)`;
- `E = qPochInfPS Q`;
- `E5 = expand5(E)`.

This is equivalent to Chan's equation (13.18):

`1/v - 1 - v = E / (X * E25)`,

with `v = X * H5/G5` and `E25 = expand25(E)`.

Can it be proved from existing infrastructure: yes, likely with moderate
packaging.

The relevant existing pieces are in `Pending/RamanujanQuinticJTP.lean`:

- `section83A = expand5(pentagonal023SeriesPS)`;
- `section83B = expand5(pentagonal014SeriesPS)`;
- `section83JTPProductPS_eq_rhs_pair14`;
- `section83JTPProductPS_eq_rhs_pair23`;
- root-of-unity product collapse lemmas for `qPochInfPS`.

Those are precisely the formal JTP/product ingredients behind the product proof
of Theorem 11.3.  What is missing is an exported rational theorem in the exact
Chapter 13 shape.

### Eq. 12.37

Needed for shortest path: yes.

The useful cleared form is

`E5^6 * core(H,G) = E^6 * H^5 * G^5`,

where

- `H = pentagonal014SeriesPS Q`;
- `G = pentagonal023SeriesPS Q`;
- `E = qPochInfPS Q`;
- `E5 = expand5(E)`;
- `core(H,G) = G^10 - 11*X*H^5*G^5 - X^2*H^10`.

This is exactly the Laurent-free version of

`1/R(q)^5 - 11 - R(q)^5 = f(-q)^6 / (q f(-q^5)^6)`.

The `q -> q^5` version is obtained by applying `expand5`, giving the same
identity with `H5`, `G5`, `E5`, `E25`, and powers `X^5`, `X^10`.

Can it be proved from existing infrastructure: yes, but this is the main
remaining mathematical packaging gap.

Important distinction: `RamanujanQuinticJTP.lean` proves the final formal MBI
through the denominator identity

`E5DenominatorCoreRat * expand25(E) = E5^6`.

That is a sibling mod-5 product identity, not Eq. 12.37 itself.

However, `Chapter16_MBI_Proof.lean` already contains the exact Eq. 12.37 core
as `ramanujanMod5ProductCoreThetaRat`, and it proves that the desired cleared
Eq. 12.37 follows from the clean quintic product

`ramanujanMod5ProductCoreThetaRat * E5 = E^11`.

See the wrappers around:

- `mod5_product_core_compressed_theta_of_clean_quintic`;
- `mod5_product_core_compressed_theta_iff_clean_quintic`.

`RamanujanQuintic.lean` also contains the algebraic factor-pair reduction for
this clean quintic core.  What is not currently exported is the unconditional
clean product theorem itself.

The best way to get Eq. 12.37 is probably Chan's Exercise 12.4(6) route:

1. use Theorem 11.3;
2. scale by fifth roots of unity;
3. multiply the five scaled identities;
4. use the existing root-of-unity collapse for `qPochInfPS`;
5. identify the left side with `ramanujanMod5ProductCoreThetaRat`.

This uses existing root-of-unity and product-collapse infrastructure.  It is
still a real proof task, but it is much smaller than formalizing Theorem 11.2
and the Gugg proof.

## Watson assembly after the prerequisites

Let

- `r = rrcf_r`;
- `s = expand5(r)`;
- `v = X*s`;
- `Y = X*r^5`;
- `A = A(v)`;
- `B = B(v)`;
- `C = 1 - v - v^2`.

From Theorem 11.3 and Eq. 12.37, Watson gives the cleared equation

`v*A*B - 11*v*A*B*Y - v*A*B*Y^2 = C^5 * Y`.

The proposed solution is

`Z = v*A/B`.

The second Watson polynomial identity gives the same cleared equation for `Z`.
If `Y` and `Z` both satisfy the cleared equation, subtracting the two equations
factors out `Y - Z`; the remaining factor has constant coefficient `-1`, hence
is a unit.  Therefore `Y = Z` inside formal power series.

Then

`X*r^5*B = v*A = X*s*A`.

The final Lean target follows by cancelling the common `X` factor, using the
standard coefficient-shift injectivity of multiplication by `X`.

So the final assembly needs only:

- the two formal prerequisite identities above;
- the two missing Watson polynomial identities;
- a small branch uniqueness/cancellation lemma;
- an `X`-multiplication injectivity lemma if one is not already available.

## Recommended route

1. Do not formalize Theorem 11.2 for this theorem.
2. Prove/export the `q -> q^5` formal Theorem 11.3 in Chapter 13 terms.
3. Prove/export Eq. 12.37 in the cleared `ramanujanMod5ProductCoreThetaRat`
   shape, then get its `expand5` version.
4. Add the two Watson polynomial identities to
   `Chapter13_Watson_Algebraic.lean`.
5. Assemble `chan_theorem_11_5` by the formal branch uniqueness argument above.

Expected difficulty ranking:

1. Eq. 12.37 clean quintic product packaging: hardest remaining part.
2. Theorem 11.3 packaging: medium.
3. Watson algebra and final cancellation: small.

