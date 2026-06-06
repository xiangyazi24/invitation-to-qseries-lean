# Chan Chapter 15 / Theorem 11.7 analysis

Source read: `Hai-Chi Chen_An invitation to q-series.pdf`, Chapter 15, via local PDF text extraction. `pdftotext` was not installed in this environment, so I used `pdfminer.six` from `/tmp`.

## Target

Chan Theorem 11.7 is

```text
5 q d/dq log R(q) = eta(tau)^5 / eta(5 tau),    q = exp(2 pi i tau).
```

Using `eta(tau) = q^(1/24) (q;q)_infty`, the right side is

```text
(q;q)_infty^5 / (q^5;q^5)_infty.
```

Chan proves the equivalent Lambert-series identity Eq. (15.8):

```text
1 - 5 * sum_{n>=1} (n/5) * n q^n/(1-q^n)
  = (q;q)_infty^5 / (q^5;q^5)_infty,
```

where `(n/5)` is the Legendre symbol modulo 5.

## Exact mathematical steps in Chan §15.2

1. Start from Dobbie's identity Eq. (15.1):

```text
x/(1-x)^2 - z/(1-z)^2
  + sum_{j>=1} j q^j/(1-q^j) * (x^j + x^(-j) - z^j - z^(-j))

= ((x-z)(1-xz))/((1-x)^2(1-z)^2)
  * (xzq, xz^(-1)q, x^(-1)zq, x^(-1)z^(-1)q, q, q, q, q)_infty
    / ((xq, x^(-1)q, zq, z^(-1)q)_infty)^2.
```

2. Specialize

```text
x = zeta = exp(2 pi i / 5),    z = x^2.
```

Let `beta = (1+sqrt(5))/2` and `theta = beta + beta^(-1) = sqrt(5)`.

3. The two rational terms on the left give Eq. (15.3):

```text
x/(1-x)^2 - x^2/(1-x^2)^2 = - theta/5.
```

In period notation this is

```text
((zeta - zeta^2)(1-zeta^3))/((1-zeta)^2(1-zeta^2)^2)
  = -theta/5.
```

4. For the Lambert coefficient in Eq. (15.1), Chan uses the residue-class values

```text
x^j + x^(-j) - x^(2j) - x^(-2j)
  =  0       if j == 0 mod 5,
     theta   if j == 1 or 4 mod 5,
    -theta   if j == 2 or 3 mod 5.
```

Therefore the infinite sum becomes Eq. (15.4):

```text
theta * sum_{n>=1} [
    (5n-1) q^(5n-1)/(1-q^(5n-1))
  + (5n-4) q^(5n-4)/(1-q^(5n-4))
  - (5n-2) q^(5n-2)/(1-q^(5n-2))
  - (5n-3) q^(5n-3)/(1-q^(5n-3))
].
```

Call the bracketed sum `S(q)`.

5. Specialize the product side of Dobbie's identity. Since `z=x^2` and `x^5=1`, the four numerator factors become the four nontrivial root twists:

```text
(xq)_infty (x^2 q)_infty (x^3 q)_infty (x^4 q)_infty.
```

The denominator contains the same four factors squared, so the product ratio simplifies to

```text
(q;q)_infty^4 / ((xq)_infty (x^2 q)_infty (x^3 q)_infty (x^4 q)_infty).
```

Then Eq. (14.35) / cyclotomic factorization gives

```text
(q;q)_infty (xq)_infty (x^2q)_infty (x^3q)_infty (x^4q)_infty
  = (q^5;q^5)_infty.
```

So Eq. (15.5) is

```text
RHS = -theta/5 * (q;q)_infty^5 / (q^5;q^5)_infty
    = -theta/5 * eta(tau)^5 / eta(5 tau).
```

6. Combine the specialized left and right sides:

```text
-theta/5 + theta*S(q)
  = -theta/5 * eta(tau)^5/eta(5 tau).
```

Cancel `-theta/5`:

```text
1 - 5*S(q) = eta(tau)^5/eta(5 tau).       -- Eq. (15.7)
```

Equivalently,

```text
1 - 5 * sum_{n>=1} (n/5) * n q^n/(1-q^n)
  = eta(tau)^5/eta(5 tau).                -- Eq. (15.8)
```

7. Use Theorem 11.1:

```text
R(q) = q^(1/5) * (q;q^5)_infty (q^4;q^5)_infty
                  / ((q^2;q^5)_infty (q^3;q^5)_infty).
```

Taking `q d/dq log` gives

```text
q d/dq log R(q)
  = 1/5
    - sum_{m == 1,4 mod 5} m q^m/(1-q^m)
    + sum_{m == 2,3 mod 5} m q^m/(1-q^m).
```

Thus

```text
5q d/dq log R(q) = 1 - 5*S(q),
```

and Eq. (15.7) proves Theorem 11.7.

## Dobbie identity proof outline in Chan

Chan also gives Dobbie's proof of Eq. (15.1). The exact structure is:

1. Rewrite the left side of Eq. (15.1) as the bilateral sum Eq. (15.9):

```text
sum_{n in Z} [ x q^n/(1-x q^n)^2 - z q^n/(1-z q^n)^2 ].
```

This is obtained by splitting the `x` sum into `n=0`, `n>0`, `n<0`, changing `n<0` to positive indices, and expanding `(1-y)^(-2)`.

2. Define `F(x,z)` to be the product side of Eq. (15.1). For fixed `z` not an integral power of `q`, `F` as a function of `x` has double poles at `x=q^n`, `n in Z`.

3. Prove symmetries:

```text
F(x,z) = -F(z,x),
F(x,z) = F(qx,z),
F(x,z) = F(q^(-1)x,z).
```

4. Partial-fraction expand `F` in the `x` variable:

```text
F(x,z) = a0/(1-x)^2
       + sum_{n>=1} [ an/(1-x q^n)^2 + a_{-n}/(1-x^(-1) q^n)^2 ]
       + H(x,z),
```

where `H` is Laurent-expandable in `x`.

5. Determine principal parts. The pole at `x=1` gives `a0=x`; q-periodicity gives

```text
a_n = x q^n,    a_{-n} = x^(-1) q^n.
```

This yields

```text
F(x,z) = G(x) + H(x,z),
G(x) = sum_{n in Z} x q^n/(1-x q^n)^2.
```

6. Show `G(x)=G(qx)`. Then `H(x,z)=H(qx,z)`. Since `H` is a Laurent series in `x`, q-periodicity forces only the constant Laurent coefficient to survive:

```text
H(x,z)=b0(z).
```

7. Use antisymmetry:

```text
G(x)+b0(z) = -G(z)-b0(x),
```

so `b0(z)=-G(z)`. Hence

```text
F(x,z)=G(x)-G(z),
```

which is Eq. (15.1).

## Existing repo infrastructure that applies

1. Formal target already exists:

```lean
QseriesFormalization/Pending/Chapter15_R_ODE.lean
  legendre5
  chan15LHSCoeffInt
  chan15LHSCoeff
  chan15LHSPS
  chan_theorem_11_7   -- open sorry target
```

The target is already in the right multiplicative formal form:

```lean
chan15LHSPS R * PowerSeries.expand 5 (by decide) (qPochInfPS R)
  = (qPochInfPS R)^5
```

2. Eta/q-Pochhammer formal infrastructure exists:

```lean
Chapter19:
  qPochInfPS
  qPochInfPS_eq_tprod
  qPochInfPS_mul_partitionGenFun
  isUnit_qPochInfPS
  map_qPochInfPS
  coeff_qPochInfPS_eq_pentagonalSign

Chapter20:
  etaPS := qPochInfPS
  etaPS_isUnit
  map_etaPS
```

So the formal eta quotient side can be stated and manipulated as

```lean
(qPochInfPS R)^5 / PowerSeries.expand 5 (qPochInfPS R)
```

or, better, in the existing denominator-cleared form.

3. AP product infrastructure exists:

```lean
Pending/JTP_FormalPS_Pentagonal.lean
  apFactorPS
  qPochAPPS
  hasProd_qPochAPPS
  pentagonalProduct014PS
  pentagonalProduct023PS
  pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat
  pentagonalProduct023PS_eq_pentagonal023SeriesPS_rat
```

This supports the product-side `R(q)` factors and the `q -> q^5` expansion.

4. Fractional-power-free RRCF product object exists:

```lean
Pending/Chapter13_RRCF_RForm.lean
  rrcf_r := pentagonal014SeriesPS ℚ * (pentagonal023SeriesPS ℚ)^(-1)
  rrcf_v := X * expand 5 rrcf_r
  rrcf_r_mul_pentagonal023SeriesPS_eq
  rrcf_v_mul_expand_pentagonal023SeriesPS_eq
```

This is enough for the product-side `r(q)=R(q) q^(-1/5)` bookkeeping. It does not prove the analytic continued-fraction equality or the ODE.

5. Fifth-root/Gaussian-period algebra exists:

```lean
Pending/RamanujanQuintic.lean
  quinticPeriodAlpha ζ = ζ + ζ^4
  quinticPeriodBeta ζ = ζ^2 + ζ^3
  quinticPeriod_sum
  quinticPeriod_mul
  quintic_zeta_pow_five_mul_add
```

These are directly relevant to the residue table

```text
ζ^j + ζ^(-j) - ζ^(2j) - ζ^(-2j).
```

Some small new lemmas are still needed for the exact `theta`/difference normalization.

6. Constant-twist q-Pochhammer infrastructure exists over `ℂ`:

```lean
Pending/RamanujanQuinticJTP.lean
  constQFactorPS c n = 1 - c X^(n+1)
  constQPochInfPS c = ∏' n, constQFactorPS c n
  constQPochInfPS_one
  section83JTPProductPS z = (q;q)_∞ (zq;q)_∞ (z^(-1)q;q)_∞
  section83JTPProductPS_eq_rhs_pair14
  section83JTPProductPS_eq_rhs_pair23
```

This is the right object for factors like `(ζ^a q;q)_∞`. Note: `scaleX` is not the right abstraction for Eq. (15.6), because `scaleX ζ (q;q)_∞` represents `(ζ q; ζ q)_∞`, not `(ζ q;q)_∞`.

## New infrastructure needed

There are two realistic routes.

### Route A: literal Chan/Dobbie proof

Need:

1. A formal analytic statement of Dobbie Eq. (15.1), or at least its specialization at `x=ζ`, `z=ζ^2`.

2. Infrastructure for bilateral Lambert sums:

```text
sum_{n in Z} c q^n/(1-c q^n)^2
```

and their conversion to ordinary Lambert series over positive `j`.

3. Analytic/meromorphic machinery in the `x` variable if proving Dobbie literally:

```text
double poles at x=q^n,
principal parts,
partial fraction expansion,
q-periodic Laurent expansion,
antisymmetry.
```

This is the hard part. Mathlib is unlikely to make this short.

4. Specialized cyclotomic product-collapse lemmas for constant twists:

```text
∏_{a=0}^4 (ζ^a q;q)_∞ = (q^5;q^5)_∞
```

in formal `constQPochInfPS` form. The per-factor algebra is just

```text
∏_{a=0}^4 (1 - ζ^a T) = 1 - T^5,
```

but the infinite-product/tprod packaging still has to be written.

5. Gaussian-period lemmas:

```text
ζ^j + ζ^(-j) - ζ^(2j) - ζ^(-2j)
```

has the four mod-5 values needed above, and the prefactor equals `-theta/5`. Better formal version: avoid `sqrt(5)` and define

```text
delta := (ζ + ζ^4) - (ζ^2 + ζ^3).
```

Then prove the whole specialized Dobbie identity is multiplied by `delta`, and cancel using `delta ≠ 0`.

6. A formal `q d/dq log` bridge for `R(q)`:

```text
qDlog (X^(1/5) * (q;q^5)(q^4;q^5)/(q^2;q^5)(q^3;q^5))
  = 1/5 - S(q).
```

The current `Chapter15.lean` q-calculus is a q-difference derivative, not the ordinary derivative/logarithmic derivative used by Chan.

### Route B: specialized formal Eq. (15.8) only

This is probably the better formalization target for now. Avoid the full two-variable Dobbie statement and prove directly:

```lean
chan15LHSPS ℚ * expand 5 qPochInfPS = qPochInfPS^5
```

Need:

1. Either a specialized proof of Eq. (15.8) from the `x=ζ,z=ζ^2` Dobbie specialization, with no general `x,z`.

2. Or a coefficient theorem:

```text
[X^N] (qPochInfPS^5)
  = [X^N] (chan15LHSPS * expand 5 qPochInfPS)
```

for all `N`, reducing to divisor sums and pentagonal coefficients. The repo has many coefficient tools, but no general theorem proving this divisor-sum convolution identity.

3. If using modular forms/Sturm instead, almost all modular-form infrastructure is missing. `Chapter20` has formal eta/discriminant power series, not a usable Sturm theorem for weight-2 level-5 eta quotients.

## Is there a shorter proof using existing MBI/quintic JTP?

Short answer: not with the current repo, and MBI alone does not imply the ODE in any direct formal way.

What the repo already has from MBI/quintic JTP:

```lean
Pending/RamanujanQuinticJTP.lean
  most_beautiful_identity
  section83JTPProductPS_eq_rhs_pair14
  section83JTPProductPS_eq_rhs_pair23
```

This closes the mod-5 product/theta identities behind MBI. It also gives strong fifth-root JTP infrastructure for products like

```text
(q;q)_∞(ζq;q)_∞(ζ^(-1)q;q)_∞.
```

But Chan 11.7 needs the Lambert/log-derivative identity

```text
1 - 5 Σ χ(n) n q^n/(1-q^n) = E(q)^5/E(q^5).
```

The MBI gives instead

```text
Σ p(5n+4) q^n = 5 E(q^5)^5/E(q)^6.
```

That is a different eta quotient and contains no logarithmic derivative/Lambert series structure. Differentiating MBI introduces the derivative of the partition-section series, not the character Lambert series in Eq. (15.8).

There is a nearby identity in Chan §16, Eq. (16.21):

```text
Σ χ(n) q^n/(1-q^n)^2 = eta(5τ)^5/eta(τ).
```

Chan remarks that Eq. (15.8) and Eq. (16.21) are equivalent by a theorem of H. H. Chan (1996). However, the repo's MBI proof did not establish Eq. (16.21); it used a different quintic/JTP route. So using MBI would still require new infrastructure: either Eq. (16.21) plus the Chan-1996 equivalence, or a new modular-form argument.

Best practical shorter route:

1. Do not formalize full Dobbie partial fractions.
2. Prove the already-stated formal target `chan_theorem_11_7` directly as Eq. (15.8).
3. Reuse:
   - `chan15LHSPS` and `legendre5`,
   - `qPochInfPS`/`etaPS`,
   - `constQPochInfPS` for root-twisted products,
   - existing primitive-5th-root period lemmas,
   - existing analytic-to-formal product/Taylor uniqueness patterns from `RamanujanQuinticJTP`.
4. Add only the specialized `ζ,ζ²` Dobbie/Lambert identity and the constant-twist all-five-root product collapse.

This is shorter than proving general Dobbie Eq. (15.1), but it is still new work. The current MBI/quintic JTP files can remove the cyclotomic/JTP bookkeeping, not the central Lambert-series proof.
