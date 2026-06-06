# Can Chan Theorem 11.7 be derived from Theorem 11.5?

Verdict: yes, but not by a straight rewrite/multiplication of the existing
identities.  The viable route is a `q -> q^5` recursion:

1. take the formal logarithmic derivative of Theorem 11.5 to show the
   Lambert/RRCF side satisfies a recursion;
2. use the product identities, especially 11.3 and 12.37, to show the eta
   quotient satisfies the same recursion;
3. use uniqueness of solutions to that recursion with constant coefficient 1.

This avoids Dobbie's two-variable identity.  It still requires new formal
derivative/log-derivative infrastructure; the current proved theorems do not
mention `chan15LHSPS`, so there is no purely algebraic `rw` chain from the
listed statements to the Ch15 target as-is.

## Notation

Use the repo's fractional-power-free variables:

```text
E   := qPochInfPS
E5  := expand 5 E
E25 := expand 25 E

H := pentagonal014SeriesPS
G := pentagonal023SeriesPS
H5 := expand 5 H
G5 := expand 5 G

r := H/G
S := expand 5 r
v := X*S
```

Theorem 11.5 is:

```text
r^5 * B(v) = S * A(v)
```

where

```text
A(t) = 1 - 2t + 4t^2 - 3t^3 + t^4
B(t) = 1 + 3t + 4t^2 + 2t^3 + t^4
C(t) = 1 - t - t^2
```

The existing target is:

```text
chan15LHSPS * E5 = E^5
```

equivalently `chan15LHSPS = M`, where `M := E^5 / E5`.

## Step 1: 11.5 gives a recursion for the Lambert side

Let `Theta` be the Euler derivation on formal power series:

```text
Theta(sum a_n X^n) = sum n*a_n X^n
```

and write `Dlog(f) := Theta(f)/f` for unit series.  Define

```text
L := 1 + 5*Dlog(r).
```

From the product form of `r` in Theorem 11.1, `L` is exactly
`chan15LHSPS`: coefficientwise,

```text
L_N = 1 if N=0,
L_N = -5 * sum_{d|N} d * legendre5(d) if N>0.
```

This is the formal version of

```text
5q d/dq log R(q) = 1 + 5q d/dq log r(q).
```

Now differentiate 11.5:

```text
5*Dlog(r) + Dlog(B(v)) = Dlog(S) + Dlog(A(v)).
```

Since `S = expand5(r)` and `v = X*S`,

```text
Dlog(S) = expand5(L) - 1,
Dlog(v) = expand5(L).
```

Also, for a polynomial `P`,

```text
Dlog(P(v)) = Dlog(v) * v*P'(v)/P(v).
```

So 11.5 implies

```text
L = Phi(v) * expand5(L)
```

where

```text
Phi(t) := 1 + t*A'(t)/A(t) - t*B'(t)/B(t).
```

The key polynomial simplification is just `ring`:

```text
A*B + t*A'*B - t*A*B' = C^4
```

hence

```text
Phi(t) = C(t)^4 / (A(t)*B(t)).
```

This answers the original concern about derivatives of `R(q^5)`: they are not
expanded explicitly.  They become `expand5(L)`, giving a self-similar recursion.

## Step 2: the eta quotient satisfies the same recursion

Let

```text
M := E^5 / E5.
```

Then `expand5(M) = E5^5 / E25`, and the desired theorem is `L = M`.

The clean algebraic proof of the eta recursion uses these already-proved
product facts:

- AP product split: `H*G = E*E5`, hence `H5*G5 = E5*E25`.
- Theorem 11.3:

```text
G5^2 - X*G5*H5 - X^2*H5^2 = E*E5.
```

Since `v*G5 = X*H5`, this is

```text
C(v)*G5^2 = E*E5.
```

- Eq. 12.37, expanded by `q -> q^5`:

```text
E5^6 * H5^5 * G5^5
  = E25^6 * G5^10 * (1 - 11*v^5 - v^10).
```

Using `H5*G5 = E5*E25`, this rearranges to

```text
E5^12 = H5 * G5^11 * (1 - 11*v^5 - v^10).
```

Now compute:

```text
M / expand5(M)
  = E^5 * E25 / E5^6
  = C(v)^5 * G5^10 * E25 / E5^11
  = C(v)^5 * H5 * G5^11 / E5^12
  = C(v)^5 / (1 - 11*v^5 - v^10).
```

Another direct polynomial identity is:

```text
A(t)*B(t)*C(t) = 1 - 11*t^5 - t^10.
```

Therefore

```text
M / expand5(M) = C(v)^4 / (A(v)*B(v)) = Phi(v),
```

so

```text
M = Phi(v) * expand5(M).
```

Thus `L` and `M` satisfy the same recursion.

## Step 3: recursion uniqueness

If `T` satisfies

```text
T = Phi(v) * expand5(T)
```

and `T.coeff 0 = 1`, then `T` is unique.

Proof idea: if two solutions differ by `Delta`, then

```text
Delta = Phi(v) * expand5(Delta),   Delta_0 = 0.
```

Induct on coefficients.  For coefficient `n > 0`, every coefficient of
`expand5(Delta)` contributing to degree `n` is either `Delta_0` or
`Delta_k` with `k < n`.  These are zero by induction, so `Delta_n = 0`.

Since both `L` and `M` have constant coefficient 1, uniqueness gives

```text
L = M.
```

After substituting `L = chan15LHSPS`, this is exactly

```text
chan15LHSPS * E5 = E^5.
```

## What is still missing formally

The route is mathematically solid, but it is not already closed in Lean.  The
new work is:

1. Define/use an Euler derivation `Theta` on formal power series, not the
   current `qDeriv` from `Chapter15.lean` (that file is q-difference calculus).
2. Prove product, inverse, `expand5`, and polynomial-composition rules for
   `Dlog`.
3. Prove `chan15LHSPS = 1 + 5*Dlog(rrcf_r)` from the product form of `rrcf_r`
   / Theorem 11.1.  This is a divisor-sum coefficient theorem for the AP
   products with residues `1,4` versus `2,3` mod 5.
4. Differentiate `chan_theorem_11_5` to get
   `chan15LHSPS = Phi(v)*expand5(chan15LHSPS)`.
5. Formalize the eta-side recursion above using `chan_theorem_11_3_formal_ps`,
   `chan_eq_12_37_cleared`, and the AP product split.
6. Add the recursion uniqueness lemma.

If one insists on using exactly the list in the prompt and excludes Theorem
11.3, then 12.37 at `q` and `q^5` plus 11.5 gives the eta recursion only up to
sixth powers:

```text
(M / expand5(M))^6 = Phi(v)^6.
```

Then a sixth-root uniqueness lemma for units with constant coefficient 1 would
recover the same conclusion.  Since `chan_theorem_11_3_formal_ps` is already in
the repo, using it is the cleaner path.

## Bottom line

Theorem 11.5 does not by itself give Theorem 11.7, and the currently proved
algebraic identities do not directly produce `chan15LHSPS`.  But 11.5 is exactly
the right modular equation: after formal logarithmic differentiation it gives
the same `q -> q^5` recursion as the eta quotient.  With 11.3/12.37 proving the
eta recursion and a short uniqueness argument, the Ch15 formal target should be
derivable without formalizing Dobbie's identity.
