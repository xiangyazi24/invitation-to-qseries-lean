# Ch15 algebra check: can `E^5/E5` be obtained rationally?

Verdict: no, not as a finite rational function of the listed quantities from
Theorem 11.3 plus Eq. 12.37.  The available algebra gives a square formula for
`E^5/E5`, and more usefully a `q -> q^5` recursion for it.  It does not give
`E^5/E5` itself as a finite rational expression in
`r, r5, G, H, G5, H5`.

Notation:

```text
E   := qPochInfPS
F   := E5  := expand5(E)
W   := E25 := expand25(E)

H   := pentagonal014SeriesPS
G   := pentagonal023SeriesPS
H5  := expand5(H)
G5  := expand5(G)

s   := r5 := H5/G5
v   := X*s
C   := 1 - v - v^2
D   := 1 - 11*v^5 - v^10
M   := E^5/F
```

Theorem 11.3 gives, in fraction notation,

```text
E*F = C*G5^2.
```

Raising to the fifth power gives

```text
M = E^5/F = C^5*G5^10/F^6.        (1)
```

Eq. 12.37 after applying `expand5` gives

```text
F^6 * H5^5 * G5^5 = W^6 * G5^10 * D.
```

Using the AP product split

```text
H5*G5 = F*W,
```

this becomes

```text
F^12 = H5 * G5^11 * D.             (2)
```

Combining (1) and (2) gives only the square:

```text
M^2
  = C^10*G5^20/F^12
  = G5^9*C^10/(H5*D)
  = (G5^8/s) * C^10/D.
```

So the direct algebra determines `M` only up to the formal square-root choice.
Since `M` has constant coefficient `1`, there is a unique square root in
`Q[[X]]`, but that is an algebraic/infinite recursive construction, not a
finite rational function in the displayed variables.

The stronger useful consequence is the recursion for `M`.  Since

```text
expand5(M) = F^5/W = F^6/(H5*G5),
```

(1) and (2) give

```text
M/expand5(M)
  = C^5*H5*G5^11/F^12
  = C^5/D.
```

With Watson's polynomial identity

```text
D = 1 - 11*v^5 - v^10 = C*A(v)*B(v),

A(t) = 1 - 2*t + 4*t^2 - 3*t^3 + t^4,
B(t) = 1 + 3*t + 4*t^2 + 2*t^3 + t^4,
```

this is

```text
M/expand5(M) = C^4/(A(v)*B(v)).
```

Equivalently,

```text
M = Phi(v) * expand5(M),
Phi(v) := C(v)^4/(A(v)*B(v)).
```

This recursion plus `M.coeff 0 = 1` determines `M` uniquely, or formally

```text
M = product_{k >= 0} expand5^k(Phi(v)).
```

But again this is not a finite rational expression in
`r, r5, G, H, G5, H5`.

For comparison, original Eq. 12.37 gives the analogous square formula.  If

```text
y := X*r^5,
Q := 1 - 11*y - y^2,
```

then Eq. 12.37 and `H*G = E*F` imply

```text
E^12 = H*G^11*Q,
M^2  = G^9*Q/H.
```

This is compatible with the expanded formula after using Theorem 11.5 and the
Watson branch identities, but it still only gives `M^2`.

## Consequence for `chan_theorem_11_7`

The target in `QseriesFormalization/Pending/Chapter15_R_ODE.lean` is

```lean
chan15LHSPS R * expand5(qPochInfPS R) = (qPochInfPS R)^5
```

i.e. `chan15LHSPS = M`.

The algebra above never identifies `chan15LHSPS` with `M`; it only proves a
recursion for the eta quotient `M`.  To finish Chan Theorem 11.7 without
Dobbie's identity, the missing step is still:

1. take the formal logarithmic derivative of Theorem 11.5;
2. prove `chan15LHSPS = 1 + 5*Dlog(rrcf_r)` from the product definition of
   `rrcf_r`;
3. derive the same recursion
   `chan15LHSPS = Phi(v)*expand5(chan15LHSPS)`;
4. use uniqueness for series with constant coefficient `1`.

That is not just a rational rewrite from 11.3 and 12.37; it requires new
formal derivative/log-derivative and divisor-sum coefficient infrastructure.

## Lean status

I did not modify `QseriesFormalization/Pending/Chapter15_R_ODE.lean`, because
the requested pure algebra does not close the existing `sorry`.

Checked:

```bash
lake env lean QseriesFormalization/Pending/Chapter15_R_ODE.lean
```

Result: success, with the existing warning:

```text
QseriesFormalization/Pending/Chapter15_R_ODE.lean:156:8: warning: declaration uses 'sorry'
```
