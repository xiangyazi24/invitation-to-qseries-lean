# Chan Chapter 10 analysis: mock theta functions

Source checked:
- Local PDF: `Hai-Chi Chen_An invitation to q-series.pdf`.
- PDF bookmarks put Chapter 10 at page object 294, printed pp. 85--94.
- Sections are 10.1--10.4:
  - 10.1 Step 1: Rewriting the identity
  - 10.2 Step 2: Two identities involving theta functions
  - 10.3 Step 3: Finishing up the proof of Eq. (10.15)
  - 10.4 Exercises
- Cross-check source for context: Sander Zwegers, arXiv:0905.1133, "The tenth order mock theta functions revisited", https://arxiv.org/abs/0905.1133. Chan explicitly says the presentation follows Zwegers (2010).

## Short answer

Chapter 10 is not just "definition + basic properties". It has a concrete main target: prove one of Ramanujan/Choi's identities involving tenth-order mock theta functions.

It is also not Watson 1936 and not a mock modular completion theorem. Chan mentions the modern Zwegers/Bringmann-Ono story historically, but the actual proof in the chapter is an elementary q-series / theta-function proof, following Zwegers' constant-term method.

The formal label `Theorem 10.1` is slightly misleading as "chapter-main": it says Eq. (10.10) is equivalent to an indefinite-theta identity, Eq. (10.14)/(10.15). The chapter's announced main result is Eq. (10.10); Theorem 10.1 is the bridge used to prove it.

## The mock theta functions involved

Chan defines two tenth-order mock theta functions:

```tex
\phi(q) := \sum_{n=0}^{\infty}
  \frac{q^{n(n+1)/2}}{(q;q^2)_{n+1}},

\psi(q) := \sum_{n=0}^{\infty}
  \frac{q^{(n+1)(n+2)/2}}{(q;q^2)_{n+1}}.
```

He sets

```tex
\omega := e^{2\pi i/3}.
```

## The chapter-main identity

The displayed identity Chan says he will prove is Eq. (10.10):

```tex
q^{2/3}\phi(q^3)
- \frac{\psi(\omega q^{1/3})-\psi(\omega^2 q^{1/3})}
       {\omega-\omega^2}
=
-q^{1/3}
  \frac{\sum_{n\in\mathbb Z}(-1)^n q^{n^2/3}}
       {\sum_{n\in\mathbb Z}(-1)^n q^{n^2}}
  \frac{\sum_{n\in\mathbb Z}(-1)^n q^{n(5n+3)/2}}
       {(q;q^2)_\infty}.
```

Chan also displays Eq. (10.11), a companion identity, but says the proof is similar and leaves it as Exercise 10.4(1). So Eq. (10.10), not Eq. (10.11), is the proved chapter target.

## What Theorem 10.1 actually says

Definition 10.1 introduces

```tex
\rho_{r,s} =
\begin{cases}
  1,  & r,s \ge 0,\\
 -1,  & r,s < 0,\\
  0,  & \text{otherwise},
\end{cases}

\delta(r) :=
\frac{1+\omega^r+\omega^{2r}}{3}
=
\begin{cases}
1, & r \equiv 0 \pmod 3,\\
0, & \text{otherwise}.
\end{cases}
```

All unqualified summation indices in the rest of the chapter run over all integers.

Theorem 10.1 says Eq. (10.10) is equivalent to:

```tex
\sum_{k,l,r,s}
\rho_{r,s}(-1)^{k+l+r+s}
(\delta(k)-\delta(r))(\delta(l)-\delta(s))
q^{(k^2+l^2+r^2+3rs+s^2+3r+3s+1)/3}

=
-(q;q)_\infty
\left(\sum_m (-1)^m q^{m^2}\right)^2
\sum_n (-1)^n q^{n(5n+3)/2}

=
-\frac{(q;q)_\infty^5}{(q^2;q^2)_\infty^2}
\sum_n (-1)^n q^{n(5n+3)/2}.
```

The first equality is Eq. (10.14); the final product-form equality is Eq. (10.15), using Jacobi's triple product.

## Proof structure

The chapter proves Eq. (10.10) by:

1. Rewriting Eq. (10.10) into the indefinite-theta identity above.
2. Using two Choi Hecke-type identities for `\phi` and `\psi`, stated as Eqs. (10.16) and (10.17).
3. Using a theta identity Eq. (10.18), whose proof is pushed to Exercise 10.4(2).
4. Proving Lemma 10.1 for a theta function `j(x;q)` by a functional-equation / zero-set / constant-term argument.
5. Using Hickerson's identity, Lemma 10.2, sourced from Hickerson (1988) and ultimately Ramanujan's `1\psi_1` summation.
6. Applying constant-term extraction in two variables to prove Eq. (10.15), hence Eq. (10.10).

So the chapter is a real proof of a specific identity, but it is not self-contained in the sense of proving every imported q-series identity from scratch.

## Formalization assessment

There is a specific theorem to formalize: Eq. (10.10), or more practically its equivalent Eq. (10.15). This is much more substantial than the current `Chapter10.lean` scaffolding, which only handles finite truncations of Ramanujan's third-order mock theta `f(q)`.

Recommended formalization target:
- Best target: Eq. (10.15) as a formal power series identity, with the four-variable indefinite theta sum on the left and the eta-product/theta-series expression on the right.
- Alternative target: Eq. (10.10) after substituting `Q = q^{1/3}` to remove fractional exponents, working over a coefficient ring containing a primitive cube root of unity.

Main blockers:
- bilateral infinite sums over integers;
- q-Pochhammer infinite products and their invertibility;
- formal support/finite-coefficient arguments for theta sums;
- root-of-unity filtering via `\delta`;
- the Choi Hecke-type identities Eqs. (10.16)/(10.17);
- Lemma 10.2 / Ramanujan `1\psi_1` infrastructure if proving the chapter proof faithfully.

Conclusion: Chapter 10 is partly expository, but it does prove a concrete theorem-level identity. The right "chapter-main" is the Ramanujan/Choi/Zwegers tenth-order mock theta identity Eq. (10.10), with Theorem 10.1/Eq. (10.15) as the formalizable bridge. It is not a mock modular completion theorem and not Watson 1936.
