I’ll use your formal JTP as the base and separate the mechanically checkable product-bookkeeping strategy from the data-dependent part: the literal exponent certificate needs the exact H00/H10/H11 term list.

Since ThetaCorr is a sum, the sound product route is to clear denominators, factor a common product, then prove the remaining finite Laurent polynomial vanishes.

The clean route is not logarithmic differentiation and not raw exponent-vector matching. For this identity, the clean formal proof is:


$$\textbf{unfold HM corrections } \longrightarrow
\textbf{clear denominator theta factors } \longrightarrow
\textbf{normalize all }j\text{-arguments } \longrightarrow
\textbf{apply finite Riemann theta relations } \longrightarrow
\texttt{ring\_nf}.$$


The reason is structural: your LHS is a sum of cross-modulus products, not one product. Exponent-vector matching proves identities of the form “monomial times one AP-product equals monomial times one AP-product.” It does not prove cancellation among 31 different AP-products unless those terms pair with identical vectors or you add genuine theta addition identities.
The missing finite identity is almost certainly a finite Riemann theta relation identity, not a new Jacobi triple product or Lambert-series identity. Hickerson–Mortenson’s correction term is exactly a quotient of four $j$’s; their Theorem 2.3 gives the correction, and their Proposition 1.1 is the Riemann relation normally used to cancel such theta quotients. In exponent notation, these are finite formal identities over $\mathbb Q((Q))$, so no analysis is needed. The HM paper states the correction formula


$$m(x,q,z_1)-m(x,q,z_0)
=
\frac{z_0J_1^3j(z_1/z_0;q)j(xz_0z_1;q)}
{j(z_0;q)j(z_1;q)j(xz_0;q)j(xz_1;q)}$$


and the Riemann relation


$$j(ac,a/c,bd,b/d;q)
=
j(ad,a/d,bc,b/c;q)+\frac bc\,j(ab,a/b,cd,c/d;q).$$


arXiv+1

1. Recommended route
Let


$$J(a,m):=jLaurent(a,m)=j(Q^a;Q^m).$$


Your target is


$$E_6^2\ThetaCorr= -E_3^5J(12,15),$$


or equivalently


$$F:=E_6^2\ThetaCorr+E_3^5J(12,15)=0.$$


Use the already-proved identifications


$$E_3=J(3,9),\qquad E_6=J(6,18),$$




$$\Theta_1=J(1,2),\qquad \Theta_9=J(9,18),$$


and by symmetry


$$J(12,15)=J(3,15).$$


Then expand


$$\ThetaCorr=\Theta_9^2H_{00}-2\Theta_9\Theta_1H_{10}+\Theta_1^2H_{11}.$$


Each HM correction term should be normalized to the following formal object. For integers $X,Z_0,Z_1$,


$$\Delta_{90}(X;Z_1,Z_0)
:=
Q^{Z_0}E_{90}^3
\frac{
J(Z_1-Z_0,90)\,J(X+Z_0+Z_1,90)
}{
J(Z_0,90)\,J(Z_1,90)\,J(X+Z_0,90)\,J(X+Z_1,90)
}.$$


So every summand of each $H_{\alpha\beta}$ has the schematic form


$$c\,Q^\ell\,J(A,18)\,\Delta_{90}(X;Z_1,Z_0),
\qquad c\in\mathbb Z.$$


The formal proof should clear the denominator factors


$$J(Z_0,90),\quad J(Z_1,90),\quad J(X+Z_0,90),\quad J(X+Z_1,90)$$


appearing in all correction summands. These are units in $\mathbb Q((Q))$ after normalization, provided none of the arguments is $0\bmod 90$. That is exactly the “generic” non-pole condition in the HM correction formula.
After multiplying by the common denominator $D$, the goal becomes


$$D\cdot F=0.$$


Now normalize all $J$-arguments and reduce the cleared expression using the formal Riemann relation below. This is the core lemma to formalize.

2. The exact finite Riemann relation to use
For $M>0$ and integers $A,B,C,D$, define $J(T,M)=jLaurent(T,M)$. Then the formal Riemann relation is


$$\boxed{
J(A+C,M)J(A-C,M)J(B+D,M)J(B-D,M)
}$$




$$\boxed{
=
J(A+D,M)J(A-D,M)J(B+C,M)J(B-C,M)
+
Q^{B-C}J(A+B,M)J(A-B,M)J(C+D,M)J(C-D,M).
}
\tag{Riemann}$$


This is HM Proposition 1.1 with


$$a=Q^A,\quad b=Q^B,\quad c=Q^C,\quad d=Q^D,\quad q=Q^M.$$


In Lean, I would state it as a Laurent-series identity:
leantheorem jLaurent_riemann    (M : ℕ) (hM : 0 < M) (A B C D : ℤ) :  J (A+C) M * J (A-C) M * J (B+D) M * J (B-D) M    =  J (A+D) M * J (A-D) M * J (B+C) M * J (B-C) M    + monomialLaurent (B-C) *      J (A+B) M * J (A-B) M * J (C+D) M * J (C-D) M
with your actual names for Laurent monomials.
This is finite and formal. It can be proved directly from the coefficient definition of $j$, or accepted as a standalone formal theta-addition lemma. It does not require analytic convergence or the infinite product form.
This is the identity that should close the 31-term cancellation. Raw AP-product expansion destroys this structure.

3. Normalization of $J(a,m)$: exact $Q$-power and sign
For $m>0$, if $a\not\equiv0\pmod m$, let


$$\rho=\rho_m(a)\in\{1,\dots,m-1\}$$


be the positive residue of $a\bmod m$, and write


$$a=\rho+tm,\qquad t\in\mathbb Z.$$


Then


$$\boxed{
J(a,m)
=
(-1)^t Q^{-t\rho-\frac{m\,t(t-1)}2}J(\rho,m).
}
\tag{shift-normalize}$$


This is the iterated form of your shift


$$J(a+m,m)=-Q^{-a}J(a,m).$$


Also


$$\boxed{
J(a,m)=J(m-a,m)
}
\tag{sym}$$


for $0<a<m$.
If $a\equiv0\bmod m$, then


$$\boxed{
J(a,m)=0.
}$$


That case should not occur in denominator factors.
This normalization lemma is important because it makes every correction term a product of canonical $J(\rho,m)$’s times one explicit Laurent monomial and one explicit sign.

4. Why route (a), logarithmic differentiation, is not the clean proof
For a single AP-product,


$$P=\prod_{n\ge1}(1-Q^n)^{e(n)},$$


one has


$$\theta\log P
=
-Q\frac{d}{dQ}\log P
=
-\sum_{n\ge1}e(n)\frac{nQ^n}{1-Q^n}.$$


Equivalently, the coefficient of $Q^N$ is


$$-\sum_{d\mid N} d\,e(d).$$


So logarithmic differentiation is excellent for proving


$$\text{one product}=\text{one product}.$$


But your LHS is


$$E_6^2\left(\Theta_9^2H_{00}-2\Theta_9\Theta_1H_{10}+\Theta_1^2H_{11}\right),$$


a sum of product terms. There is no useful identity


$$\theta\log(P_1+P_2+\cdots)
=
\text{sum of Lambert series}.$$


Taking $\theta$ of the whole identity gives another 31-term identity of differentiated products. It does not linearize the problem. It is strictly worse than the original unless the whole LHS has already been factored as one product, which is exactly what you are trying to prove.
So I would not use route (a).

5. Route (b): exact exponent bookkeeping, and why it does not close the sum
For a single normalized $J(a,m)$, with $0<a<m$, and for common modulus $M=270$, define the exponent vector


$$v_{J(a,m)}(r)$$


for $1\le r\le270$, where $r=270$ represents the residue class $0\bmod270$. Since $m\mid270$ in your problem,


$$\boxed{
v_{J(a,m)}(r)
=
\mathbf 1_{r\equiv0\pmod m}
+
\mathbf 1_{r\equiv a\pmod m}
+
\mathbf 1_{r\equiv -a\pmod m}.
}
\tag{J-vector}$$


For Euler products,


$$\boxed{
v_{E_m}(r)=\mathbf 1_{m\mid r}.
}
\tag{E-vector}$$


For the RHS


$$-E_3^5J(12,15)=-E_3^5J(3,15),$$


the exponent vector is


$$v_R(r)
=
5\mathbf 1_{3\mid r}
+
\mathbf 1_{15\mid r}
+
\mathbf 1_{r\equiv3\pmod{15}}
+
\mathbf 1_{r\equiv12\pmod{15}}.$$


Equivalently,


$$\boxed{
v_R(r)=
\begin{cases}
6,& r\bmod15\in\{0,3,12\},\\
5,& r\bmod15\in\{6,9\},\\
0,& \text{otherwise}.
\end{cases}
}
\tag{RHS-vector}$$


The scalar sign is $-1$, and the Laurent monomial shift is $Q^0$.
For the three LHS prefactors, before the $H$-terms, the vectors are:


$$\boxed{
p_{00}(r)
=
2\mathbf 1_{6\mid r}
+
2\mathbf 1_{18\mid r}
+
4\mathbf 1_{r\equiv9\pmod{18}}.
}$$


This is the vector of $E_6^2\Theta_9^2$.


$$\boxed{
p_{10}(r)
=
2\mathbf 1_{6\mid r}
+
\mathbf 1_{18\mid r}
+
2\mathbf 1_{r\equiv9\pmod{18}}
+
\mathbf 1_{2\mid r}
+
2\mathbf 1_{r\equiv1\pmod2}.
}$$


This is the vector of $E_6^2\Theta_9\Theta_1$.


$$\boxed{
p_{11}(r)
=
2\mathbf 1_{6\mid r}
+
2\mathbf 1_{2\mid r}
+
4\mathbf 1_{r\equiv1\pmod2}.
}$$


This is the vector of $E_6^2\Theta_1^2$.
For a correction summand


$$cQ^\ell J(A,18)\Delta_{90}(X;Z_1,Z_0)$$


inside $H_{\alpha\beta}$, the unnormalized vector contribution is


$$v_{\alpha\beta}(r)
+
v_{J(A,18)}(r)
+
3\mathbf 1_{90\mid r}
+
v_{J(Z_1-Z_0,90)}(r)
+
v_{J(X+Z_0+Z_1,90)}(r)$$




$$-
v_{J(Z_0,90)}(r)
-
v_{J(Z_1,90)}(r)
-
v_{J(X+Z_0,90)}(r)
-
v_{J(X+Z_1,90)}(r),$$


where $v_{\alpha\beta}$ is $p_{00},p_{10},p_{11}$ according to the term.
The Laurent power before normalization is


$$\ell+Z_0.$$


After normalizing every $J(T,M)$, add the explicit normalization shift


$$\nu(T,M)
=
-t\rho-\frac{M\,t(t-1)}2,
\qquad
T=\rho+tM,\quad 1\le\rho<M,$$


with sign factor $(-1)^t$. Numerator $J$-factors contribute $+\nu$, denominator factors contribute $-\nu$.
So the exact normalized lead exponent of the summand is


$$\boxed{
L
=
\ell+Z_0
+
\nu(A,18)
+
\nu(Z_1-Z_0,90)
+
\nu(X+Z_0+Z_1,90)
}$$




$$\boxed{
-
\nu(Z_0,90)
-
\nu(Z_1,90)
-
\nu(X+Z_0,90)
-
\nu(X+Z_1,90).
}
\tag{lead}$$


The exact normalized scalar is


$$\boxed{
c\cdot
(-1)^{
t(A,18)
+t(Z_1-Z_0,90)
+t(X+Z_0+Z_1,90)
-t(Z_0,90)
-t(Z_1,90)
-t(X+Z_0,90)
-t(X+Z_1,90)
}.
}
\tag{sign}$$


That is the complete exponent bookkeeping formula.
But there is no single “net exponent vector of the LHS” because the LHS is a sum. Route (b) closes only if the cleared expression groups into products with identical $(L,v)$-keys and cancelling integer coefficients. From your description, it does not. Therefore route (b) is useful for normalization and oracle checking, but it is not the final formal proof.

6. Sturm-type finite check
A Sturm check can work, but only after proving modularity and holomorphy at every cusp. It is not a pure $\mathbb Q((Q))$ finite-prefix theorem.
The weight is


$$\boxed{3.}$$


Reason:


$$E_m \text{ has weight }1/2,\qquad J(a,m)\text{ has weight }1/2.$$


The HM correction quotient


$$E_{90}^3
\frac{J(\cdot,90)J(\cdot,90)}
{J(\cdot,90)J(\cdot,90)J(\cdot,90)J(\cdot,90)}$$


has weight


$$3/2+1-2=1/2.$$


Multiplying by the extra $J(A,18)$ in each $H_{\alpha\beta}$ gives


$$H_{\alpha\beta}\text{ has weight }1.$$


Then


$$\Theta^2H_{\alpha\beta}\text{ has weight }1+1=2,$$


and


$$E_6^2\ThetaCorr\text{ has weight }1+2=3.$$


The RHS


$$E_3^5J(12,15)$$


has weight


$$5/2+1/2=3.$$


For the level, the safe statements are:


If you prove the difference is a holomorphic modular form of weight $3$ on $\Gamma_0(90)$ with character, the Sturm bound is




$$\left\lfloor \frac{3}{12}[SL_2(\mathbb Z):\Gamma_0(90)]\right\rfloor
=
\left\lfloor \frac{3}{12}\cdot216\right\rfloor
=
54.$$


The index formula is


$$[SL_2(\mathbb Z):\Gamma_0(N)]
=
N\prod_{p\mid N}\left(1+\frac1p\right),$$


so for $N=90$,


$$90\cdot\frac32\cdot\frac43\cdot\frac65=216.$$


Sturm’s bound with character uses the same $\Gamma_0(N)$ index bound. William Stein's Homepage


If the only level you can safely prove is $\Gamma_0(270)$, the bound is




$$[SL_2(\mathbb Z):\Gamma_0(270)]
=
270\cdot\frac32\cdot\frac43\cdot\frac65
=
648,$$


so the Sturm bound is


$$\left\lfloor \frac{3}{12}\cdot648\right\rfloor
=
162.$$




If you only prove modularity on $\Gamma_1(270)$, the index is




$$[SL_2(\mathbb Z):\Gamma_1(270)]
=
270^2
\left(1-\frac14\right)
\left(1-\frac19\right)
\left(1-\frac1{25}\right)
=
46656,$$


so the bound is


$$\left\lfloor \frac{3}{12}\cdot46656\right\rfloor
=
11664.$$


Thus your $Q^{44}$ verification is not enough for the safe $\Gamma_0(90)$ bound, and far from enough for $\Gamma_0(270)$ or $\Gamma_1(270)$. It would only be a Sturm proof if you have an independent modular-form argument putting the difference in a weight-$3$ space with index at most $176$.
So Sturm is mathematically legitimate, but it is not the clean Lean route unless your modular-forms infrastructure already has generalized eta/theta modularity and cusp holomorphy.

7. Ordered Lean lemma list
Here is the proof path I would formalize.
A. Basic $J$-normalization
leandef J (a : ℤ) (m : ℕ) : LaurentSeries ℚ := jLaurent a m
Lemmas:
leanJ_shift_int :  J (a + t * m) m    =  (-1 : ℚ)^t • Q^(-t*a - m*t*(t-1)/2) * J a m
or, more conveniently:
leanJ_normalize :  let ρ := posResidue a m  let t := (a - ρ) / m  J a m =    (-1 : ℚ)^t • Q^(-t*ρ - m*t*(t-1)/2) * J ρ m
with hypotheses
lean0 < ma % m ≠ 01 ≤ ρ ∧ ρ < ma = ρ + t*m
Also:
leanJ_symm :  0 < a → a < m → J a m = J (m-a) mJ_zero_of_dvd :  m ∣ a → J a m = 0J_unit_of_norm :  0 < a → a < m → IsUnit (J a m)
The last follows from constant coefficient $1$.

B. Named products
leanE_eq_J :  E m = J m (3*m)E3_eq :  E3 = J 3 9E6_eq :  E6 = J 6 18Theta1_eq :  Theta1 = J 1 2Theta9_eq :  Theta9 = J 9 18J12_15_eq_J3_15 :  J 12 15 = J 3 15

C. HM correction as a formal quotient
Define:
leandef Delta90 (X Z1 Z0 : ℤ) : LaurentSeries ℚ :=  Q^Z0 * E 90^3 *    J (Z1 - Z0) 90 *    J (X + Z0 + Z1) 90 /    (J Z0 90 * J Z1 90 * J (X+Z0) 90 * J (X+Z1) 90)
Better in Lean: do not use / until units are available. Define it using inverses of units after normalization.
Lemma:
leanDelta90_unfold :  Delta90 X Z1 Z0 =    Q^Z0 * E 90^3 *    J (Z1 - Z0) 90 *    J (X + Z0 + Z1) 90 *    (J Z0 90)⁻¹ *    (J Z1 90)⁻¹ *    (J (X+Z0) 90)⁻¹ *    (J (X+Z1) 90)⁻¹
This is exactly the formal version of the HM correction term.

D. Riemann theta relation
Formalize the finite relation:
leantheorem J_riemann    (M : ℕ) (hM : 0 < M) (A B C D : ℤ) :  J (A+C) M * J (A-C) M * J (B+D) M * J (B-D) M    =  J (A+D) M * J (A-D) M * J (B+C) M * J (B-C) M    + Q^(B-C) *      J (A+B) M * J (A-B) M * J (C+D) M * J (C-D) M
This is the key non-product identity. Once this exists, most of the collapse should be algebraic.

E. Clear denominators
Let DenArgs be the finite multiset of all denominator arguments appearing in all expanded correction terms:


$$Z_0,\ Z_1,\ X+Z_0,\ X+Z_1$$


for every correction summand.
Define
leandef Den : LaurentSeries ℚ :=  ∏ T in DenArgs, J T 90
or, better, after normalization:
leandef DenNorm : LaurentSeries ℚ :=  ∏ T in DenArgs, J (posResidue T 90) 90
with the Laurent monomial and sign normalization pulled out separately.
Prove:
leanDen_isUnit : IsUnit Den
and
leantarget_iff_cleared :  E6^2 * ThetaCorr = - E3^5 * J 12 15    ↔  Den * (E6^2 * ThetaCorr + E3^5 * J 12 15) = 0

F. Expand and normalize the cleared expression
Prove a lemma that unfolds the definitions and normalizes all $J$-arguments:
leanthetaCorr_cleared_expand :  Den * (E6^2 * ThetaCorr + E3^5 * J 12 15)    =  clearedExpr
where clearedExpr is a finite sum of monomials times products of canonical $J(\rho,m)$’s.
This lemma is mostly simp [ThetaCorr_def, H00_def, H10_def, H11_def, Delta90_unfold, E3_eq, E6_eq, Theta1_eq, Theta9_eq, J12_15_eq_J3_15], followed by J_normalize.

G. Riemann-reduce the finite expression
The certificate lemma should look like:
leanthetaCorr_cleared_riemann_reduce :  clearedExpr = 0
Its proof should be a finite sequence of rewrites by J_riemann, followed by ring_nf.
Schematically:
lean  rw [J_riemann 90 A₁ B₁ C₁ D₁]  rw [J_riemann 90 A₂ B₂ C₂ D₂]  ...  ring_nf
The exact list of $(A_i,B_i,C_i,D_i)$ depends on the actual $H_{00},H_{10},H_{11}$ term table. From the schematic information in the question, that term table is the only missing data needed to write the final certificate.

H. Final theorem
leantheorem theta_correction_cleared_product_identity :  E6^2 * ThetaCorr = - E3^5 * J 12 15 := by  rw [target_iff_cleared]  rw [thetaCorr_cleared_expand]  exact thetaCorr_cleared_riemann_reduce

Bottom line
Use route (c), but with the Riemann theta relation, not only shifts and symmetry. Shifts/symmetry normalize the expression; Riemann is what actually cancels the cross-modulus correction terms.
Route (b) gives useful bookkeeping. The exact RHS vector is


$$v_R(r)=
\begin{cases}
6,& r\bmod15\in\{0,3,12\},\\
5,& r\bmod15\in\{6,9\},\\
0,& \text{otherwise},
\end{cases}$$


and the LHS summand vectors are given by the formulas above. But there is no single LHS exponent vector because the LHS is a sum.
A Sturm check is possible only after proving modularity and cusp holomorphy. The weight is $3$. The safe $\Gamma_0(90)$ bound would be $54$, $\Gamma_0(270)$ gives $162$, and $\Gamma_1(270)$ gives $11664$. Your $Q^{44}$ oracle is therefore not, by itself, a Sturm proof for the natural safe levels.