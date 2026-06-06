I’ll first verify the coefficient-level form of Dobbie’s identity, then extract the exact 5-dissection/reindexing or isolate the minimal missing lemma for a Lean FPS proof.

A cleaner route is emerging: reduce Dobbie to the level-5 Lambert identity already present in Chapter 15, plus product logarithmic differentiation. One normalization caveat: the bilateral weighted Jacobi sum is $2P^3$, not $P^3$.

I’ll focus next on making the Lambert identity self-contained: proving it by JTP/quintuple-product and FPS algebra, not importing modularity or analytic convergence.

There is a crucial normalization issue first:


$$\sum_{a\in\mathbb Z}(-1)^a(2a+1)q^{a(a+1)/2}=2(q;q)_\infty^3,$$


not $(q;q)_\infty^3$. The two terms $a$ and $-a-1$ are equal. The standard Jacobi identity is the one-sided version


$$(q;q)_\infty^3=\sum_{a\ge 0}(-1)^a(2a+1)q^{a(a+1)/2}.$$


So if you use the bilateral shell over all $a,b\in\mathbb Z$, the correct identity is


$$(q;q)_\infty^6
=
\frac14
\sum_{a,b\in\mathbb Z}
(-1)^{a+b}(2a+1)(2b+1)
q^{a(a+1)/2+b(b+1)/2}.$$


That factor $1/4$ is exactly what makes the 5-string proof work.
The product descriptions of $A=f(-q,-q^4)$, $B=f(-q^2,-q^3)$, and their appearance in the Rogers–Ramanujan continued fraction are standard consequences of Jacobi triple product; the Rogers–Ramanujan page records the same $f(a,b)$-notation and the formula $R(q)=q^{1/5}f(-q,-q^4)/f(-q^2,-q^3)$. Wikipedia The Euler function page also records $P=(q;q)_\infty$ and Euler’s pentagonal theorem notation. Wikipedia
Below is the full formal-power-series proof.

Dobbie identity
Let


$$p(r)=\frac{r(5r-3)}2,\qquad
b(s)=\frac{s(5s-1)}2.$$


Then


$$A=\sum_{r\in\mathbb Z}(-1)^r q^{p(r)},\qquad
B=\sum_{s\in\mathbb Z}(-1)^s q^{b(s)}.$$


The formal Euler operator satisfies


$$\theta(q^n)=nq^n,$$


so, coefficientwise,


$$\theta A=\sum_{r\in\mathbb Z}(-1)^r p(r)q^{p(r)},
\qquad
\theta B=\sum_{s\in\mathbb Z}(-1)^s b(s)q^{b(s)}.$$


Hence


$$B\theta A-A\theta B
=
\sum_{r,s\in\mathbb Z}
(-1)^{r+s}\bigl(p(r)-b(s)\bigr)q^{p(r)+b(s)}.$$


Therefore the Dobbie left side is


$$D(q):=AB+5(B\theta A-A\theta B)$$


with coefficient formula


$$[q^N]D(q)
=
\sum_{\substack{r,s\in\mathbb Z\\p(r)+b(s)=N}}
(-1)^{r+s}
\left(1+5(p(r)-b(s))\right).
\tag{1}$$


We prove this equals $[q^N]P^6$ for every $N$.

1. Convert the pentagonal pair shell to a two-square shell
Define


$$c=3r+s-1,\qquad d=-r+3s.
\tag{2}$$


Then direct expansion gives


$$c^2+d^2
=
(3r+s-1)^2+(-r+3s)^2
=
4(p(r)+b(s))+1.
\tag{3}$$


So on the coefficient shell $p(r)+b(s)=N$,


$$c^2+d^2=4N+1.$$


The inverse transformation is


$$r=\frac{3c-d+3}{10},\qquad
s=\frac{c+3d+1}{10}.
\tag{4}$$


The image condition is


$$d\equiv 3c-2\pmod 5.
\tag{5}$$


Indeed,


$$d-3c+2
=
(-r+3s)-3(3r+s-1)+2
=
-10r+5,$$


so $5\mid d-3c+2$.
Conversely, suppose


$$c^2+d^2=4N+1,\qquad d\equiv 3c-2\pmod5.$$


Since $4N+1$ is odd, $c,d$ have opposite parity. Write


$$d=3c-2+5t.$$


Because $d$ and $3c-2$ have opposite parity, $t$ is odd. Then


$$3c-d+3=5(1-t)$$


is divisible by $10$, and similarly


$$c+3d+1
=
c+3(3c-2+5t)+1
=
10c-5+15t
=
5(2c-1+3t)$$


is divisible by $10$, because $2c-1+3t$ is even when $t$ is odd. Thus (4) gives integers $r,s$.
So (2) is a bijection between the pentagonal shell


$$\{(r,s):p(r)+b(s)=N\}$$


and the selected two-square shell


$$\left\{(c,d):
c^2+d^2=4N+1,\ d\equiv 3c-2\pmod5
\right\}.$$


Now compute the sign. From (4),


$$r+s
=
\frac{3c-d+3+c+3d+1}{10}
=
\frac{2c+d+2}{5}.$$


Using $d=3c-2+5t$, this becomes


$$r+s=c+t.$$


Since $t$ is odd,


$$(-1)^{r+s}=(-1)^{c+t}=(-1)^{c-1}.
\tag{6}$$


Now compute the weight. Direct expansion gives


$$1+5(p(r)-b(s))
=
c^2-d^2-\frac32cd.
\tag{7}$$


The term $\frac32cd$ is integral because $c,d$ have opposite parity.
Thus (1) becomes


$$[q^N]D(q)
=
\sum_{\substack{c,d\in\mathbb Z\\c^2+d^2=4N+1\\d\equiv 3c-2\!\!\!\pmod5}}
(-1)^{c-1}
\left(c^2-d^2-\frac32cd\right).
\tag{8}$$


This is the exact pentagonal-side coefficient formula.

2. Convert Jacobi’s square to the same shell
Use the standard one-sided Jacobi identity


$$P^3
=
(q;q)_\infty^3
=
\sum_{a\ge0}(-1)^a(2a+1)q^{a(a+1)/2}.$$


Equivalently, if


$$J(q)=\sum_{a\in\mathbb Z}(-1)^a(2a+1)q^{a(a+1)/2},$$


then


$$J(q)=2P^3$$


because the terms $a$ and $-a-1$ are equal. Therefore


$$P^6=\frac14J(q)^2.$$


So


$$[q^N]P^6
=
\frac14
\sum_{\substack{a,b\in\mathbb Z\\
a(a+1)/2+b(b+1)/2=N}}
(-1)^{a+b}(2a+1)(2b+1).
\tag{9}$$


Now define


$$c=a+b+1,\qquad d=b-a.
\tag{10}$$


Then


$$2a+1=c-d,\qquad 2b+1=c+d.$$


Also


$$\frac{a(a+1)}2+\frac{b(b+1)}2
=
\frac{c^2+d^2-1}{4}.$$


Thus the shell condition is again


$$c^2+d^2=4N+1.$$


The sign satisfies


$$(-1)^{a+b}=(-1)^{c-1},$$


and the weight satisfies


$$(2a+1)(2b+1)=(c-d)(c+d)=c^2-d^2.$$


Therefore


$$[q^N]P^6
=
\frac14
\sum_{\substack{c,d\in\mathbb Z\\c^2+d^2=4N+1}}
(-1)^{c-1}(c^2-d^2).
\tag{11}$$


So Dobbie’s identity is reduced to the following purely finite shell identity.

3. The finite shell identity
For every odd positive integer $M$,


$$\boxed{
\sum_{\substack{c,d\in\mathbb Z\\c^2+d^2=M\\d\equiv 3c-2\!\!\!\pmod5}}
(-1)^{c-1}
\left(c^2-d^2-\frac32cd\right)
=
\frac14
\sum_{\substack{c,d\in\mathbb Z\\c^2+d^2=M}}
(-1)^{c-1}(c^2-d^2).
}
\tag{12}$$


Here $M=4N+1$. Since $M$ is odd, $c,d$ automatically have opposite parity.
This is the exact “5-string” combinatorial core.
There is not a genuine global $\mathbb Z/5$-action by isometries on the integer norm shell. The correct object is a finite string under transfer of Gaussian prime factors over $5$.
Let


$$\pi=2+i,\qquad \bar\pi=2-i,\qquad 5=\pi\bar\pi.$$


The norm-preserving string moves are multiplication by


$$\frac{\pi}{\bar\pi}=\frac{3+4i}{5}$$


or its inverse. In coordinates $z=c+di$, these are


$$T_+(c,d)
=
\left(\frac{3c-4d}{5},\frac{4c+3d}{5}\right),
\tag{13}$$


defined when the two numerators are divisible by $5$, equivalently


$$d\equiv 2c\pmod5,$$


and


$$T_-(c,d)
=
\left(\frac{3c+4d}{5},\frac{-4c+3d}{5}\right),
\tag{14}$$


defined when


$$d\equiv -2c\pmod5.$$


Both preserve $c^2+d^2$.
In the original $(a,b)$-coordinates, using $c=a+b+1$, $d=b-a$, these become


$$T_+(a,b)
=
\left(
\frac{3a-4b-3}{5},
\frac{4a+3b+1}{5}
\right),
\tag{15}$$


defined when


$$3a+b+2\equiv0\pmod5,$$


and


$$T_-(a,b)
=
\left(
\frac{3a+4b+1}{5},
\frac{-4a+3b-3}{5}
\right),
\tag{16}$$


defined when


$$a+3b+2\equiv0\pmod5.$$


The pentagonal selected class is


$$d\equiv3c-2\pmod5,$$


equivalently


$$2a+b+3\equiv0\pmod5,
\tag{17}$$


with inverse


$$r=\frac{2a+b+3}{5},\qquad
s=\frac{-a+2b+1}{5}.
\tag{18}$$



4. The 5-string proof of the shell identity
Fix $M$. Write


$$M=5^hM_0,\qquad 5\nmid M_0.$$


In $\mathbb Z[i]$, every representation $z=c+di$ of norm $M$ is obtained by choosing a primitive representation $w$ of norm $M_0$, then distributing the $h$ Gaussian prime factors over $\pi$ and $\bar\pi$.
Thus the relevant string is


$$z_t=\pi^t\bar\pi^{h-t}w,\qquad t=0,1,\dots,h.
\tag{19}$$


Together with unit multiples $\pm z_t,\pm iz_t$ and conjugates, these strings partition the two-square shell. If $w$ is associated to $\bar w$, the multiset double-counts uniformly; both sides of (12) are doubled, so the identity descends to the actual set.
Write


$$z_t=c_t+id_t.$$


Define


$$A_t=c_t^2-d_t^2,\qquad B_t=c_td_t.$$


Then


$$z_t^2=A_t+2iB_t.$$


Also multiplication by either $\pi$ or $\bar\pi$ flips the parity of the real part, because


$$\pi(c+di)=(2c-d)+i(c+2d),$$


and $2c-d$ has the parity of $d$, opposite to the parity of $c$. Therefore


$$(-1)^{c_t-1}
=
(-1)^h(-1)^{\Re(w)-1}$$


is independent of $t$. Denote this common sign by $\varepsilon$.

4.1. Interior terms
If $0<t<h$, then $z_t$ is divisible by both $\pi$ and $\bar\pi$, hence by $5$. Therefore


$$c_t\equiv d_t\equiv0\pmod5.$$


No unit multiple or conjugate of $z_t$ can satisfy


$$d\equiv3c-2\pmod5,$$


because the left side would be $0$ and the right side would be $-2$.
So the selected pentagonal side receives contributions only from the endpoints $t=0$ and $t=h$.

4.2. Endpoint selection table
Suppose $z=c+di$ satisfies


$$d\equiv2c\pmod5,\qquad 5\nmid c.$$


Among the four unit multiples $z,-z,iz,-iz$, exactly one satisfies


$$d\equiv3c-2\pmod5.$$


The selected unit is:


$$\begin{array}{c|c}
c\bmod5 & \text{selected associate}\\
\hline
2 & z\\
3 & -z\\
4 & iz\\
1 & -iz
\end{array}$$


In every case, the selected contribution equals


$$(-1)^{c-1}
\left(c^2-d^2-\frac32cd\right).
\tag{20}$$


Indeed, for $z$ and $-z$, both $c^2-d^2$ and $cd$ are unchanged. For $iz=(-d)+ic$, since $c,d$ have opposite parity,


$$(-1)^{-d-1}=-(-1)^{c-1},$$


and


$$(-d)^2-c^2=-(c^2-d^2),\qquad
(-d)c=-cd,$$


so the same value (20) results. The case $-iz$ is identical.
If instead


$$d\equiv-2c\pmod5,$$


then apply the previous case to $\bar z=c-di$. The selected contribution becomes


$$(-1)^{c-1}
\left(c^2-d^2+\frac32cd\right).
\tag{21}$$


For the string $z_t$, the endpoint $z_0=\bar\pi^hw$ lies on the $d\equiv2c$ line, and $z_h=\pi^hw$ lies on the $d\equiv-2c$ line. Therefore the selected endpoint contribution of the whole string is


$$\varepsilon
\left[
\left(A_0-\frac32B_0\right)
+
\left(A_h+\frac32B_h\right)
\right].
\tag{22}$$



4.3. Full Jacobi contribution of the string
For a fixed $z_t=c_t+id_t$, the quantity


$$(-1)^{c_t-1}(c_t^2-d_t^2)$$


is invariant under multiplication by $\pm1,\pm i$ and under conjugation. Hence, after the global factor $1/4$, the Jacobi side contributes


$$2\varepsilon A_t$$


from $z_t$ and its conjugate.
Thus the full string contribution to the right side of (12) is


$$2\varepsilon\sum_{t=0}^h A_t.
\tag{23}$$


So it remains to prove


$$\left(A_0-\frac32B_0\right)
+
\left(A_h+\frac32B_h\right)
=
2\sum_{t=0}^h A_t.
\tag{24}$$



4.4. The scalar string identity
Let


$$\lambda=\pi^2=(2+i)^2=3+4i,\qquad
\bar\lambda=3-4i.$$


Then


$$z_t^2
=
\pi^{2t}\bar\pi^{2h-2t}w^2
=
\lambda^t\bar\lambda^{h-t}w^2.$$


Since


$$A_t=\Re(z_t^2),\qquad 2B_t=\Im(z_t^2),$$


we prove (24) by a one-line geometric sum.
First,


$$2\sum_{t=0}^h z_t^2
=
2w^2\sum_{t=0}^h\lambda^t\bar\lambda^{h-t}.$$


Because


$$\lambda-\bar\lambda=8i,$$


we have


$$2\sum_{t=0}^h\lambda^t\bar\lambda^{h-t}
=
2\cdot
\frac{\lambda^{h+1}-\bar\lambda^{h+1}}{\lambda-\bar\lambda}
=
\frac{\lambda^{h+1}-\bar\lambda^{h+1}}{4i}.$$


Now


$$\frac{\lambda}{4i}
=
\frac{3+4i}{4i}
=
1-\frac34 i,$$


and


$$-\frac{\bar\lambda}{4i}
=
-\frac{3-4i}{4i}
=
1+\frac34 i.$$


Therefore


$$2\sum_{t=0}^h z_t^2
=
\left(1-\frac34i\right)z_h^2
+
\left(1+\frac34i\right)z_0^2.$$


Taking real parts gives


$$2\sum_{t=0}^h A_t
=
\left(A_h+\frac34\Im(z_h^2)\right)
+
\left(A_0-\frac34\Im(z_0^2)\right).$$


Since


$$\Im(z_t^2)=2B_t,$$


this is exactly


$$2\sum_{t=0}^h A_t
=
\left(A_h+\frac32B_h\right)
+
\left(A_0-\frac32B_0\right).$$


This proves (24), hence the string identity, hence the shell identity (12).
Combining (8), (11), and (12), we obtain


$$[q^N]D(q)=[q^N]P^6$$


for every $N$. Therefore, as formal power series over $\mathbb Q$,


$$\boxed{
A B+5(B\theta A-A\theta B)=P^6.
}$$


No analytic convergence, modular forms, Sturm bounds, or valence formulae are used.

5. Product/logarithmic-derivative route
There is also a very short formal route if you have the following Lambert identity available.
Let


$$\chi_5(n)=
\begin{cases}
1,&n\equiv1,4\pmod5,\\
-1,&n\equiv2,3\pmod5,\\
0,&5\mid n.
\end{cases}$$


From the product forms,


$$\frac AB
=
\prod_{n\ge1}(1-q^n)^{\chi_5(n)}.$$


Therefore


$$\theta\log\left(\frac AB\right)
=
-\sum_{n\ge1}\chi_5(n)\frac{nq^n}{1-q^n}.$$


Since


$$B\theta A-A\theta B
=
AB\cdot\theta\log(A/B),$$


we get


$$AB+5(B\theta A-A\theta B)
=
AB
\left(
1-5\sum_{n\ge1}\chi_5(n)\frac{nq^n}{1-q^n}
\right).$$


Also


$$AB
=
(q;q)_\infty(q^5;q^5)_\infty
=
PP_5.$$


Thus Dobbie follows from


$$\boxed{
1-5\sum_{n\ge1}\chi_5(n)\frac{nq^n}{1-q^n}
=
\frac{P^5}{P_5}.
}
\tag{25}$$


Then


$$AB+5(B\theta A-A\theta B)
=
PP_5\cdot\frac{P^5}{P_5}
=
P^6.$$


Identity (25) is exactly the same finite shell identity above, repackaged as a Lambert-series identity. So the logarithmic-derivative proof is formally clean, but the hard elementary content is still the same 5-string theorem.

6. Lean formalization skeleton
I would formalize this in the following order.
A. Euler operator and coefficient expansion
leandef theta (F : ℚ⟦q⟧) : ℚ⟦q⟧ :=  -- coeff n = n * coeff n F
Core lemmas:
leantheorem coeff_theta :  coeff ℚ n (theta F) = n * coeff ℚ n Ftheorem theta_monomial :  theta (monomial n (1 : ℚ)) = n • monomial n (1 : ℚ)theorem theta_add :  theta (F + G) = theta F + theta Gtheorem theta_mul :  theta (F * G) = theta F * G + F * theta G
Then define the exponents:
leandef pA (r : ℤ) : ℤ := r * (5*r - 3) / 2def pB (s : ℤ) : ℤ := s * (5*s - 1) / 2def tri (a : ℤ) : ℤ := a * (a + 1) / 2
Bank nonnegativity lemmas:
leantheorem pA_nonneg (r : ℤ) : 0 ≤ pA rtheorem pB_nonneg (s : ℤ) : 0 ≤ pB stheorem tri_nonneg (a : ℤ) : 0 ≤ tri a
Then:
leantheorem coeff_dobbie_lhs :  coeff ℚ N (A*B + 5*(B*theta A - A*theta B))    =  ∑' r : ℤ, ∑' s : ℤ,    if pA r + pB s = N then      (-1 : ℚ)^r * (-1 : ℚ)^s *        (1 + 5 * (pA r - pB s))    else 0
In practice, avoid tsum by using your existing locally finite coefficient function.

B. The pentagonal shell change of variables
Define:
leandef cOfRS (r s : ℤ) : ℤ := 3*r + s - 1def dOfRS (r s : ℤ) : ℤ := -r + 3*sdef rOfCD (c d : ℤ) : ℤ := (3*c - d + 3) / 10def sOfCD (c d : ℤ) : ℤ := (c + 3*d + 1) / 10
Main algebra lemmas:
leantheorem cd_norm_of_rs :  cOfRS r s ^ 2 + dOfRS r s ^ 2    = 4 * (pA r + pB s) + 1 := by ringtheorem cd_selector_of_rs :  dOfRS r s ≡ 3 * cOfRS r s - 2 [ZMOD 5]theorem cd_weight_of_rs :  1 + 5 * (pA r - pB s)    =  cOfRS r s ^ 2 - dOfRS r s ^ 2    - (3 * cOfRS r s * dOfRS r s) / 2 := by ringtheorem cd_sign_of_rs :  (-1 : ℚ)^(r+s)    =  (-1 : ℚ)^(cOfRS r s - 1)
The inverse-direction lemma:
leantheorem rs_cd_bijection :  -- pairs (r,s) with pA r + pB s = N  -- equivalent to pairs (c,d) with c^2+d^2 = 4*N+1  -- and d ≡ 3*c - 2 mod 5
Result:
leantheorem coeff_dobbie_lhs_cd :  coeff ℚ N dobbieLHS    =  ∑ cd in cdShellSelected (4*N+1),    eps cd.c *      (cd.c^2 - cd.d^2 - (3 * cd.c * cd.d) / 2)
where
leandef eps (c : ℤ) : ℚ := (-1 : ℚ)^(c - 1)

C. Jacobi square shell
Define bilateral Jacobi theta:
leandef jacobiBi : ℚ⟦q⟧ :=  ∑ a : ℤ, (-1 : ℚ)^a * (2*a + 1) • q^(tri a)
Lemma:
leantheorem jacobiBi_eq_two_P_cubed :  jacobiBi = 2 * P^3
This is just the pairing $a\leftrightarrow -a-1$ plus standard one-sided Jacobi.
Then:
leantheorem P_six_eq_quarter_jacobiBi_sq :  P^6 = (1/4 : ℚ) * jacobiBi^2
Change variables:
leandef cOfAB (a b : ℤ) : ℤ := a + b + 1def dOfAB (a b : ℤ) : ℤ := b - a
with inverse
leana = (c - d - 1) / 2b = (c + d - 1) / 2
Main lemma:
leantheorem coeff_P_six_cd :  coeff ℚ N (P^6)    =  (1/4 : ℚ) *  ∑ cd in cdShell (4*N+1),    eps cd.c * (cd.c^2 - cd.d^2)

D. The 5-string shell identity
State this as the central finite theorem:
leantheorem cd_shell_identity (M : ℕ) (hM : Odd M) :  ∑ cd in cdShellSelected M,    eps cd.c *      (cd.c^2 - cd.d^2 - (3 * cd.c * cd.d) / 2)  =  (1/4 : ℚ) *  ∑ cd in cdShell M,    eps cd.c * (cd.c^2 - cd.d^2)
Prove it using integer-pair Gaussian arithmetic.
Define multiplication by $\pi$, $\bar\pi$:
leandef piMul (z : ℤ × ℤ) : ℤ × ℤ :=  (2*z.1 - z.2, z.1 + 2*z.2)def pibarMul (z : ℤ × ℤ) : ℤ × ℤ :=  (2*z.1 + z.2, -z.1 + 2*z.2)
The norm lemmas:
leantheorem norm_piMul :  norm (piMul z) = 5 * norm ztheorem norm_pibarMul :  norm (pibarMul z) = 5 * norm z
The string move lemmas:
leandef Tplus (z : ℤ × ℤ) : ℤ × ℤ :=  ((3*z.1 - 4*z.2)/5, (4*z.1 + 3*z.2)/5)def Tminus (z : ℤ × ℤ) : ℤ × ℤ :=  ((3*z.1 + 4*z.2)/5, (-4*z.1 + 3*z.2)/5)
with domain lemmas:
leantheorem Tplus_integral_iff :  -- Tplus integral iff z.2 ≡ 2*z.1 mod 5theorem Tminus_integral_iff :  -- Tminus integral iff z.2 ≡ -2*z.1 mod 5theorem norm_Tplus :  norm (Tplus z) = norm ztheorem norm_Tminus :  norm (Tminus z) = norm z
Endpoint table:
leantheorem selected_unit_bar_line  (h : z.2 ≡ 2*z.1 [ZMOD 5]) :  selectedUnitContribution z    =  eps z.1 * (z.1^2 - z.2^2 - (3*z.1*z.2)/2)theorem selected_unit_pi_line  (h : z.2 ≡ -2*z.1 [ZMOD 5]) :  selectedUnitContributionConj z    =  eps z.1 * (z.1^2 - z.2^2 + (3*z.1*z.2)/2)
Scalar string identity:
leantheorem string_scalar_identity  (w : ℤ × ℤ) (h : ℕ) :  let z t := gaussianString w h t  let A t := (z t).1^2 - (z t).2^2  let B t := (z t).1 * (z t).2  (A 0 - (3 * B 0)/2) + (A h + (3 * B h)/2)    =  2 * ∑ t in Finset.range (h+1), A t
This is the Lean version of the calculation with


$$\lambda=3+4i,\qquad \bar\lambda=3-4i.$$


Finally:
leantheorem cd_shell_identity := by  -- partition cdShell M into Gaussian 5-strings  -- interiors have no selected contribution  -- endpoint table gives selected contribution  -- string_scalar_identity gives equality stringwise

E. Final theorem
leantheorem dobbie_identity :  A * B + 5 * (B * theta A - A * theta B) = P^6 := by  ext N  rw [coeff_dobbie_lhs_cd]  rw [coeff_P_six_cd]  exact cd_shell_identity (4*N + 1) (by omega)

Practical recommendation
For Lean, the most valuable single theorem to bank is:
leantheorem cd_shell_identity
Once that is available, the rest of Dobbie is just:


formal Euler-operator coefficient expansion,


the linear change of variables $(r,s)\leftrightarrow(c,d)$,


Jacobi’s $P^3$ identity with the bilateral factor $1/2$,


coefficient extensionality.


The difficult $5\mid(4N+1)$ case is exactly handled by the Gaussian strings


$$z_t=\pi^t\bar\pi^{h-t}w.$$


Interior points $0<t<h$ are divisible by $5$, hence are invisible to the pentagonal selected class, and the endpoint identity


$$\left(A_0-\frac32B_0\right)
+
\left(A_h+\frac32B_h\right)
=
2\sum_{t=0}^hA_t$$


is the whole reason the missing interior Jacobi mass reappears on the pentagonal side.