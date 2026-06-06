I’ll pin down the finite identity in the exact exponent normalization, then separate the algebraic proof from the Lean coefficient-stabilization plumbing.

I’ll assume the clean $b>0,\ 0<a<b$ power-series case; otherwise Laurent shifts are needed. I’ll use symmetric finite products/windows, where stabilization bounds are simplest.

Assume the normalized case


$$0<a<b,\qquad a,b\in\mathbb N.$$


Then everything lives already in $\mathbb Q\llbracket Q\rrbracket$, hence also in $\mathbb Q((Q))$. For arbitrary integer $a$, first reduce $a$ modulo $b$ using the shift relation at the end.
The cleanest route is finite Jacobi triple product + coefficient stabilization. No analytic argument is needed.

1. The finite JTP to use
Write


$$(q;q)_N=\prod_{i=1}^{N}(1-q^i),
\qquad
(z;q)_N=\prod_{i=0}^{N-1}(1-zq^i).$$


Use this finite identity:


$$\boxed{
(z;q)_N(q/z;q)_N
=
\sum_{r=-N}^{N}
(-1)^r z^r q^{r(r-1)/2}
\binom{2N}{N+r}_q .
}
\tag{FJTP0}$$


Equivalently, after multiplying by $(q;q)_N$,


$$\boxed{
(q;q)_N(z;q)_N(q/z;q)_N
=
\sum_{r=-N}^{N}
(-1)^r z^r q^{r(r-1)/2} R_{N,r}(q),
}
\tag{FJTP}$$


where


$$R_{N,r}(q):=(q;q)_N\binom{2N}{N+r}_q.$$


For $|r|\le N$, this correction factor has the concrete product form


$$\boxed{
R_{N,r}(q)
=
\prod_{i=N-|r|+1}^{N}(1-q^i)
\prod_{i=N+|r|+1}^{2N}(1-q^i).
}
\tag{R}$$


The empty product is $1$. In particular,


$$\boxed{
R_{N,r}(q)\equiv 1 \pmod {q^{N-|r|+1}}.
}
\tag{R-stab}$$


This is the key stabilization input.
Mathlib’s formal power series API is the right target for the normalized case; PowerSeries R is the univariate formal power series type in mathlib. Lean Community

2. Substitute $q=Q^b,\ z=Q^a$
Define


$$E(r):=\frac{b r(r-1)}2+ar.$$


Since $0<a<b$, $E(r)\ge 0$ for all $r\in\mathbb Z$. More Lean-friendly, split into positive and negative parts:


$$E_+(k):=\frac{b k(k-1)}2+ak,\qquad k\ge 0,$$


and


$$E_-(s):=\frac{b s(s-1)}2+(b-a)s,\qquad s\ge 1,$$


so that


$$E(-s)=E_-(s).$$


Define the $N$-th product truncation


$$P_N(a,b):=
(Q^b;Q^b)_N
(Q^a;Q^b)_N
(Q^{b-a};Q^b)_N.$$


Explicitly,


$$P_N(a,b)=
\prod_{i=1}^{N}(1-Q^{bi})
\prod_{i=0}^{N-1}(1-Q^{a+bi})
\prod_{i=0}^{N-1}(1-Q^{b-a+bi}).$$


Substituting $q=Q^b,\ z=Q^a$ in FJTP gives


$$\boxed{
P_N(a,b)
=
\sum_{r=-N}^{N}
(-1)^r Q^{E(r)} R_{N,r}(Q^b).
}
\tag{FJTP-sub}$$


Equivalently, avoiding integer exponents in Lean,


$$\boxed{
P_N(a,b)
=
\sum_{k=0}^{N}
(-1)^k Q^{E_+(k)} R_{N,k}(Q^b)
+
\sum_{s=1}^{N}
(-1)^s Q^{E_-(s)} R_{N,-s}(Q^b).
}
\tag{FJTP-split}$$


Since $R_{N,r}(q)\equiv 1\pmod{q^{N-|r|+1}}$, we get


$$R_{N,r}(Q^b)\equiv 1
\pmod{Q^{b(N-|r|+1)}}.$$


Therefore


$$Q^{E(r)}R_{N,r}(Q^b)
\equiv
Q^{E(r)}
\pmod{Q^{E(r)+b(N-|r|+1)}}.$$



3. Exact coefficient cutoff
Set


$$\delta:=\min(a,b-a).$$


Then the exact useful cutoff is


$$\boxed{
bN+\delta.
}$$


The stabilization lemma is:


$$\boxed{
[d<bN+\delta]
\quad\Longrightarrow\quad
[Q^d]\,P_N(a,b)
=
[Q^d]\,j(a,b).
}
\tag{theta-stab}$$


Here


$$j(a,b)=
\sum_{r\in\mathbb Z}
(-1)^r Q^{E(r)}.$$


Why the cutoff is $bN+\delta$
There are two possible discrepancies between $P_N$ and $j(a,b)$.
First, for $|r|\le N$, the correction factor $R_{N,r}(Q^b)$ differs from $1$ only starting at degree


$$E(r)+b(N-|r|+1).$$


For $r=k\ge 1$,


$$E(k)+b(N-k+1)
=
bN+a+(k-1)\left(\frac{b(k-2)}2+a\right)
\ge bN+a
\ge bN+\delta.$$


For $r=0$,


$$E(0)+b(N+1)=b(N+1)\ge bN+\delta.$$


For $r=-s,\ s\ge 1$,


$$E(-s)+b(N-s+1)
=
bN+(b-a)+(s-1)\left(\frac{b(s-2)}2+(b-a)\right)
\ge bN+(b-a)
\ge bN+\delta.$$


So correction terms cannot affect coefficients of degree $d<bN+\delta$.
Second, the infinite theta sum has terms with $|r|>N$ that do not appear in the finite sum. But the first omitted positive term is $r=N+1$, and the first omitted negative term is $r=-(N+1)$. Their degrees are


$$E(N+1)=\frac{bN(N+1)}2+a(N+1),$$


and


$$E(-(N+1))=\frac{bN(N+1)}2+(b-a)(N+1).$$


Both are at least $bN+\delta$. Therefore no omitted theta term contributes below degree $bN+\delta$.
Hence


$$[Q^d]P_N(a,b)=[Q^d]j(a,b)$$


for every


$$d<bN+\delta.$$


This bound is generally sharp: the correction from $r=1$ can start at $bN+a$, and the correction from $r=-1$ can start at $bN+b-a$.

4. Infinite product stabilization
Let


$$\Pi(a,b):=
(Q^b;Q^b)_\infty
(Q^a;Q^b)_\infty
(Q^{b-a};Q^b)_\infty.$$


The omitted factors after $P_N(a,b)$ begin at degrees


$$b(N+1),\qquad a+bN,\qquad b-a+bN.$$


Their minimum is


$$bN+\delta.$$


Thus the tail product is


$$1+O(Q^{bN+\delta}),$$


so


$$\boxed{
[d<bN+\delta]
\quad\Longrightarrow\quad
[Q^d]\,\Pi(a,b)
=
[Q^d]\,P_N(a,b).
}
\tag{prod-stab}$$


Combining theta-stab and prod-stab gives


$$[Q^d]\,\Pi(a,b)=[Q^d]\,j(a,b)$$


for every $d$, by choosing any $N$ with


$$d<bN+\delta.$$


A simple Lean choice is $N=d+1$, since $b\ge 1$ and $\delta\ge 1$.
Therefore, by coefficient extensionality in $\mathbb Q\llbracket Q\rrbracket$,


$$\boxed{
j(a,b)=
(Q^b;Q^b)_\infty
(Q^a;Q^b)_\infty
(Q^{b-a};Q^b)_\infty.
}$$


Then coerce to $\mathbb Q((Q))$.

5. Relation to your existing qPochInfPS machinery
Yes: use the existing infinite-product machinery for the three arithmetic-progression products. You do not need a new analytic bridge.
But the theorem


$$\texttt{qPochInfPS}^3=\texttt{jacobiThetaPS}$$


is only the Jacobi cube / derivative specialization. It does not by itself imply the two-parameter triple product $j(a,b)$ by a mere specialization or reindexing. What you can reuse is the infrastructure: finite partial products, coefficient stabilization of qPochInfPS, and coefficient extensionality.
The exact reduction is:


$$(Q^b;Q^b)_\infty
=
\text{the product over } i\ge 1 \text{ of } (1-Q^{bi}),$$




$$(Q^a;Q^b)_\infty
=
\text{the product over } i\ge 0 \text{ of } (1-Q^{a+bi}),$$




$$(Q^{b-a};Q^b)_\infty
=
\text{the product over } i\ge 0 \text{ of } (1-Q^{b-a+bi}).$$


If your qPochInfPS is only Euler’s product


$$\prod_{i\ge 1}(1-Q^i),$$


then $(Q^b;Q^b)_\infty$ is obtained by the substitution $Q\mapsto Q^b$. The other two factors require the same generalized arithmetic-progression version, unless your project already has qPochInfPS with parameters $(c,b)$. Once those are available, the proof is exactly the coefficient-stabilization argument above.

6. Ordered Lean lemma list
Here is the sequence I would formalize.
A. Basic definitions
leanpochPart (c b N : ℕ) : PowerSeries ℚ  := ∏ k in Finset.range N, (1 - monomial (c + b*k) 1)prodPart (a b N : ℕ) : PowerSeries ℚ  := pochPart b b N * pochPart a b N * pochPart (b-a) b N
with hypotheses
leanha : 0 < ahab : a < b
and
leandelta a b := min a (b-a)
Define theta exponents without integer division:
leanEpos a b k := b * k*(k-1)/2 + a*kEneg a b s := b * s*(s-1)/2 + (b-a)*s
Then
leanjacobiJPS a b  = sum over k ≥ 0 (-1)^k Q^(Epos a b k)    + sum over s ≥ 1 (-1)^s Q^(Eneg a b s)
implemented coefficientwise.

B. Finite JTP
Formalize either the Gaussian-binomial form
leanfinite_jtp :  (z;q)_N * (q/z;q)_N    =  ∑ r in Icc (-N) N,    (-1)^r * z^r * q^(r*(r-1)/2) * qBinom (2*N) (N+r)
in Laurent polynomials, then specialize $q=Q^b,\ z=Q^a$, or directly formalize the split substituted version:
leanfinite_jtp_sub :  prodPart a b N    =  ∑ k in range (N+1),      (-1)^k • monomial (Epos a b k) 1 * R N k  +  ∑ s in Icc 1 N,      (-1)^s • monomial (Eneg a b s) 1 * R N s
where
leanR N s :=  ∏ i in Icc (N-s+1) N,     (1 - monomial (b*i) 1)*  ∏ i in Icc (N+s+1) (2*N), (1 - monomial (b*i) 1)
for $s\le N$.
This split version is usually easiest downstream.

C. Correction-factor stabilization
For $s\le N$,
leanR_coeff_zero_of_lt :  0 < d →  d < b*(N-s+1) →  coeff d (R N s) = 0
and
leanR_coeff_zero :  coeff 0 (R N s) = 1
Equivalently,


$$R_{N,s}(Q^b)=1+O(Q^{b(N-s+1)}).$$


Then prove:
leanmonomial_mul_R_coeff_eq :  d < Epos a b k + b*(N-k+1) →  coeff d (monomial (Epos a b k) 1 * R N k)    =  coeff d (monomial (Epos a b k) 1)
and similarly for Eneg.

D. Quadratic cutoff inequalities
Let


$$\delta=\min(a,b-a).$$


For $k\le N$,
leanEpos_corr_cutoff :  Epos a b k + b*(N-k+1) ≥ b*N + delta
For $1\le s\le N$,
leanEneg_corr_cutoff :  Eneg a b s + b*(N-s+1) ≥ b*N + delta
For omitted positive theta terms:
leanEpos_omitted_cutoff :  N < k → Epos a b k ≥ b*N + delta
For omitted negative theta terms:
leanEneg_omitted_cutoff :  N < s → Eneg a b s ≥ b*N + delta
These four inequalities are the arithmetic heart of the stabilization proof.

E. Partial product equals theta below cutoff
leanprodPart_coeff_eq_jacobiJPS_coeff_of_lt :  d < b*N + delta →  coeff d (prodPart a b N) = coeff d (jacobiJPS a b)
This uses finite_jtp_sub, the correction-factor stabilization, and the omitted-term cutoff.

F. Infinite product equals partial product below cutoff
For each arithmetic-progression Pochhammer factor:
leanpochInf_coeff_eq_pochPart_of_lt :  d < c + b*N →  coeff d (pochInf c b) = coeff d (pochPart c b N)
For the triple product:
leanprodInf_coeff_eq_prodPart_of_lt :  d < b*N + delta →  coeff d    (pochInf b b * pochInf a b * pochInf (b-a) b)  =  coeff d (prodPart a b N)
because the first omitted exponents are


$$b(N+1),\quad a+bN,\quad b-a+bN,$$


and their minimum is $bN+\delta$.

G. Final coefficient extensionality
For arbitrary $d$, choose $N=d+1$. Then


$$d<bN+\delta.$$


So
leanjacobi_triple_product_formal :  jacobiJPS a b    =  pochInf b b * pochInf a b * pochInf (b-a) b
by PowerSeries.ext.
Finally coerce this identity into $\mathbb Q((Q))$.

7. Optional extension to arbitrary integer $a$
For $b>0$, reduce $a$ modulo $b$. The shift relation is


$$\boxed{
j(a+b,b)=-Q^{-a}j(a,b).
}$$


Indeed,


$$E_{a+b}(n)=E_a(n+1)-a,$$


and reindex $n\mapsto n+1$.
The product side satisfies the same relation:


$$\boxed{
(Q^{a+b};Q^b)_\infty
(Q^{-a};Q^b)_\infty
=
-Q^{-a}
(Q^a;Q^b)_\infty
(Q^{b-a};Q^b)_\infty.
}$$


This follows from


$$(Q^{a+b};Q^b)_\infty
=
\frac{(Q^a;Q^b)_\infty}{1-Q^a},$$


and


$$(Q^{-a};Q^b)_\infty
=
(1-Q^{-a})(Q^{b-a};Q^b)_\infty
=
-Q^{-a}(1-Q^a)(Q^{b-a};Q^b)_\infty.$$


Thus the normalized $0<a<b$ theorem implies the Laurent-series theorem for all $a\not\equiv 0\pmod b$. If $a\equiv0\pmod b$, both sides are $0$: the theta series cancels by the involution $n\mapsto 1-n$, and the product has a factor $1-Q^0$.