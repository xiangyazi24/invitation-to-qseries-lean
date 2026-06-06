The clean proof is to avoid constructing log itself: use the logarithmic derivative as thetaOp f * f⁻¹, then prove a coefficient-wise uniqueness lemma for units. I’ll keep the factor-of-5 bookkeeping explicit.

Below is the clean Lean-oriented route. The key correction is this:


$$D(\operatorname{expand}_5 f)=5\,\operatorname{expand}_5(Df),$$


so


$$D\log(\operatorname{expand}_5 f)
=
5\,\operatorname{expand}_5(D\log f).$$


For $qPoch=(X;X)_\infty$,


$$D\log(qPoch)
=
-\sum_{n\ge 1}\frac{nX^n}{1-X^n},$$


hence


$$D\log(\operatorname{expand}_5 qPoch)
=
-5\sum_{n\ge 1}\frac{nX^{5n}}{1-X^{5n}}.$$


Equivalently, after reindexing by $m=5n$,


$$D\log(\operatorname{expand}_5 qPoch)
=
-\sum_{\substack{m\ge 1\\5\mid m}}
m\,\frac{X^m}{1-X^m}.$$


No extra factor $25$. The $5$ comes only from the chain rule.

Target identity
You want


$$\boxed{
\operatorname{apSigmaLambertFactor}\cdot \operatorname{expand}_5(qPoch)
=
qPoch^5.
}$$


Let


$$F:=\operatorname{apSigmaLambertFactor}\cdot \operatorname{expand}_5(qPoch),
\qquad
G:=qPoch^5.$$


The formal proof should be:


$F$ and $G$ have constant term $1$.


$D\log F=D\log G$.


Therefore $F=G$.


The only genuinely reusable formal-power-series lemma is the uniqueness lemma in step 3.

1. Formal logarithmic derivative
Let


$$D := \thetaOp := X\frac{d}{dX}.$$


For a unit $f\in \mathbb Q\llbracket X\rrbracket$, define


$$\operatorname{Dlog}(f):=D(f)\,f^{-1}.$$


Lean-style:
leandef Dlog (f : ℚ⟦X⟧) : ℚ⟦X⟧ :=  thetaOp f * f⁻¹
This definition requires Inv on PowerSeries; it is mathematically clean only when f is a unit. In statements, assume IsUnit f.
The basic algebraic lemmas are:
leantheorem Dlog_mul    {f g : ℚ⟦X⟧}    (hf : IsUnit f) (hg : IsUnit g) :    Dlog (f * g) = Dlog f + Dlog g := by  -- thetaOp_mul + inverse of product of units
Mathematically:


$$D\log(fg)
=
D(fg)(fg)^{-1}
=
(Df)g(fg)^{-1}+f(Dg)(fg)^{-1}
=
(Df)f^{-1}+(Dg)g^{-1}.$$


Because the ring is commutative, the cancellation is painless.
Power lemma:
leantheorem Dlog_pow    {f : ℚ⟦X⟧}    (hf : IsUnit f) (n : ℕ) :    Dlog (f^n) = n • Dlog f := by  -- induction on n using Dlog_mul
For rational coefficient rings, you may prefer scalar notation:
leanDlog (f^n) = (n : ℚ) • Dlog f
or
leanDlog (f^n) = (n : ℚ⟦X⟧) * Dlog f
For your concrete use:


$$D\log(qPoch^5)=5D\log(qPoch).$$



2. The uniqueness lemma: logarithmic derivative determines a normalized unit
This is the crux, but it is easy over $\mathbb Q\llbracket X\rrbracket$.
Preferred statement
Avoid explicitly mentioning formal log. State:
leantheorem eq_of_theta_mul_eq_mul_theta_of_constantCoeff_eq    {f g : ℚ⟦X⟧}    (hfg : thetaOp f * g = thetaOp g * f)    (hconst : constantCoeff ℚ f = constantCoeff ℚ g)    (hg_unit : IsUnit g) :    f = g := by  ...
You only need one of $f,g$ to be a unit for the proof below; in practice both are units.
Mathematically, set


$$h:=f g^{-1}.$$


Then


$$D(h)
=
D(fg^{-1})
=
Df\cdot g^{-1}
+
f\cdot D(g^{-1}).$$


Since


$$D(g^{-1})=-g^{-2}Dg,$$


we get


$$D(h)
=
\frac{Df\cdot g-f\cdot Dg}{g^2}.$$


The hypothesis $Df\cdot g=Dg\cdot f$ gives


$$D(h)=0.$$


Also,


$$h(0)=f(0)g(0)^{-1}=1$$


if $f(0)=g(0)\neq 0$. Hence $h=1$, so $f=g$.
The last step uses the lemma:
leantheorem thetaOp_eq_zero_of_constantCoeff? :  thetaOp h = 0 → h = C (constantCoeff ℚ h)
or, more directly:
leantheorem eq_constantCoeff_of_thetaOp_eq_zero    {h : ℚ⟦X⟧}    (hh : thetaOp h = 0) :    h = PowerSeries.C ℚ (constantCoeff ℚ h) := by  ext n  cases n with  | zero =>      simp  | succ n =>      -- coefficient of X^(n+1) in thetaOp h is (n+1) * coeff h (n+1)      -- over ℚ, n+1 ≠ 0, so coeff h (n+1)=0
Coefficient fact:


$$[X^n]\,D(h)=n[X^n]h.$$


For $n>0$, $n\neq 0$ in $\mathbb Q$, so $[X^n]h=0$. Thus $h$ is constant.
A very useful special case:
leantheorem eq_one_of_thetaOp_eq_zero_and_constantCoeff_one    {h : ℚ⟦X⟧}    (hD : thetaOp h = 0)    (h0 : constantCoeff ℚ h = 1) :    h = 1 := by  rw [eq_constantCoeff_of_thetaOp_eq_zero hD]  simp [h0]
Then the Dlog uniqueness lemma is:
leantheorem eq_of_Dlog_eq_of_constantCoeff_eq    {f g : ℚ⟦X⟧}    (hf : IsUnit f) (hg : IsUnit g)    (hDlog : Dlog f = Dlog g)    (hconst : constantCoeff ℚ f = constantCoeff ℚ g) :    f = g := by  -- Convert Dlog equality to thetaOp f * g = thetaOp g * f  -- Then apply the previous quotient argument.
For Lean, I would use the cross-multiplied version rather than fighting simplification of inverses:
leantheorem eq_of_theta_cross_eq_of_constantCoeff_eq    {f g : ℚ⟦X⟧}    (hf : IsUnit f) (hg : IsUnit g)    (hcross : thetaOp f * g = thetaOp g * f)    (hconst : constantCoeff ℚ f = constantCoeff ℚ g) :    f = g := by  ...
This is likely cleaner than Dlog equality.

3. Formal chain rule for expand5
Let


$$\operatorname{expand}_5(f)(X)=f(X^5).$$


Then


$$D(\operatorname{expand}_5 f)
=
X\frac{d}{dX}f(X^5)
=
5X^5 f'(X^5)
=
5\operatorname{expand}_5\left(Xf'(X)\right).$$


Thus:


$$\boxed{
\thetaOp(\operatorname{expand}_5 f)
=
5\operatorname{expand}_5(\thetaOp f).
}$$


Lean statement:
leantheorem thetaOp_expand5 (f : ℚ⟦X⟧) :  thetaOp (expand5 f) = 5 * expand5 (thetaOp f) := by  ext n  -- coefficient proof
Coefficient proof:


$$[X^n]\thetaOp(\operatorname{expand}_5 f)
=
n[X^n]\operatorname{expand}_5 f.$$


Now


$$[X^n]\operatorname{expand}_5 f
=
\begin{cases}
[X^{n/5}]f,& 5\mid n,\\
0,&5\nmid n.
\end{cases}$$


If $n=5m$, the coefficient is


$$5m[X^m]f.$$


The RHS coefficient is


$$[ X^{5m}]\, 5\operatorname{expand}_5(Df)
=
5[X^m]Df
=
5m[X^m]f.$$


If $5\nmid n$, both sides are $0$.
This is a pure formal-power-series lemma. It does not use convergence, products, or eta theory.
Then for a unit $f$,


$$D\log(\operatorname{expand}_5 f)
=
D(\operatorname{expand}_5 f)\cdot(\operatorname{expand}_5 f)^{-1}$$




$$=
5\operatorname{expand}_5(Df)\cdot\operatorname{expand}_5(f^{-1})$$




$$=
5\operatorname{expand}_5(Df\cdot f^{-1})
=
5\operatorname{expand}_5(D\log f).$$


Lean statement:
leantheorem Dlog_expand5    {f : ℚ⟦X⟧}    (hf : IsUnit f) :    Dlog (expand5 f) = 5 * expand5 (Dlog f) := by  unfold Dlog  rw [thetaOp_expand5]  -- need expand5_inv_of_isUnit:  -- (expand5 f)⁻¹ = expand5 (f⁻¹)  -- then map_mul  ring
You need:
leantheorem expand5_inv_of_isUnit    {f : ℚ⟦X⟧}    (hf : IsUnit f) :    (expand5 f)⁻¹ = expand5 (f⁻¹) := by  -- because expand5 is a ring hom and preserves f * f⁻¹ = 1
This is usually easier if you work with Units instead of raw inverse:
leandef expand5Unit : (ℚ⟦X⟧)ˣ → (ℚ⟦X⟧)ˣ :=  Units.map expand5
Then inverse preservation is definitional/simp-friendly.

4. Lambert-series bookkeeping
Let


$$L(q):=\sum_{n\ge 1} n\frac{X^n}{1-X^n}.$$


Then


$$D\log(qPoch)=-L(q).$$


Therefore:


$$D\log(qPoch^5)
=
5D\log(qPoch)
=
-5L(q).$$


Also,


$$D\log(\operatorname{expand}_5 qPoch)
=
5\operatorname{expand}_5(D\log qPoch)
=
-5\operatorname{expand}_5 L(q).$$


Since


$$\operatorname{expand}_5 L(q)
=
\sum_{n\ge 1} n\frac{X^{5n}}{1-X^{5n}},$$


we get:


$$D\log(\operatorname{expand}_5 qPoch)
=
-5\sum_{n\ge 1}n\frac{X^{5n}}{1-X^{5n}}.$$


Thus


$$D\log(qPoch^5)
-
D\log(\operatorname{expand}_5 qPoch)$$




$$=
-5\sum_{n\ge 1}n\frac{X^n}{1-X^n}
+
5\sum_{n\ge 1}n\frac{X^{5n}}{1-X^{5n}}.$$


Equivalently,


$$=
-5\sum_{\substack{n\ge1\\5\nmid n}}
n\frac{X^n}{1-X^n}.$$


But your apSigmaLambertFactor is


$$1-5\sum_{n\ge1}\chi(n)n\frac{X^n}{1-X^n}.$$


Important: this means $D\log(\operatorname{apSigmaLambertFactor})$ is not automatically the same as


$$-5\sum_{\substack{n\ge1\\5\nmid n}}
n\frac{X^n}{1-X^n}.$$


It is only the same if your already-proved quintupleLogFactor = apSigmaLambertFactor theorem includes the identity


$$D\log(\operatorname{quintuple product})
=
D\log(qPoch^5)-D\log(\operatorname{expand}_5 qPoch),$$


or equivalently if apSigmaLambertFactor was already proved to be the logarithmic derivative factor of the product quotient.
So the formal proof should use your existing theorem exactly as:
leantheorem Dlog_apSigmaLambertFactor :  Dlog apSigmaLambertFactor    =  Dlog (qPoch^5) - Dlog (expand5 qPoch) := by  -- from thetaLog_P014_eq_neg_apSigmas,  -- thetaLog_P023_eq_neg_apSigmas,  -- quintupleLogFactor_eq_apSigmaLambertFactor
Do not try to rederive this purely from the displayed definition unless you have already proved the quintuple-product logarithmic derivative identity. The Legendre-symbol Lambert series is subtler than the ordinary divisor series.
Once you have:


$$D\log(apSigmaLambertFactor)
=
D\log(qPoch^5)-D\log(\operatorname{expand}_5 qPoch),$$


then:


$$D\log(apSigmaLambertFactor)
+
D\log(\operatorname{expand}_5 qPoch)
=
D\log(qPoch^5).$$


By Dlog_mul,


$$D\log(apSigmaLambertFactor\cdot \operatorname{expand}_5 qPoch)
=
D\log(qPoch^5).$$


Then normalized-unit uniqueness gives the identity.

5. Constant terms and units
You need these facts:
leantheorem constantCoeff_qPoch :  constantCoeff ℚ qPoch = 1 := ...theorem isUnit_qPoch :  IsUnit qPoch := by  -- constant coefficient nonzerotheorem constantCoeff_expand5_qPoch :  constantCoeff ℚ (expand5 qPoch) = 1 := by  -- expand preserves constant coefficienttheorem isUnit_expand5_qPoch :  IsUnit (expand5 qPoch) := by  -- constant coefficient = 1theorem constantCoeff_apSigmaLambertFactor :  constantCoeff ℚ apSigmaLambertFactor = 1 := by  -- Lambert terms have zero constant termtheorem isUnit_apSigmaLambertFactor :  IsUnit apSigmaLambertFactor := by  -- constant coefficient = 1
Then:
leantheorem constantCoeff_lhs :  constantCoeff ℚ (apSigmaLambertFactor * expand5 qPoch) = 1 := by  rw [constantCoeff_mul]  simp [constantCoeff_apSigmaLambertFactor,        constantCoeff_expand5_qPoch]theorem constantCoeff_rhs :  constantCoeff ℚ (qPoch^5) = 1 := by  simp [constantCoeff_qPoch]

6. Final proof using Dlog
Assume you have this already-proved or easily derivable theorem:
leantheorem Dlog_apSigmaLambertFactor_eq :  Dlog apSigmaLambertFactor    =  Dlog (qPoch^5) - Dlog (expand5 qPoch) := by  ...
Then the main proof is:
leantheorem apSigmaLambertFactor_mul_expand5_qPoch_eq_qPoch_pow5 :  apSigmaLambertFactor * expand5 qPoch = qPoch^5 := by  apply eq_of_Dlog_eq_of_constantCoeff_eq  · exact isUnit_mul isUnit_apSigmaLambertFactor isUnit_expand5_qPoch  · exact isUnit_pow isUnit_qPoch 5  · calc      Dlog (apSigmaLambertFactor * expand5 qPoch)          = Dlog apSigmaLambertFactor + Dlog (expand5 qPoch) := by              rw [Dlog_mul isUnit_apSigmaLambertFactor isUnit_expand5_qPoch]      _ = (Dlog (qPoch^5) - Dlog (expand5 qPoch))            + Dlog (expand5 qPoch) := by              rw [Dlog_apSigmaLambertFactor_eq]      _ = Dlog (qPoch^5) := by              abel  · calc      constantCoeff ℚ (apSigmaLambertFactor * expand5 qPoch)          = 1 := constantCoeff_lhs      _ = constantCoeff ℚ (qPoch^5) := by          symm          exact constantCoeff_rhs
This is the clean mathematical proof.

7. Alternative: cross-multiplied proof avoiding inverses
For Lean, this may be even cleaner because it avoids rewriting raw inverses.
Use the lemma:
leantheorem eq_of_theta_cross_eq_of_constantCoeff_eq    {f g : ℚ⟦X⟧}    (hf : IsUnit f) (hg : IsUnit g)    (hcross : thetaOp f * g = thetaOp g * f)    (hconst : constantCoeff ℚ f = constantCoeff ℚ g) :    f = g := by  ...
Then define:
leanlet F := apSigmaLambertFactor * expand5 qPochlet G := qPoch^5
Instead of proving:


$$D\log F=D\log G,$$


prove:


$$D(F)\cdot G=D(G)\cdot F.$$


This follows from the Dlog equation but can be derived directly using product rules:


$$D(F)
=
D(aE)
=
Da\cdot E+a\cdot DE,$$


where $a=\operatorname{apSigmaLambertFactor}$ and $E=\operatorname{expand}_5(qPoch)$.
The assumed logarithmic derivative identity is equivalent to


$$Da\cdot a^{-1}
=
D(G)G^{-1}-D(E)E^{-1}.$$


Cross-multiplied:


$$Da\cdot E\cdot G
=
D(G)\cdot a\cdot E
-
D(E)\cdot a\cdot G.$$


Then


$$D(aE)\cdot G
=
(Da\cdot E+aDE)\cdot G$$




$$=
D(G)\cdot aE
-
D(E)\cdot aG
+
aDEG
=
D(G)\cdot aE.$$


This is algebraically robust, but in Lean it is not necessarily shorter unless your existing thetaLog identities are already cross-multiplied.
So choose based on the form of your existing library:
If your existing facts are stated as thetaLog ... = ...
Use the Dlog route.
If your existing facts are stated as thetaOp f * g = ...
Use the cross-multiplied route.
My recommendation: prove both infrastructure lemmas once, but use the cross-multiplied final uniqueness lemma for the final theorem. It avoids fragile inverse simplification.

8. Minimal lemma list for a <100-line final proof
Here is the exact ordered list I would implement.
Formal PS infrastructure
leantheorem coeff_thetaOp    (f : ℚ⟦X⟧) (n : ℕ) :    coeff ℚ n (thetaOp f) = (n : ℚ) * coeff ℚ n f
leantheorem thetaOp_eq_zero_iff_eq_constant    (f : ℚ⟦X⟧) :    thetaOp f = 0 ↔ f = PowerSeries.C ℚ (constantCoeff ℚ f)
leantheorem eq_of_theta_cross_eq_of_constantCoeff_eq    {f g : ℚ⟦X⟧}    (hf : IsUnit f) (hg : IsUnit g)    (hcross : thetaOp f * g = thetaOp g * f)    (hconst : constantCoeff ℚ f = constantCoeff ℚ g) :    f = g
Log-derivative infrastructure
leandef Dlog (f : ℚ⟦X⟧) : ℚ⟦X⟧ :=  thetaOp f * f⁻¹
leantheorem Dlog_mul    {f g : ℚ⟦X⟧}    (hf : IsUnit f) (hg : IsUnit g) :    Dlog (f * g) = Dlog f + Dlog g
leantheorem Dlog_pow    {f : ℚ⟦X⟧}    (hf : IsUnit f) (n : ℕ) :    Dlog (f^n) = (n : ℚ) • Dlog f
leantheorem eq_of_Dlog_eq_of_constantCoeff_eq    {f g : ℚ⟦X⟧}    (hf : IsUnit f) (hg : IsUnit g)    (hDlog : Dlog f = Dlog g)    (hconst : constantCoeff ℚ f = constantCoeff ℚ g) :    f = g
Expand-5 infrastructure
leantheorem thetaOp_expand5    (f : ℚ⟦X⟧) :    thetaOp (expand5 f) = 5 * expand5 (thetaOp f)
leantheorem Dlog_expand5    {f : ℚ⟦X⟧}    (hf : IsUnit f) :    Dlog (expand5 f) = 5 * expand5 (Dlog f)
Product-specific facts
leantheorem Dlog_qPoch :  Dlog qPoch =    - ordinarySigmaLambert
where


$$ordinarySigmaLambert
=
\sum_{n\ge1} nX^n/(1-X^n).$$


leantheorem Dlog_qPoch_pow5 :  Dlog (qPoch^5) =    -5 * ordinarySigmaLambert
leantheorem Dlog_expand5_qPoch :  Dlog (expand5 qPoch) =    -5 * expand5 ordinarySigmaLambert
But these two are optional if your already-proved thetaLog_* lemmas imply the next theorem directly.
The one bridge theorem from your existing work
leantheorem Dlog_apSigmaLambertFactor_eq :  Dlog apSigmaLambertFactor    =  Dlog (qPoch^5) - Dlog (expand5 qPoch)
This is the exact bridge from your thetaLog_P014_eq_neg_apSigmas, thetaLog_P023_eq_neg_apSigmas, and quintupleLogFactor = apSigmaLambertFactor.
Final theorem
leantheorem apSigmaLambertFactor_mul_expand5_qPoch_eq_qPoch_pow5 :  apSigmaLambertFactor * expand5 qPoch = qPoch^5
Proof skeleton:
leantheorem apSigmaLambertFactor_mul_expand5_qPoch_eq_qPoch_pow5 :  apSigmaLambertFactor * expand5 qPoch = qPoch^5 := by  apply eq_of_Dlog_eq_of_constantCoeff_eq  · exact isUnit_mul isUnit_apSigmaLambertFactor isUnit_expand5_qPoch  · exact isUnit_pow isUnit_qPoch 5  · calc      Dlog (apSigmaLambertFactor * expand5 qPoch)          = Dlog apSigmaLambertFactor + Dlog (expand5 qPoch) := by              exact Dlog_mul isUnit_apSigmaLambertFactor isUnit_expand5_qPoch      _ = (Dlog (qPoch^5) - Dlog (expand5 qPoch))            + Dlog (expand5 qPoch) := by              rw [Dlog_apSigmaLambertFactor_eq]      _ = Dlog (qPoch^5) := by              abel  · rw [constantCoeff_mul]    simp [constantCoeff_apSigmaLambertFactor,          constantCoeff_expand5_qPoch,          constantCoeff_qPoch]
That is the best route.

Final recommendation
Use this exact theorem as the bridge:


$$\boxed{
D\log(\operatorname{apSigmaLambertFactor})
=
D\log(qPoch^5)
-
D\log(\operatorname{expand}_5 qPoch).
}$$


Then the target follows by normalized-unit uniqueness.
The two infrastructure lemmas most worth investing in are:


$$\boxed{
D(\operatorname{expand}_5 f)=5\operatorname{expand}_5(Df)
}$$


and


$$\boxed{
D\log f=D\log g,\quad f(0)=g(0)=1
\quad\Longrightarrow\quad
f=g.
}$$


Once these are in your library, the final proof really should be under 100 lines.