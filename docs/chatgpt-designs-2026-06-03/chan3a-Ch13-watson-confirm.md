Verdict
Yes: you can avoid the $\sqrt t$ fractional framework completely for the final Lean target. The clean formal target should be the Rogers–Watson degree-5 modular equation, stated directly for the removed-fractional-power series.
The exact classical relation is:


$$\boxed{
u^5
=
v\,
\frac{1-2v+4v^2-3v^3+v^4}
     {1+3v+4v^2+2v^3+v^4}
}$$


where, classically,


$$u = R(q),\qquad v = R(q^5).$$


Equivalently,


$$\boxed{
u^5\,
(1+3v+4v^2+2v^3+v^4)
=
v\,
(1-2v+4v^2-3v^3+v^4).
}$$


This is exactly Theorem 5.5 in the Berndt–Chan–Huang–Kang–Sohn survey: “Let $u=R(q)$ and $v=R(q^5)$. Then


$$u^5
=
v\frac{1-2v+4v^2-3v^3+v^4}
        {1+3v+4v^2+2v^3+v^4}.$$


” The same page says this equation was communicated by Ramanujan, first proved in print by Rogers, and later proved by Watson and Ramanathan. mrc.sdu.edu.cn
Now translate to your notation. Since


$$R(q)=q^{1/5}r(q),
\qquad
R(q^5)=q\,r(q^5)=v,$$


the classical equation becomes


$$(q^{1/5}r(q))^5 B(v)
=
v A(v).$$


That is,


$$q\,r(q)^5 B(v)
=
q\,r(q^5) A(v).$$


Since $\mathbb Q\llbracket q\rrbracket$ is an integral domain and $q=X$ is nonzero, cancellation gives


$$\boxed{
r(q)^5B(v)=r(q^5)A(v).
}$$


This is precisely your Theorem 11.5 r-form.
So the identity you want is not merely “derived from” the degree-5 modular equation: it is the degree-5 modular equation after removing the $q^{1/5}$ factor and cancelling one $q$.

1. Can it be proved using only the product forms already formalized?
Short answer
Not cheaply. The product forms for $r(q)$ and $r(q^5)$ reduce the theorem to a concrete eta-product identity, but the remaining identity is still exactly Watson/Rogers’s nontrivial modular equation. There is no obvious ring closure from the Rogers–Ramanujan product forms alone.
The bankable algebraic reduction is:


$$r(q)^5B(qr(q^5))-r(q^5)A(qr(q^5))=0,$$


where


$$r(q)
=
\frac{(q;q^5)_\infty(q^4;q^5)_\infty}
     {(q^2;q^5)_\infty(q^3;q^5)_\infty}.$$


Substituting $r(q^5)$ gives the explicit eta-quotient form


$$\left(
\frac{(q;q^5)_\infty(q^4;q^5)_\infty}
     {(q^2;q^5)_\infty(q^3;q^5)_\infty}
\right)^5
B\!\left(
q\frac{(q^5;q^{25})_\infty(q^{20};q^{25})_\infty}
       {(q^{10};q^{25})_\infty(q^{15};q^{25})_\infty}
\right)
=
\frac{(q^5;q^{25})_\infty(q^{20};q^{25})_\infty}
     {(q^{10};q^{25})_\infty(q^{15};q^{25})_\infty}
A\!\left(
q\frac{(q^5;q^{25})_\infty(q^{20};q^{25})_\infty}
       {(q^{10};q^{25})_\infty(q^{15};q^{25})_\infty}
\right).$$


After clearing denominators, this is a finite sum of eta-products at moduli $5$ and $25$. But proving that cleared eta-product identity is already a 5-dissection / modular-equation theorem. It will not collapse by finite polynomial algebra unless you add additional 5-dissection identities.
So the clean options are:
Route A: Add the degree-5 modular equation as the crux theorem
This is the best Lean architecture.
State a formal-power-series theorem:


$$\operatorname{rrcf\_R}^5 B(\operatorname{expand}_5\operatorname{rrcf\_R})
=
\operatorname{expand}_5\operatorname{rrcf\_R}
  A(\operatorname{expand}_5\operatorname{rrcf\_R}),$$


or, avoiding fractional powers, directly:


$$X\cdot r(q)^5B(Xr(q^5))
=
X\cdot r(q^5)A(Xr(q^5)).$$


Then cancel $X$.
This isolates the real mathematics into one theorem:
leantheorem rogers_watson_modular_equation_removed :  X * rrcf_r^5 * B (X * expand_5 rrcf_r)    =  X * expand_5 rrcf_r * A (X * expand_5 rrcf_r) := ...
Then your desired theorem follows by rw, associativity, and cancellation in the domain $\mathbb Q⟦X⟧$.
Route B: Prove the modular equation from a 5-dissection identity
This is formalizable, but it is the multi-week route. You would need to prove one or more of:


$$G(q)=G(q^{25})+\cdots,
\qquad
H(q)=\cdots,$$


or equivalent 5-dissections of theta functions / eta products. Once those are available, the rest is polynomial algebra.
Route C: Use analytic modular forms and Sturm bounds
This is conceptually nice but probably worse in Mathlib today. You would need a formal theory of eta-quotients, modular functions, levels, weights, orders at cusps, and a Sturm or valence theorem. This is not the minimal Lean path.
So: do not try to prove Theorem 11.5 from Theorem 11.1 alone by ring and product algebra. Theorem 11.1 gives the product expression for $R(q)$, but the relation between $R(q)$ and $R(q^5)$ is genuinely the modular equation.

2. Classical proof chain: $11.1 \to 11.3 \to 12.37 \to 11.5$
The classical chain in Chan is roughly:
Theorem 11.1: Rogers–Ramanujan identities and product form
This gives


$$R(q)
=
q^{1/5}\frac{H(q)}{G(q)}
=
q^{1/5}
\frac{(q;q^5)_\infty(q^4;q^5)_\infty}
     {(q^2;q^5)_\infty(q^3;q^5)_\infty}.$$


In your notation:


$$r(q)
=
\frac{R(q)}{q^{1/5}}
=
\frac{H(q)}{G(q)}
=
\frac{(q;q^5)_\infty(q^4;q^5)_\infty}
     {(q^2;q^5)_\infty(q^3;q^5)_\infty}.$$


This part you already have.
Theorem 11.3: a product/theta relation involving $R(q)$
The usual identity used around this point is the fundamental relation


$$\boxed{
\frac{1}{R(q)^5}-11-R(q)^5
=
\frac{f(-q)^6}{q f(-q^5)^6}.
}$$


Equivalently, with $R(q)=q^{1/5}r(q)$,


$$\boxed{
\frac{1}{q r(q)^5}
-
11
-
q r(q)^5
=
\frac{f(-q)^6}{q f(-q^5)^6}.
}$$


Multiplying by $q$,


$$\boxed{
r(q)^{-5}
-
11q
-
q^2 r(q)^5
=
\frac{f(-q)^6}{f(-q^5)^6}.
}$$


This version is entirely in $\mathbb Q⟦X⟧$, because $r(q)$ is a unit. No $q^{1/5}$ remains.
This theorem is itself nontrivial but can be proved from the Rogers–Ramanujan product forms plus a 5-dissection of Euler’s product. It is often one of the standard gateway identities for the RRCF.
Equation 12.37: the theta/product identity needed to eliminate the eta quotient
Chan’s Eq. 12.37 is used to express the eta quotient


$$\frac{f(-q)^6}{q f(-q^5)^6}$$


or its shifted version in terms of $R(q)$ and $R(q^5)$. This is where the proof enters the $\sqrt t$-style framework in the textbook.
In the proof of 11.5, the role of Eq. 12.37 is not cosmetic: it is the step that converts the eta/theta expression into the algebraic relation between $R(q)$ and $R(q^5)$. This is the genuine crux.
Theorem 11.5: Watson relation
The final statement is:


$$R(q)^5
=
R(q^5)
\frac{
1-2R(q^5)+4R(q^5)^2-3R(q^5)^3+R(q^5)^4
}{
1+3R(q^5)+4R(q^5)^2+2R(q^5)^3+R(q^5)^4
}.$$


Equivalently:


$$R(q)^5B(R(q^5))
=
R(q^5)A(R(q^5)).$$


Then substitute $R(q)=q^{1/5}r(q)$ and $R(q^5)=q r(q^5)$, and cancel $q$.
Which step is the genuine crux?
The genuine crux is not the final algebra from 12.37 to 11.5. The final algebra is finite polynomial manipulation.
The crux is proving the modular-equation input: either Theorem 11.3 plus Eq. 12.37, or directly the degree-5 Watson/Rogers modular equation


$$R(q)^5B(R(q^5))=R(q^5)A(R(q^5)).$$


For Lean, I would not reproduce the textbook’s $\sqrt t$ path unless you are trying to formalize the book line by line. I would instead isolate the crux as a clean formal-power-series theorem.

3. Exact relation and sign check
Let


$$A(T)=1-2T+4T^2-3T^3+T^4,$$




$$B(T)=1+3T+4T^2+2T^3+T^4.$$


The exact Rogers–Watson degree-5 modular equation is:


$$\boxed{
R(q)^5
=
R(q^5)\frac{A(R(q^5))}{B(R(q^5))}.
}$$


Equivalently,


$$\boxed{
R(q)^5B(R(q^5))
=
R(q^5)A(R(q^5)).
}$$


Substitute


$$R(q)=q^{1/5}r(q),
\qquad
R(q^5)=q r(q^5)=v.$$


Then


$$q r(q)^5 B(v)=vA(v).$$


Since $v=q r(q^5)$, this is


$$q r(q)^5B(v)=q r(q^5)A(v).$$


Cancel $q$:


$$\boxed{
r(q)^5B(v)=r(q^5)A(v).
}$$


Therefore your signs and coefficients are correct:


$$A(v)=1-2v+4v^2-3v^3+v^4,$$




$$B(v)=1+3v+4v^2+2v^3+v^4.$$


No coefficient $3v^2$, no sign reversal, and no missing factor $5$.

4. Formalization plan in $\mathbb Q⟦X⟧$
I would organize the Lean proof in three layers.

Layer 0: polynomial infrastructure
Define the Watson polynomials as actual polynomials, not ad hoc functions on FPS if possible.
leandef watsonA : Polynomial ℚ :=  1 - 2 * X + 4 * X^2 - 3 * X^3 + X^4def watsonB : Polynomial ℚ :=  1 + 3 * X + 4 * X^2 + 2 * X^3 + X^4
Then define evaluation into FPS:
leandef A (v : ℚ⟦X⟧) : ℚ⟦X⟧ :=  watsonA.eval₂ (algebraMap ℚ ℚ⟦X⟧) vdef B (v : ℚ⟦X⟧) : ℚ⟦X⟧ :=  watsonB.eval₂ (algebraMap ℚ ℚ⟦X⟧) v
Useful lemmas:
lean@[simp] theorem A_def_eval (v : ℚ⟦X⟧) :  A v = 1 - 2*v + 4*v^2 - 3*v^3 + v^4 := by  unfold A watsonA  ring@[simp] theorem B_def_eval (v : ℚ⟦X⟧) :  B v = 1 + 3*v + 4*v^2 + 2*v^3 + v^4 := by  unfold B watsonB  ring
And your existing ring identities:
leantheorem A_sub_B (v : ℚ⟦X⟧) :  A v - B v = -5 * v * (1 + v^2) := by  simp [A_def_eval, B_def_eval]  ring

Layer 1: define $r$, $r(q^5)$, and $v$
You already have this, but the key normalization lemmas should be explicit:
leandef expand5 : ℚ⟦X⟧ →+* ℚ⟦X⟧ := ...def rrcf_r : ℚ⟦X⟧ := ...def rrcf_r5 : ℚ⟦X⟧ :=  expand5 rrcf_rdef rrcf_v : ℚ⟦X⟧ :=  X * rrcf_r5
Lemmas:
leantheorem rrcf_v_eq :  rrcf_v = X * expand5 rrcf_r := rfltheorem constantCoeff_rrcf_r :  constantCoeff ℚ rrcf_r = 1 := ...theorem isUnit_rrcf_r :  IsUnit rrcf_r := ...theorem isUnit_expand5_rrcf_r :  IsUnit (expand5 rrcf_r) := ...
You also want a cancellation lemma for $X$:
leantheorem X_mul_cancel    {F G : ℚ⟦X⟧}    (h : X * F = X * G) :    F = G := by  exact mul_left_cancel₀ X_ne_zero h
Depending on Mathlib names, this may be:
leanexact mul_left_cancel₀ (show (X : ℚ⟦X⟧) ≠ 0 by exact X_ne_zero) h
or may require the integral domain instance for formal power series over a field.

Layer 2: state the modular equation as the single crux theorem
This is the best target theorem:
leantheorem rogers_watson_modular_equation_removed_X :  X * rrcf_r^5 * B rrcf_v    =  X * (expand5 rrcf_r) * A rrcf_v := by  -- crux
Then the final theorem is easy:
leantheorem chan_11_5_r_form :  rrcf_r^5 * B rrcf_v    =  (expand5 rrcf_r) * A rrcf_v := by  apply X_mul_cancel  calc    X * (rrcf_r^5 * B rrcf_v)        = X * rrcf_r^5 * B rrcf_v := by ring    _ = X * (expand5 rrcf_r) * A rrcf_v := by        exact rogers_watson_modular_equation_removed_X    _ = X * ((expand5 rrcf_r) * A rrcf_v) := by ring
This avoids any formal $q^{1/5}$.

Best bankable partial
The strongest bankable partial is to reduce the theorem to one named eta-product identity, with no fractional powers.
Define:


$$P_1=(X;X^5)_\infty,\quad
P_2=(X^2;X^5)_\infty,\quad
P_3=(X^3;X^5)_\infty,\quad
P_4=(X^4;X^5)_\infty.$$


Then


$$r=\frac{P_1P_4}{P_2P_3}.$$


Similarly,


$$r_5
=
\frac{P_{5,25}P_{20,25}}
     {P_{10,25}P_{15,25}}.$$


Let


$$v=Xr_5.$$


Your theorem is equivalent to the cleared denominator identity:


$$(P_1P_4)^5
\cdot
\bigl(P_{10,25}P_{15,25}\bigr)^5
\cdot
B(v)
=
(P_2P_3)^5
\cdot
(P_{5,25}P_{20,25})
\cdot
\bigl(P_{10,25}P_{15,25}\bigr)^4
\cdot
A(v),$$


with $v=X(P_{5,25}P_{20,25})/(P_{10,25}P_{15,25})$. More cleanly, avoid rational notation by clearing $B(v)$ and $A(v)$ termwise.
If


$$C=P_{5,25}P_{20,25},
\qquad
D=P_{10,25}P_{15,25},
\qquad
v=X C D^{-1},$$


then multiplying the desired identity by $(P_2P_3)^5D^4$ gives the finite eta-product sum:


$$(P_1P_4)^5
\left(
D^4+3XCD^3+4X^2C^2D^2+2X^3C^3D+X^4C^4
\right)$$




$$=
(P_2P_3)^5C
\left(
D^3-2XCD^2+4X^2C^2D-3X^3C^3+X^4C^4D^{-1}
\right)$$


Actually the last display still has a denominator in the $X^4C^4$ term if multiplied only by $D^4$. Multiply by $D^5$ instead. The denominator-free version is:


$$\boxed{
(P_1P_4)^5
\left(
D^5+3XCD^4+4X^2C^2D^3+2X^3C^3D^2+X^4C^4D
\right)
}$$




$$\boxed{
=
(P_2P_3)^5C
\left(
D^4-2XCD^3+4X^2C^2D^2-3X^3C^3D+X^4C^4
\right).
}$$


This is a very good “bankable partial” theorem:
leantheorem watson_eta_product_cleared :  (P1 * P4)^5 *    (D^5 + 3*X*C*D^4 + 4*X^2*C^2*D^3       + 2*X^3*C^3*D^2 + X^4*C^4*D)  =  (P2 * P3)^5 * C *    (D^4 - 2*X*C*D^3 + 4*X^2*C^2*D^2       - 3*X^3*C^3*D + X^4*C^4)
where
leanP1 = qpoch_mod 1 5P2 = qpoch_mod 2 5P3 = qpoch_mod 3 5P4 = qpoch_mod 4 5C = qpoch_mod 5 25 * qpoch_mod 20 25D = qpoch_mod 10 25 * qpoch_mod 15 25
Then prove mechanically:
leantheorem watson_eta_product_cleared_implies_chan_11_5 :  watson_eta_product_cleared_statement →  rrcf_r^5 * B rrcf_v = expand5 rrcf_r * A rrcf_v := by  -- unfold rrcf_r, rrcf_v  -- use unit inverses for P2,P3,D  -- field_simp-style algebra over a commutative ring with units  -- ring
This gives you a single concrete eta-product identity as the remaining hard lemma. That is a much better endpoint than a vague “modular equation” axiom, because every symbol is a formal product in $\mathbb Q⟦X⟧$.

Recommended final architecture
I would make the file structure like this:
leanRRCF/WatsonPolynomials.lean
Contains watsonA, watsonB, and all ring lemmas.
leanRRCF/RRemoved.lean
Contains rrcf_r, expand5, rrcf_v, product forms, unit lemmas.
leanRRCF/WatsonModularEquation.lean
Contains the single crux theorem, either as:
leantheorem rogers_watson_modular_equation_removed_X : ...
or as the cleared eta-product identity plus the derivation.
leanRRCF/Chan11_5.lean
Contains the final theorem:
leantheorem chan_11_5_r_form :  rrcf_r^5 * B rrcf_v =  expand5 rrcf_r * A rrcf_v
The proof of Chan11_5.lean should be less than 30 lines after the crux theorem is available.

Practical recommendation
For Lean, the cleanest route is:


Do not formalize $\sqrt t$.


Do not introduce $q^{1/5}$.


State Watson’s degree-5 modular equation in the multiplied-by-$X$ removed form:


$$Xr(q)^5B(Xr(q^5))=Xr(q^5)A(Xr(q^5)).$$




Derive Chan 11.5 by cancelling $X$.


If you want a fully internal proof later, reduce the crux to the denominator-free eta-product identity above.


The exact final mathematical crux is:


$$\boxed{
R(q)^5B(R(q^5))=R(q^5)A(R(q^5)).
}$$


Everything after that is formal algebra.