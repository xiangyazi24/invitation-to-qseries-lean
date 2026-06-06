# ChatGPT Pro (chan3): Chan Eq 10.15 via the SOURCE route — two-variable Hahn design (complete)

Avoids the level-90 AP-product identity ENTIRELY. The only heavy identities are Zwegers Lemma 10.1 and
Hickerson Lemma 10.2, both via recurrence/string proofs (not Macaulay/Riemann product algebra).

## Core type (q-first lexicographic Hahn kernel)
```lean
abbrev ExpXY  := Lex (ℤ × ℤ)
abbrev ExpQXY := Lex (ℤ × ExpXY)      -- (Q-degree, x-degree, y-degree), lex q-first
abbrev K := HahnSeries ℤ ℚ            -- ℚ((Q))
abbrev S := HahnSeries ExpQXY ℚ       -- q-adic x/y Laurent-Hahn field
def expQXY (a i j : ℤ) : ExpQXY := toLex (a, toLex (i, j))
def monom (a i j : ℤ) (c : ℚ) : S := HahnSeries.single (expQXY a i j) c
def coeffQXY (F : S)(a i j : ℤ) : ℚ;  def coeffXY (F:S)(i j:ℤ) : K (slice);  def CTxy (F:S) : K := coeffXY F 0 0
def embedQ : K →+* S  with CTxy_embedQ_mul : CTxy (embedQ f * F) = f * CTxy F
```
WHY: Θ(x;q) has support ALL of ℤ in x (so NOT HahnSeries ℤ K — not well-ordered in x; NOT LaurentPolynomial
— finite support). But Q-degree grows quadratically ⟹ support well-ordered in q-first lex. Products like
Θ(x;q²)Θ(x;q) have per-x-power coefficients that are INFINITE q-adic sums — must use Hahn multiplication,
not finite convolution. Use HahnSeries.coeff_mul / single_mul_single / SummableFamily from Mathlib.

## Conventions
Internal Q with q = Q^3 (so q^{1/3} = Q). Nome exponent A: q ↔ A=3, q² ↔ A=6.
T n := n(n-1)/2; Tplus n := n(n+1)/2; P10 n := n(5n+3)/2 (with evenness lemmas; T_neg_reindex:
(-n)(5(-n)-3)/2 = n(5n+3)/2).
def thetaMon (A e i j : ℤ) : S := ∑' n, monom (A*T n + e*n) (i*n) (j*n) ((-1)^n)   -- Θ with w = Q^e x^i y^j, nome Q^A
thetaX_q := thetaMon 3 0 1 0;  thetaY_q := thetaMon 3 0 0 1;  thetaXY_q := thetaMon 3 0 1 1;
thetaX_q2 := thetaMon 6 0 1 0; thetaY_q2 := thetaMon 6 0 0 1.
FE (10.33): thetaMon A e i j = - monom e i j 1 * thetaMon A (e+A) i j   (0<A).
Symmetries: thetaMon 3 3 (-1) 0 = thetaMon 3 0 1 0 (θ(q/x)=θ(x)); same for y;
(10.33 with w=x⁻¹y⁻¹q): monom 3 (-1) (-1) 1 * thetaMon 3 6 (-1) (-1) = - thetaMon 3 3 (-1) (-1).

## Lemma 10.1 (Zwegers) — functional equation route
LHS: zwegersLHS_x := ∑'_{k,l} monom (k²+l²) l 0 ((-1)^{k+l}(δ3 k − δ3 l))   [q^{(k²+l²)/3} = Q^{k²+l²}]
RHS: zwegersRHS_x := - monom 1 (-1) 0 1 * embedQ (poch_q/poch_q2) * thetaX_q2 * thetaX_q.
Coefficient FE (both sides): a(n+3) = - Qpow (6n+9) * a(n).
Closed form: a(s+3t) = (-1)^t Qpow (9t²+6st) a(s) for all s t : ℤ.
Uniqueness: coeff_eq_zero_of_fe_step3: FE + a(s)=a(s+1)=a(s+2)=0 ⟹ ∀n a(n)=0 (write n = s+r+3t, r∈{0,1,2}).
Match 3 initial coefficients ⟹ zwegers_lemma_10_1 : LHS = RHS. Repeat for y.
DO NOT define generic substXQ on all of S (x↦xQ^m not closed); prove the FE directly on the two concrete sides.

## Lemma 10.2 (Hickerson) — ρ-line strings (the Ch15 Dobbie analogue)
ρ r s := 1 if 0≤r∧0≤s; -1 if r<0∧s<0; 0 else.
Rho : S directly by coefficient (coeff z = if qDeg z = 3·xDeg z·yDeg z then ρ (xDeg z) (yDeg z) else 0);
support: q=0 fiber = two nonneg axes (still PWO in q-first lex), positive q-fibers finite (divisor fibers).
MULTIPLIED form (the target): thetaX_q * thetaY_q * Rho = embedQ (poch_q^3) * thetaXY_q.
Coefficient extraction at x^a y^b (set d=a-b; substitutions t=k+l-b, r=a-k, s=b-l):
  [x^a y^b](Θx Θy Rho) = (-1)^b q^{T b} ∑_t (-1)^t q^{T t} · StringSum(a-t, d)
where StringSumQ(m,d) := ∑'_s single (3ds) (ρ (m-s) s)   [the ρ-line string = contiguous same-sign segment:
  m≥0: s=0..m (weight +1); m=-1: ∅; m≤-2: s=m+1..-1 (weight −1)].
KEY string lemmas: StringSumQ(m,0) = m+1;  (1 − Qpow(3d))·StringSumQ(m,d) = 1 − Qpow(3d(m+1)) for d≠0.
OFF-DIAGONAL (a≠b): multiply by (1−q^d): both resulting theta-sums vanish by theta-at-one
  ∑_t(-1)^t q^{T t} = 0 and its shift (t=u+d: T t − dt = T u − d(d+1)/2, sign (−1)^d). 1−q^d ≠ 0 ⟹ coeff 0.
DIAGONAL (a=b): StringSum(a−t,0)=a−t+1; split: (a+1)·0 − ∑_t(−1)^t t q^{T t} = poch_q³ by JACOBI DERIVATIVE
  identity −∑(−1)^t t q^{T t} = (q;q)³  [reuse Ch15 Dobbie machinery / jacobiTripleSign].
⟹ coeff = if a=b then (−1)^a q^{T a} poch_q³ else 0 = coeff of embedQ(poch_q³)·thetaXY_q. Done.
Then division form + substituted form Rho(q/x,q/y) = embedQ(poch_q³)·thetaMon 3 6 (-1)(-1)/(thetaX_q·thetaY_q).

## Step 3 collapse + diagonal extraction
Zx := - monom 1 (-1) 0 1 * embedQ (poch_q/poch_q2) * thetaX_q2 * thetaX_q  (= zwegersRHS_x); same Zy.
Step3Expr := monom 1 0 0 1 * Rho_q_over_x_q_over_y * Zx * Zy.
step3_collapse: Step3Expr = - embedQ (poch_q^5/poch_q2^2) * thetaMon 3 3 (-1)(-1) * thetaX_q2 * thetaY_q2.
  (signs: two negative Z's cancel; 10.33 w=x⁻¹y⁻¹q gives the final −.)
CTxy_triple_theta: CTxy (thetaMon 3 3 (-1)(-1) * thetaX_q2 * thetaY_q2) = ∑' n single (3·P10 n) ((-1)^n):
  expand three thetas: Θ(x⁻¹y⁻¹q;q)=∑(-1)^n q^{Tplus n}x^{-n}y^{-n}; Θ(x;q²)=∑(-1)^k q^{k(k-1)}x^k; same y.
  [x⁰y⁰] forces k=n, l=n ⟹ ∑(-1)^{3n}q^{n(n+1)/2+2n(n-1)} = ∑(-1)^n q^{n(5n-3)/2}; reindex n↦−n ⟹ P10.
FINAL: chan_eq_10_15_Q : LHS_10_15_Q = - (poch_q^5/poch_q2^2) * ∑' n single (3·P10 n) ((-1)^n).

## Build order (A-I)
A exponent/monom/coeffQXY/coeffXY/CTxy/embedQ infra (+ext lemmas, monom_mul, CTxy_embedQ_mul).
B integer quadratic helpers (T, Tplus, P10, parity, T_add_three, closed-form recurrence lemma).
C thetaMon def + SummableFamily support proof + thetaMon_coeff + FE (10.33) + symmetries.
D poch bridge: poch_q=(Q³;Q³)∞, poch_q2=(Q⁶;Q⁶)∞ from qPochAPLaurent; embedQ lemmas; theta_one_zero;
  jacobi_derivative_poch_cube (reuse Ch15).
E Zwegers 10.1 (FE + 3 coeffs + uniqueness) for x and y.
F Hickerson 10.2 (Rho def, support PWO, string lemmas, off-diag/diag, multiplied identity, substituted form).
G Step3Expr collapse (signs + 10.33).
H CTxy triple-theta diagonal extraction (+ reindex n↦−n).
I chan_eq_10_15_Q final + bridge to the chapter's existing q-language target.
