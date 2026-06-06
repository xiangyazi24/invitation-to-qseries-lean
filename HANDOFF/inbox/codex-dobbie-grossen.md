# Task: prove the Dobbie shell identity via the ℤ[i] Größencharakter (Ch15 closure)

## Goal
Close the single remaining `sorry` in
`QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean`
(theorem `pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff`, the `5∣4N+1` branch).
This is the last blocker for Chan §15 (the RRCF differential equation
`apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ)^5`).
STRICT: no `sorry`/`axiom`/`native_decide` committed. Self-verify with
`lake env lean` on the edited file. One writer; do NOT touch `QseriesFormalization.lean`/`Audit.lean`.
You MAY create a new helper file `Chapter15_Grossen.lean` and import it.

## The identity, reduced (verified numerically to q^119 and N<300)
The crux is the finite arithmetic identity, for every N with 5∣4N+1:

  L(N) := ∑_{x≡7(10), y≡9(10), x²+y²=40N+10} (-1)^{(x+y+4)/10}·(x²-y²)/8
        = R(N) := ∑_{u,v>0 odd, u²+v²=8N+2} (-1)^{(u+v-2)/2}·u·v

where R(N) = [X^N](qPochInfPS ℚ)^6 (via Jacobi P³ = ∑_{a≥0}(-1)^a(2a+1)X^{a(a+1)/2},
UNILATERAL normalization — do NOT use the bilateral sum, which is 2P³ hence 4P⁶),
and L(N) = pentagonalWronskianCoeff N is [X^N](pentagonal014·pentagonal023 + 5·Wronskian).

## THE PROOF (this is the new content — both shells are ONE multiplicative function)
Define f(k) := R((k-1)/4) for k = 4N+1 (so k ≡ 1 mod 4). Then **f is the ℤ[i]
Größencharakter / weight-3 CM newform coefficient**, VERIFIED:
- f(1)=1; f multiplicative: f(k₁k₂)=f(k₁)f(k₂) for coprime k₁,k₂≡1 mod 4.
- For p ≡ 1 mod 4, p = a²+b² (π=a+bi primary): f(p) = 2·Re(π²) = 2(a²-b²).
  Examples: f(5)=-6, f(13)=10, f(17)=-30, f(29)=42, f(37)=-70, f(41)=18.
  Hecke recursion holds: f(p^{j+1}) = f(p)·f(p^j) - p²·f(p^{j-1}).
- For p ≡ 3 mod 4 (inert in ℤ[i]): f(p^{2j}) = p^{2j}, and f(k)=0 if any such p
  divides k to an ODD power. Examples: f(9)=9, f(49)=49, f(121)=121, f(21)=0, f(77)=0.

CRUCIAL: L(N) is the SAME function (verified): L multiplicative in 4N+1, L(p)=2(a²-b²)=R(p)
for all tested p. So L=R because both are this Größencharakter.

## Formalization strategy (elementary; Mathlib has `GaussianInt = ℤ[i]` with `EuclideanDomain`/UFD)
Define the multiplicative weight directly on Gaussian integers and express BOTH shells as
the same sum, then conclude by ℤ[i] unique factorization. Concretely:

1. **Größencharakter as a Gaussian-integer sum.** For z = u+vi ∈ ℤ[i] with N(z)=u²+v² odd,
   define ψ(z) := χ₄(u)·χ₄(v)·u·v  (χ₄(t)=(-1)^{(t-1)/2} for odd t). Note ψ(z) = (1/2)·χ(z)·Im(z²)
   is invariant under the unit/conjugation action appropriately; prove
     R(N) = ∑_{z: N(z)=8N+2, u,v>0 odd} ψ(z) = (1/4)∑_{z: N(z)=8N+2, u,v odd, z over ℤ²} ψ(z)
   (the /4 from the 4 sign variants; ψ is sign-symmetric: ψ(-u,v)=ψ(u,-v)=ψ(u,v) since
   χ₄(-t)=-χ₄(t) and the u·v flips sign too — verify the cancellation).

2. **Left shell via the (2-i) reindex (a BIJECTION).** The map (u,v) ↦ (x,y)=(2u+v, 2v-u)
   [multiplication by (2-i) in ℤ[i]] is a bijection from {z odd, N(z)=8N+2, 2u+v≡7 mod 10}
   onto leftShell(N), with N(x+yi)=5·N(u+vi)=40N+10, and
     (x²-y²)/8 = (3u²+8uv-3v²)/8,   (-1)^{(x+y+4)/10} = χ₄(u)χ₄(v)  when 2u+v≡7 mod 10.
   So L(N) = ∑_{z: N(z)=8N+2, odd, 2u+v≡7(10)} χ₄(u)χ₄(v)·(3u²+8uv-3v²)/8.

3. **The core local identity (prove via ℤ[i] factorization, NOT orbit/Sturm).** Reduce both
   sides to the multiplicative function on k=4N+1 using GaussianInt unique factorization:
   representations of k by the principal form correspond to ideal factorizations; the weighted
   sum factors over primes. Prove the prime-power local factors of L and R agree (use the
   explicit f(p)=2Re(π²) for split p, f(p^{2j})=p^{2j} and 0-at-odd for inert p). Then
   multiplicativity ⟹ L(N)=R(N) for all N.

   If the full multiplicative machine is too large in one pass, the HIGH-VALUE bankable
   milestones (commit each as it lands, 0 sorry):
   (a) `coeff_P_six`: [X^N](qPochInfPS ℚ)^6 = R(N) (the unilateral Jacobi-square shell form).
   (b) `leftShell_gaussian_reindex`: L(N) = the residue-filtered (2-i) sum (pure bijection+ring).
   (c) `R_multiplicative` and/or `L_multiplicative` via GaussianInt factorization.
   (d) the prime-power evaluations f(p)=2(a²-b²), Hecke recursion, inert-prime vanishing.

## Anti-circularity (do NOT)
- Do NOT route through `apSigmaLambertFactor * expandFive = qPoch^5` or the theta-log ODE
  `θW = -6 S₁ W` — both are EQUIVALENT to the goal (circular).
- Do NOT search for a `ZMod 5` orbit action on the shell — none exists (the auto group of u²+v² is
  the order-8 dihedral group). The "5" is the (2-i) Gaussian reindex + residue filter, already given above.
- Do NOT use native_decide on the ∀N statement.

## On success
Report `#print axioms pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff` (must be the clean three),
confirm `lake env lean` passes, commit. Write progress/blockers to
`HANDOFF/outbox/codex-dobbie-grossen-reply.md`. If you cannot finish, commit every clean milestone
(a)-(d) above and report the exact remaining lemma.
