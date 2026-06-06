# Task: close Ch15 via the 5-Hecke recurrence (cleanest finish)

## Status
`string_scalar_identity` and the local Gaussian-string lemmas are committed (good).
The remaining gap is the GLOBAL shell coverage. Use the **recurrence route** (option 2 from
your own reply) — it avoids the no-overlap partition proof.

## The verified target (numerically confirmed for BOTH sides, M=4N+1<400)
Let S_left(M) = the pentagonal selected sum and S_right(M) = (1/4)·Jacobi shell sum, i.e.
  S_left(M)  = ∑_{c²+d²=M, d≡3c-2 (5)} (-1)^{c-1}·(c²-d² - (3/2)cd)        = pentagonalWronskianCoeff N
  S_right(M) = (1/4)∑_{c²+d²=M} (-1)^{c-1}·(c²-d²)                          = jacobiThetaSquareCoeff N
(M = 4N+1.) BOTH satisfy the same recurrence:

  **S(5M) = -6·S(M) - 25·S(M/5)**      (the (M/5) term present only when 5∣M).

VERIFIED: holds for S_left and S_right, all M=4N+1<400; and S_left(M)=S_right(M) throughout.
This is the Hecke relation at the split prime 5 = (2+i)(2-i): coefficient -6 = f(5), 25 = 5².

## Proof to formalize
1. `S_right_recurrence (M) : S_right (5*M) = -6*S_right M - 25*S_right (M/5)` (M/5 term guarded by 5∣M).
   Proof: every Gaussian rep z of norm 5M factors as (2+i)·z' or (2-i)·z' (z' norm M), plus reps from
   norm-5²M' when 5²∣5M; the weighted sum telescopes. Use piMul/pibarMul (norm ×5), the string
   lemmas, and `string_scalar_identity`. This is pure ℤ[i] arithmetic (Mathlib GaussianInt UFD).
2. `S_left_recurrence (M)` : same recurrence for the pentagonal selected sum. The selector
   d≡3c-2 mod 5 + interior-vanishing (`fiveStringPoint_interior_unitConjOrbitK_zero`) gives the same
   telescoping; endpoints via `string_scalar_identity`.
3. **Base case**: for 5∤M, S_left(M)=S_right(M) is the ALREADY-PROVED `_of_t0` branch
   (`pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_t0`).
4. **Strong induction** on the 5-adic valuation of M (= padicValNat 5 (4N+1)):
   `S_left(M)=S_right(M)` for all M. Concretely induct on k where M = 5^k·M₀, 5∤M₀:
   k=0 is the base case; step uses both recurrences with equal S(M), S(M/5).
5. This closes the `5∣4*N+1` branch of `pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff`.

## Discipline
STRICT: 0 sorry / 0 axiom / NO native_decide in committed proofs. Self-verify `lake env lean`.
Edit only Chapter15_WronskianIndependent.lean (+ new helper file if useful). Commit each clean
milestone: (1) S_right_recurrence, (2) S_left_recurrence, (3) the induction closing the branch.
On success: `#print axioms pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff` must be clean three.
Write HANDOFF/outbox/codex-dobbie-recurrence-reply.md (proved, or exact remaining sub-lemma).
