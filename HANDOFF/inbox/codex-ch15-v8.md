# Ch15: Close rogers_ramanujan_wronskian_cleared via 5-string proof

## The file
Edit `QseriesFormalization/Pending/Chapter15_WronskianBridge.lean`.

## The single remaining sorry
```lean
theorem rogers_ramanujan_wronskian_cleared :
    rrProductA ℚ * rrProductB ℚ +
      5 * (rrProductB ℚ * thetaOp (rrProductA ℚ) -
           rrProductA ℚ * thetaOp (rrProductB ℚ)) =
    (qPochInfPS ℚ) ^ 4 * (rrProductA ℚ) ^ 2 * (rrProductB ℚ) ^ 2
```

## Equivalent target (already proved equivalent in the file)
```lean
theorem wronskian_at_pentagonal_level :
    pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
      5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
           pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ)) =
    (qPochInfPS ℚ) ^ 6
```

The file already has `wronskian_at_pentagonal_level` proved FROM `rogers_ramanujan_wronskian_cleared` (via thetaOp_mul + C^2 cancellation), and `rogers_ramanujan_wronskian_cleared_of_pentagonal_level` in the reverse direction.

So you can prove EITHER one and derive the other.

## Available infrastructure
- `qPochInfPS_pow_six_eq_jacobiThetaPS_pow_two`: E^6 = (jacobiThetaPS)^2
- `qPochInfPS_pow_three_eq_jacobiThetaPS`: E^3 = jacobiThetaPS
- `coeff_thetaOp`: (thetaOp f).coeff n = f.coeff n * n
- `pentagonal014Coeff`, `pentagonal023Coeff`: bilateral theta series coefficients
- `pentagonalWronskianCoeff`, `jacobiThetaSquareCoeff`: computable coefficient functions
- `wronskian_at_pentagonal_level_of_coeff_identity`: reduces to ∀ N, pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N
- `pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_le_fifty`: verified through degree 50

## Proof strategy: 5-adic string grouping over representations as sums of two squares

### Setup
Set L = 4N+1. Both W_N (Wronskian coeff) and J_N (Jacobi square coeff) can be written as sums over {(A,B) ∈ Z² : A²+B² = L}:

W_N = (1/4) ∑_{A²+B²=L} K(A,B)
J_N = (1/4) ∑_{A²+B²=L} H(A,B)

where:
- H(A,B) = ε(A)(A²-B²), with ε(A) = (-1)^(A+1) for A odd
- K(A,B) = sum of Wronskian weights over the 4 unit rotations of (R,S) = (A-B,A+B) that satisfy R-2S ≡ 2 (mod 5)

### Core lemma: string identity
Let π = (1,2) and π̄ = (1,-2) as Gaussian integers (norm 5 each).
For a primitive representation g = (c,d) with c²+d² = L₀ (where L = 5^t · L₀, gcd(L₀,5)=1), form the 5-string:

w_j = π^j · π̄^(t-j) · g, for j = 0, ..., t

and the conjugate string:

w_j* = π^j · π̄^(t-j) · ḡ

The STRING IDENTITY is:
∑_{j=0}^t [H(w_j) + H(w_j*)] = K(π^t·g) + K(π^t·ḡ) = 2·ε(c)·(c²-d²)·C_t

where C_t satisfies C_0 = 1, C_1 = -6, C_{t+2} = -6·C_{t+1} - 25·C_t.

### Why this works
1. For 0 < j < t, the point w_j has both coordinates divisible by 5 (since it contains both π and π̄ as factors). So K(w_j) = 0.
2. The "wrong" endpoint π̄^t·g also gives K = 0.
3. Only the "right" endpoints π^t·g and π^t·ḡ contribute to K.
4. The Jacobi side H sees ALL string points.
5. Both sides sum to 2·ε(c)·(c²-d²)·C_t.

### Implementation plan in Lean

1. Define Gaussian integer multiplication as pairs of ℤ:
```lean
def gaussMul (a b : ℤ × ℤ) : ℤ × ℤ := (a.1*b.1 - a.2*b.2, a.1*b.2 + a.2*b.1)
def pi5 : ℤ × ℤ := (1, 2)
def piBar5 : ℤ × ℤ := (1, -2)
```

2. Define H, K as functions ℤ × ℤ → ℤ.

3. Define C_t by the recurrence.

4. Prove the string identity for each string.

5. Prove the partition of {A²+B²=L} into strings (this uses unique factorization in Z[i], but for Lean can be done via explicit Finset manipulations).

6. Sum over all strings to get W_N = J_N.

### Alternative simpler approach
If the 5-string proof is too heavy, try proving that BOTH sides satisfy the same linear recurrence:

n · E^6.coeff(n) = -6 · ∑_{k=1}^{n-1} σ₁(k) · E^6.coeff(n-k)

and similarly for the Wronskian LHS (using thetaOp properties). Then since they agree through degree 50 > any reasonable recurrence order, they are equal.

The recurrence follows from θ(E^6) = 6·E^6·(-∑nσ₁(n)X^n/(something))... but deriving the Wronskian's recurrence independently is the hard part.

## Build
```bash
export PATH=$HOME/.elan/bin:$PATH
lake env lean QseriesFormalization/Pending/Chapter15_WronskianBridge.lean
```

Reply to HANDOFF/outbox/codex-ch15-v8-reply.md
