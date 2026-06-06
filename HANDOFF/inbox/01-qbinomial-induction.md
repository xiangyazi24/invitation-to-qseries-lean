# Task 01: extend `finiteQBinomialTheorem` to all `n`

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.
**The whole project must `lake build` clean** when you finish. Run it.

## Background

The file `QseriesFormalization/Chapter03.lean` defines:

```lean
def qBinomialLHS (q x : R) : Nat → R
  | 0 => 1
  | Nat.succ n => qBinomialLHS q x n * (1 + x * q ^ n)

def qBinomialTerm (q x : R) (n k : Nat) : R :=
  gaussianBinom q n k * q ^ (k * (k - 1) / 2) * x ^ k

def qBinomialRHS (q x : R) (n : Nat) : R :=
  natSum (fun k => qBinomialTerm q x n k) n
```

(`gaussianBinom`, `natSum` are defined in `QseriesFormalization/Basic.lean`.)
Working over `[CommSemiring R]` (current setting). If you genuinely need
`[CommRing R]` for the proof, you may strengthen the typeclass — but please
keep it as weak as possible.

The statement currently proved is the **base range only**:

```lean
theorem finiteQBinomialTheorem (q x : R) (n : Nat) (hn : n ≤ 1) :
    qBinomialLHS q x n = qBinomialRHS q x n := …
```

## Goal

**Replace** the hypothesis `n ≤ 1` and prove the theorem for **all** `n : Nat`:

```lean
theorem finiteQBinomialTheorem (q x : R) (n : Nat) :
    qBinomialLHS q x n = qBinomialRHS q x n
```

This is **Theorem 3.2** of Hei-Chi Chan, *An Invitation to q-Series* (the
finite q-binomial theorem). Mathematically it is

`∏_{k=0}^{n-1} (1 + x q^k) = ∑_{k=0}^{n} [n, k]_q q^{k(k-1)/2} x^k`.

## Suggested approach

1. Prove a q-Pascal recursion lemma:
   `gaussianBinom q (n+1) k = gaussianBinom q n k + q^(n-k+1) * gaussianBinom q n (k-1)` (for `1 ≤ k ≤ n+1`).
   Note our defining recursion is the cousin
   `gaussianBinom q (n+1) (k+1) = gaussianBinom q n (k+1) + q^(n-k) * gaussianBinom q n k`.
2. Prove the diagonal `gaussianBinom q n n = 1`.
3. Prove the "out-of-range" vanishing `gaussianBinom q n k = 0` for `k > n` (likely needed; you may need an auxiliary `natSum` re-indexing lemma instead).
4. Induction on `n`. The inductive step uses
   `qBinomialLHS q x (n+1) = qBinomialLHS q x n * (1 + x * q^n)` (definitional)
   and the IH to expand `qBinomialRHS q x n * (1 + x * q^n)`, then match
   coefficients with `qBinomialRHS q x (n+1)` via the q-Pascal identity.
5. Update `QseriesFormalization/Exercises.lean` (it currently calls
   `finiteQBinomialTheorem … (by simp)` to discharge `n ≤ 1`; remove the
   hypothesis at call sites).

You may add helper lemmas — keep them in `Chapter03.lean` (or `Basic.lean`
if they're truly generic about `gaussianBinom` / `natSum`).

## Constraints

- **No `axiom` and no `sorry`** in the final code. Per project policy
  (爸爸: "all axioms are to be eliminated").
- `lake build` must end "Build completed successfully" with zero error.
- You may freely use Mathlib lemmas and tactics (`ring`, `simp`, `omega`,
  `nlinarith`, `induction`, etc.).
- If you genuinely cannot close the proof, **don't fabricate** — leave a
  detailed note in the reply describing exactly where you got stuck (which
  goal, which subgoal, what tactic state).

## Deliverable

1. Modified files in the repo (commit them to a feature branch named
   `task-01-qbinomial` if convenient; otherwise just leave the working
   tree changed and the dispatcher will see the diff).
2. A reply file (path is mandated by the dispatcher) with:
   - Status: completed / blocked.
   - Summary of what changed (files + lemmas added/modified).
   - `lake build` final line.
   - If blocked: the exact subgoal you were stuck on.
