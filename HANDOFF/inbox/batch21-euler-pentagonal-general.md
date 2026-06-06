# Batch 21: Euler Pentagonal Truncated Identity for All N

## Context
Chapter03.lean already has `finite_jacobi_triple_product` (line 731):
```lean
theorem finite_jacobi_triple_product (q z : R) (hz : z ≠ 0) (hq : q ≠ 0) (n : Nat) :
    qPoch z q n * qPoch (z⁻¹ * q) q n = finiteJTPRHS q z n
```

Chapter04.lean has pentagonal cases for N=1,2,3. The goal: derive the general Euler pentagonal truncated identity by specializing the finite JTP at z=1.

## Task: Prove the general truncated pentagonal identity

The pentagonal number theorem (truncated) says:
```
(q;q)_n = ∑_{k=-n}^{n} (-1)^k q^{k(3k-1)/2} * [2n choose n+k]_q
```
This follows from `finite_jacobi_triple_product` at z=1 (noting z⁻¹*q = q when z=1).

### Step 1: Specialize finite JTP at z=1
```lean
theorem finite_jtp_at_z_one (q : R) (hq : q ≠ 0) (n : Nat) :
    qPoch 1 q n * qPoch q q n = finiteJTPRHS q 1 n := by
  have := finite_jacobi_triple_product q 1 one_ne_zero hq n
  simpa using this
```

### Step 2: Simplify qPoch(1,q,n)
Note `qPoch 1 q n = ∏_{k=0}^{n-1}(1-q^k) = qPochhammer q n`.
```lean
theorem qPoch_one_eq_qPochhammer (q : R) (n : Nat) :
    qPoch 1 q n = qPochhammer q n := by
  induction n with
  | zero => simp [qPoch, qPochhammer]
  | succ m ih => simp [qPoch_succ, qPochhammer_succ, ih]; ring
```

### Step 3: Connect to pentagonal numbers
Show `finiteJTPRHS q 1 n` simplifies to the pentagonal number sum.

## File: QseriesFormalization/Chapter04.lean
Insert after existing pentagonal theorems.

## Constraints
- No sorry, no axiom, no native_decide
- `lake build QseriesFormalization.Chapter04` must pass
- Must import Chapter03 (already imported)
- Work within `section Field` / `variable {R : Type*} [Field R]`

## Build command
```
lake build QseriesFormalization.Chapter04
```
