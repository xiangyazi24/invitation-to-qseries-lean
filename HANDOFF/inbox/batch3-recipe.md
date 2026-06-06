# Q-series Lean 4 Tasks — Batch 3 (5 tasks)

Build: `lake build`
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 82: Ch6 — dedekindEtaTrunc N=6 through N=8

In `QseriesFormalization/Chapter06.lean`, add after `dedekindEtaTrunc_five`:

```lean
theorem dedekindEtaTrunc_six (q : R) :
    dedekindEtaTrunc q 6 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_seven (q : R) :
    dedekindEtaTrunc q 7 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_eight (q : R) :
    dedekindEtaTrunc q 8 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) := by
  simp [dedekindEtaTrunc, qPochhammer]
```

## Task 83: Ch11 — G_trunc and H_trunc N=2

In `QseriesFormalization/Chapter11.lean`, add after `H_trunc_one`:

G_trunc and H_trunc are Rogers-Ramanujan products. Check their definitions in the file and compute at N=2.

```lean
theorem G_trunc_two (q : ℂ) :
    G_trunc q 2 = 1 / ((1 - q ^ 4) * (1 - q) * (1 - q ^ 9) * (1 - q ^ 6)) := by
  simp [G_trunc]
  ring

theorem H_trunc_two (q : ℂ) :
    H_trunc q 2 = 1 / ((1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 7) * (1 - q ^ 8)) := by
  simp [H_trunc]
  ring
```

Check the actual definition of G_trunc and H_trunc before writing — adjust factors to match.

## Task 84: Ch12 — R_trunc connection to G/H ratio

In `QseriesFormalization/Chapter12.lean`, add a theorem connecting R_trunc to G/H (Chan Ch 12 states R(q) = H(q)/G(q)):

```lean
/-- R_trunc q 1 expressed as a ratio matching H_trunc/G_trunc pattern at N=0. -/
theorem R_trunc_one_eq_inv_one_plus_q :
    ∀ q : ℂ, R_trunc q 1 = 1 / (1 + q) := Ch11.R_trunc_one
```

This is just a re-export. If you can prove something deeper (like R_trunc 2 = H_trunc 1 / G_trunc 1 under suitable hypotheses), add that too.

## Task 85: Ch13 — deepIdentityLHSTrunc N=2

In `QseriesFormalization/Chapter13.lean`, add after `deepIdentityLHSTrunc_one`:

```lean
/-- N=2: `1 + q/(1-q)^2 + q^4/((1-q)*(1-q^2))^2`. -/
theorem deepIdentityLHSTrunc_two (q : R) :
    deepIdentityLHSTrunc q 2 =
      1 + q / (1 - q) ^ 2 +
      q ^ 4 / ((1 - q) * (1 - q ^ 2)) ^ 2 := by
  simp [deepIdentityLHSTrunc, natSum, qPochhammer, Nat.mul_comm]
```

The n=2 term: exponent = 2*2 = 4, denominator = (qPochhammer q 2)^2 = ((1-q)(1-q^2))^2.

## Task 86: Ch8 — D_trunc N=3

In `QseriesFormalization/Chapter08.lean`, add after `D_trunc_two`:

```lean
/-- N=3 closed form for D_partialSum. -/
theorem D_partialSum_three (q : R) (a : Nat) :
    D_partialSum q a 3 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=3 closed form for D_trunc. -/
theorem D_trunc_three (q : R) (a : Nat) :
    D_trunc q a 3 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) := by
  exact D_partialSum_three q a
```

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify the specific module.
- If a proof doesn't work, try alternatives (unfold, ring, field_simp, norm_num).
- When done, write summary to `HANDOFF/outbox/gemini-batch-82-86-reply.md`.
