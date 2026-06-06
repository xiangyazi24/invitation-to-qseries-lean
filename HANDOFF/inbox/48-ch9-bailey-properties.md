# Task 48: Ch9 — Bailey pair small-n properties

## Goal

In `Chapter09.lean` (current state has BaileyTerm, BaileyBeta,
BaileyBeta_trivial_zero):

Add these:

```lean
/-- Trivial Bailey pair with α = δ_0: BaileyBeta is 1 at every n with proper hypotheses. -/
theorem BaileyBeta_trivial_succ (a q : R) (h_q1 : 1 - q ≠ 0)
    (h_aq1 : 1 - a * q ≠ 0) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 1 =
      1 / ((1 - q) * (1 - a * q ^ 2) * (1 - a * q)) := by
  …
```

(This is the n=1 value; you'll need to compute (q;q)_0 = 1, (q;q)_1 = 1-q,
(aq;q)_0 = 1, (aq;q)_1 = 1-aq, (aq;q)_2 = (1-aq)(1-aq²).)

If the algebra is too gnarly, deliver `BaileyTerm` simp lemmas instead.

Touch only `Chapter09.lean`. No axiom/sorry/native_decide. lake build clean.

## Deliverable

Modified file + reply.
