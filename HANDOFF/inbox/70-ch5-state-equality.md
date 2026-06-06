# Task 70: Ch5 — admissible state equality / extension

In `Chapter05.lean`:

```lean
/-- Two admissible states are equal iff their added/removed finsets match. -/
@[ext] theorem AdmissibleState.ext {S T : AdmissibleState}
    (h_added : S.added = T.added) (h_removed : S.removed = T.removed) :
    S = T := by
  cases S; cases T; simp [h_added, h_removed]

theorem charge_eq_zero_iff (S : AdmissibleState) :
    charge S = 0 ↔ S.added.card = S.removed.card := by
  unfold charge; omega
```

Touch only Chapter05.lean. No axiom/sorry/native_decide. lake build clean.
