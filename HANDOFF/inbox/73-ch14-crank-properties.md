# Task 73: Ch14 — crank placeholder properties

In `Chapter14.lean`:

```lean
@[simp] theorem crankPlaceholder_one : crankPlaceholder 1 = 0 := rfl
@[simp] theorem crankPlaceholder_two : crankPlaceholder 2 = 0 := rfl
```

(Trivially true since the current crankPlaceholder is identically 0.)

Touch only Chapter14.lean. No axiom/sorry/native_decide. lake build clean.
