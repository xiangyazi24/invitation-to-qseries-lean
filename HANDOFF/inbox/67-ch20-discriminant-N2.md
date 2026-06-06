# Task 67: Ch20 — discriminantPolyPart N=2 explicit

In `Chapter20.lean`:

```lean
theorem etaPolyPart_two (q : R) :
    etaPolyPart q 2 = (1 - q) * (1 - q^2)

theorem discriminantPolyPart_two (q : R) :
    discriminantPolyPart q 2 = q * ((1 - q) * (1 - q^2))^24
```

Touch only Chapter20.lean. No axiom/sorry/native_decide. lake build clean.
