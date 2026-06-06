Status: done.

Modified `QseriesFormalization/Chapter09.lean` with the Bailey term/beta scaffold and proved `BaileyBeta_trivial_zero` without `axiom`, `sorry`, or `native_decide`.

Validation:

```text
lake build
Build completed successfully (7908 jobs).
```

Note: `lake build` also reported an existing warning in `QseriesFormalization/Chapter02.lean:88:8` for a declaration using `sorry`; this was outside the requested file.
