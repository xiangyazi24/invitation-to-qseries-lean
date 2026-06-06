Status: done

Modified `QseriesFormalization/Chapter01.lean` only. Added `partitionGenFn_ten` for `N = 10`, using the existing `partitionCount_zero` through `partitionCount_ten` lemmas.

Validation:

```text
lake env lean QseriesFormalization/Chapter01.lean
lake build
```

`lake build` final line:

```text
Build completed successfully (7908 jobs).
```

Note: `lake build` also emitted the existing warning `QseriesFormalization/Chapter02.lean:88:8: declaration uses 'sorry'`; this task did not touch `Chapter02.lean`.
