# Codex Batch C15 Reply

All five requested modules were checked in order.

## Results

- C15-1 Chapter11: requested `G_trunc_six`, `H_trunc_six`, and `R_trunc_six` are present.
- C15-2 Chapter09: requested `BaileyBeta_trivial_seven` is present.
- C15-3 Chapter16: the recipe names `mbiNumeratorTrunc` / `mbiDenominatorTrunc` do not exist in the current file. The current Chapter16 uses `mbiRHSNumeratorTrunc` / `mbiRHSDenominatorTrunc`; their N=9 theorems are present and build.
- C15-4 Chapter18: requested `tCoreDenominatorTrunc_eight` is present.
- C15-5 Chapter20: requested `etaPolyPart_ten` and `discriminantPolyPart_ten` are present.

## Verification

- `lake build QseriesFormalization.Chapter11` passed.
- `lake build QseriesFormalization.Chapter09` passed.
- `lake build QseriesFormalization.Chapter16` passed.
- `lake build QseriesFormalization.Chapter18` passed.
- `lake build QseriesFormalization.Chapter20` passed.

No `sorry`, `axiom`, or `native_decide` was added.
