Done.

Changed `QseriesFormalization/Chapter07.lean` only for the requested Lean work:
- added `rogersRamanujanRHSTrunc_two_a0`
- added `rogersRamanujanRHSTrunc_two_a1`

Proofs use recursive unfolding by `simp [rogersRamanujanRHSTrunc]` and denominator cleanup by `field_simp` with the supplied nonzero hypotheses.

Validation:
- `lake build QseriesFormalization.Chapter07` passes.
- `rg -n "sorry|axiom|native_decide" QseriesFormalization/Chapter07.lean` has no matches.
- Full `lake build` does not pass because of existing failures outside this task:
  - `QseriesFormalization/Chapter11.lean`
  - `QseriesFormalization/Chapter16.lean`
  - existing `Chapter02.lean` sorry warning
