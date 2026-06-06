已完成。

- 在 `QseriesFormalization/Chapter06.lean` 添加：
  - `dedekindEtaTrunc_four`
  - `dedekindEtaTrunc_five`
- 证明沿用现有 `N=1..3` 风格：`simp [dedekindEtaTrunc, qPochhammer]`
- 未使用 `axiom` / `sorry` / `native_decide`
- 验证：`lake build` 通过

备注：构建输出里仍有既有 `QseriesFormalization/Chapter02.lean` 的 `sorry` warning，但本任务修改的 `Chapter06.lean` 中没有。
