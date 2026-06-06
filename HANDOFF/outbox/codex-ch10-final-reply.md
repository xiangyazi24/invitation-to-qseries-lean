# Ch10 final assessment

我读了 PDF Ch10 pp.85--94 和现有
`QseriesFormalization/Pending/Chapter10_MockTheta_PS.lean`。本轮没有改 Lean。

结论：**Ch10 不能在本 session 诚实关闭；应保持 AUX / EXCURSUS-AUX，不是 PASS。**

## 章节主目标

Chan Ch10 的主目标不是现在文件里的 third-order `f(q)`，而是第十阶 mock theta 身份：

- (10.7) `phi(q) = sum q^{n(n+1)/2} / (q;q^2)_{n+1}`
- (10.8) `psi(q) = sum q^{(n+1)(n+2)/2} / (q;q^2)_{n+1}`
- (10.10) 是 Chan 明说 “We will prove Eq. (10.10)” 的目标。

Theorem 10.1 只是桥：把 (10.10) 等价改写成四重 indefinite-theta 身份 (10.14)，再用 JTP 得到产品形式 (10.15)。Section 10.3 最后证明的是 (10.15)，然后靠 Theorem 10.1 回到 (10.10)。

所以三个选项里：

- (a) **完整 (10.10)**：最忠实，但最重；要定义 `phi/psi`、三次单位根过滤、分数幂或 `q = Q^3` 规避。
- (b) **只 formalize Theorem 10.1**：不是 PASS。它只证明等价，不证明 (10.10)。而且它本身仍要 `phi/psi`、Choi 的 Hecke-type identities (10.16)/(10.17)、theta identity (10.18) 和根单位过滤。
- (c) **mock theta definition + basic properties**：不是 PASS，而且当前文件定义的是 Ramanujan third-order `f(q)`，不是 Chan Ch10 的 tenth-order `phi/psi`。

**最简单的诚实 PASS 目标**应是：

> formalize Eq. (10.15) as the equivalent chapter-main identity, and also formalize enough of Theorem 10.1 to transport (10.15) back to Eq. (10.10).

如果只证明 (10.15) 而不证明等价桥，只能说“closed Chan's equivalent final identity”, 不能说 Ch10 PASS under the playbook. 如果只证明 Theorem 10.1，更不能 PASS，因为没有证明任一边为真。

## 为什么 Excursus / sketch 不降低 PASS 标准

Chan 在 Lemma 10.1 明说 “Let us sketch Zwegers' proof”，并把若干细节推到练习；Lemma 10.2 直接引用 Hickerson (1988), Theorem 1.5 / Ramanujan `1 psi 1`。这说明源码章节不是完全自包含，但 playbook 的 PASS 标准仍是 theorem-centric：

> chapter-main result stated + fully proved end-to-end in Lean.

Excursus 可以解释为什么保持 AUX 是合理的；不能把定义、特例、或相邻基础设施升级成 PASS。

## 当前 Lean 状态

`Chapter10.lean` 和 `Pending/Chapter10_MockTheta_PS.lean` 只覆盖：

- finite truncations of Ramanujan third-order `f(q) = sum q^{n^2}/(-q;q)_n^2`;
- formal-PS summand/partial sums for that same `f(q)`;
- low-degree coefficient checks.

代码里没有 Chan 的 `phi`, `psi`，也没有 Ch10 的 `rho_{r,s}`, `delta`, `chi_3`, Eq. (10.10), Eq. (10.14), Eq. (10.15), Lemma 10.1, Lemma 10.2。

## Precise blockers

1. **Wrong mock-theta family**: existing infra is third-order `f(q)`, while Chan Ch10 uses tenth-order `phi/psi`.
2. **No formal target yet**: Eq. (10.15)'s four-variable indefinite theta side is not even defined in Lean.
3. **Local finiteness/support proof missing**: the LHS of (10.15) is a `k,l,r,s : Z` sum with `rho_{r,s}` and exponent divided by 3; formal-PS use needs proofs that nonzero terms have integral exponent and finite support per coefficient.
4. **No Laurent/constant-term calculus**: Chan's proof uses `[x^0 y^0]` in two auxiliary variables. The repo has univariate `PowerSeries` and residue-section tools, but not the two-variable Laurent constant-term framework needed here.
5. **Lemma 10.1 not present**: the sketched theta identity (10.34) needs a formal proof or a different formal route.
6. **Lemma 10.2 not present**: Hickerson's identity (10.39), essentially a `1 psi 1`/indefinite theta identity, is not in the repo.
7. **Theorem 10.1 bridge not present**: even after (10.15), transporting back to (10.10) needs the root-of-unity filtering rewrite plus Choi identities (10.16)/(10.17) and theta identity (10.18).

The RHS product pieces are the only comparatively nearby part: the repo has JTP and `qPochInfPS` infrastructure, so the final product/theta side is plausible. The hard part is the indefinite-theta/constant-term side and the equivalence bridge.

## Verdict

Ch10 is genuinely multi-session. Minimum honest status now:

> AUX / EXCURSUS-AUX. Current code gives useful but off-target mock-theta scaffolding; Chan's tenth-order Eq. (10.10), its Theorem 10.1 bridge, and the equivalent Eq. (10.15) proof are not formalized.

No Lean code should be added here unless we are prepared to define the actual Ch10 target and close at least the (10.15) theorem plus the bridge needed for (10.10).
