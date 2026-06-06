# UNDERSTANDING.md — Q-series Formalization

Session 启动后先读这个文件恢复上下文。

## 状态总览（2026-06-01 更新）

**整个库 0 sorry / 0 axiom（latest full build: `lake build QseriesFormalization`, 8011 jobs, 2026-06-01）。**

### Playbook audit per-chapter status (per `PLAYBOOK_AUDIT.md` end-of-day 2026-05-27, + 05-30 updates)

- ✅ PASS (17/20): Ch01, 02, 03, 04, 05, 06, 07, 08, 09, 11, 12, 13, 14, 16, 17, 18, 19.
- 🟡 AUX (3): Ch10, Ch15, Ch20 (details below).
- ❌ SHADOW (0), 🔀 MISLABELED (0).

### Ch20 theorem list after tau consolidation (2026-06-01)

Ch20 remains AUX for the full analytic/modular-form story (Ono/half-integral
weight modular forms are still out of reach), but the formal-PS and finite
Ramanujan-tau layer is now substantially stronger:

- **Tau values:** `ramanujanTau_zero`, `ramanujanTau_one`, ...,
  `ramanujanTau_fifty`.
- **Bounded Hecke/multiplicativity:**
  `ramanujanTau_mul_of_coprime_mul_le_50` and
  `ramanujanTau_hecke_prime_power_le_50`, plus the named small instance
  checks already in the file.
- **Log-derivative recurrence:**
  `ramanujanTau_log_derivative_recurrence`
  (`((n : Z) - 1) * tau(n)` equals the divisor-sum convolution for all
  `n >= 2`).
- **Parity theorem:** `ramanujanTau_mod_two_eq_one_iff_odd_square`,
  `ramanujanTau_odd_iff_odd_square_param`,
  `ramanujanTau_odd_iff_odd_square`.
- **Mod-691 finite verification:** `sigma11` and
  `ramanujanTau_congr_sigma11_mod_691_through_fifty`.

### Ch11/Ch13 progress (2026-05-30 session)

**Ch11 — Thm 11.1 (`rrcf_r_via_CF = rrcf_r`) coefficient verification extended:**

1. **CF-side coefficients** (`Chapter11_RRCF_Convergent.lean`, build-graph-external):
   Extended from degrees 0-1 to **degrees 0-20**. Key results:
   `rrcf_r_via_CF.coeff k` for `k = 0..20`:
   `[1, -1, 1, 0, -1, 1, -1, 1, 0, -1, 2, -3, 2, 0, -2, 4, -4, 3, -1, -3, 6]`.
   Proof method: `rrcf_RPS_mul_APS` (denominator-cleared product identity)
   + Cauchy product coefficient extraction + recurrence.

2. **Product-side coefficients** (`Chapter11_Thm111.lean`, new, Pending):
   - Pentagonal series coefficients at degrees 1-5 for both pentagonal014
     and pentagonal023 (10 theorems, proved via series definition + `norm_cast`).
   - Formal inverse `(pentagonal023SeriesPS ℚ)⁻¹` at degrees 0-5
     (6 theorems, proved via `PowerSeries.coeff_inv` recurrence).
   - `rrcf_r.coeff k` at degrees 0-5 (6 theorems, via Cauchy product).
   - **11 unconditional coefficient matches**: `rrcf_r.coeff k = rrcf_r_via_CF.coeff k`
     for `k = 0..10` (product side computed to degree 10).

3. **Analysis of full-proof approach**: Attempted recurrence-based induction
   (`E_n := rrcf_r · A_n - B_n` satisfies same recurrence as convergents).
   **Result: INSUFFICIENT.** The recurrence `E_{n+2} = E_{n+1} + X^{n+2}·E_n`
   only preserves constant X-adic valuation bounds, not the quadratic
   `tri(n+1)` growth needed. Full proof requires Rogers-Ramanujan identity
   in formal PS (connecting `rrJInf`/Bailey pair to pentagonal products).

**Ch13 — Thm 11.5 Watson algebraic framework:**

4. **Watson polynomials** (`Chapter13_Watson_Algebraic.lean`, new, Pending,
   0 sorry): 20 ring-identity lemmas about `A(v) = 1-2v+4v²-3v³+v⁴` and
   `B(v) = 1+3v+4v²+2v³+v⁴`: product, sum, difference `A-B = -5v(1+v²)`,
   coefficient reversal `Rev(A) = B(-v)`, evaluations. All by `ring`.

5. **Coefficient verification** (`Chapter13_CoeffVerification.lean`, new,
   Pending): `rrcf_v` coefficients at degrees 0-6 proved; pentagonal and
   inverse coefficients; `rrcf_r.coeff 0,1` proved. Some sorry stubs remain
   for higher-degree identity verification.

6. **Watson central identity is NOT a polynomial identity** — verified by
   Python that `(v⁻¹-1-v)⁶ ≠ (v⁻⁵-11-v⁵)·v·A·B` as formal Laurent
   polynomials. Watson's proof requires Theorems 11.1 → 11.3 → Eq 12.37
   as prerequisites.

### Critical path for Ch11 Thm 11.1

The Rogers-Ramanujan identity as formal PS:
`∑_{n≥0} X^{n²}/(X;X)_n = 1/pentagonal023SeriesPS` (G(q) side)
`∑_{n≥0} X^{n(n+1)}/(X;X)_n = 1/pentagonal014SeriesPS` (H(q) side)

Assembly path: Ch09 `rrAlpha`/`rrBeta` Bailey pair → specialize parameters
→ finite RR identity → formal-PS limit → `rrJInf ↔ pentagonal products`
→ CF functional equation → `rrcf_r = rrcf_r_via_CF`.

Key infrastructure available: `BaileyTransform_preserves_pair_unconditional`
(Ch09/BaileyqPS.lean), `rrJInf` + functional equation (Ch07), JTP (Ch02/03).

### 本 session 成果 (2026-05-27 session)

**Ch11 RRCF convergence machinery + Ch15 MISLABELED resolved + Ch20 Hecke extension:**

1. **Ch15 MISLABELED → AUX**: `Pending/Chapter15_R_ODE.lean` with precise
   Chan §15 Theorem 11.7 / Eq 15.8 stated as sorry-stub. Includes
   `legendre5`, `chan15LHSPS`, the multiplicative form `chan15LHSPS ·
   expand5 qPochInfPS = qPochInfPS^5`.

2. **Ch11 RRCF convergence infrastructure** (12 new theorems):
   - BUGFIX yesterday's `rrcf_A/B/T` base cases (was computing wrong CF).
   - Correct backward recurrence with `rrcf_A 1 = 1+X`, `rrcf_B 0 = 1`.
   - Both scalar (`rrcf_A/B/T q : ℂ`) and formal-PS (`rrcf_APS/BPS/TPS/RPS`)
     versions; explicit values at small n.
   - **CF cross-determinant identity** (`rrcf_cross_det_PS`):
     `A_{n+1}·B_n − A_n·B_{n+1} = (−1)^n · X^{(n+1)(n+2)/2}` proved by
     induction.
   - **Multiplicative diff formulas**: `(T_{n+1}−T_n)·B_n·B_{n+1} =
     (−1)^n·X^{(n+1)(n+2)/2}` and analogue for R.
   - **X-adic divisibility**: `X^{(n+1)(n+2)/2} ∣ (T_{n+1}−T_n)` and R.
   - **Coefficient stabilization**: for `n ≥ k`,
     `(rrcf_TPS (n+1)).coeff k = (rrcf_TPS n).coeff k` (concrete Cauchy).
   - **`rrcf_r_via_CF`**: defined as `PowerSeries.mk (fun k => (rrcf_RPS k).coeff k)`
     — the X-adic limit of the convergents, well-defined by stabilization.
   - Chan §11 chapter-main reduced to: `rrcf_r_via_CF = rrcf_r` (open).

3. **Ch20 Hecke extension**:
   - 4 new prime-power Hecke recursion instances (p=2 at k=3,4; p=3 at k=1,2;
     p=5 at k=1) on top of existing (p=2 at k=1,2).
   - 5 new Hecke multiplicativity instances: (2,9)→τ(18), (3,7)→τ(21),
     (2,11)→τ(22), (3,11)→τ(33), (2,17)→τ(34), (5,7)→τ(35).
   - τ values extended to τ(35).

### 之前 session 成果 (2026-05-26 session: Ch10/11/12/13/Ch15 SHADOW/MISLABELED eliminated)

### 本 session 成果 (2026-05-26 session)

**Multi-day frontier landed + Ch13 SHADOW → AUX:**

1. **Committed 100+ files of staged work** (2026-05-17..05-25, multi-agent):
   Ch01 p(0)..p(54) partition values + GenFun bridge; Ch05 Boson-Fermion JTP;
   Ch06 Macdonald A1 (Jacobi cube); Ch08 Thm 8.1 (a=0,1); Ch09 Bailey
   unconditional via lemma91_operator; Ch14 Thm 11.6 closed; Ch16 MBI
   unconditional; Ch17 all three Ramanujan congruences + ASD η-quotient
   mod 5/7; Ch19 formal-PS Ramanujan framework; Ch20 τ(0)..τ(15) +
   τ-parity. Build 8003 jobs, clean-3 axioms.

2. **PLAYBOOK_AUDIT.md updated** (2026-05-22 → 2026-05-26): per-chapter
   verdict table refreshed; summary count 8 PASS → 13 PASS (+5),
   SHADOW 4 → 2 (−2).

3. **Ch13 SHADOW → AUX**: 9 new theorems on `rrcf_r := pentagonal014SeriesPS·
   pentagonal023SeriesPS⁻¹` over ℚ⟦X⟧:
   - `coeff_zero_pentagonal{014,023}SeriesPS_rat = 1` (both bilateral
     pentagonal AP series have constant term 1 — k=0 contribution).
   - `isUnit_pentagonal023SeriesPS_rat` (the denominator is a unit).
   - `rrcf_r_mul_pentagonal023SeriesPS_eq` (defining algebraic relation,
     no fake division).
   - `rrcf_v_mul_expand_pentagonal023SeriesPS_eq` (image under `expand 5`).
   - `coeff_zero_rrcf_v_eq_zero` (rrcf_v vanishes at X=0).
   - `isUnit_rrcfDenom{LHS,RHS}` (both quartic-in-rrcf_v denominators
     are units in ℚ⟦X⟧).
   - Chan Thm 11.5 stated precisely in `Pending/Chapter13_DeepIdentity.lean`
     as `chan_theorem_11_5` (sorry-stub, NOT imported into main build,
     proof requires Gugg telescoping — multi-session).
   All theorems clean-3 axioms.

### 之前 session 成果 (2026-05-22 session: Ch19/20 formal-PS Ramanujan)

**主线：Ch19/20 formal-PS Ramanujan framework**

1. **Ch19 算法核心 (formal power series)**
   - `partitionGenFun R : R⟦X⟧` (Mathlib `Nat.Partition.genFun`)
   - `qPochInfPS R : R⟦X⟧ = invOfUnit partitionGenFun 1` (formal `(q;q)∞`)
   - `partitionGenFun_mul_qPochInfPS : J · (q;q)∞ = 1`
   - `powerSeries_charP`: `CharP (R⟦X⟧) p` inherited from `CharP R p`
   - `PowerSeries.expand_eq_pow_zmod`: in `(ZMod p)⟦X⟧`, `expand p f = f^p` (Frobenius)
   - `ramanujan_key_identity`: in `(ZMod p)⟦X⟧`, `J · expand_p (q;q)∞ = (q;q)∞^(p-1)`
   - `coeff_mul_expand_of_lt`: `(f · expand_p g).coeff (p·n+r) = ∑_{k=0}^n f.coeff(p(n-k)+r) · g.coeff k`
     (via `Finset.sum_bij'` on the antidiagonal)

2. **Ch19 Conditional Ramanujan (通用 prime)**
   - `ramanujan_from_pochInf_vanishes p hp r hr hvanish`: if `(q;q)∞^(p-1)` vanishes
     on `p·n+r` for all n, then `p(p·n+r) ≡ 0 (mod p)` for all n. Strong induction.
   - 三个 corollaries: `ramanujan_mod_5/7/11_conditional` at (p, r) = (5, 4), (7, 5), (11, 6).

3. **Ch19 N=0 bridge**
   - `coeff_pochInfPow_eq_partitionCount_of_lt`: for `r < p`,
     `((qPochInfPS (ZMod p))^(p-1)).coeff r = (p(r) : ZMod p)`.
     Derived from `coeff_mul_expand_of_lt` at n=0 (sum collapses to k=0 term).

4. **Ch19 qPochInfPS / partitionGenFun coefficient lemmas**
   - `coeff_{zero,one,two,three,four,five,six}_qPochInfPS`: 1, -1, -1, 0, 0, 1, 0
     (Euler pentagonal small coefficients, derived from `J · qPoch = 1` recurrence)
   - `coeff_{zero,one,two,three,four,five,six}_partitionGenFun`: 1, 1, 2, 3, 5, 7, 11

5. **Ch20 Formal modular forms**
   - `etaPS R : R⟦X⟧ = qPochInfPS R` (no q^{1/24} prefactor)
   - `discriminantPS R := X · (etaPS R)^24`
   - `ramanujanTau R n := (discriminantPS R).coeff n`
   - `etaPS_isUnit`, `discriminantPS_not_isUnit`, `etaPS_mul_partitionGenFun = 1`
   - **τ values**: τ(0)..τ(8) = 0, 1, -24, 252, -1472, 4830, -6048, -16744, 84480 (OEIS A000594)
   - **τ multiplicativity**: `ramanujanTau_mul_two_three`: τ(6) = τ(2)·τ(3)
   - **τ Hecke relations**: `ramanujanTau_hecke_two_one` (τ(4) = τ(2)²-2¹¹·τ(1)),
     `ramanujanTau_hecke_two_two` (τ(8) = τ(2)·τ(4)-2¹¹·τ(2))
   - **τ prime congruences**: τ(2,3,5,7) ≡ 0 (mod 2,3,5,7)

6. **Ch20 Unconditional Ramanujan n=0 trio**
   - `coeff_{n}_pow_of_constantCoeff_one` helpers for n=1..6 (binomial expansion of f^k.coeff n)
   - `coeff_four_qPochInf_pow_four = -5` → `ramanujan_partition_four_mod_five`
   - `coeff_five_qPochInf_pow_six = 0` → `ramanujan_partition_five_mod_seven`
   - `coeff_six_qPochInf_pow_ten = 0` → `ramanujan_partition_six_mod_eleven`
   - 三个 unconditional, all derived from formal-PS framework (not direct partition count).

7. **Ch14 Andrews-Garvan crank statistic**
   - `crankOnes`, `crankMu`, `crankLargest`, `crank : Nat.Partition n → Int` 定义
   - `crank_singleton (n) (hn : 2 ≤ n) : crank ⟨{n}, ..⟩ = n`
   - `crank_allOnes (n) (hn : 1 ≤ n) : crank ⟨replicate n 1, ..⟩ = -n`
   - `crankDistMod5OfFour : Multiset (ZMod 5)` — distribution at n=4 defined

8. **Ch19 formal Euler product** (UNCONDITIONAL, 本 session 主战果)
   - `partitionGenFun_eq_tprod`: `partitionGenFun R = ∏' i, (1 + ∑' j, X^((i+1)(j+1)))`
     用 Mathlib 的 `Nat.Partition.genFun_eq_tprod`. R 需要 `[TopologicalSpace R] [T2Space R]`.
   - `multipliable_one_sub_X_pow_succ`: Mathlib 的 `multipliable_one_sub_X_pow` 包装.
   - `factor_geom_series_identity`: `(1 + ∑' j, X^((i+1)(j+1))) · (1 - X^(i+1)) = 1` in R⟦X⟧.
     证明用 `mk_one_mul_one_sub_eq_one` + `PowerSeries.expand (i+1)` ring hom +
     `Summable.map_tsum` for coefficient extraction.
   - **`qPochInfPS_eq_tprod`**: `qPochInfPS R = ∏' i, (1 - X^(i+1))`. 
     这是 `(q;q)_∞ = ∏(1-q^n)` 的 formal power series 版本, UNCONDITIONAL.

9. **Ch20 modular discriminant formal Euler product**
   - `discriminantPS_eq_X_mul_etaPS_pow_24`: `discriminantPS R = X · η^24` (rfl).
   - **`discriminantPS_eq_X_mul_tprod_pow_24`**: `discriminantPS R = X · (∏'(1-X^(n+1)))^24`.
     这是 Ramanujan tau generating function 的 formal Euler product 表达, UNCONDITIONAL.
   - `ramanujanTau_eq_coeff_X_mul_tprod_pow_24`: ramanujanTau 显式表达为 coeff of formal Euler product.
   - `map_etaPS`, `map_discriminantPS` 在 ring hom 下 naturality.
   - **`cast_ramanujanTau_int`**: `((ramanujanTau ℤ n : ℤ) : R) = ramanujanTau R n`.
     Ramanujan τ 是 canonical integer-valued sequence。

10. **Ch19 partial product stabilization**
    - `partial_prod_one_sub_X_pow_succ_coeff_stable`: 对 k ≤ N,
      `(∏_{i<N+1}(1-X^(i+1))).coeff k = (∏_{i<N}(1-X^(i+1))).coeff k`.
    - `partial_prod_one_sub_X_pow_succ_coeff_eq`: 扩展到任意 M ≥ N
    - **`coeff_tprod_one_sub_X_pow_succ`**: tprod 和 partial product 在低系数一致
    - **`coeff_qPochInfPS_eq_coeff_finite_product`**: qPochInfPS 的 coefficient
      可由有限多项式乘积计算 (closed-form formal Euler product)。
    - **`coeff_qPochInfPS_pow_eq_coeff_finite_product_pow`**: 推广到 `(qPochInfPS R)^e`，
      用 `PowerSeries.trunc_trunc_pow` 实现。

11. **Ch20 A1 bridge to finite Euler product** (Ripple-compatible form)
    - **`ramanujanTau_eq_coeff_finite_product`**: τ(n) = (X · (∏_{i<N}(1-X^(i+1)))^24).coeff n
    - **`ramanujanTau_eq_coeff_prod_of_pow`**: τ(n) = (X · ∏_{i<N}(1-X^(i+1))^24).coeff n
      (匹配 Ripple's `deltaEulerCoeffZ` 定义)

12. **Ch19 B1 Step 1 + 2: Euler Pentagonal Number Theorem as formal PS** 🎯
    - Step 1: `coeff_qPochInfPS_eq_signedStrictCount` (via `Nat.Partition.genFun`).
    - Step 2: bridge `signedStrictCount` to Ch05 via `Finset.sum_nbij'`.
    - **`coeff_qPochInfPS_int_eq_pentagonalSign`**:
      `(qPochInfPS ℤ).coeff n = pentagonalSign n` for ALL n.
    - **`coeff_qPochInfPS_eq_pentagonalSign`**: 推广到 any CommRing R via cast.
    - **意义**: 经典 Euler 五边形数定理作为 formal-PS identity. **Unconditional.**

13. **Ch19 B2 groundwork**: `jacobiTripleSign n` + `jacobiThetaPS R` defined.
    Target `(qPochInfPS R)^3 = jacobiThetaPS R` left for future work
    (needs Sylvester-style combinatorial proof or analytic-formal bridge).

14. **`QseriesFormalization/Audit.lean`** (本 session 创建)
    - Runs `#print axioms` on 24+ flagship theorems across Ch02/03/04/14/17/19/20.
    - All formal-PS framework theorems: clean `{propext, Classical.choice, Quot.sound}`.
    - Final Euler pentagonal inherits `Lean.ofReduceBool` via Ch05's native_decide.
    - Honest audit per playbook criterion #11.

15. **Ch19 explicit Ramanujan convolution formula**
    - `coeff_qPochInfPS_pow_p_in_ZMod_p`:
      `((qPoch ZMod p)^p).coeff n = if p ∣ n then (pentagonalSign (n/p) : ZMod p) else 0`
    - `coeff_qPochInfPS_pow_pred_at_AP`:
      `((qPoch ZMod p)^(p-1)).coeff (p·n+r) =
         ∑_{k<n+1} (p(p·(n-k)+r) : ZMod p) · (pentagonalSign k : ZMod p)`
    - 这是经典 Ramanujan 证明的 explicit form, 集 Frobenius + Euler pentagonal
      + coeff_mul_expand_of_lt 于一身.

16. **Ch20 B2 small cases**: (qPoch R)^3 . coeff n for n = 1, 2, 3, 4, 5, 6 verified
    matching `jacobiTripleSign n`. Concrete unconditional verifications of the
    Jacobi triple product at z=1, in any commutative ring.

**Modular form 接口路径 (剩余)**:
- Mathlib v4.27 已有 `ModularForm.discriminant : ℍ → ℂ = η^24` + `CuspForm.discriminant : CuspForm 𝒮ℒ 12`
- 闭环只剩: `(ModularForm.discriminant).qExpansion = discriminantPS ℂ` (need Dedekind eta q-expansion principle in Mathlib).
  Mathlib 还没显式证 η 的 q-expansion identity 作为 formal power series。

**剩余开放问题**:
- Full Ramanujan for all n: need Euler pentagonal / Jacobi triple product as formal PS
  (analytic versions in Ch04 done; lifting to R⟦X⟧ requires Franklin combinatorial generality
  which Ch05 has only at small n via native_decide)
- τ(8), τ(9), ... : need coeff_seven_pow, coeff_eight_pow, ... helpers (shape count grows rapidly)
- τ multiplicativity at (2,5): need τ(10), which needs coeff_nine_pow with 30 shapes
- Crank generating function bridge: connect `crank` statistic to `crankGenTrunc` from earlier in Ch14

### 之前 session 成果 (2026-05-19 session 5)
1. **Ch09 §9.2 Lemma 9.1 基础设施** — 修复 + 新证 [当时还有 1 sorry，本 session 已闭环]
   - **修复 `lemma91Target_recurrence`**：原来 `rw [qPoch_succ, qPoch_succ_shift]` 两步 rewrite 冲突，改用 `qPoch_xq_succ_shift` 一步到位 + `field_simp` + `linear_combination` 关闭
   - **修复 `rrAStar_one` / `rrAStar_two`**：simp 已关闭 goal，多余 `ring` 导致 "no goals" 错误
   - **修复 N=1,2,3 base cases**：`simp only` 添加 `sum_range_zero` + 修复 `field_simp` 假设匹配（`x*q*q` vs `x*q^2` 归一化问题）
   - **`lemma91Base_recurrence` 证明框架**（`scratch_lemma91.lean`）——数学推导完整，Lean 证明结构已写好，待编译验证

2. **scratch_franklin.lean 已全部证完**（上 session 遗留）
   - `euler_pentagonal_combinatorial` 和 `fixed_sum_eq_pentagonalSign` 均 0 sorry

### 当前攻坚: `lemma91Base_recurrence`（Ch09 唯一 sorry）
- **数学**：Gaussian binomial 递推 [N+1;k+1] = [N;k+1] + q^{N-k}[N;k] 拆 sum → 一半重组回 `lemma91Base x q N`，另一半 factor 出 `xq^{N+1}/(1-xq)` 得 `lemma91Base (xq) q N`
- **Lean 证明**在 `scratch_lemma91.lean`，分 5 步：
  1. `sum_range_succ'` 剥 k=0
  2. GB recurrence + `sum_add_distrib` 拆 sum
  3. `mul_sum` factor 常数
  4. `sum_range_succ` + `gaussianBinom_eq_zero_of_lt` 去零项
  5. `sum_range_succ'` + `ring` 匹配 add_comm
- **helper lemma** `shift_term_eq` 证每项 q^{N-k} 贡献等于 shifted 版：用 `qPoch_xq_succ_shift` + `pow_add` + `omega` + `ring`
- **状态**：框架已写完，等 build 验证（N=2/N=3 修复后 rebuild 进行中）

### 之前成果
- Session 4 (2026-05-18): Franklin involution 数学内容全部证完
- Session 3 (2026-05-17): Franklin involution 重建到 4 sorry
- Session 1-2 (2026-05-17): BaileyqPS.lean (17 theorems), Ch05_Franklin 启动

### ChatGPT Bridge
- 每个窗口只用自己的 channel (research 用 `--channel research`)
- Pro 模式 30 min timeout, 垃圾回答自动 reset+重试
- 调用: `CHATGPT_CHANNEL_GUARD=0 ~/repos/chatgpt-bridge/ask-chatgpt.sh --pipe --channel research --stdin < /tmp/query.md`
- 读回答: `cat /tmp/chatgpt-bridge/<task_id>.md`

## 项目概况

Lean 4 + Mathlib v4.27.0 形式化 Hei-Chi Chan 的书 *An Invitation to q-Series*（20 章）。Chan 是爸爸的 UIS 同事。目标：全书每章每个习题都形式化。

## 当前状态（2026-05-17）

- **146,701 行代码，~19,000 个 declarations，全部 `lake build` 通过**
- `Exercises.lean`: 7194 行，933 个 declarations
- **0 个 `sorry`**（Ch05_Franklin.lean 有 sorry 但不在 build graph）
- 20 个 chapter 文件 + Basic.lean + BaileyqPS.lean + Ch07_RR*.lean + Ch05_Franklin.lean

## 各章覆盖度

| Ch | Lines | Decls | 内容 | 状态 |
|----|-------|-------|------|------|
| 01 | 6653 | 54 | 分拆函数 p(0..11)，生成函数截断 | 完整 |
| 02 | 755 | 66 | Jacobi Triple Product foundations; product `Multipliable`/`HasProd`, Nat-indexed product factorization and component split, finite product/series partial convergence, even-factor qPoch limit/nonzero package, symmetric series pair expansion, two-term norm majorant, and tail `HasSum`/`tsum` package, product/series/difference functional equations, bilateral series `Summable`/`HasSum`, and `q=0` case | 完整 |
| 03 | 1523 | 98 | Gaussian polynomials, q-binomial, finite JTP, centered Gaussian q-Pochhammer forms, fixed symmetric partial coefficient and tail limits, zero-extended Gaussian tail summands, fixed-pair tail splitting, weighted Laurent reindexing, Ch02 finite-product bridge, centered finite-product core+tail form, uniform Gaussian coefficient bounds, tail majorant domination, and full JTP proof exported as `Ch02.jacobiTripleProduct` | 完整 |
| 04 | 3426 | 330 | 五元乘积应用 + Euler pentagonal general (finite JTP at z=1) + `z = -1` JTP specialization bridge, Nat-indexed product factorization/`HasProd`, explicit bilateral theta `tsum`/summability/`HasSum` forms, Euler pentagonal JTP product/series substitution, cubic residue product to ordinary Euler product reindexing, square-root norm bridge, final Chan exponent `tsum` theorem, quintuple product LHS infinite product convergence/finite-limit interface, Theorem 4.4 product partial/convergence/q-Pochhammer interface, double-sum regrouping arithmetic (`z`/sign/sixfold exponent/residue lemmas) plus complete residue-class coefficient exponent/sign/residue simplifications, reverse residue-condition `iff` parametrizations, natural coefficient exponent index with nonnegativity/divisibility/spec, divided-form residue lemmas, coefficient `q`-power splitting, signed coefficient term splitting, full monomial splitting, paired zero/one branch factorized difference, and named paired-branch outer/inner/term interfaces with unfold/explicit bridges, left/right theta-like inner finite-partial split, base theta finite partials with fixed `z`-power extraction and finite `j ↦ -j` symmetry, raw monomial-pair finite partial bridges including single-theta compressed form, paired-branch theta term/series bridge to `jacobiInfiniteSeries (q^3) (-q⁻¹)` with summability/`HasSum` and symmetric-partial `Tendsto`, and symmetric finite partial-sum outer-factor extraction plus inner/term/raw monomial-pair finite-partial convergence for the two nonzero residue branches, plus third-residue `(1;q^6)` zero-factor interface, original Theorem 4.4 series term/RHS interface with `q ↦ q^2, z ↦ z/q` bridge to the substituted RHS and summability/`HasSum`, product/series-side substituted interfaces with bridges to Eq. (2.12), substituted Theorem 4.4 identity iff Eq. (2.12) quintuple identity, explicit-product RHS bottleneck `quintupleProductExplicitRHS` with iff/transport interfaces, finite partial convergence/reduction for the full quintuple identity, explicit RHS partial rewrite to Ch02 `jacobiProductPartial`s, Ch02-product-partial finite-difference reduction, finite q-Pochhammer/finite-JTP reduction, weighted Laurent finite-sum reduction, weighted Laurent monomial `z`/`q` power splitting, combined weighted Laurent finite-sum reduction with common q-Pochhammer factor, monomial-split combined finite-sum reduction, fixed centered positive/negative monomial-summand limits to the bilateral RHS term, and fixed pair/symmetric partial limits for the monomial-split combined finite sum, substituted Theorem 4.4 series summability/`HasSum`, RHS Jacobi-series `tsum`/summability/`HasSum` interface, RHS-to-JTP-series/product bridges, explicit Nat-indexed JTP product factors, and finite partial/convergence interfaces for the two explicit JTP products | 理论扩展中 |
| 05 | 3746 | 393 | Ferrers diagrams, Franklin down/up branches, shifted/pentagonal staircase fixed shapes + recognition/boundary lemmas + `IsPentagonalFixedShape` boundary/shifted-staircase/up-shape/down-branch/low-offset residual characterization + shifted-staircase relation-target iff classification + shifted-staircase branch-predicate iff classification + shifted-staircase move/no-move iff classification + last-part boundary iff classification + relation-form `IsFranklinMovePair` with domain iff, left/right uniqueness, symmetry iff, weight/sign, sign-sum cancellation, no-fixed-point, involution package, fixed-shape exclusion theorems, strict nonempty last-row branch criteria, strict nonempty last-row four-way split, middle-boundary-plus-successive no-edge bridge, successive-difference low/up/fixed/down split with no-edge iff, successive-difference active-domain iff, active-domain unique target/involution package, active-domain exact up/down target split, and up-branch preservation of successive differences + exact residual iff and complementary non-low boundary iff + explicit up/down move formulas on shifted staircases + shifted-staircase up/down branch transition, inverse, and strict/weight/sign packages + positive-height shifted-staircase raw and predicate offset splits + explicit branch-input predicates, `up (down ...)`/`down (up ...)` inverses, both branch-input transition interfaces, branch transition+inverse packages, fixed-shape branch exclusions, and down/up branch disjointness | 理论扩展中 |
| 06 | 612 | 132 | Dedekind eta 截断 N=1..130 | 完整 |
| 07 | 1136 | 65+ | Rogers-Ramanujan LHS/RHS truncations, finite+infinite FE, `rrJInf` definition+summability+FE, qPochhammer nonvanishing | 理论证明 |
| 08 | 373 | 38 | D_trunc series | 完整 |
| 09 | 7708 | 413 | Bailey pair up-to interface, BaileyBeta/rrAlpha seeds, finite Bailey-transform preservation through N=6; up-to-six component/assembly/iff infrastructure; RR seed β/α expansions through N=6; N=6 transformed-α/β expansion/up-to-pair package, all seven α₀..α₆ coefficient identities, standard-terms assembly, and preservation theorem | 理论扩展中 |
| 10 | 179 | 14 | Mock theta f(q) N=0..13 | 完整 |
| 11 | 60252 | 10044 | 黄金比 α/β, G/H_trunc N=0..5000, R_trunc | 持续扩展 |
| 12 | 557 | 115 | RRCF evaluation N=0..110 | 完整 |
| 13 | 324 | 21 | Deep identity LHS N=0..20 | 完整 |
| 14 | 235 | 36 | Crank numerator N=1..20, denominator N=1..12 | 完整 |
| 15 | 3141 | 521 | q-calculus theory (qDeriv_pow, Leibniz, qDerivIter, qFactorial, qExpTrunc, qDeriv_qPoch, qFallingFactorial, qDerivIter_pow) + q-Taylor reconstruction for `Polynomial.eval` bounds `≥`/`>` natDegree, including coefficient-congruence, weakened natDegree-only coefficient matching, strict/global zero-tail variants, and zero-tail stability bridge lemmas + R_trunc N=1..400 | 理论证明 |
| 16 | 30514 | 5056 | MBI numerator N=1..50, denominator N=1..5000 | 持续扩展 |
| 17 | 1039 | 322 | 分拆 mod 2..97 (25 primes) | 持续扩展 |
| 18 | 3242 | 316 | t-core N=1..30 + 2/3/5/7-core specialized; hook-length theory + bounded-hook core criterion + gcd/lcm hook-core and obstruction monotonicity packages + staircase transpose hooks + Ferrers conjugation hook invariance + staircase `2`-core/even-modulus theorem + `t ≥ 2n` staircase core bound, divisor obstructions from the top hook `2n-1`, exact hook spectrum, odd/even hook multiplicities including unconditional `n-k`, unified cardinal formula `if 2 ∣ t then 0 else n - t/2`, general odd-layer antidiagonal formula, odd-layer sum equals triangular/weight, empty/nonempty hook-layer iff/card criteria, exact odd-modulus staircase core iff, complete staircase core criterion `2 ∣ t ∨ 2*n ≤ t`, and the dual hook-obstruction criterion | 理论扩展中 |
| 19 | 338 | 89 | Ramanujan congruences III, mod 3/4 | 扩展中 |
| 20 | 1449 | 142 | 模判别式 eta/discriminant | 扩展中 |

## 关键技术

### 证明策略
- 截断展开（绝大多数定理）：`simp [definition, natSum, qPochhammer]` 或 `simp + ring_nf` 或 `simp + field_simp`
- 递推式：`change ... * (1 - q ^ ...) = _; rw [prev_theorem]`
- 黄金比：`calc ... = ... := by simpa using recurrence N; _ = ... := by nlinarith [prev]`
- R_trunc/continued fraction：`simp [R_trunc]; field_simp`
- 分拆 congruence：`simp [Ch01.partitionCount_N]`

### 构建
- `lake build QseriesFormalization.ChapterXX` 验证单章（秒级）
- **不要跑 `lake build`**：Chapter01 有 6653 行，rebuild 需要 20+ 分钟
- Basic.lean 改动后必须等 Ch01.olean 重建完成

### 协作管线
- `HANDOFF/inbox/` — 任务 recipe（batch 格式）
- `HANDOFF/outbox/` — 完成回报
- Gemini CLI（`gemini --yolo`）在 tmux `research-gemini` 窗口，仅用于观察/交互调试，不用于派发长任务
- 2026-05-04/05 事故记录：`research-gemini` 里曾有长消息停在输入框未提交；2026-05-05 已再次用 `C-c` + 单独 `C-m` 清空并确认回到 shell prompt，后续不要用 interactive pane 承接一次性派发
- 一次性 handoff 禁止裸用 `tmux send-keys` 发长消息；容易出现文本留在输入框但没有最终 Enter 的失败模式
- Codex/Gemini/Sonnet 均通过 `~/.openclaw/scripts/handoff-dispatch.sh <codex|gemini|sonnet> <path>` 派发
- 若临时必须手工用 tmux，只能发短控制键或短命令；`C-m` 必须作为单独一次 `tmux send-keys` 发送，并立刻 `capture-pane` 确认 prompt 为空
- 每批 5 个任务，每批 10-15 分钟完成验证

### 约束
- No sorry, no axiom, no native_decide
- `lake build` 必须 pass
- 代码里不要 Nat.mul_comm 等 unused simp args（linter 会报 warning）

## Jacobi Triple Product

```lean
theorem jacobiTripleProduct (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    jacobiInfiniteProduct q z = jacobiInfiniteSeries q z
```

这是全书核心定理。当前证明在 `Chapter03.lean` 中通过 finite JTP、centered Gaussian reindexing、
Tannery dominated convergence、uniform q-Pochhammer/Gaussian coefficient bound 和
two-term symmetric-pair majorant 完成，并在 `Ch02` namespace 下导出同名 theorem。

## 下一步方向（2026-05-17 更新）

1. **Ch05 Franklin involution 收尾** — `euler_pentagonal_combinatorial` 一般证明
   填 5 个 sorry (franklinInv 性质), 用 Finset.sum splitting 关闭
2. **Ch15 q-Taylor 扩展** — 已有 530 decl, 可以加更多理论
3. **Ch18 t-core 深化** — hook-length 深层定理
4. **Ch04 五元乘积推论** — 已完整, 可加特化/应用

### 历史记录
1. **理论证明为主**（2026-05-03 起转向）
   - Ch02: 已证 Jacobi triple product 两侧的基础收敛事实：
     `summable_jacobiSeries_nat`,
     `summable_jacobiInfiniteSeries_terms`,
     `multipliable_jacobiInfiniteProduct_factors`,
     `hasProd_jacobiInfiniteProduct_factors`, and
     `hasSum_jacobiInfiniteSeries_terms`; product 侧已补
     `jacobiProductEvenFactor`, `jacobiProductOddFactor`,
     `jacobiProductNatFactor`, and
     `jacobiProductPartial`, plus
     `jacobiInfiniteProduct_eq_tprod_natFactor` and
     `jacobiProductPartial_eq_qPoch`; product components 已补
     `multipliable_jacobiProductEvenFactor`,
     `jacobiProductEvenFactor_ne_zero`,
     `qPochhammer_qsq_eq_jacobiProductEvenPartial`,
     `qPoch_qsq_eq_jacobiProductEvenPartial`,
     `tendsto_qPoch_qsq`,
     `tprod_jacobiProductEvenFactor_ne_zero`,
     `multipliable_jacobiProductOddFactor`,
     `multipliable_jacobiProductNatFactor`,
     `hasProd_jacobiProductNatFactor`,
     `tendsto_jacobiProductPartial`,
     `jacobiInfiniteProduct_eq_tprod_components`, and
     `jacobiInfiniteProduct_qsq_mul_uncancelled`; product 侧还已证零因子引理
     `jacobiInfiniteProduct_zero_of_one_add_z_mul_q_eq_zero` 和同形函数方程
     `jacobiInfiniteProduct_qsq_mul`; series 侧已补
     `jacobiSeriesSymmetricPartial` and
     `tendsto_jacobiSeriesSymmetricPartial`; symmetric nonzero term pairs
     已补 `jacobiSeriesSymmetricPairTerm`,
     `jacobiSeriesSymmetricPairPartial`,
     `jacobiSeriesSymmetricPartial_succ`,
     `jacobiSeriesSymmetricPartial_eq_one_add_pairPartial`, and
     `tendsto_jacobiSeriesSymmetricPairPartial`; pair-tail package 已补
     `jacobiSeriesSymmetricPairTail`,
     `jacobiSeriesSymmetricPairPartial_eq_add_tail`,
     `jacobiSeriesSymmetricPairNormMajorant`,
     `summable_jacobiSeriesSymmetricPairTerm_neg`,
     `summable_jacobiSeriesSymmetricPairTerm_pos`,
     `summable_jacobiSeriesSymmetricPairTerm`,
     `summable_jacobiSeriesSymmetricPairNormMajorant`,
     `norm_jacobiSeriesSymmetricPairTerm_le_majorant`,
     `hasSum_jacobiSeriesSymmetricPairTerm`,
     `hasSum_jacobiSeriesSymmetricPairTerm_tail`, and
     `tsum_jacobiSeriesSymmetricPairTerm_tail`; 已证 series 侧函数方程
     `jacobiInfiniteSeries_qsq_mul`; 差函数已补
     `jacobiDifference`, `jacobiDifference_qsq_mul`,
     `jacobiDifference_qsq_mul_iterate`, and
     `jacobiDifference_qsq_mul_iterate_eq_zero_iff`; 退化情形
     `jacobiTripleProduct_q_zero` 已关闭；完整 `jacobiTripleProduct`
     已在 Chapter03 通过 finite-JTP/Gaussian-tail argument 导出到 Ch02 namespace。
   - Ch03: finite JTP 现在有桥接定理
     `jacobiProductPartial_eq_qPoch_mul_finiteJTPRHS`, connecting Ch02's
     `jacobiProductPartial` to `qPoch(q²;q²)_N * finiteJTPRHS(q², -zq, N)`.
     已补 centered Gaussian coefficient product forms
     `gaussianBinom_center_add_mul_qPochhammer_eq` and
     `gaussianBinom_center_sub_mul_qPochhammer_eq` for `[2N, N±r]_q`.
     还已补 finite-limit coefficient interfaces:
     `qPochhammer_qsq_ne_zero`,
     `qPoch_mul_gaussian_center_add_eq_ratio`,
     `qPoch_mul_gaussian_center_sub_eq_ratio`,
     `tendsto_qPoch_qsq_two_mul`,
     `tendsto_qPoch_mul_gaussian_center_add`,
     `tendsto_qPoch_mul_gaussian_center_sub`,
     `tendsto_qPoch_mul_gaussian_center_pair`,
     `tendsto_qPoch_mul_gaussianWeightedPairTerm`,
     `gaussianWeightedPairTerm`, `gaussianWeightedPairPartial`,
     `gaussianWeightedPairTail`, `gaussianWeightedTailSummand`,
     `tendsto_gaussianWeightedTailSummand`,
     `qPoch_mul_gaussianWeightedPairTail_eq_shiftedRange_sum`,
     `qPoch_mul_gaussianWeightedPairTail_eq_shiftedTailSummand_sum`,
     `tsum_gaussianWeightedTailSummand`,
     `gaussianWeightedPairPartial_eq_add_tail`,
     `tendsto_qPoch_mul_gaussianWeightedPairTail`, and
     `tendsto_qPoch_mul_gaussianWeightedPairPartial`, plus
     `gaussianWeightedSymmetricPartial` and
     `gaussianWeightedSymmetricPartial_eq_add_tail` and
     `tendsto_qPoch_mul_gaussianWeightedSymmetricPartial`. 还已补
     `natSum_eq_sum_range`, `gaussianWeightedLaurentSummand`,
     `gaussianWeightedSymmetricPartial_eq_weightedLaurentNatSum`, and
     `jacobiProductPartial_eq_qPoch_mul_gaussianWeightedSymmetricPartial`,
     plus `jacobiProductPartial_eq_qPoch_mul_fixedSymmetricPartial_add_tail`,
     and `jacobiTripleProduct_of_gaussianWeightedTail_tendsto`,
     `jacobiTripleProduct_of_gaussianWeightedTail_tendsto_tsum`,
     and `jacobiTripleProduct_of_gaussianWeightedTail_dominated`,
     plus `jacobiTripleProduct_of_gaussianWeightedTail_norm_le_seriesTail`,
     and `jacobiTripleProduct_of_gaussianWeightedTail_norm_le_pairMajorant`,
     `exists_qPoch_mul_gaussian_center_norm_bound`,
     `exists_gaussianWeightedTailSummand_pairMajorant_bound`, and
     `jacobiTripleProduct_via_finiteJTP`,
     connecting the `k = 0..2N` finite-JTP weighted Laurent sum to the
     centered symmetric block form, its fixed-core-plus-tail split, and the
     Gaussian-tail convergence target for JTP, in
     series-tail-difference, `tsum`, dominated-convergence,
     constant-times-series-tail-norm, cancellation-free pair-majorant
     domination, and final closed-theorem forms.
     还已补 `finiteJTPSummand_qsq_neg_zq`,
     `finiteJTPRHS_qsq_neg_zq`, and
     `jacobiProductPartial_eq_qPoch_mul_weightedLaurentSum`, expressing the
     same finite product as `(q²;q²)_N` times a Gaussian-weighted Laurent sum
     with monomials `z^l q^{l²}`.
   - Ch07: **Infinite Rogers-Ramanujan series infrastructure** (2026-05-10):
     `qPochhammer_ne_zero_of_norm_lt_one` (nonvanishing for ‖q‖<1),
     `norm_qPochhammer_ge` (lower bound (1-‖q‖)^n),
     `rrJTerm`/`rrJInf` (infinite series definition),
     `summable_rrJTerm` (absolute convergence via super-exponential decay + q-Pochhammer lower bound),
     `hasSum_rrJTerm`, `rrJInf_functional_eq` (infinite FE: J(x)-J(xq)=xq·J(xq²)),
     `rrJInf_zero` (J(0)=1), `rrJInf_eq_shift_add`, `rrJInf_one_sub_q`, `rrJInf_q_sub_qsq`,
     `rrJ_functional_eq_complex` (clean finite FE with no manual hypotheses),
     `rrJ_eq_shift_add`, `rrJ_ratio_eq`.
     The infinite FE was proved via termwise identity decomposition:
     `∑' diff(n) = diff(0) + ∑' diff(n+1) = 0 + xq · ∑' rrJTerm(xq²,n)`.
   - Ch15: 已证 qDeriv_pow (一般), qDeriv_mul (Leibniz rule), qDeriv_add/smul/sub (线性)
   - Ch15: 已证 qDerivIter (迭代 q-导数), qDerivIter_two_pow (D_q^2(x^n))
   - Ch15: 已定义 qFactorial, qExpTrunc + 基本性质
   - Ch15: 已证 qDeriv_qPoch: D_q((z;q)_n)(a) = -[n]_q·(aq;q)_{n-1} (连接 q-calculus ↔ 分拆理论)
   - Ch15: 已证 q-Taylor top-term reconstruction for finite coefficient sequences,
     plus bridge to Mathlib `Polynomial.eval` for truncation bound ≥ `natDegree`
     and strict bound > `natDegree`, including coefficient-congruence bridges
     and zero-tail stability lemmas showing ordinary/q-Taylor truncations do
     not change when enlarged past vanishing coefficients, specialized to
     polynomial coefficients above `natDegree`; external coefficient functions
     can now reconstruct `p.eval x` by matching `p.coeff` only through
     `p.natDegree` and vanishing on the added tail up to the chosen truncation,
     with both strict-bound and global-tail variants
   - Ch09: Bailey pair up-to interface and Rogers-Ramanujan rrAlpha/BaileyBeta
     finite term expansions now extend through `N = 6`; finite Bailey-lemma
     preservation is packaged through `N = 6` under explicit nonzero
     denominator hypotheses. The `N = 6` package includes the general
     seven-term `BaileyBeta` expansion, `rrAlpha_six`, all seven
     `BaileyTerm_rrAlpha_six_*` simplifications, `BaileyBeta_rrAlpha_six_terms`,
     `rrBeta_six_terms`, transformed-α and transformed-β expansions, transformed-β
     under an up-to-six pair hypothesis, all seven transformed-α evaluated
     terms, `BaileyBeta_transformAlpha_six_terms_linear`, all seven
     α₀/α₁/α₂/α₃/α₄/α₅/α₆ coefficient identities, the standard-terms assembly,
     `BaileyTransform_preserves_pair_six_of_nonzero`, and
     `BaileyTransform_preserves_pair_upTo_six_of_nonzero`.
   - Ch05: Ferrers conjugation now has positive-parts double-conjugation list
     equality and general staircase self-conjugacy; Franklin's non-fixed
     down move (shorten all rows and append old length) is packaged with
     strictness, weight preservation, and sign reversal; the inverse-shaped
     up move recovers any positive-parts list after a down move, and has its
     own explicit last-row strict/weight/sign package. Shifted staircase and
     lower/upper pentagonal fixed-shape row-length lemmas now include `getD`
     formulas, first/last-part formulas, adjacent-row difference formulas,
     extensional recognition from displayed row formulas, from
     first-row-plus-adjacent-difference formulas, and from
     last-row-plus-adjacent-difference formulas; last-part membership;
     proofs that the two pentagonal fixed-shape families fail the strict
     Franklin down-branch inequality; proofs that they are not of the
     explicit `mu ++ [numberOfParts mu]` up-branch input shape; and a
     positive-length iff characterization of pentagonal fixed shapes by the
     last-part boundary (`#parts` or `#parts + 1`) plus adjacent row
     differences equal to one. General shifted staircases are now proved to
     be pentagonal fixed shapes exactly at offsets `d = k - 1` and `d = k`,
     not to be pentagonal fixed shapes exactly when both offset equalities
     fail,
     to have the explicit up-branch input shape and satisfy the
     `IsFranklinUpBranchInput` predicate exactly when `d + 2 = k`,
     and to satisfy the Franklin down-branch inequality and
     `IsFranklinDownBranchInput` predicate exactly when `d > k`
     (with the negated branch exactly `d ≤ k`). The low-offset case
     `d + 2 < k` is now explicitly packaged as outside the fixed-shape,
     explicit up-shape, and down-branch boundary cases, and also outside both
     branch-input predicates, with the converse iff also proved. The complement
     `¬ d + 2 < k` is characterized exactly by the disjunction of up-input,
     fixed-shape, or down-input cases. Positive-height shifted staircases now
     have exhaustive raw and predicate offset splits into the low residual case,
     explicit up-shape/up-input case, fixed-shape case, or down-branch case.
     Explicit shifted-staircase move formulas are now proved: uniform shifts
     compose, positive row-shortening lowers the offset by one, `franklinUpMove`
     sends a nonempty shifted staircase to height `k - 1` and offset `d + 2`,
     and `franklinDownMove` on positive offset lowers the offset and appends
     the old height. Predicate-level shifted-staircase branch transitions are
     now proved: the up-boundary case lands in `IsFranklinDownBranchInput`,
     and the down-boundary case lands in `IsFranklinUpBranchInput`. The two
     corresponding shifted-staircase boundary inverse identities
     `down (up ...) = ...` and `up (down ...) = ...` are also packaged.
     Each shifted-staircase boundary move now has a strict/weight/sign package,
     and a full package combining strictness, weight preservation, sign
     reversal, target branch predicate, and inverse identity. The same
     shifted-staircase low/up/fixed/down split is now characterized by the
     last part relative to `numberOfParts`: `< #parts - 1`, `= #parts - 1`,
     `= #parts or #parts + 1`, and `> #parts + 1`.
   - Ch05: Relation form `IsFranklinMovePair` now packages the two active
     Franklin branches without using a decidable `if`; for strict branch inputs
     it is symmetric, outputs a strict partition, preserves weight, and reverses
     Franklin sign. The relation also has no fixed points on strict inputs
     (`¬ IsFranklinMovePair lam lam`, equivalently `mu ≠ lam` for a pair), and
     is single-valued from a fixed source; for strict sources it is also
     right-unique from a fixed target. A consolidated involution package now
     returns target strictness, reverse pair, weight preservation, sign reversal,
     and non-fixedness from one relation edge. Pentagonal fixed shapes are
     excluded from the relation domain, and a strict move cannot land in a fixed
     shape. The relation domain is characterized exactly by the disjunction of
     down/up branch-input predicates, with an existential no-move form for fixed
     shapes. On strict endpoints, symmetry is also available as an iff. Pair
     signs also cancel additively as `partSign lam + partSign mu = 0`, with the
     symmetric order packaged too. For any strict nonempty source, the relation
     domain and exact target are also characterized by the last displayed row:
     `#parts + 1 < last` gives the down target, while `last = #parts - 1`
     gives the up target; the complement is packaged as a no-edge criterion,
     and an exhaustive low-residual/up/middle-boundary/down four-way split is
     available. The middle boundary together with successive row differences
     now bridges directly to pentagonal fixed-shape no-edge theorems. With the
     same successive-difference hypothesis, no relation edge exists iff the
     source is in the low residual case or is a pentagonal fixed shape; the
     active-domain complement is also packaged as not-low and not-fixed. In
     that active domain, the Franklin relation now has a unique target and the
     target comes with the consolidated involution package. The active-domain
     target is also classified exactly as the up target or the down target by
     the corresponding last-row boundary. The up branch preserves successive
     row differences; the down branch intentionally only lands in the up-branch
     input shape and need not preserve successive differences because a gap can
     appear at the appended row.
   - Ch05: For positive-height shifted staircases, existence of a relation-form
     Franklin move is now exactly `d + 2 = k ∨ k < d`; nonexistence is exactly
     the pentagonal fixed-shape case or the low residual case `d + 2 < k`.
     The exact target classification is also proved: the up-boundary target is
     `franklinUpMove`, and the down-boundary target is `franklinDownMove`.
   - Ch18: General hook-core monotonicity now includes explicit lcm obstruction
     projections and pair packaging, `gcd` obstruction projections from either
     modulus, `gcd`-core consequences to both moduli, paired gcd-core packaging,
     and contrapositives showing a failure of either larger modulus core
     property rules out the `gcd`-core property.
   - Ch18: Ferrers conjugation now has general hook-length preservation at
     transposed cells, so `HasHookDivisibleBy` and `IsTCoreByHooks` transfer
     to the conjugate partition for every partition. General staircase hook
     theory proves the filter row-count formula, `legLength` formula, closed
     hook-length formula, hook-length preservation under transposition for
     every staircase partition, the sharp bound that every staircase hook is
     at most `2n - 1`, the consequence that a staircase of height `n` is a
     `t`-core when `t ≥ 2n`, the stronger even-modulus core theorem, the
     top-left hook obstruction showing a positive-height staircase is not a
     `(2n - 1)`-core, the generalized obstruction for every divisor
     `t ∣ (2n - 1)`, and the sharper first-row realization of every odd hook
     `2k+1` with `k < n`, the exact hook-spectrum iff
     `∃ r c, hookLength (staircasePartition n) r c = t ↔ ¬ 2 ∣ t ∧ t < 2*n`,
     the antidiagonal description of the cells with hook length `2k+1` and
     the multiplicity formula `(StaircaseHookCellsOfLength n (2*k+1)).card = n-k`,
     plus the unconditional formula for all `k` with natural subtraction,
     the even-layer formulas `StaircaseHookCellsOfLength n (2*k) = ∅` and
     `(StaircaseHookCellsOfLength n (2*k)).card = 0`,
     the unified cardinal formula
     `(StaircaseHookCellsOfLength n t).card = if 2 ∣ t then 0 else n - t/2`
     and the general odd antidiagonal formula
     `StaircaseHookCellsOfLength n t = Finset.antidiagonal (n - (t/2 + 1))`
     under `¬ 2 ∣ t` and `t < 2*n`,
     summing all odd-layer multiplicities over `k < n` gives `triangular n`
     and the staircase partition weight,
     the empty-layer criteria
     `StaircaseHookCellsOfLength n t = ∅ ↔ 2 ∣ t ∨ 2*n ≤ t` and
     `(StaircaseHookCellsOfLength n t).card = 0 ↔ 2 ∣ t ∨ 2*n ≤ t`,
     the nonempty/card-positive criteria
     `(StaircaseHookCellsOfLength n t).Nonempty ↔ ¬ 2 ∣ t ∧ t < 2*n` and
     `0 < (StaircaseHookCellsOfLength n t).card ↔ ¬ 2 ∣ t ∧ t < 2*n`,
     the exact odd-modulus core criterion
     `IsTCoreByHooks (2*k+1) (staircasePartition n) ↔ n ≤ k`, plus the
     complete criterion
     `IsTCoreByHooks t (staircasePartition n) ↔ 2 ∣ t ∨ 2*n ≤ t` and its
     dual obstruction form
     `HasHookDivisibleBy t (staircasePartition n) ↔ ¬ 2 ∣ t ∧ t < 2*n`.
   - 下一步: 用已关闭的 JTP 继续推进 quintuple product（Theorem 4.4 乘积侧代换桥已接到 Eq. (2.12)），
     RRCF 微分方程 (Ch15 §15.2)
   - Codex 已派任务（batch20-theory-recipe）
2. **General Bailey lemma (Ch09)** — **0 sorry, but conditional**. Precise status
   (verified 2026-05-16): `BaileyTransform_preserves_pair_general`
   (Chapter09.lean:13702) is the *structural* theorem — proved, but it takes the
   q-Pfaff–Saalschütz kernel identity `baileyKernelSum = baileyKernelTarget` as a
   **hypothesis** `hkernel`. Unconditionally discharged only for: boundary `j=n`
   (`baileyKernelSum_eq_target_n`) and the small `(n,j)` instances consumed by the
   `BaileyTransform_preserves_pair_{one,two}_general` specializations (n≤2,
   brute field_simp+ring). So the *unconditional* general finite Bailey lemma for
   all `n` still needs the **general q-Pfaff–Saalschütz / Jackson summation** — a
   genuine classical hard theorem (induction / q-WZ), on the critical path,
   multi-session. The old n=2..7 `*_alpha_zero_*_ratio` /
   `*_common_denominator_identity` ladder is **superseded scaffolding** (n=8
   identity unreferenced; n=8 ratio lemmas no consumers — do NOT re-chase it as a
   "gap"; comment fixed at commit 573e059). Next after general q-PS: lift to
   infinite version using Ch07 convergence infra (`summable_rrJTerm`,
   `rrJInf_functional_eq`).
   **General q-PS WIP (2026-05-16, resumable)** — dev in
   `scratch_qPS.lean` (repo root, untracked, imports cached Chapter09, NOT in
   build graph; library stays 0-sorry). Plan: downward induction on `n−j`
   from base `baileyKernelSum_eq_target_n` (j=n) via a telescoping q-WZ
   certificate (ChatGPT pro gave the method; saved
   `HANDOFF/cgpt_qPS_telescoping_strategy.txt`). Two foundational shift
   lemmas: (a) **DONE, verified EXIT=0** `baileyTransformCoeff_succ_k` —
   coeff(n,k+1)·(1−b·q^{n−k−1}) = coeff(n,k)·(1−ρ₁q^k)(1−ρ₂q^k)·b·(1−q^{n−k}),
   proof = unfold + targeted qPoch_succ rw (obtain-m index lemmas) +
   field_simp; (b) **WIP** `baileyKernelTarget_succ_j` (full spec + blocker +
   solution in scratch_qPS.lean comment): statement algebraically correct;
   `field_simp;ring` fails because field_simp *recombines* opaque-qPoch
   denominators into expanded polys whose ≠0 can't be matched factor-wise —
   the fundamental reason the file's `simp[qPoch];field_simp;ring` idiom only
   does CONCRETE small (n,j). Fix: structural `div_eq_div_iff hDj1 hDj` with
   explicit `mul_ne_zero` denominator products (file's hX-pattern,
   Chapter09.lean:13496-13517), never field_simp the whole fraction.
   ChatGPT bridge unreliable for the heavy general-q-PS query (timed out ×2,
   pro mode) — proceed by self-derivation + oracle-verification against the
   proved small instances.
   **Verified building blocks (scratch_qPS.lean, EXIT=0)**: (1)
   `baileyTransformCoeff_succ_k` coeff consecutive-k recurrence; (2)
   `baileyKernelSum_peel` — peels lowest `k=j` term (for `j ≤ n`):
   `baileyKernelSum n j = coeff n j / qPoch(aq) q (2j) + ∑_{k:j+1≤k}
   coeff n k/(qPochhammer q (k-j)·qPoch(aq) q (k+j))`, pure Finset
   (filter=insert j…; sum_insert; qPochhammer_zero), no b^j fraction.
   Two of three downward-induction ingredients done; only target-shift
   (b^j-wall) remains. (3) `baileyKernelSum_summand_shift` (EXIT=0) — for
   `j+1≤k`, term-wise: `S_j(k)·(1-q^(k-j)) = S_{j+1}(k)·(1-a*q*q^(k+j))`
   where `S_j(k)=coeff n k/(qPochhammer q (k-j)·qPoch(aq) q (k+j))`; this is
   the explicit per-term factor linking the peel tail to the
   `baileyKernelSum _ (j+1)` summand. THREE verified building blocks now.
   NEXT: assemble — `Finset.sum_congr`/`mul_sum` to turn the peel tail
   (×(1-q^(k-j)) per term, but k-dependent so needs the certificate not a
   scalar) into a combination of `baileyKernelSum n (j+1)` terms, then
   downward induction from boundary `baileyKernelSum_eq_target_n`,
   oracle-checking each step vs the proved small instances.
   (4) `baileyKernelTarget_as_frac` (EXIT=0) — KTgt as a single explicit
   fraction `(qPρ₁_j·qPρ₂_j·(aq)^j)/((ρ₁ρ₂)^j·qP(aq/ρ₁)_j·qP(aq/ρ₂)_j·
   qPochhammer(n-j)·qPoch(aq)(n+j))`, resolving the nested b^j. FOUR verified
   building blocks. The target-shift factor F(n,j) is derived (= the ×ρ₁ρ₂
   cleared form in scratch WIP). REMAINING target-shift blocker CONFIRMED:
   field_simp recombines the `a*q/ρᵢ` divisions inside the qPoch_succ
   `(1-a*q/ρᵢ*q^j)` factors + `(ρ₁ρ₂)^j` into `(ρ₁-aq^{j+1})(ρ₂-aq^{j+1})`
   (unmatchable). CONFIRMED DEAD-END (tested): the field_simp route fails even with as_frac +
   qPoch_succ + pre-rewrite `1-a*q/ρᵢ*q^j → (ρᵢ-a*q*q^j)/ρᵢ` (e1/e2) +
   factored `hX₁,hX₂`. field_simp still recombines the two `(ρᵢ-a*q*q^j)`
   denominator factors into the EXPANDED product, unmatchable by factored
   hyps. ONLY robust route = structural `div_eq_div_iff hD1 hD2` (NEVER
   field_simp): apply e1/e2 FIRST (removes the `_/_*_` collision), fold to
   single fractions with TARGETED `mul_div_assoc'`/`div_div` (not blanket
   div_mul_eq_mul_div), then `div_eq_div_iff` + opaque-atom `ring`. Remaining: (i) that goal-rewrite [mechanical];
   (ii) q-WZ telescoping certificate W(k) joining peel+summand_shift to
   `baileyKernelSum n (j+1)` [research crux]; (iii) downward induction from
   `baileyKernelSum_eq_target_n`. (5) `baileyKernelSum_eq_target_of_step` (EXIT=0) — downward-induction ARCHITECTURE: reduces the ENTIRE kernel identity (∀ j≤n) to the proved boundary `baileyKernelSum_eq_target_n` + ONE inductive `hstep` (:= peel + target-shift + q-WZ tail telescoping). Induction skeleton machine-verified; whole crux now isolated to `hstep`. FIVE verified lemmas. (6) `peelTail_telescope` (EXIT=0) — generic telescoping over peel's tail {j+1..n}: Σ(W(k+1)-W k)=W(n+1)-W(j+1), the q-WZ mechanic independent of the certificate. SIX verified lemmas; hstep now = peel(✓)+telescope(✓)+target-shift(WIP)+the certificate G,W (only true unknown, ChatGPT-pro query in flight). ChatGPT bridge: focused query a0ca7bdb
   succeeded (method saved HANDOFF/); heavy/general queries timed out ×2 +
   1 connection-fail — unreliable for the crux, self-derive + oracle-verify.
   REVERTED (2026-05-16): an attempt to add LIBRARY theorems
   `baileyKernelSum_eq_target_two_three` (n=3,j=2) +
   `BaileyTransform_preserves_pair_three_general` (extend unconditional
   Bailey n≤2→n≤3) was reverted as UNVERIFIABLE: two_three's brute
   `simp[qPoch,qPochhammer];field_simp;ring` under `maxHeartbeats 0` did not
   complete in 36+ min. Its `qPoch(aq) q 5` factor (k+j=5) is HIGHER degree
   than the proven `one_three`'s max `q 4`, so the "smaller-than-one_three"
   mirror argument is INVALID — likely pathological like the n=8 region.
   Lesson: do NOT extend coverage via more brute kernel-instance ladder
   rungs; the n≤2 cutoff is the practical brute limit. The ONLY scalable
   path is the general q-PS certificate route. Library kept known-good
   (committed HEAD, 0-sorry); the verified lemmas live in untracked
   `scratch_qPS.lean` (not in build graph).
   CERTIFICATE DELIVERED + FORMALIZED AS REDUCTION (2026-05-16, EXIT=0, 8
   verified thms). q-WZ certificate (G(n,j), W(n,j,k), boundaries) saved in
   `HANDOFF/cgpt_qWZ_certificate.txt` (tracked, commit 81bf211).
   `hstep_certified` assembles the FULL downward step from peel(✓) +
   peelTail_telescope(✓) + certificate; `baileyKernelSum_eq_target_certified`
   gives general q-PS for ALL j≤n CONDITIONAL on per-j certificate data.
   General q-PS is now machine-reduced to exactly TWO pure algebraic
   identities: (A) per-term `S_j(k)=G·S_{j+1}(k)+(W(k+1)-W k)`; (B) TGT_SHIFT
   `KTgt(n,j)=G·KTgt(n,j+1)`. Both field_simp/ring rational identities,
   certificate-guaranteed true.
   **(A) and (B) BOTH VERIFIED (2026-05-16)**: breakthrough via change-of-variables
   `k = j+1+d, n = j+1+d+e` (eliminates ALL Nat subtraction in q-exponents)
   + `simp only [pow_add, pow_succ, ...]` (consistent q-power normalization)
   + `field_simp; ring` closes both. (A) `per_term_telescope` EXIT=0 ~7 min;
   (B) `tgt_shift_cleared` EXIT=0 ~5 min; `tgt_shift_div` EXIT=0 (derives
   `KTgt(n,j) = G·KTgt(n,j+1)` via `eq_div_iff + exact tgt_shift_cleared`).
   12 verified theorems in scratch_qPS.lean (0 sorry).
   
   **COMPLETE (2026-05-17)**: All building blocks verified + assembled.
   `baileyKernelSum_eq_target_general` (unconditional, ∀ j≤n) EXIT=0.
   `BaileyTransform_preserves_pair_unconditional` (unconditional finite
   Bailey lemma) EXIT=0. 17 theorems, 0 sorry, in `BaileyqPS.lean`.
   Full proof history in `CHANGELOG-qPS.md`.
3. **Infinite Rogers-Ramanujan (Ch07)** — `rrJInf` defined, summability + infinite FE proved.
   Next: connect `rrJInf 1 q` and `rrJInf q q` to G(q) and H(q) product sides,
   or prove R(q) = H(q)/G(q) via continued fraction iteration of the FE.
4. Franklin involution（Ch05, 组合证明）
4. 截断展开到 N=400 已够，不再扩展

## 文件路径速查

- `QseriesFormalization/Basic.lean` — qPochhammer, qPoch, natSum, triangularNum, pentagonalNum
- `QseriesFormalization/Chapter01.lean` — partitionCount, generating functions (6653 lines!)
- `CHECKPOINT.md` — 更详细的章节状态（可能过时，以本文件为准）
- `GEMINI.md` — Gemini agent 的规则（yolo, 不问问题）
- `HANDOFF/inbox/batch*.md` — 任务 recipe
- `WORK_LOG.md` — 工作日志

### 已知限制
- `ring` tactic 在 3 变量 (z, z⁻¹, q) × 13+ 因子时 SIGABRT (stack overflow)，Ch14 denominator N≥13 不可用
- `ring_nf` 在 Ch10/Ch13 约 N=13-20 时需 3.2M-6.4M heartbeats，继续扩展代价指数增长
- `simp [qPochhammer]` 在 20 因子时需 ~10 分钟、15GB RAM（Ch14 numerator N=20）

---
_Last updated: 2026-05-10_
