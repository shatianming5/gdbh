# Binary Goldbach Lean Formalization

This repository contains a Lean 4 / mathlib v4.29.1 formalization project for
Binary Goldbach attack paths. It is a research worktree, not a completed proof
of Binary Goldbach.

Key files:

- `AGENTS.md`: authoritative project rules for agents, axiom hygiene, false
  Prop catches, and verification gates.
- `goal.md`: long-form mission prompt and multi-vector attack plan.
- `GOAL_PROMPT.md`: active controller goal prompt and workflow summary.
- `pathc_master_scoreboard.md`: Path C controller score decisions,
  decompositions, and verification history.
- `Gdbh/`: Lean source files.
- `Gdbh.lean`: root import barrel.
- `scripts/audit_full.sh` and `audit_lean_source.py`: verification/audit tools.

Recreate dependencies and verify:

```bash
source "$HOME/.elan/env"
lake update
lake exe cache get
lake build
python3 audit_lean_source.py
bash scripts/audit_full.sh
python3 scripts/regenerate_agents_md.py
```

The `.lake/` directory and Python/Lean build caches are intentionally not
tracked; they are generated locally by the commands above.

---

# 强哥德巴赫猜想研究起点

## 结论边界

强哥德巴赫猜想断言：

> 每个大于 2 的偶数都能表示为两个素数之和。

截至 2026-05-19，没有公认的无条件证明。这个目录里的内容不能替代证明，只能作为继续研究、审查证明草稿和做有限范围计算验证的起点。

## 已知背景

- 强哥德巴赫猜想仍是公开问题。
- 已有大规模计算验证，但计算验证只能覆盖有限范围，不能推出全体偶数成立。
- 弱哥德巴赫猜想已经由 Harald Helfgott 证明：每个大于 5 的奇数是三个素数之和。弱形式不能直接推出强形式。
- Chen 定理给出了接近结果：充分大的偶数可以表示为一个素数与一个至多两个素数乘积的数之和，但这仍不是两个素数之和。

## 一个合格证明至少要通过的检查项

1. 明确证明对象是所有偶数 `N > 2`，而不是某个有限上界以内的偶数。
2. 给出存在性结论：存在素数 `p`，使得 `N - p` 也是素数。
3. 每个不等式、渐近式和误差项都必须有量词和有效常数，尤其要能覆盖所有充分大的 `N`。
4. 如果证明分为“小数计算 + 大数解析估计”，必须证明两个区间无缝覆盖，没有遗漏区间。
5. 不得暗中使用未证明假设，例如 GRH、素数随机模型、未经证明的素数间隔估计或未量化的“均匀分布”。
6. 不能只证明候选素数集合很大；必须证明集合 `{p prime}` 与集合 `{N - p prime}` 有非空交集。
7. 不能从弱哥德巴赫猜想、三素数表示或“素数 + 半素数”表示直接推出强哥德巴赫猜想，除非补上额外且充分的论证。

## 常见错误模式

- 把有限范围验证当成全体证明。
- 用素数定理的平均密度替代具体存在性。
- 假设两个大集合必有交集，但没有证明它们在同一个有限宇宙中的大小和分布足以强制相交。
- 用概率模型说明“几乎必然”，却没有转化为严格的确定性下界。
- 在模小素数筛选后，误认为剩下的候选数必有素数。

## 当前可执行工具

`verify_goldbach.py` 可以验证给定上界以内的偶数是否都有两个素数表示：

```bash
python3 verify_goldbach.py 100000
```

也可以导出有限区间的见证证书：

```bash
python3 verify_goldbach.py 1000 --export-csv goldbach_1000.csv
python3 verify_goldbach.py 100 --export-lean Gdbh/Certificate100.lean --export-manifest certificate_manifest.json
python3 verify_goldbach.py 200 --interval-start 100 --export-lean Gdbh/Certificate100To200.lean
python3 verify_goldbach.py 1000 --interval-start 100 --chunk-size 100 --export-lean Gdbh/Certificate100To1000.lean
python3 verify_goldbach.py 1000 --interval-start 2 --chunk-size 100 --export-lean Gdbh/Certificate2To1000.lean
python3 generate_proof_status.py
```

这类工具只能寻找反例或增强经验信心，不能证明强哥德巴赫猜想。

`analyze_von_mangoldt.py` 可以对有限范围内的 raw von Mangoldt Goldbach 卷积、旧的 count/log 污染预算和新的 weight-sum 污染预算做数值探索：

```bash
python3 analyze_von_mangoldt.py 1000
python3 analyze_von_mangoldt.py 10000 --start 1000 --coefficient 1.0 --relative-error 0.5
python3 analyze_von_mangoldt.py 1000 --export-csv mangoldt_1000.csv
```

它输出 `RawVonMangoldtGoldbachSum(n)/n`、素数对 `Λ` 贡献、实际非素数对污染项、截断 Goldbach 奇异级数近似、相对 HL 主项的近似归一化误差、以及 `2 * vonMangoldtLogCountContaminationBudget nonPrimePrimePowerSqrtLogCountBound n / n` 等比值；给出 `--coefficient` 与 `--relative-error` 时，还会报告 canonical HL 证书形状在有限样本中的尾阈值。它只用于校准解析证明需要达到的常数量级并判断当前污染预算有多粗；这同样不是证明。

## Lean 形式化框架

本目录包含一个 Lean 4/mathlib 项目，用来形式化“有限证书 + 解析桥接定理 => 强哥德巴赫”的结构：

```bash
source "$HOME/.elan/env"
lake update
lake exe cache get
lake build
```

`Gdbh/Goldbach.lean` 没有把缺失的解析数论部分声明成 `axiom`。当前最精确的拼接结果是条件定理：有限证书已经把目标归约为 `ExplicitGoldbachLowerBound 100`，也就是证明每个 `n > 100` 的偶数都有正的 `GoldbachCount n`。内置 `Certificate100` 的字面目标桥位于 `Gdbh/AnalyticBridge.lean`；从 `2` 开始生成的自包含 chunked 证书也会自动导出“有限证书 + 解析阈值不超过证书上界 => ExplicitGoldbachLowerBound 100”的字面目标桥。自包含 chunked 证书还会导出对应的 `StrongGoldbach` 条件定理，覆盖显式计数下界、圆法下界、major/minor arc 估计、计数正性、带权下界、带权 major/minor arc 估计、污染项扣除下界、污染项扣除 major/minor arc 估计、实数权重版本污染项扣除接口、mathlib von Mangoldt 专用接口、von Mangoldt 素数幂污染项接口、左右拆分的素数幂污染项接口、逐点控制的左右素数幂污染项接口、“统一项上界 × 个数上界”的左右素数幂污染项接口、把左右污染集合个数都归约到同一个非素数素数幂计数的接口、使用平凡计数上界 `NonPrimePrimePowerCount n <= n + 1` 的接口、把污染项乘积上界归约为单个 `Λ` 因子上界的接口、用 mathlib 的 `Λ(m) <= log n` 消去外部 `Λ` 因子上界的接口、把左右污染预算固定为显式 `vonMangoldtLogContaminationBudget n = (n+1)*(log n)^2` 的 canonical 接口、保留显式 `countBound` 的 log 污染预算、直接 raw Λ 卷积下界接口、relative-error raw Λ 线性下界接口、eventually relative-error positive-linear raw Λ 下界接口、relative-error weight-sum major/minor arc 接口、split-threshold relative-error weight-sum major/minor arc 接口、eventually relative-error weight-sum major/minor arc 接口、eventually relative-error sqrt-log count major/minor arc 接口、split-threshold relative-error sqrt-log count major/minor arc 接口、直接 weight-sum 污染预算接口、直接 weight-sum major/minor arc 接口，以及 Lean 已证明的 `NonPrimePrimePowerCount n <= (sqrt n + 1)*(log₂ n + 1)` 计数上界的 raw、线性 raw 和 major/minor arc 接口。当前项目不是强哥德巴赫猜想的完整证明。

新增的 `VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound` 适合把文献中常见的绝对误差估计接入 Lean：只要最终证明 `|RawVonMangoldtGoldbachSum n - mainTerm n| <= relativeError * mainTerm n` 和 `mainTerm n >= coefficient*n`，Lean 会先推出 eventually relative-error raw 下界，再进入已经形式化的污染预算桥。

新增的 `VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound` 进一步贴近渐近式写法：证明绝对误差是 `o(mainTerm)` 且主项最终正线性即可，Lean 会选取 `relativeError = 1/2` 并转入 abs-error raw 桥。

新增的 `VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound` 覆盖 `RawVonMangoldtGoldbachSum ~ mainTerm` 这种论文中常见的等价渐近表述；Lean 会把它展开成 `Raw-main = o(main)`，再转入 little-o/abs-error raw 桥。

新增的 `VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound` 覆盖归一化误差写法：证明 `(Raw-main)/main -> 0` 且主项最终正线性后，Lean 会取最终相对误差 `1/2` 并转入 abs-error raw 桥。

新增的 `VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate` 进一步固定论文常见主项 `singularSeries(n) * n`：证明奇异级数最终有正下界，且 `RawVonMangoldtGoldbachSum` 相对该主项的归一化误差趋于 0 后，Lean 会自动转入 normalized-error raw 桥。

新增的 `VonMangoldtHardyLittlewoodNormalizedEstimate` 是显式阈值版本：解析侧给出具体 `threshold` 和固定 `relativeError < 1`，证明所有偶数 `n > threshold` 上的奇异级数正下界与归一化误差界后，Lean 直接推出正线性 raw Λ 下界，避免从 `eventually` 命题中抽取不可见阈值。

新增的 `VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate` 固定使用 `goldbachSingularSeriesFromQuarter` 和系数 `1/4`，并自动接入 canonical weight-sum 污染扣除路线。使用这条入口时，解析侧只需要给出该固定主项下的逐点归一化 raw Λ 误差界和最终阈值覆盖。

新增的 `VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate` 是更窄的一边下界入口：解析侧只需证明 `(1 - relativeError) * goldbachSingularSeriesFromQuarter(n) * n <= RawVonMangoldtGoldbachSum n`，再给出显式 canonical 污染预算支配。Lean 用 `one_fourth_le_goldbachSingularSeriesFromQuarter` 自动转成正线性 raw Λ 下界，并由 `threshold` 与 `contaminationThreshold` 合成最终阈值；这条入口现在也有 JSON 证书模板。

新增的 `VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate` 把这一边下界再拆到 major/minor 层：解析侧给出 `Raw = Major + Minor`、`(1-relativeError)*goldbachSingularSeriesFromQuarter(n)*n + minorArcError(n) <= Major(n)`、`-minorArcError(n) <= Minor(n)` 和显式 canonical 污染预算支配，Lean 自动合成 `rawRelativeLowerBound` 并进入上面的 lower-bound handoff。这条 Lean 入口还没有单独 JSON 模板。

新增的 `DiscreteCircleMethod.VonMangoldtFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate` 把同一条一边 lower-bound handoff 固定到 Fourier major/minor 分解上：Lean 自动使用 `rawVonMangoldtGoldbachSum_eq_fourier_major_add_minor` 给出 `Raw = Major + Minor`，并把 `‖MinorComplex(n)‖ <= minorArcError(n)` 转成 `-minorArcError(n) <= Minor(n)`。进一步的 `VonMangoldtDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate` 和 fixed-error 版本把 minor arc 义务压成统一 DFT 上界 `‖S(k)‖ <= M(n)`，其中 fixed-error 版本直接使用 `M(n)^2` 作为保留误差；新的 `VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate` 还把污染项字段从直接 `contaminationDominated` 降成 `contaminationThreshold >= 2` 加显式 `sqrt(n)*log(n)^3` 模型界。fixed-error DFT 一边路线已有 JSON 证书模板 `analytic_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_handoff_certificate.example.json`。

新增的 `rawVonMangoldtGoldbachSum_eq_weight_sum` 和 `rawVonMangoldtGoldbachSum_eq_arithmeticFunction_sum` 固定了 raw Λ 卷积的记号边界：`RawVonMangoldtGoldbachSum n` 就是 `Finset.range n.succ` 上的有限和 `sum_m Λ(m)Λ(n-m)`。后续 major/minor arc 估计必须落在这个同一对象上。

新增的 `Gdbh/DiscreteCircleMethod.lean` 把 raw Λ 卷积接到有限 `ZMod (n+1)` 傅里叶反演：Lean 证明 `zmodDftConvolution_apply`、`zmodConvolution_eq_fourier_sum`，并专门化成 `rawVonMangoldtGoldbachSum_eq_fourier_major_add_minor`。因此只要解析侧选择每个 `n` 的 major 频率集合，`RawVonMangoldtGoldbachSum n = Major(n) + Minor(n)` 这条 decomposition 不再需要作为外部解析义务；新的 `VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate` 自动使用这个恒等式，剩下的是 major arc 近似、minor arc 贡献界、线性总误差界和最终污染阈值覆盖。该文件还提供 `VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate`，允许解析侧直接证明复数频率和的范数界；Lean 用 `Complex.abs_re_le_norm` 自动转成实部估计。Fourier 项也已命名为显式 DFT 平方项 `1/(n+1) * e(kn/(n+1)) * S(k)^2`，并证明了 major 复贡献可由逐频率 DFT 平方项近似模型项再加模型和误差得到主项近似界；次弧复贡献可由这些项在 minor 频率集合上的逐项上界求和控制。解析侧也可以直接给出 `‖S(k)‖` 型统一上界和频率数量上界，Lean 自动平方、乘归一化因子并汇总成 minor arc 贡献界。使用所有 `n+1` 个频率的平凡数量上界时，Lean 还直接给出 `‖Minor‖ <= M(n)^2` 的交接形式；也可以走 L2 型平方和接口，直接证明 `(1/(n+1))*sum_minor ‖S(k)‖^2 <= minorArcError(n)`，或给每个 minor 频率不同上界 `B(k)` 并证明 `(1/(n+1))*sum_minor B(k)^2 <= minorArcError(n)`。`VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate` 把这些 major 模型项字段、minor L2 平方和字段和 total linear error 字段打包成当前最直接的 DFT 级 circle-method handoff，并自动转入复数 Fourier handoff；`VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate` 进一步把 minor L2 字段压缩成统一 DFT 上界、minor 频率数量上界和一个标量平方误差不等式。`VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate` 则使用平凡频率数上界和傅里叶归一化，直接把 minor 部分压成 `minorArcDftBound(n)^2 <= minorArcError(n)`。新的 `VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound` 给出更短的正线性 DFT 路线：解析侧若能证明 major 实部至少为 `coefficient*n + minorArcError(n)`，并给出同样的统一 minor DFT 界和 `M(n)^2 <= minorArcError(n)`，Lean 会直接转成 raw Λ 正线性下界并接 canonical 污染项扣除。`VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound` 进一步把最终污染阈值改成显式 `contaminationThreshold` 和逐点 `contaminationDominated` 证明，避免覆盖 noncomputable `canonicalLinearContaminationThreshold`。`VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound` 再把 minor 预算固定为 `minorArcDftBound(n)^2`，Lean 内部自动生成 `minorArcError` 和平方误差证明，少交一个独立解析义务。

新增的 `VonMangoldtHardyLittlewoodAbsErrorEstimate` 和 `raw_normalized_error_bound_of_hardy_littlewood_abs_error_bound` 覆盖更常见的显式绝对误差写法：若解析侧先证明 `|RawVonMangoldtGoldbachSum n - singularSeries(n)*n| <= relativeError * singularSeries(n)*n`，Lean 会利用同一个奇异级数正下界把它转换成证书要求的归一化误差界。

新增的 `VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate` 把上述绝对误差入口接到推荐的 canonical weight-sum 路线：Lean 负责从绝对误差转 normalized error、使用 canonical prime-power weight-sum 上界，并保留 direct raw weight-sum 阈值拆分。

新增的 `VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate`、`VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate`、split-threshold canonical 版本和 `VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate` 把 major/minor arc 输出再往前接一层：解析侧可以先证明 `|Raw-main| <= majorArcError + minorArcError` 和 `majorArcError + minorArcError <= relativeError * main`，Lean 会合成为总绝对误差，再进入 normalized/canonical handoff。quarter split 版本固定 `main = goldbachSingularSeriesFromQuarter(n) * n` 和系数 `1/4`。

新增的 `VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate` 是更贴近圆法论文结构的 R2/R3 入口：解析侧可分别给出 `Raw = majorArcContribution + minorArcContribution`、major arc 对 `goldbachSingularSeriesFromQuarter(n) * n` 的近似误差界，以及 minor arc 贡献界；Lean 用三角不等式自动合成 quarter split absolute-error handoff。

新增的 `VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate` 再把 total-error 义务压成常见的线性输出形态：解析侧只需证明 `majorArcError(n) + minorArcError(n) <= epsilon * n`，并给出 `epsilon <= relativeError / 4`；Lean 使用 `goldbachSingularSeriesFromQuarter(n) >= 1/4` 自动恢复 `majorArcError + minorArcError <= relativeError * goldbachSingularSeriesFromQuarter(n) * n`。

新增的 `VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate` 是完全显式阈值版本：除上述 Hardy-Littlewood 归一化误差外，还要求解析侧给出 `NonPrimePrimePowerVonMangoldtWeightSum` 的显式上界并证明污染预算被有效主项压倒；最终拼接条件就是 `estimate.threshold <= B`，没有隐藏的渐近阈值。

## 本目录文件

- `completion_audit.md`：当前目标完成度审计，记录哪些要求已有证据、哪些仍缺失。
- `proof_status.json`：机器可读的证明状态摘要，明确记录当前还没有完整证明；顶层 `blocking_obligations` 给出当前剩余 Lean 目标、推荐 canonical HL 路线缺少的证明项、quarter explicit-contamination canonical shortcut、positive-linear raw canonical shortcut、positive-linear raw explicit-contamination canonical shortcut、positive-linear canonical major/minor shortcut、positive-linear explicit-contamination canonical major/minor shortcut、备用显式 weight-sum 路线和最终检查命令模板；顶层 `attack_plan` 给出逐阶段攻克顺序、交付物和验收门禁。
- `generate_proof_status.py`：从证书 manifest 和 Lean 公理审计配置生成 `proof_status.json`。
- `analytic_attack_plan.md`：人类可读的解析攻坚计划，按 singular series、显式阈值、raw estimate ledger、major/minor arcs、有限证书扩展和最终 handoff 排序。
- `certificate_manifest.json`：记录当前生成证书的上界、生成命令和 SHA-256。
- `analytic_handoff_certificate.py`：校验 Hardy-Littlewood weight-sum、canonical weight-sum、quarter canonical weight-sum、quarter explicit-contamination canonical weight-sum、positive-linear raw canonical weight-sum、positive-linear raw explicit-contamination canonical weight-sum、positive-linear canonical major/minor、positive-linear explicit-contamination canonical major/minor、quarter major/minor decomposition、quarter linear-error decomposition、DFT/L2 minor-arc、uniform-minor DFT、uniform-minor-square DFT、direct positive-linear uniform-minor-square DFT explicit-contamination、fixed-square-error direct positive-linear uniform-minor-square DFT explicit-contamination，以及 fixed-error DFT quarter one-sided sqrt-log contamination 等解析交接证书的机器可读字段和 Lean imports，区分结构合法、估计对象完成 `estimate_complete` 和最终交接完成 `complete`；可用 `--check-formalized-lean` 核对已经标为 formalized 的局部义务，估计对象完整时再用 `--check-lean` 核对 Lean 义务声明的精确类型以及生成的 handoff wrapper，并用 `--export-lean` 生成 Lean 交接包装。如果证书同时给出 `finiteCertificateTheorem`，导出的 Lean 文件会额外生成无参数的 `StrongGoldbach` theorem。
- `analytic_handoff_certificate.example.json`：解析交接证书模板；当前使用 Lean 已证明的 quarter-base singular-series 下界和 canonical sqrt-log prime-power weight-sum 上界，但仍缺 HL 归一化误差和显式污染预算支配，不构成解析证明。
- `analytic_canonical_handoff_certificate.example.json`：canonical weight-sum 解析交接证书模板；Lean 负责 quarter-base singular-series 下界、canonical weight-sum 上界，并把 eventual 污染支配包装成命名的 `canonicalHLContaminationThreshold` 及 split-threshold direct raw weight-sum 桥；模板现在只留下 HL 归一化误差解析义务。该义务形式化后只能得到 `estimate_complete: true`；最终仍需在 `derivedThresholdBound` 字段给出派生 direct raw weight-sum 阈值被有限证书覆盖的 Lean 证明项，并让 `--check-lean` 在生成 wrapper 的上下文中通过，才能得到可用的最终 handoff。
- `analytic_quarter_canonical_handoff_certificate.example.json`：quarter canonical weight-sum 解析交接证书模板；字段直接对应 `VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate`。Lean 固定使用 `goldbachSingularSeriesFromQuarter`、系数 `1/4` 和 `one_fourth_le_goldbachSingularSeriesFromQuarter`，所以模板只要求形式化该固定主项下的逐点 raw 归一化误差，最终可用 `canonicalContaminationThresholdBound` 加显式 threshold 覆盖完成 handoff。
- `analytic_quarter_explicit_contamination_canonical_handoff_certificate.example.json`：quarter explicit-contamination canonical 证书模板；字段直接对应 `VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate`。Lean 固定 `goldbachSingularSeriesFromQuarter`、系数 `1/4` 和奇异级数下界，解析侧只需形式化逐点 raw 归一化误差和显式 canonical 污染预算支配；最终阈值由 `threshold` 与 `contaminationThreshold` 自动合成。
- `analytic_quarter_lower_bound_explicit_contamination_canonical_handoff_certificate.example.json`：quarter lower-bound explicit-contamination canonical 证书模板；字段对应 `VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate`。解析侧只需形式化 `rawRelativeLowerBound` 和 `contaminationDominated`，不要求 `rawNormalizedErrorBound` 的上侧误差；可选 `contamination_sqrt_log_model_bound` 能通过已形式化的 sqrt-log 比较定理导出污染支配。
- `analytic_positive_linear_raw_canonical_handoff_certificate.example.json`：positive-linear raw canonical 证书模板；字段直接对应 `VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound`。解析侧只需形式化逐点 `coefficient * n <= RawVonMangoldtGoldbachSum n`，Lean 固定 canonical non-prime-prime-power weight-sum 上界并自动引入 `canonicalLinearContaminationThreshold`；最终仍需 `canonicalContaminationThresholdBound` 或直接 `derivedThresholdBound` 覆盖阈值。
- `analytic_positive_linear_raw_explicit_contamination_canonical_handoff_certificate.example.json`：positive-linear raw explicit-contamination canonical 证书模板；字段直接对应 `VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound`。解析侧给出逐点 raw 正线性下界和显式 canonical 污染预算支配阈值；最终阈值由 `rawThreshold` 与 `contaminationThreshold` 自动合成，不需要覆盖 noncomputable `canonicalLinearContaminationThreshold`。
- `analytic_positive_linear_canonical_major_minor_handoff_certificate.example.json`：positive-linear canonical major/minor 证书模板；字段直接对应 `VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate`。解析侧需形式化 `mainTerm - majorArcError <= RawVonMangoldtGoldbachSum + minorArcError` 和 `coefficient*n + minorArcError <= mainTerm - majorArcError` 两条逐点不等式；Lean 自动消去 minor error、使用 canonical weight-sum 上界并加入 `canonicalLinearContaminationThreshold`，最终仍需 `canonicalContaminationThresholdBound` 或直接 `derivedThresholdBound` 覆盖阈值。
- `analytic_positive_linear_explicit_contamination_canonical_major_minor_handoff_certificate.example.json`：positive-linear explicit-contamination canonical major/minor 证书模板；字段直接对应 `VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate`。它仍由 Lean 固定 canonical weight-sum 上界，但解析侧显式提交 `contaminationThreshold` 和污染预算支配不等式，因此最终阈值由 `combinedThreshold`、`linearNetThreshold`、`contaminationThreshold` 三个数值字段自动合成，不再需要覆盖 noncomputable `canonicalLinearContaminationThreshold`。
- `analytic_decomposition_handoff_certificate.example.json`：quarter-base major/minor decomposition 证书模板；字段直接对应 `VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate`，要求形式化 raw decomposition、major arc 近似、minor arc 贡献界、total analytic error 支配和最终 `canonicalContaminationThresholdBound`。四个显式解析阈值字段由生成的 Lean wrapper 自动组合成 direct raw weight-sum 阈值证明；仍可用 `derivedThresholdBound` 作为直接阈值证明的后备路径。模板合法但没有任何解析义务证明。
- `analytic_linear_decomposition_handoff_certificate.example.json`：quarter-base linear-error decomposition 证书模板；字段直接对应 `VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate`，把 total-error 义务写成 `majorArcError + minorArcError <= analyticErrorCoefficient * n`，并要求 `analyticErrorCoefficient <= relativeError/4`。生成的 Lean wrapper 会自动接入 `total_analytic_error_bound_of_quarter_linear_error_bound` 和同一套 canonical contamination 阈值交接。模板合法但没有任何解析义务证明。
- `analytic_dft_model_l2_handoff_certificate.example.json`：DFT-level L2 minor-arc 证书模板；字段直接对应 `DiscreteCircleMethod.VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate`，要求形式化 major frequency 的逐项 DFT-square 模型逼近、模型和逼近、major error 汇总、minor DFT 点态界、minor L2 平方和界、total linear error bound 和最终 `canonicalContaminationThresholdBound`。这是当前最直接贴近圆法 major/minor arc 的机器可读入口，模板合法但没有任何解析义务证明。
- `analytic_dft_model_uniform_minor_handoff_certificate.example.json`：uniform-minor DFT 证书模板；字段直接对应 `DiscreteCircleMethod.VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate`，保留同一套 major DFT-square 模型义务，但把 minor 部分改成统一 DFT 上界、minor 频率数量上界和一个标量平方误差不等式。模板合法但没有任何解析义务证明。
- `analytic_dft_model_uniform_minor_sq_handoff_certificate.example.json`：uniform-minor-square DFT 证书模板；字段直接对应 `DiscreteCircleMethod.VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate`，保留同一套 major DFT-square 模型义务，但让 Lean 使用平凡 minor 频率数上界和平方型 uniform-bound 桥，把 minor 部分压成统一 DFT 上界与 `minorArcDftBound(n)^2 <= minorArcError(n)`，不再要求单独证明非负性。模板合法但没有任何解析义务证明。
- `analytic_dft_uniform_minor_sq_positive_linear_explicit_contamination_handoff_certificate.example.json`：direct positive-linear uniform-minor-square DFT explicit-contamination 证书模板；解析侧直接证明 major 实部至少为 `coefficient*n + minorArcError(n)`，再给出 uniform minor DFT 界、`minorArcDftBound(n)^2 <= minorArcError(n)` 和显式 canonical 污染预算支配。最终阈值由 major、minor、contamination 三个阈值自动合成。
- `analytic_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_handoff_certificate.example.json`：fixed-square-error direct positive-linear uniform-minor-square DFT explicit-contamination 证书模板；解析侧把 major lower bound 写成 `coefficient*n + minorArcDftBound(n)^2 <= Major(n)`，Lean 内部令 `minorArcError := minorArcDftBound(n)^2`，因此不再需要独立 `minorArcError` 字段和 `minor_arc_dft_bound_sq_error_bound` 义务。这是当前最窄的 DFT 交接表面，模板合法但没有任何解析义务证明。
- `analytic_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_handoff_certificate.example.json`：fixed-error DFT quarter one-sided sqrt-log contamination 证书模板；解析侧证明 major lower bound、uniform minor DFT 界和显式 `sqrt(n)*log(n)^3` 污染模型界，Lean 负责从 `contaminationThreshold >= 2` 导出 canonical prime-power 污染预算支配。uniform minor DFT 界也可用标准 off-major-arcs 形式 `k ∉ majorArcs(n)` 提交，Lean 通过 `DiscreteCircleMethod.minorArcDftBoundValid_of_not_mem_majorArcs` 转成 handoff 需要的 minor-frequency 形式；若解析侧证明的是所有非零频率的统一界，则再给出 `0 ∈ majorArcs(n)`，Lean 可用 `DiscreteCircleMethod.minorArcDftBoundValid_of_ne_zero_of_zero_mem_majorArcs` 接入同一 handoff。
- `Gdbh/Goldbach.lean`：Lean 形式化定义、有限证书示例和条件拼接定理。
- `Gdbh/FiniteIntervals.lean`：分块有限证书接口，证明区间证书 `GoldbachBetween A B` 可以拼接成更大的 `GoldbachUpTo B`；生成器支持单区间、chunked 区间和从 2 开始的自包含 chunked 输出，自包含输出会导出 `ExplicitGoldbachLowerBound 100` 字面目标桥和所有已形式化解析接口的最终 `StrongGoldbach` 桥。
- `Gdbh/Certificate100.lean`：由 `verify_goldbach.py` 生成的 Lean 可检查有限证书，证明 `GoldbachUpTo 100`；它保持在低层，不依赖解析接口，配合任意覆盖阈值的 `ExplicitGoldbachLowerBound T` 直接得到 `ExplicitGoldbachLowerBound 100` 的条件桥在 `Gdbh/AnalyticBridge.lean` 中给出。
- `Gdbh/AnalyticBridge.lean`：解析下界接口，证明 `ExplicitGoldbachLowerBound 100` 等价于当前剩余目标。
- `Gdbh/SingularSeries.lean`：Goldbach 奇异级数下界的第一块形式化，证明有限 odd-prime 局部修正因子乘积不小于 `1`，证明任意非负 base 项乘以该局部乘子不会低于 base，并给出当前证书可直接引用的 `goldbachSingularSeriesFromQuarter` 与 `one_fourth_le_goldbachSingularSeriesFromQuarter`；`VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate` 已把这组下界固定进 canonical HL 入口。raw 归一化误差义务仍必须使用同一个 `singularSeries` 归一化，或同时替换该字段和下界定理。
- `Gdbh/DiscreteCircleMethod.lean`：有限圆法恒等式层，证明 `ZMod N` 上卷积的 DFT 是 DFT 乘积，证明 inverse DFT 的频率和可按任意 major/minor 频率集合拆分，并把 `ZMod (n+1)` 专门化回 `RawVonMangoldtGoldbachSum n`；提供 complex-valued/real-valued Fourier major/minor contributions、显式 DFT 平方项 `rawVonMangoldtDftSquareFourierTerm`、major arc 逐频率模型项近似桥、次弧逐项求和范数桥、`‖S(k)‖` 型 minor arc 上界桥、L2 型 minor arc 平方和桥、直接 `M(n)^2` minor arc 桥、自动 raw decomposition 的 `VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate`、接受复数范数 major/minor 估计的 `VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate`，以及打包 major 模型项和 minor L2 平方和义务的 `VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate`；uniform-minor 变体可由统一 DFT 上界、minor 频率数量上界和一个标量平方误差不等式自动构造 L2 handoff，uniform-minor-square 变体则用平凡频率数上界直接接受 `M(n)^2 <= minorArcError(n)`；正线性 Fourier/DFT 变体可直接从 `Major >= coefficient*n + minorError` 和 minor DFT 统一界推出 raw Λ 正线性下界，显式污染版本还可用数值 `contaminationThreshold` 直接闭合最终阈值，fixed-square-error 版本把 minor error 固定为 `M(n)^2` 以删除独立平方误差义务。
- `Gdbh/Conditional.lean`：条件证明接口，用于表达 GRH 或 Hardy-Littlewood 型假设如何推出强哥德巴赫。
- `Gdbh/CircleMethod.lean`：抽象圆法下界接口，证明主项压倒误差项的计数下界可推出强哥德巴赫。
- `Gdbh/MajorMinorArcs.lean`：把圆法接口细化为 major arc 下界和 minor arc 误差共同推出计数下界的 Lean 工作包。
- `Gdbh/WeightedGoldbach.lean`：加权 Goldbach 和的桥接层，证明素数支撑权重的带权和为正足以推出普通两个素数表示，并证明素数指示权重的带权和等于 `GoldbachCount`。
- `Gdbh/WeightedMajorMinorArcs.lean`：带权 major/minor arc 拼接层，把带权圆法估计转成 `WeightedGoldbachLowerBound`。
- `Gdbh/ContaminatedWeightedGoldbach.lean`：原始带权卷积与非素数对污染项扣除层，适合 von Mangoldt/素数幂型权重；证明总带权和严格大于非素数对贡献时可推出普通 Goldbach 表示。
- `Gdbh/RealContaminatedWeightedGoldbach.lean`：实数非负权重版本的污染项扣除层，适合含 `log p` 的 von Mangoldt 型权重；证明实数带权和严格大于非素数对贡献时可推出普通 Goldbach 表示。
- `Gdbh/VonMangoldtGoldbach.lean`：mathlib `ArithmeticFunction.vonMangoldt` 的专用接口，证明 `Λ` 权重非负，证明 `RawVonMangoldtGoldbachSum n` 等于 `Finset.range n.succ` 上的 `sum_m Λ(m)Λ(n-m)`，证明非素数对污染项等于素数幂污染项，证明素数幂污染项可由左右两侧污染项控制，证明左右污染项可由逐点项上界和有限和上界控制，证明统一逐项上界乘以污染集合个数上界足以控制污染和，证明左右污染集合个数都不超过 `NonPrimePrimePowerCount n`，证明 `NonPrimePrimePowerCount n <= n + 1`，证明更强的 `NonPrimePrimePowerCount n <= (sqrt n + 1)*(log₂ n + 1)`，定义 `NonPrimePrimePowerVonMangoldtWeightSum` 并证明更紧的污染项上界 `PrimePowerContaminationVonMangoldtGoldbachSum n <= 2 * (NonPrimePrimePowerVonMangoldtWeightSum n * log n)`，同时证明 `NonPrimePrimePowerVonMangoldtWeightSum n <= NonPrimePrimePowerCount n * log n` 及其 sqrt-log 计数上界版本，从而旧的 `VonMangoldtSqrtLogCountRawLowerBound` 可自动转换为新的 `VonMangoldtDirectRawWeightSumLowerBound`，正线性 raw Λ、relative-error raw Λ、relative-error major/minor arc、eventually raw Λ 和 eventually major/minor arc 下界也可直接走 weight-sum 终局桥，并提供 `VonMangoldtSplitThresholdDirectRawWeightSumLowerBound` 自动取 raw 下界和 weight-sum 上界两个阈值的最大值，提供 `VonMangoldtEventuallyDirectRawWeightSumLowerBound` 从两个 eventually raw weight-sum 条件自动抽取阈值，提供 `VonMangoldtPositiveLinearRawWeightSumLowerBound` 把 `Raw Λ >= c*n` 与任意 weight-sum 污染预算支配条件合并，提供 `VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound` 把 `Raw Λ >= (1-delta)*mainTerm` 和 `mainTerm >= c*n` 合成为正线性 raw Λ 桥，提供 `VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound` 把 eventually 形式的渐近主项 raw Λ 下界压成有效正线性 raw Λ 桥，提供 `VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate` 把 `major + minor <= delta*mainTerm` 的 major/minor arc 相对误差形式转回 relative-error raw 桥，提供 `VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate` 自动取 main、combined、total error、weight-sum 和 contamination 五个阈值的最大值，提供 `VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate` 从五个 eventually relative-error 条件抽取共同阈值，提供 `VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate` 把三条 eventual relative-error major/minor 条件转成正线性 net 下界并自动使用 Lean 证明的 sqrt-log 污染预算，提供 `VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate` 自动取三条显式 relative-error sqrt-log 条件阈值的最大值并自动使用 sqrt-log 污染预算，提供 `VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound` 自动取 weight-sum、raw 线性下界和污染预算支配三个阈值的最大值，提供 `VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound` 从三个 eventually 条件抽取共同阈值，提供 `VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate` 把正线性 major/minor arc 估计与任意 weight-sum 污染预算合并，提供 `VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate` 把四个显式 major/minor/weight-sum 阈值合并到三阈值 raw 桥，提供 `VonMangoldtDirectWeightSumMajorMinorArcEstimate` 直接表达 `major + minor + 2*weightSumBound*log n < main` 的解析交接，提供 `VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate` 自动取三个显式阈值的最大值，并提供 `VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate` 从 eventually 形式自动抽取阈值；证明实变量模型 `sqrt(x)*(log x)^3 = o(x)`，并把它转移到精确自然数污染预算：任意 `c > 0` 时最终有 `2 * vonMangoldtLogCountContaminationBudget nonPrimePrimePowerSqrtLogCountBound n < c*n`；同时证明两个 `Λ` 因子各自有上界时其乘积由上界平方控制，并用 mathlib 的 `ArithmeticFunction.vonMangoldt_le_log` 证明素数幂上 `Λ(m) <= log n`；最终把 `VonMangoldtDirectRawWeightSumLowerBound`、`VonMangoldtSplitThresholdDirectRawWeightSumLowerBound`、`VonMangoldtEventuallyDirectRawWeightSumLowerBound`、`VonMangoldtPositiveLinearRawWeightSumLowerBound`、`VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound`、`VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound`、`VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound`、`VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate`、`VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate`、`VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate`、`VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate`、`VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate`、`VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound`、`VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound`、`VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate`、`VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate`、`VonMangoldtDirectWeightSumMajorMinorArcEstimate`、`VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate`、`VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate`、`VonMangoldtSqrtLogCountRawLowerBound`、`VonMangoldtSqrtLogCountLinearRawLowerBound`、`VonMangoldtPositiveLinearRawLowerBound`、`VonMangoldtEventuallyPositiveLinearRawLowerBound`、`VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate` 和 `VonMangoldtSqrtLogCountMajorMinorArcEstimate` 接到最终强哥德巴赫桥，其中正线性接口会自动选择污染预算被 `c*n` 支配的后续阈值，relative-error 接口会把 `(1-delta)*mainTerm` 自动压缩成有效正线性系数 `(1-delta)*c`，eventually relative-error raw 接口会从渐近主项下界抽取共同阈值，relative-error major/minor arc 接口会把 combined bound 和总解析误差占比合成 raw 相对误差下界，split-threshold relative-error major/minor arc 接口允许这些条件有五个显式阈值，eventually relative-error major/minor arc 接口允许这些条件只以 `∀ᶠ n in atTop` 形式给出并自动抽取共同阈值，eventually relative-error sqrt-log count 接口进一步让 Lean 自动承担污染预算支配，split-threshold relative-error sqrt-log count 接口保留 main/combined/error 三个显式阈值并自动加入污染预算阈值，positive-linear raw weight-sum 接口允许解析侧使用任意显式 weight-sum 上界，split-threshold 版本允许解析侧给出分开的显式阈值，eventually 接口还会从 `∀ᶠ n in atTop` 形式自动抽取 raw Λ 下界阈值，eventually major/minor 接口会把 `c*n + minor <= main - major <= Raw + minor` 自动转成 raw Λ 正线性下界，eventually positive-linear weight-sum major/minor 接口会同时携带任意 weight-sum 上界和预算支配条件，split-threshold positive-linear weight-sum major/minor 接口会把 combined/linear 两个阈值合成 raw 阈值后接三阈值 raw 桥，eventually direct weight-sum major/minor 接口会先合并三项 weight-sum 条件再抽取共同阈值。
  该文件还固定了 `canonicalNonPrimePrimePowerVonMangoldtWeightSumBound`，并证明它满足完全显式 HL weight-sum 证书里的 `NonPrimePrimePowerVonMangoldtWeightSum n <= weightSumBound n` 义务。
  同时证明该 canonical weight-sum 污染预算最终小于任意正线性函数，特别是最终小于 HL 有效系数 `((1-relativeError)*coefficient)*n`；这仍不是显式阈值证书，还需要给出具体 threshold。
  新增的 `VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound` 把这条 canonical 污染预算直接接到正线性 raw Λ 下界：解析侧只需证明 `coefficient * n <= RawVonMangoldtGoldbachSum n`，Lean 自动补上 canonical weight-sum 上界和 `canonicalLinearContaminationThreshold`，最后仍需显式阈值覆盖。
  新增的 `VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate` 把同一 canonical 污染预算接到显式 major/minor 正线性净下界：解析侧证明 `mainTerm - majorArcError <= RawVonMangoldtGoldbachSum + minorArcError` 和 `coefficient*n + minorArcError <= mainTerm - majorArcError` 后，Lean 消去 minor error 得到 raw Λ 正线性下界。
  `VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound` 是 abs-error raw 入口，会把绝对值误差形式自动转换为 eventually relative-error raw 桥。
  `VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound` 是 little-o raw 入口，会把 `|Raw-main| = o(main)` 转成固定相对误差 `1/2` 的 abs-error raw 桥。
  `VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound` 是 asymptotic-equivalent raw 入口，会把 `Raw ~ main` 展开为 little-o 误差形式。
  `VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound` 是 normalized-error raw 入口，会把 `(Raw-main)/main -> 0` 转成固定相对误差 `1/2` 的 abs-error raw 桥。
  `VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate` 是 Hardy-Littlewood 主项入口，会把 `singularSeries(n) * n` 的归一化误差形式转入 normalized-error raw 桥。
  `VonMangoldtHardyLittlewoodNormalizedEstimate` 是显式阈值 Hardy-Littlewood 主项入口，会把固定相对误差界转成有效系数 `(1-relativeError)*coefficient` 的正线性 raw Λ 桥。
  `raw_normalized_error_bound_of_hardy_littlewood_abs_error_bound`、`VonMangoldtHardyLittlewoodAbsErrorEstimate` 和 `VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate` 让显式 major/minor arc 总绝对误差界直接转成证书需要的 normalized error 义务，并可走 canonical weight-sum 终局桥。
  `raw_abs_error_bound_of_hardy_littlewood_major_minor_abs_error_bound` 和 `VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate` 进一步把 major/minor error ledger 接到这条路线，并保留 singular-series、major/minor 绝对误差、总误差三个显式阈值。
  `VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate` 使用同样的显式 HL 主项条件，但固定使用 Lean 已证明的 canonical weight-sum 上界和 eventually 污染支配，自动接入 eventually direct raw weight-sum 桥。
  `VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate` 进一步携带显式 prime-power weight-sum 污染预算，直接进入 `VonMangoldtDirectRawWeightSumLowerBound`，最终阈值就是结构里的 `threshold`。
- `Gdbh/GeneralHandoff.lean`：通用阈值拼接层，证明有限证书上界 `B` 可以和任意阈值 `<= B` 的解析下界组合推出强哥德巴赫；同时证明同样的数据可直接推出字面目标 `ExplicitGoldbachLowerBound 100`，因此完整解析 wrapper 会导出 `explicitLowerBound100_from_*`。
- `research_plan.md`：Lean4 中继续推进无条件证明所需的解析数论路线图。
- `audit_lean_source.py`：语法级审计 `Gdbh.lean` 和 `Gdbh/**/*.lean`，忽略注释/字符串后检查 `axiom`、`constant`、`opaque`、`unsafe`、`sorry`、`admit`，防止在项目源码里引入假设或占位证明。
- `audit_lean_axioms.py`：用 Lean 的 `#print axioms` 审计关键定理是否只依赖允许的基础公理；这是环境级依赖检查，和源码语法审计互补。
- `test_no_project_axioms.py`：测试源码审计器本身，并检查本项目 Lean 源文件没有使用上述禁用 token 来伪造证明。
- `test_proof_status.py`：检查 `proof_status.json` 的生成逻辑会记录未完成状态和剩余目标。
- `test_analytic_handoff_certificate.py`：检查解析交接证书校验器会拒绝坏常数、能 Lean-check 局部 formalized 义务，并且不会把模板误判为完整证明。
- `test_generated_lean_certificates.py`：生成完整、单区间和 chunked 临时 Lean 证书，并调用 Lean 内核检查。
- `lakefile.lean`、`lean-toolchain`：Lean/mathlib 项目配置。
- `proof_audit.md`：审查任何强哥德巴赫证明草稿时使用的清单。
- `references.md`：当前已知结果、常用引用和它们不能直接完成证明的原因。
- `verify_goldbach.py`：有限范围计算验证工具。
- `analyze_von_mangoldt.py`：有限范围 raw von Mangoldt 卷积、实际非素数对污染、count/log 污染预算和 weight-sum 污染预算比例探索工具。
- `test_verify_goldbach.py`：验证计算工具本身行为的单元测试。

## 下一步工作方式

如果有证明草稿，按以下结构放入本目录最容易审查：

```text
theorem.md      # 完整证明草稿
lemmas.md       # 单独列出的引理、假设和引用
computations.md # 若使用计算验证，写明上界、算法和可复现实验
```

审查时优先检查量词、误差项、区间覆盖和是否暗含未证明的素数分布假设。
