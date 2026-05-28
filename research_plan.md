# Lean4 强哥德巴赫证明路线图

## 当前形式化目标

当前 Lean 项目已经把完整强哥德巴赫猜想压缩为以下接口：

```lean
ExplicitGoldbachLowerBound 100
```

它展开后是：

```lean
∀ n : Nat, 100 < n → Even n → 0 < GoldbachCount n
```

也就是说，要真正完成证明，必须无条件证明 `100` 以上每个偶数的 Goldbach 表示计数为正。

## 解析数论需要补上的核心定理

一个可接入 Lean 的证明应当最终给出：

```lean
theorem explicit_goldbach_lower_bound_100 :
    ExplicitGoldbachLowerBound 100 := ...
```

该定理不能使用 `axiom`、`sorry`、`admit`，也不能依赖 GRH、Hardy-Littlewood 猜想或随机模型，除非目标明确改成条件证明。

## 最有希望的无条件路线

### 1. 显式圆法下界

目标是为 Goldbach 表示计数建立有效下界：

```text
GoldbachCount n >= main_term(n) - error_term(n)
```

需要证明：

- `main_term(n)` 在所有足够大偶数上严格为正。
- `error_term(n) < main_term(n)`，且所有常数有效。
- 阈值 `N0` 是具体自然数。
- `N0 <= 100 + 1`，或者有限证书覆盖到 `N0 - 1`。

如果 `N0` 大于当前证书上界，应先生成更大的 Lean 有限证书，或接入可验证分块证书。

该拼接在 Lean 中已经是通用的：`GeneralHandoff.lean` 证明了只要有 `GoldbachUpTo B` 和阈值 `T <= B` 的解析下界，就能推出 `StrongGoldbach`。因此后续解析证明若只能覆盖巨大阈值，不需要改核心定理，只需要把有限证书上界提高到该阈值。

有限证书也已经支持分块：`FiniteIntervals.lean` 定义 `GoldbachBetween A B`，并证明可由区间证书拼接成更大的 `GoldbachUpTo B`。从 `2` 开始生成的自包含 chunked 证书还会同时导出连接最终 `StrongGoldbach` 的条件定理，覆盖 `ExplicitGoldbachLowerBound`、`CircleMethodLowerBound`、`MajorMinorArcEstimate`、`GoldbachCountPositiveAbove`、`WeightedGoldbachLowerBound`、`WeightedMajorMinorArcEstimate`、`ContaminatedWeightedGoldbachLowerBound`、`ContaminatedWeightedMajorMinorArcEstimate`、`RealContaminatedWeightedGoldbachLowerBound`、`RealContaminatedWeightedMajorMinorArcEstimate`、`VonMangoldtGoldbachLowerBound`、`VonMangoldtMajorMinorArcEstimate`、`VonMangoldtPrimePowerContaminationLowerBound`、`VonMangoldtPrimePowerContaminationMajorMinorArcEstimate`、`VonMangoldtSplitPrimePowerContaminationLowerBound`、`VonMangoldtSplitPrimePowerContaminationMajorMinorArcEstimate`、`VonMangoldtPointwiseSplitContaminationLowerBound`、`VonMangoldtPointwiseSplitContaminationMajorMinorArcEstimate`、`VonMangoldtUniformSplitContaminationLowerBound`、`VonMangoldtUniformSplitContaminationMajorMinorArcEstimate`、`VonMangoldtCountedSplitContaminationLowerBound`、`VonMangoldtCountedSplitContaminationMajorMinorArcEstimate`、`VonMangoldtTrivialCountSplitContaminationLowerBound`、`VonMangoldtTrivialCountSplitContaminationMajorMinorArcEstimate`、`VonMangoldtWeightBoundSplitContaminationLowerBound`、`VonMangoldtWeightBoundSplitContaminationMajorMinorArcEstimate`、`VonMangoldtLogWeightSplitContaminationLowerBound`、`VonMangoldtLogWeightSplitContaminationMajorMinorArcEstimate`、`VonMangoldtCountBoundLogWeightSplitContaminationLowerBound`、`VonMangoldtCountBoundLogWeightSplitContaminationMajorMinorArcEstimate`、`VonMangoldtCanonicalLogCountContaminationLowerBound`、`VonMangoldtCanonicalLogCountContaminationMajorMinorArcEstimate`、`VonMangoldtDirectRawLogCountLowerBound`、`VonMangoldtDirectRawWeightSumLowerBound`、`VonMangoldtSplitThresholdDirectRawWeightSumLowerBound`、`VonMangoldtEventuallyDirectRawWeightSumLowerBound`、`VonMangoldtPositiveLinearRawWeightSumLowerBound`、`VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound`、`VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate`、`VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate`、`VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate`、`VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate`、`VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate`、`VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound`、`VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound`、`VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound`、`VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound`、`VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound`、`VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound`、`VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound`、`VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate`、`VonMangoldtHardyLittlewoodNormalizedEstimate`、`VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate`、`VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate`、`VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate`、`VonMangoldtDirectWeightSumMajorMinorArcEstimate`、`VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate`、`VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate`、`VonMangoldtSqrtLogCountRawLowerBound`、`VonMangoldtSqrtLogCountLinearRawLowerBound`、`VonMangoldtPositiveLinearRawLowerBound`、`VonMangoldtEventuallyPositiveLinearRawLowerBound`、`VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate`、`VonMangoldtSqrtLogCountMajorMinorArcEstimate`、`VonMangoldtCanonicalLogContaminationLowerBound`、`VonMangoldtCanonicalLogContaminationMajorMinorArcEstimate` 和 `VonMangoldtDirectRawLogLowerBound` 六十七类接口。生成器支持：

```bash
python3 verify_goldbach.py 200 --interval-start 100 --export-lean Gdbh/Certificate100To200.lean
python3 verify_goldbach.py 1000 --interval-start 100 --chunk-size 100 --export-lean Gdbh/Certificate100To1000.lean
python3 verify_goldbach.py 1000 --interval-start 2 --chunk-size 100 --export-lean Gdbh/Certificate2To1000.lean
```

当前 Lean 接口已经分成两层：

```lean
CircleMethodLowerBound
MajorMinorArcEstimate
```

`CircleMethodLowerBound` 是最终可接入强猜想的主项-误差下界。`MajorMinorArcEstimate` 是更接近圆法证明形态的工作包：它要求给出 major arc 下界、minor arc 误差项，以及两类误差之和小于主项的有效不等式。

许多圆法证明更自然地估计带权和，而不是直接估计 `GoldbachCount`。当前项目还提供了：

```lean
WeightedGoldbachLowerBound
WeightedMajorMinorArcEstimate
```

`WeightedGoldbachLowerBound` 把“素数支撑权重的带权 Goldbach 和为正”转回普通的两个素数表示。`WeightedMajorMinorArcEstimate` 是更贴近带权圆法的工作包：它要求给出带权 major arc 下界、带权 minor arc 误差项，以及总误差小于主项的有效不等式。后续如果形式化 von Mangoldt 型权重，应先证明该权重满足 `PrimeSupportedWeight`，再给出对应的显式带权下界。

Lean 里还定义了 `primeIndicatorWeight`，并证明：

```lean
ExplicitGoldbachLowerBound B ↔
  WeightedGoldbachPositiveAbove primeIndicatorWeight B
```

因此素数指示权重的带权目标与当前 `GoldbachCount` 目标完全等价。

更接近 von Mangoldt 权重的路线还要处理一个额外问题：`Λ(n)` 对素数幂为正，而不是只对素数为正。因此仅证明原始带权卷积为正，不足以推出两个素数表示；正贡献可能来自包含非素数的配对。当前项目新增了自然数权重版：

```lean
ContaminatedWeightedGoldbachLowerBound
ContaminatedWeightedMajorMinorArcEstimate
```

它们要求同时给出：

- 原始带权卷积的解析下界。
- 所有非素数对贡献的显式上界。
- 解析误差与污染项之和严格小于主项。

Lean 已证明，只要这些条件在阈值以上成立，就能推出普通 `GoldbachCount` 为正。这是将 von Mangoldt/素数幂型圆法估计接到强哥德巴赫目标时更合适的接口。

由于实际的 von Mangoldt 权重包含 `log p`，项目还提供了实数非负权重版：

```lean
RealContaminatedWeightedGoldbachLowerBound
RealContaminatedWeightedMajorMinorArcEstimate
```

该接口使用 `Nat → ℝ` 权重和实数主项/误差项，更适合接入真正的解析估计。Lean 已证明：只要实数权重非负、总带权卷积下界超过非素数对污染项，就能推出普通 Goldbach 表示。

项目还把 mathlib 的 von Mangoldt 函数直接封装成：

```lean
vonMangoldtWeight
VonMangoldtGoldbachLowerBound
VonMangoldtMajorMinorArcEstimate
```

Lean 已证明 `vonMangoldtWeight_nonneg`，所以后续真正需要补的是一个具体的 `VonMangoldtMajorMinorArcEstimate`：给出 `Λ` 卷积的 major/minor arc 下界、非素数对污染项上界，以及总误差小于主项的显式不等式。

进一步地，Lean 已证明：

```lean
NonPrimePairVonMangoldtGoldbachSum n =
  PrimePowerContaminationVonMangoldtGoldbachSum n
```

也就是 `Λ` 的非素数对污染项只来自“两个位置都是素数幂、但不是两个素数”的配对。因此目前最具体的解析交接对象是：

```lean
VonMangoldtPrimePowerContaminationMajorMinorArcEstimate
```

它要求给出 `Λ` major/minor arc 估计，以及素数幂污染项的显式上界。

再进一步，项目定义了左右两侧的素数幂污染项：

```lean
LeftPrimePowerContaminationVonMangoldtGoldbachSum
RightPrimePowerContaminationVonMangoldtGoldbachSum
```

并证明：

```lean
PrimePowerContaminationVonMangoldtGoldbachSum n ≤
  LeftPrimePowerContaminationVonMangoldtGoldbachSum n +
  RightPrimePowerContaminationVonMangoldtGoldbachSum n
```

所以可以先把污染项拆成左右两个求和上界：

```lean
VonMangoldtSplitPrimePowerContaminationMajorMinorArcEstimate
```

它允许后续解析证明分别给出左、右两个污染项上界。

进一步地，项目现在提供逐点控制版本：

```lean
VonMangoldtPointwiseSplitContaminationMajorMinorArcEstimate
```

这个接口把左右污染项上界拆成两步：先对每个进入污染集合的项给出逐点上界，再证明这些逐点上界在有限区间上的和分别不超过左右污染项。Lean 已证明这两个逐点求和上界足以恢复 `VonMangoldtSplitPrimePowerContaminationMajorMinorArcEstimate`。

更贴近常用解析估计写法的是统一上界版本：

```lean
VonMangoldtUniformSplitContaminationMajorMinorArcEstimate
```

它把每个污染项控制为同一个 `leftTermBound n` 或 `rightTermBound n`，再把污染集合的基数控制为 `leftCountBound n` 或 `rightCountBound n`，最后要求 `countBound * termBound` 被左右污染项预算吸收。Lean 已证明有限和引理 `realFinsetSum_le_card_mul_of_pointwise_bound`，因此这类“逐项统一上界 × 项数上界”的估计可自动接回 pointwise 接口。

左右污染集合的基数还可以归约到一个共同的一维计数：

```lean
NonPrimePrimePowerCount
VonMangoldtCountedSplitContaminationMajorMinorArcEstimate
```

Lean 已证明左污染集合是非素数素数幂集合的子集，右污染集合经 `p ↦ n - p` 注入到同一个集合，所以左右两个基数都不超过 `NonPrimePrimePowerCount n`。

当前还提供一个完全由 Lean 内部完成计数控制的粗接口：

```lean
VonMangoldtTrivialCountSplitContaminationMajorMinorArcEstimate
```

它使用平凡上界 `NonPrimePrimePowerCount n <= n + 1`，因此不再要求外部证明素数幂计数估计；代价是污染预算必须吸收 `(n + 1) * termBound`。

污染项统一上界还可以继续归约到单个 `Λ` 因子上界：

```lean
VonMangoldtWeightBoundSplitContaminationMajorMinorArcEstimate
```

Lean 已证明：如果 `Λ(p) <= weightBound n` 且 `Λ(n-p) <= weightBound n`，那么 `Λ(p) * Λ(n-p) <= weightBound n * weightBound n`。

这一层又已经用 mathlib 的 von Mangoldt 对数上界继续具体化：

```lean
VonMangoldtLogWeightSplitContaminationMajorMinorArcEstimate
```

Lean 已证明：若 `m <= n` 且 `m` 是素数幂，则 `Λ(m) <= log n`。

最后，左右污染预算已经固定为同一个显式量：

```lean
VonMangoldtCanonicalLogContaminationMajorMinorArcEstimate
```

这里 `vonMangoldtLogContaminationBudget n = (n.succ : ℝ) * (log n * log n)`。如果继续保留 major/minor arc 拆分，需要证明单个支配不等式

```lean
majorArcError n + minorArcError n + 2 * vonMangoldtLogContaminationBudget n
  < mainTerm n
```

这个 `n + 1` 预算是完全形式化但解析上太粗的保守接口。更有希望的路线先保留一个外部显式计数上界 `countBound`：

```lean
VonMangoldtDirectRawLogCountLowerBound
```

它要求证明：

```lean
(NonPrimePrimePowerCount n : ℝ) <= countBound n
2 * vonMangoldtLogCountContaminationBudget countBound n
  < RawVonMangoldtGoldbachSum n
```

也就是把污染预算降到 `2 * countBound(n) * (log n)^2`。如果后续能证明 `countBound` 为平方根量级，而 raw Λ 卷积有 `~ n` 的有效下界，这条路线才有可能闭合。

Lean 还提供了一个更紧的权重和交接对象：

```lean
VonMangoldtDirectRawWeightSumLowerBound
```

它要求直接控制非素数素数幂上的 `Λ` 权重和：

```lean
NonPrimePrimePowerVonMangoldtWeightSum n <= weightSumBound n
2 * weightSumBound n * Real.log n < RawVonMangoldtGoldbachSum n
```

该接口利用 Lean 已证明的

```lean
PrimePowerContaminationVonMangoldtGoldbachSum n
  <= 2 * (NonPrimePrimePowerVonMangoldtWeightSum n * Real.log n)
```

避免再把所有非素数素数幂统一粗略估成同一个 `log n` 因子后再乘一次计数上界；如果解析侧能给出更细的 prime-power 权重和估计，这通常比 `countBound * (log n)^2` 更有希望。
如果 raw Λ 卷积下界和 `NonPrimePrimePowerVonMangoldtWeightSum` 上界只有各自阈值，可用 `VonMangoldtSplitThresholdDirectRawWeightSumLowerBound`；Lean 会取 `max weightSumThreshold rawThreshold` 并转回 `VonMangoldtDirectRawWeightSumLowerBound`。
如果这两条只先以 eventually 形式给出，可用 `VonMangoldtEventuallyDirectRawWeightSumLowerBound`；Lean 会合并两个 eventually 条件并抽取共同阈值。
如果解析侧先证明更标准的正线性 raw Λ 下界 `coefficient * n <= RawVonMangoldtGoldbachSum n`，并另外证明 `2 * weightSumBound n * log n < coefficient * n`，可用 `VonMangoldtPositiveLinearRawWeightSumLowerBound`；三条条件都只有 eventually 形式时可用 `VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound`，Lean 会合并并抽取共同阈值。
如果文献侧先给出渐近主项形态的 raw Λ 下界，可用 `VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound`：只需证明 `RawVonMangoldtGoldbachSum n >= (1-relativeError)*mainTerm n` 和 `mainTerm n >= coefficient*n` 最终成立，且 `relativeError < 1`、`coefficient > 0`。Lean 会把有效系数压成 `(1-relativeError)*coefficient`，再接自动 sqrt-log 污染预算。
如果文献侧的误差项写成绝对值形式，可用 `VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound`：证明 `|RawVonMangoldtGoldbachSum n - mainTerm n| <= relativeError * mainTerm n` 和 `mainTerm n >= coefficient*n` 最终成立即可，Lean 会先推出上一条 eventually relative-error raw 下界。
如果文献只给出渐近式 `|RawVonMangoldtGoldbachSum n - mainTerm n| = o(mainTerm n)`，可用 `VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound`；Lean 会从 little-o 定义中取 `relativeError = 1/2` 的最终误差界，再进入上一条 abs-error raw 桥。
如果文献给出的结论是 `RawVonMangoldtGoldbachSum ~ mainTerm`，可用 `VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound`；Lean 会把等价渐近展开成 `Raw-main = o(main)`，再转入 little-o absolute-error raw 桥。
如果文献以归一化误差给出 `((RawVonMangoldtGoldbachSum n - mainTerm n) / mainTerm n) -> 0`，可用 `VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound`；Lean 会从趋于 0 的邻域球中取最终相对误差 `1/2`，再进入 abs-error raw 桥。
如果文献直接采用 Hardy-Littlewood/Vinogradov 主项 `singularSeries(n) * n`，可用 `VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate`；Lean 只要求奇异级数在偶数上最终有正下界，并要求相对该主项的归一化误差趋于 0，然后自动转入 normalized-error raw 桥。
如果已经有有效常数并能给出显式阈值，可用 `VonMangoldtHardyLittlewoodNormalizedEstimate`：解析侧给出具体 `threshold`、`relativeError < 1`、偶数 `n > threshold` 上的 `singularSeries(n) >= coefficient` 和归一化误差绝对值界。Lean 会直接得到有效系数 `(1-relativeError)*coefficient` 的正线性 raw Λ 下界，避免从 eventually 命题中抽取不可见阈值。
如果还要完全避免自动污染预算产生的隐藏阈值，可用 `VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate`：解析侧在同一个具体 `threshold` 后同时给出 `NonPrimePrimePowerVonMangoldtWeightSum` 上界和 `2*weightSumBound(n)*log n < (1-relativeError)*coefficient*n`，Lean 直接进入 direct raw weight-sum 桥，最终只需检查 `estimate.threshold <= B`。
如果文献侧给出的形式是相对误差下界 `RawVonMangoldtGoldbachSum n >= (1 - delta) * mainTerm n`，且还能证明 `mainTerm n >= c*n` 与 `delta < 1`，可用 `VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound`；Lean 已证明有效系数 `(1 - delta) * c` 为正，并自动转回 positive-linear raw weight-sum 桥。
如果相对误差下界来自 major/minor arc，可用 `VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate`：解析侧只需给出 `mainTerm - majorArcError <= RawVonMangoldtGoldbachSum + minorArcError` 和 `majorArcError + minorArcError <= delta * mainTerm`，Lean 会推出 `RawVonMangoldtGoldbachSum >= (1 - delta) * mainTerm`，再转入 relative-error raw 桥。
如果这条 relative-error major/minor 路线的五个条件只有分开的显式阈值，可用 `VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate`；Lean 会取 `max mainTermThreshold (max combinedThreshold (max totalAnalyticErrorThreshold (max weightSumThreshold contaminationThreshold)))` 并转回单阈值 relative-error major/minor 桥。
如果这五条条件只以 `∀ᶠ n in atTop` 形式给出，可用 `VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate`；Lean 会用 `vonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate_conditions_eventually` 合并条件，再用 `vonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate_ge_threshold` 抽取共同阈值。
如果解析侧不想显式给出 weight-sum 污染预算，可用 `VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate`；只需证明 main-term lower bound、combined lower bound 和 total relative error bound 三条 eventually 条件。Lean 会把有效系数设为 `(1-relativeError)*coefficient`，转成 `VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate`，并自动使用 `eventually_vonMangoldt_sqrt_log_count_budget_lt_const_mul_linear` 处理 sqrt-log count 污染预算。
如果这三条 relative-error sqrt-log count 条件有显式分阈值，可用 `VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate`；Lean 先取 `max mainTermThreshold (max combinedThreshold totalAnalyticErrorThreshold)`，再加入自动 sqrt-log 污染预算支配阈值。
这两个 relative-error sqrt-log count 接口现在也各自提供阈值不超过 100 时直接使用当前有限证书的 `StrongGoldbach` 桥，包括普通 sqrt-log 阈值版本和 weight-sum 终局阈值版本。
如果 positive-linear raw weight-sum 的三条条件有三个显式阈值，可用 `VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound`；Lean 会取 `max weightSumThreshold (max rawThreshold contaminationThreshold)` 并转回单阈值桥。
如果这些正线性 raw Λ 下界来自 major/minor arc 形式，可用 `VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate`：Lean 会从 `main - major <= Raw + minor` 与 `coefficient*n + minor <= main - major` 消去 minor error，得到 `Raw >= coefficient*n`，再携带任意 `weightSumBound` 污染预算进入 weight-sum 终局桥。
如果 major/minor arc 版本给出四个显式阈值，可用 `VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate`；Lean 会先取 `max combinedThreshold linearNetThreshold` 作为 raw 线性下界阈值，再转入三阈值 positive-linear raw weight-sum 桥。
`analyze_von_mangoldt.py` 也会有限范围计算这个 weight-sum 预算，方便和旧的 `countBound * (log n)^2` 预算对比；现在还会输出截断 Goldbach 奇异级数近似、相对 HL 主项的近似归一化误差，并在给定 `--coefficient` 与 `--relative-error` 时报告 canonical HL 证书形状的有限尾阈值。这些数值只用于定位下一步估计目标，不构成证明。
Lean 同时证明了兼容性上界

```lean
nonPrimePrimePowerVonMangoldtWeightSum_le_count_mul_log
nonPrimePrimePowerVonMangoldtWeightSum_le_sqrt_log_count_bound_mul_log
```

所以新的 weight-sum 接口至少能退化回旧的 count/log 预算；`VonMangoldtSqrtLogCountRawLowerBound.toDirectRawWeightSumLowerBound` 也已把旧的 sqrt-log raw 交接对象自动转成新的 weight-sum 交接对象。真正的收益仍要来自解析侧给出比 `countBound(n) * log n` 更强的 `weightSumBound(n)`。
此外 `VonMangoldtPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound`、`VonMangoldtEventuallyPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound`、`VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound` 和 `VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate.toDirectRawWeightSumLowerBound` 已把“正线性 raw Λ 下界”、eventually raw Λ 下界、eventually relative-error raw Λ 下界和 eventually major/minor arc 下界都直接接到 weight-sum 终局桥，避免解析侧在接口层面绕回旧的 count/log 结构。
如果解析侧已经有主项、major arc 误差、minor arc 误差和 `weightSumBound`，可直接使用 `VonMangoldtDirectWeightSumMajorMinorArcEstimate`：它要求证明 `mainTerm - majorArcError <= RawVonMangoldtGoldbachSum + minorArcError`，证明 `NonPrimePrimePowerVonMangoldtWeightSum <= weightSumBound`，以及证明 `majorArcError + minorArcError + 2 * weightSumBound * log n < mainTerm`。
如果这三条估计只有各自的显式阈值，可用 `VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate`；Lean 定义共同阈值为 `max combinedThreshold (max weightSumThreshold totalErrorThreshold)`，并证明三类阈值都不超过该共同阈值。
若论文或后续形式化只先得到 eventually 形式，则使用 `VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate`：三条条件都可写成 `∀ᶠ n in atTop`，Lean 先用 `vonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate_conditions_eventually` 合并它们，再抽取共同阈值并转成 direct weight-sum major/minor arc 交接对象；若抽出的阈值不超过当前 `GoldbachUpTo 100` 证书，还可直接用 `strongGoldbach_of_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate_le100`。

当前 Lean 已经证明了一个具体平方根乘对数的计数上界：

```lean
nonPrimePrimePowerCount_le_sqrt_succ_mul_log_succ
```

即

```lean
NonPrimePrimePowerCount n <= (n.sqrt + 1) * (Nat.log 2 n + 1)
```

因此当前最直接的 raw 卷积交接对象可写成：

```lean
VonMangoldtSqrtLogCountRawLowerBound
```

它只剩下证明 raw Λ 卷积下界

```lean
2 * vonMangoldtLogCountContaminationBudget
  nonPrimePrimePowerSqrtLogCountBound n
  < RawVonMangoldtGoldbachSum n
```

也就是压倒 `2*(sqrt n+1)*(log₂ n+1)*(log n)^2` 级污染预算。

如果解析侧能直接证明标准的线性 raw Λ 下界，可使用更压缩的接口：

```lean
VonMangoldtSqrtLogCountLinearRawLowerBound
```

它要求给出常数 `coefficient`，并证明

```lean
coefficient * (n : ℝ) <= RawVonMangoldtGoldbachSum n
2 * vonMangoldtLogCountContaminationBudget
  nonPrimePrimePowerSqrtLogCountBound n
  < coefficient * (n : ℝ)
```

这把圆法输出常见的 `R(n) >= c*n` 形式和污染预算支配分开。

Lean 现在已经证明了支配不等式背后的实变量增长模型：

```lean
real_sqrt_mul_log_cube_isLittleO_linear
eventually_real_sqrt_mul_log_cube_lt_const_mul_linear
```

也就是对任意 `c > 0`，最终有 `sqrt(x) * (log x)^3 < c*x`。Lean 也已经证明了把这个实变量模型转移到精确的自然数预算

```lean
2 * ((n.sqrt + 1) * (Nat.log 2 n + 1)) * (log n)^2
```

的最终支配结论：

```lean
eventually_vonMangoldt_sqrt_log_count_budget_lt_const_mul_linear
```

因此对任意正线性系数 `c`，污染预算最终小于 `c*n`。项目现在还提供更压缩的接口：

```lean
VonMangoldtPositiveLinearRawLowerBound
```

它只要求解析侧给出 `coefficient > 0` 和最终的正线性 raw Λ 下界 `coefficient * n <= RawVonMangoldtGoldbachSum n`。Lean 会自动转成 `VonMangoldtSqrtLogCountLinearRawLowerBound`，并选择一个足够靠后的污染支配阈值。接下来困难部分集中在证明这个无条件 raw Λ 卷积正线性下界，并把得到的阈值与有限证书上界拼接。

如果解析侧更自然地给出 filter 形式，也可以使用：

```lean
VonMangoldtEventuallyPositiveLinearRawLowerBound
```

它要求证明 `∀ᶠ n : Nat in atTop, Even n -> coefficient * n <= RawVonMangoldtGoldbachSum n`。Lean 会从 `eventually_atTop` 中抽取 raw Λ 下界阈值，再复用正线性接口和污染支配阈值。

更贴近圆法拆分的 filter 版本是：

```lean
VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate
```

它要求最终证明 `mainTerm n - majorArcError n <= RawVonMangoldtGoldbachSum n + minorArcError n` 和 `coefficient * n + minorArcError n <= mainTerm n - majorArcError n`。Lean 会消去 minor error，得到 eventual raw Λ 正线性下界。

更贴近实际圆法证明书写的交接对象是：

```lean
VonMangoldtSqrtLogCountMajorMinorArcEstimate
```

它要求给出 raw Λ major/minor arc 估计

```lean
mainTerm n - majorArcError n
  <= RawVonMangoldtGoldbachSum n + minorArcError n
```

以及单个显式支配不等式

```lean
majorArcError n + minorArcError n
  + 2 * vonMangoldtLogCountContaminationBudget
      nonPrimePrimePowerSqrtLogCountBound n
  < mainTerm n
```

这也是当前最适合继续形式化外部解析数论估计的接口。

另有一个不再要求 Lean 外部提供 `mainTerm` 和误差拆分的粗接口：

```lean
VonMangoldtDirectRawLogLowerBound
```

它只要求证明

```lean
2 * vonMangoldtLogContaminationBudget n < RawVonMangoldtGoldbachSum n
```

对所有超过阈值的偶数成立。由于这里隐含的是 `(n+1)*(log n)^2` 级污染预算，这个接口只适合作为保守充分条件，不是当前最有希望的解析路线。

### 2. 条件证明里程碑

可以先形式化条件版本，例如：

```lean
def GRHGoldbachHypotheses : Prop := ...

theorem explicit_lower_bound_of_grh
    (h : GRHGoldbachHypotheses) :
    ExplicitGoldbachLowerBound 100 := ...
```

这不会证明强哥德巴赫猜想，但能检验 Lean API、下界接口和证明拼接方式。

### 3. 大规模有限验证

有限验证只能处理 `n <= B`，不能替代无限区间证明。它的作用是把解析阈值以下的区域封闭。

当前项目的有限证书机制已经支持：

```bash
python3 verify_goldbach.py 100 --export-lean Gdbh/Certificate100.lean --export-manifest certificate_manifest.json
```

如果解析证明只覆盖 `n > B`，需要把证书上界同步提高到 `B`，并让 `lake build` 复核生成的 Lean 证书。

完全显式 Hardy-Littlewood weight-sum 交接还配套了机器可读模板：

```bash
python3 analytic_handoff_certificate.py analytic_handoff_certificate.example.json
python3 analytic_handoff_certificate.py analytic_handoff_certificate.example.json --check-formalized-lean
python3 analytic_handoff_certificate.py analytic_canonical_handoff_certificate.example.json
```

第一条校验只检查字段、常数范围、规范化义务和阈值覆盖关系；模板当前会报告 `valid: true`、`estimate_complete: false`、`complete: false`。第二条会用 Lean 核对已经标为 `formalized` 的局部义务；当前模板只把 canonical sqrt-log prime-power weight-sum 上界作为已形式化义务。Lean 还证明了该 canonical 污染预算最终被任意正线性函数压倒，因此最终也会被 HL 有效系数压倒；但显式阈值版本的污染支配、奇异级数下界和 HL 归一化误差仍未证明。
第三条校验 canonical weight-sum 证书模板；这个模板把 weight-sum 上界和 eventual 污染支配固定为 Lean 已证明的 canonical 结果，只留下奇异级数下界与 HL 归一化误差两项解析义务。即使这两项都形式化，最多只是 `estimate_complete: true`；最终 `complete: true` 仍需要在 `derivedThresholdBound` 字段给出派生的 direct raw weight-sum 阈值被有限证书上界覆盖的 Lean 证明项。
当显式 weight-sum 证书的四个解析义务或 canonical 证书的两个 HL 解析义务都有 Lean 声明且证书状态为 `formalized` 时，可先加 `--check-lean` 用临时 Lean 文件核对这些声明的精确类型，并同时类型检查生成的 handoff wrapper；这会在 canonical 证书中实际检查 `derivedThresholdBound.lean_term` 是否能在所选 `--definition-name` 的上下文中证明阈值覆盖。之后再加 `--export-lean` 生成包含交接对象和最终条件 theorem 的 Lean 包装文件。若证书还提供 `finiteCertificateTheorem`，并且 canonical 证书也补齐 `derivedThresholdBound`，导出文件会额外生成无参数的 `StrongGoldbach` theorem。

## Lean 实现分层

- `Gdbh/Goldbach.lean`：基础命题、计数函数、等价归约。
- `Gdbh/FiniteIntervals.lean`：分块有限证书接口，把 `GoldbachBetween A B` 拼接为更大的 `GoldbachUpTo B`；Python 生成器支持 chunked 区间证书和从 2 开始的自包含 chunked 有限证书输出，并为所有已形式化解析接口导出最终 `StrongGoldbach` 桥。
- `Gdbh/Certificate100.lean`：当前有限证书和 `StrongGoldbach ↔ GoldbachCountPositiveAbove 100`。
- `Gdbh/AnalyticBridge.lean`：解析下界接口 `ExplicitGoldbachLowerBound 100` 与完整强猜想的连接。
- `Gdbh/Conditional.lean`：条件证明程序接口，用于记录 GRH 或 Hardy-Littlewood 型假设如何推出显式下界。
- `Gdbh/CircleMethod.lean`：抽象圆法充分条件，形式化“主项大于误差项且给出计数下界”如何推出显式下界。
- `Gdbh/MajorMinorArcs.lean`：major/minor arc 拼接层，把更细的圆法估计转成 `CircleMethodLowerBound`。
- `Gdbh/WeightedGoldbach.lean`：加权表示数桥接层，把素数支撑权重的正下界转成普通 Goldbach 表示，并证明素数指示权重的带权和与 `GoldbachCount` 等价。
- `Gdbh/WeightedMajorMinorArcs.lean`：带权 major/minor arc 拼接层，把带权圆法估计转成 `WeightedGoldbachLowerBound`。
- `Gdbh/ContaminatedWeightedGoldbach.lean`：原始带权卷积加污染项扣除接口，把 von Mangoldt/素数幂型估计中“总和大于非素数对贡献”的条件转成普通 Goldbach 表示。
- `Gdbh/RealContaminatedWeightedGoldbach.lean`：实数非负权重版本的污染项扣除接口，用于接入含 `log p` 的 von Mangoldt 型解析估计。
- `Gdbh/VonMangoldtGoldbach.lean`：mathlib `ArithmeticFunction.vonMangoldt` 的专用 Goldbach 接口，证明 `Λ` 权重非负，证明非素数对污染项等于素数幂污染项，证明素数幂污染项可由左右两侧污染项控制，证明左右污染项可由逐点项上界和有限和上界控制，证明统一逐项上界乘以污染集合个数上界足以控制污染和，证明左右污染集合个数都不超过 `NonPrimePrimePowerCount n`，证明 `NonPrimePrimePowerCount n <= n + 1`，证明更强的 `NonPrimePrimePowerCount n <= (n.sqrt + 1) * (Nat.log 2 n + 1)`，定义 `NonPrimePrimePowerVonMangoldtWeightSum` 并证明更紧的 weight-sum 污染预算，证明 weight-sum 可由 `NonPrimePrimePowerCount n * log n` 以及 sqrt-log 计数上界控制，证明 split-threshold direct raw weight-sum 可取两个阈值最大值，证明 eventually direct raw weight-sum 可抽取共同阈值，证明 positive-linear raw weight-sum 可由 `Raw Λ >= c*n` 与 weight-sum 污染预算支配推出 direct raw weight-sum，证明 relative-error positive-linear raw weight-sum 可由 `Raw Λ >= (1-delta)*mainTerm` 和 `mainTerm >= c*n` 推出有效正线性 raw 下界，证明 eventually relative-error positive-linear raw 可由 eventually 渐近主项下界推出 eventually 正线性 raw 下界，证明 relative-error weight-sum major/minor arc 可由 combined lower bound 和总解析误差占比推出 relative-error raw 下界，证明 split-threshold relative-error weight-sum major/minor arc 可取五个阈值最大值，证明 eventually relative-error weight-sum major/minor arc 可抽取共同阈值，证明 eventually relative-error sqrt-log count major/minor arc 可转成正线性 eventual major/minor arc 并自动使用 sqrt-log 污染预算，证明 split-threshold relative-error sqrt-log count major/minor arc 可取三条显式阈值并自动使用 sqrt-log 污染预算，证明 split-threshold positive-linear raw weight-sum 可取三个阈值最大值，下游 eventually 版本也可抽取共同阈值，证明 eventually positive-linear weight-sum major/minor arc 可先消去 minor error 再接任意 weight-sum 污染预算，证明 split-threshold positive-linear weight-sum major/minor arc 可先合并 combined/linear 阈值再接三阈值 raw 桥，证明 direct weight-sum major/minor arc 条件可推出 direct raw weight-sum 下界，证明 split-threshold direct weight-sum major/minor arc 可取三个阈值最大值，证明 eventually direct weight-sum major/minor arc 条件可抽取阈值，证明实变量模型 `sqrt(x)*(log x)^3 = o(x)`，并证明精确自然数污染预算最终小于任意正线性函数 `c*n`，证明两个 `Λ` 因子各自有上界时其乘积由上界平方控制，使用 mathlib 的 `ArithmeticFunction.vonMangoldt_le_log` 证明素数幂上 `Λ(m) <= log n`，把污染预算细化为 `vonMangoldtLogCountContaminationBudget countBound n`，并把 `VonMangoldtDirectRawWeightSumLowerBound`、`VonMangoldtSplitThresholdDirectRawWeightSumLowerBound`、`VonMangoldtEventuallyDirectRawWeightSumLowerBound`、`VonMangoldtPositiveLinearRawWeightSumLowerBound`、`VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound`、`VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate`、`VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate`、`VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate`、`VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate`、`VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate`、`VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound`、`VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound`、`VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound`、`VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound`、`VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate`、`VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate`、`VonMangoldtDirectWeightSumMajorMinorArcEstimate`、`VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate`、`VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate`、`VonMangoldtSqrtLogCountRawLowerBound`、`VonMangoldtSqrtLogCountLinearRawLowerBound`、`VonMangoldtPositiveLinearRawLowerBound`、`VonMangoldtEventuallyPositiveLinearRawLowerBound`、`VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate` 和 `VonMangoldtSqrtLogCountMajorMinorArcEstimate` 接到最终强哥德巴赫桥。
  该文件还新增 `VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound`，把 little-o 绝对误差渐近式转成固定相对误差 `1/2` 的 abs-error raw 桥，再接入最终强哥德巴赫桥。
  还新增 `VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound`，直接接收 `Raw ~ mainTerm` 形式并转入 little-o raw 桥。
  另有 `VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound`，直接接收 `(Raw-main)/main -> 0` 形式并转入 abs-error raw 桥。
  `VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate` 固定 `singularSeries(n) * n` 主项，把 Hardy-Littlewood/Vinogradov 常见归一化误差形式转入 normalized-error raw 桥。
  `VonMangoldtHardyLittlewoodNormalizedEstimate` 是同一主项的显式阈值版，把固定相对误差界转成正线性 raw Λ 桥。
  `VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate` 保留显式 HL 主项阈值，但固定使用 canonical weight-sum 上界和 Lean 已证明的 eventually 污染支配，自动抽取 direct raw weight-sum 阈值。
  `VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate` 是完全显式阈值版，携带 prime-power weight-sum 污染预算并直接接入 direct raw weight-sum 桥。
- `Gdbh/GeneralHandoff.lean`：通用阈值拼接层，把任意有限证书上界和不超过该上界的解析阈值组合起来。

## 完成标准

只有同时满足以下条件，才能说本项目证明了强哥德巴赫猜想：

- `lake build` 成功。
- `rg -n "\\b(axiom|sorry|admit)\\b" Gdbh` 无匹配。
- 存在无条件定理：

```lean
theorem explicit_goldbach_lower_bound_100 :
    ExplicitGoldbachLowerBound 100
```

- 该定理没有依赖未证明假设。
- `StrongGoldbach` 由该定理和当前证书推出。

当前状态：尚未完成；缺少无条件解析下界定理。
