# 参考结果与边界

本文件记录常用事实和它们对强哥德巴赫猜想的实际作用。它们是研究起点，不是完整证明。

## 强哥德巴赫猜想

命题：

```text
Every even integer N > 2 is a sum of two primes.
```

当前边界：截至 2026-05-19 联网核查，没有公认的无条件证明。MathWorld 仍把 strong/binary Goldbach 作为未解决问题记录，并列出有限验证最高到 `4 * 10^18`；Landau problems 条目也仍把 Goldbach 列为 2026 年未解决的四个素数问题之一。

可核查链接：

- https://mathworld.wolfram.com/GoldbachConjecture.html
- https://en.wikipedia.org/wiki/Landau%27s_problems

## 有限计算验证

T. Oliveira e Silva, S. Herzog, S. Pardi, *Empirical verification of the even Goldbach conjecture and computation of prime gaps up to 4 * 10^18*.

作用：

- 给出非常大的有限范围验证。
- 可排除该范围内的反例。

不能完成证明的原因：

- 任何固定上界仍只覆盖有限多个偶数。
- 还需要一个覆盖上界之后所有偶数的无条件解析论证。

可核查链接：

- https://www.ams.org/journals/mcom/2014-83-288/S0025-5718-2013-02787-1/
- https://mathworld.wolfram.com/GoldbachConjecture.html

## 近期声称证明的资料处理

联网搜索会出现 SSRN、Zenodo、arXiv 或预印本中的“证明”“反证”声称。处理原则：

- 只把同行评审文献、作者代码、可复现证书或 Lean 可检查对象作为证明输入。
- 未被主流数学文献接受、没有完整可验证常数链、或只给出启发式/有限计算的资料，不能填入 `ExplicitGoldbachLowerBound 100`。
- 即使某篇资料声称扩展了有限验证上界，也只能扩大 `GoldbachUpTo B`，不能替代无限区间解析证明。

## 弱哥德巴赫猜想

Harald Helfgott 证明了三元形式：每个大于 5 的奇数都是三个素数之和。

作用：

- 解决弱哥德巴赫猜想。
- 可作为理解圆法和有效估计的入口。

不能完成强猜想的原因：

- “奇数 = 三个素数之和”不推出“偶数 = 两个素数之和”。
- 从三个素数减少到两个素数需要额外结构，而这正是强猜想的难点。

## Chen 定理

Chen 定理说明：充分大的偶数可表示为一个素数加上一个至多两个素数的乘积。

作用：

- 是强哥德巴赫方向的著名接近结果。
- 说明筛法可以接近目标。

不能完成强猜想的原因：

- “至多两个素数的乘积”允许半素数，不等于素数。
- 要把半素数项进一步排除或降为素数，会遇到筛法的奇偶障碍。

## Hardy-Littlewood 预测

Hardy-Littlewood 圆法给出强哥德巴赫表示数的预期渐近形式。粗略地说，偶数 `N` 的表示数预期约为 `N / log(N)^2` 量级，并带有奇异级数修正。

作用：

- 解释为什么猜想在概率和渐近意义上很可信。
- 指导解析数论中的主项与误差项结构。

不能完成证明的原因：

- 预期渐近式本身没有在强到覆盖每个偶数的无条件形式下证明。
- “平均上很多”不等于“每个偶数至少一个”。

## 审查原则

任何声称完成强哥德巴赫猜想的证明，必须把这些已知结果中缺失的最后一步补上：

```text
For every even N > 2, prove at least one Goldbach representation exists.
```

如果证明只得到有限验证、几乎所有、充分大但无有效阈值、三素数表示、素数加半素数表示，或条件于未证明假设，则仍未证明强哥德巴赫猜想。
