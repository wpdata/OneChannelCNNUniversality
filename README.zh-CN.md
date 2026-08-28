# 二维单通道扩张型 ReLU CNN 万能逼近的机器验证

[English](README.md)

本仓库给出一个 Lean 4 形式化证明：带仿射读出的有限深度二维单通道扩张型
ReLU 卷积神经网络具有万能逼近性质。

## 主要结果

设输入尺寸 $d_1,d_2$ 均为正，固定卷积形状
$k_{\mathrm{rows}}\times k_{\mathrm{cols}}$ 的两条边均至少为二，$K$ 是实值输入图像
构成的紧集，$f\colon K\to\mathbb{R}$ 是连续目标函数，并且 $\varepsilon>0$。本形式化
证明构造出一个有限深度网络，使其在 $K$ 上的一致逼近误差小于 $\varepsilon$。

精确定义的模型具有以下特征：

- 输入是尺寸为 $d_1\times d_2$ 的有限二维实值数组；
- 每个隐藏层使用同一个固定的扩张卷积形状；
- 每个隐藏层只有一个特征通道；
- 使用零延拓的全卷积、任意空间偏置和逐点 ReLU；
- 从最后一层特征图进行任意仿射读出。

导出的顶层定理是
[`ICM2022NumCS97.twoDimensional_oneChannel_universal_approximation`](ICM2022NumCS97/Main.lean)：

```lean
theorem twoDimensional_oneChannel_universal_approximation
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {K : Set (Image d₁ d₂)} (hK : IsCompact K)
    (f : C(K, ℝ)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (outRows outCols : ℕ)
      (net : NetworkTo kRows kCols d₁ d₂ outRows outCols)
      (weight : Image outRows outCols) (constant : ℝ),
      ∀ x : K, |net.realize weight constant x.1 - f x| < epsilon
```

## 证明架构

| 文件 | 职责 |
| --- | --- |
| [`Basic.lean`](ICM2022NumCS97/Basic.lean) | 有限数组图像、卷积、ReLU 层、网络与仿射读出的语义 |
| [`Carrier.lean`](ICM2022NumCS97/Carrier.lean)、[`Register.lean`](ICM2022NumCS97/Register.lean) | 精确载体与掩码寄存器操作 |
| [`Program.lean`](ICM2022NumCS97/Program.lean)、[`RegisterProgram.lean`](ICM2022NumCS97/RegisterProgram.lean)、[`HybridProgram.lean`](ICM2022NumCS97/HybridProgram.lean) | 将寄存器程序编译为真正的卷积／ReLU 层 |
| [`Encoder.lean`](ICM2022NumCS97/Encoder.lean)、[`SparseEncoder.lean`](ICM2022NumCS97/SparseEncoder.lean) | 单射稀疏卷积编码以及二项式／Vandermonde 可逆性论证 |
| [`RouteGeometry.lean`](ICM2022NumCS97/RouteGeometry.lean)、[`Routing.lean`](ICM2022NumCS97/Routing.lean)、[`GridRouting.lean`](ICM2022NumCS97/GridRouting.lean) | 对编码坐标进行精确空间路由 |
| [`GridMachine.lean`](ICM2022NumCS97/GridMachine.lean)、[`LatticeCompiler.lean`](ICM2022NumCS97/LatticeCompiler.lean) | 使用 ReLU 的最小值／最大值恒等式精确计算有限仿射格表达式 |
| [`Ridge.lean`](ICM2022NumCS97/Ridge.lean)、[`Universal.lean`](ICM2022NumCS97/Universal.lean) | 通过 Mathlib 的格版本 Stone--Weierstrass 定理证明稠密性 |
| [`Simulation.lean`](ICM2022NumCS97/Simulation.lean)、[`Main.lean`](ICM2022NumCS97/Main.lean) | 汇总精确编译与稠密性，得到最终网络定理 |
| [`Tests/`](ICM2022NumCS97/Tests) | 模块测试、回归测试、顶层测试与公理审计 |

编译器使用精确恒等式
$\min(a,b)=a-\operatorname{ReLU}(a-b)$ 与
$\max(a,b)=b+\operatorname{ReLU}(a-b)$。

## 固定环境

- Lean 4.32.1
- Mathlib v4.32.1

[`lean-toolchain`](lean-toolchain) 固定 Lean 工具链；
[`lake-manifest.json`](lake-manifest.json) 与
[`vendor/mathlib`](vendor/mathlib) 子模块记录准确的 Mathlib 修订版本。

## 安装

安装 [elan](https://github.com/leanprover/elan)，然后连同 Mathlib 子模块克隆本仓库：

```bash
git clone --recurse-submodules git@github.com:wpdata/machine-checked-2d-one-channel-relu-cnn-universality.git
cd machine-checked-2d-one-channel-relu-cnn-universality
```

如果克隆时没有包含子模块，请运行：

```bash
git submodule update --init --recursive
```

## 构建与验证

构建完整形式化工程：

```bash
lake build
```

运行全部证明测试：

```bash
for test_file in ICM2022NumCS97/Tests/*.lean; do
  lake env lean "$test_file"
done
```

审计顶层定理使用的公理：

```bash
lake env lean ICM2022NumCS97/Tests/Axioms.lean
```

预期报告为：

```text
'ICM2022NumCS97.twoDimensional_oneChannel_universal_approximation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

三者均属于 Lean／Mathlib 的标准基础。本工程没有自定义 `axiom` 声明，也没有
`sorry` 或 `admit` 证明占位符。以下源码扫描应当没有任何匹配：

```bash
rg -n --glob '*.lean' \
  '(^|[^[:alnum:]_])(sorry|admit|unsafe)([^[:alnum:]_]|$)|^[[:space:]]*axiom([^[:alnum:]_]|$)' \
  ICM2022NumCS97 ICM2022NumCS97.lean
```

编译器的 linter 警告是代码风格诊断，不代表存在未证明目标。验证标准是：完整构建
成功、全部测试成功、禁用词源码扫描为空，并得到上述公理报告。

## 范围与状态

本仓库发布 Lean 源码及其可由机器复核的定理。Lean 内核验证说明该定理可由给定定义
与报告中的基础推出；它本身不等同于外部同行评审，也不构成历史优先权判断。
