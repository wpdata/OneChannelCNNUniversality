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
[`OneChannelCNNUniversality.twoDimensional_oneChannel_universal_approximation`](OneChannelCNNUniversality/Main.lean)：

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

## 共享标量偏置拓展：当前状态

仓库现在还包含一个约束更强、也更接近常见实现的隐藏层模型：

$$
H_\ell(X)=\mathrm{ReLU}\!\left(W_\ell*H_{\ell-1}(X)+b_\ell\mathbf 1\right),
$$

即第 $\ell$ 层只有一个标量偏置 $b_\ell$，并把它广播到所有空间位置。
[`SharedBias.lean`](OneChannelCNNUniversality/SharedBias.lean) 精确定义了这类网络，
并证明它的求值语义可以原样嵌入一般的逐位置偏置模型。

[`SharedBiasGeometry.lean`](OneChannelCNNUniversality/SharedBiasGeometry.lean)
对零延拓全卷积产生的边界效应进行了机器验证：零卷积核加正共享偏置会产生常数矩形；
横向一阶差分再经过 ReLU 会精确保留正的左边界；继续做纵向一阶差分会精确保留西北角
单点。定理覆盖所有有限尺寸，包括空矩形的退化情形。

[`SharedBiasCarrier.lean`](OneChannelCNNUniversality/SharedBiasCarrier.lean)
进一步证明了第一个“非破坏性共存”结果：在紧输入集上，一个广播标量足以让有限输出
矩形的全部位置同时落在 ReLU 线性区。如果输入状态由可变信号与固定图像组成，下一层
就精确等于卷积后的可变信号加上新的固定空间载波。对于横向边界核，可变信号所经历的
差分变换是单射；与此同时，常数输入载波在左边界变为 $b+c$，在原始内部位置变为 $b$。

这些是实验性的形式化证明基础，**不是**共享偏置万能逼近定理。上面的已验证主定理仍然
允许任意逐位置偏置数组。本工程目前尚未判定共享标量偏置子类究竟万能还是不万能：已经
验证的边界载波间隙还不能为任意有限位置提供彼此独立的地址，也尚未形成一个能够对单个
位置实施局部 ReLU、同时保存所有其他寄存器的编译器。

## 证明架构

| 文件 | 职责 |
| --- | --- |
| [`Basic.lean`](OneChannelCNNUniversality/Basic.lean) | 有限数组图像、卷积、ReLU 层、网络与仿射读出的语义 |
| [`Carrier.lean`](OneChannelCNNUniversality/Carrier.lean)、[`Register.lean`](OneChannelCNNUniversality/Register.lean) | 精确载体与掩码寄存器操作 |
| [`Program.lean`](OneChannelCNNUniversality/Program.lean)、[`RegisterProgram.lean`](OneChannelCNNUniversality/RegisterProgram.lean)、[`HybridProgram.lean`](OneChannelCNNUniversality/HybridProgram.lean) | 将寄存器程序编译为真正的卷积／ReLU 层 |
| [`Encoder.lean`](OneChannelCNNUniversality/Encoder.lean)、[`SparseEncoder.lean`](OneChannelCNNUniversality/SparseEncoder.lean) | 单射稀疏卷积编码以及二项式／Vandermonde 可逆性论证 |
| [`RouteGeometry.lean`](OneChannelCNNUniversality/RouteGeometry.lean)、[`Routing.lean`](OneChannelCNNUniversality/Routing.lean)、[`GridRouting.lean`](OneChannelCNNUniversality/GridRouting.lean) | 对编码坐标进行精确空间路由 |
| [`GridMachine.lean`](OneChannelCNNUniversality/GridMachine.lean)、[`LatticeCompiler.lean`](OneChannelCNNUniversality/LatticeCompiler.lean) | 使用 ReLU 的最小值／最大值恒等式精确计算有限仿射格表达式 |
| [`Ridge.lean`](OneChannelCNNUniversality/Ridge.lean)、[`Universal.lean`](OneChannelCNNUniversality/Universal.lean) | 通过 Mathlib 的格版本 Stone--Weierstrass 定理证明稠密性 |
| [`Simulation.lean`](OneChannelCNNUniversality/Simulation.lean)、[`Main.lean`](OneChannelCNNUniversality/Main.lean) | 汇总精确编译与稠密性，得到最终网络定理 |
| [`SharedBias.lean`](OneChannelCNNUniversality/SharedBias.lean) | 共享标量偏置的精确语义，以及到一般模型的保语义嵌入 |
| [`SharedBiasGeometry.lean`](OneChannelCNNUniversality/SharedBiasGeometry.lean) | 使用共享偏置精确生成常数、左边界与西北角位置信号 |
| [`SharedBiasCarrier.lean`](OneChannelCNNUniversality/SharedBiasCarrier.lean) | 共享偏置紧集线性化、信号与载波非破坏性共存、单射横向差分和精确边界载波间隙 |
| [`Tests/`](OneChannelCNNUniversality/Tests) | 模块测试、回归测试、顶层测试与公理审计 |

编译器使用精确恒等式
$\min(a,b)=a-\mathrm{ReLU}(a-b)$ 与
$\max(a,b)=b+\mathrm{ReLU}(a-b)$。

## 固定环境

- Lean 4.32.1
- Mathlib v4.32.1

[`lean-toolchain`](lean-toolchain) 固定 Lean 工具链；
[`lakefile.lean`](lakefile.lean) 与 [`lake-manifest.json`](lake-manifest.json)
固定 Mathlib 的 Git 依赖及准确修订版本。Lake 会把依赖下载到已忽略的本地
`.lake/packages/` 目录，本仓库不保存 Mathlib 源码。

## 安装

安装 [elan](https://github.com/leanprover/elan)，然后克隆本仓库：

```bash
git clone git@github.com:wpdata/OneChannelCNNUniversality.git
cd OneChannelCNNUniversality
```

下载固定版本的依赖：

```bash
lake update
```

## 构建与验证

构建完整形式化工程：

```bash
lake build
```

运行全部证明测试：

```bash
for test_file in OneChannelCNNUniversality/Tests/*.lean; do
  lake env lean "$test_file"
done
```

审计顶层定理使用的公理：

```bash
lake env lean OneChannelCNNUniversality/Tests/Axioms.lean
```

预期报告为：

```text
'OneChannelCNNUniversality.twoDimensional_oneChannel_universal_approximation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

三者均属于 Lean／Mathlib 的标准基础。本工程没有自定义 `axiom` 声明，也没有
`sorry` 或 `admit` 证明占位符。以下源码扫描应当没有任何匹配：

```bash
rg -n --glob '*.lean' \
  '(^|[^[:alnum:]_])(sorry|admit|unsafe)([^[:alnum:]_]|$)|^[[:space:]]*axiom([^[:alnum:]_]|$)' \
  OneChannelCNNUniversality OneChannelCNNUniversality.lean
```

编译器的 linter 警告是代码风格诊断，不代表存在未证明目标。验证标准是：完整构建
成功、全部测试成功、禁用词源码扫描为空，并得到上述公理报告。

## 范围与状态

本仓库发布 Lean 源码及其可由机器复核的结果。Lean 内核验证说明：逐位置偏置万能逼近
定理和约束更强的共享偏置边界／载波引理都可由给定定义与报告中的基础推出；但这并不会把尚未
解决的共享偏置万能性问题变成定理。机器验证本身也不等同于外部同行评审，不构成历史
优先权判断。
