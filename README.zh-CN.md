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

[`SharedBiasSelection.lean`](OneChannelCNNUniversality/SharedBiasSelection.lean)
把经过证明的载波间隙转化为一次精确的局部 ReLU：如果目标载波比其他载波低出的间隙
大于信号波动，那么唯一的共享偏置
$\theta-C_{s_*}$ 会在目标位置实施所需 ReLU，同时让其他受保护位置全部保持在线性区；
不保存寄存器的扩张边缘不需要满足多余条件。一旦给出单位间隙的空间地址，紧致性还能
机器验证地为任意连续有限信号族选出统一尺度。

[`SharedBiasAddress.lean`](OneChannelCNNUniversality/SharedBiasAddress.lean)
使用两个具有正二抽头卷积核的真实共享偏置 ReLU 层，在受保护的西北寄存器生成这种地址。
该文件精确计算原矩形内四类位置的载波值，证明西北位置是具有定量间隙的唯一最低点，
并证明输入相关的两层变换是单射。端到端定理
`exists_northwest_protected_selection_layers` 在紧输入族上统一选取全部所需幅度，并验证
第三个共享偏置层只在西北寄存器实施指定 ReLU，而其余受保护寄存器保持在线性支路。

[`SharedBiasScan.lean`](OneChannelCNNUniversality/SharedBiasScan.lean)
把地址机制扩展到任意一行。重复使用正二抽头全卷积，会精确生成载波

$$
C(i,j)=cP_m(j),\qquad
P_m(q)=\sum_{r=0}^{q}\binom{m}{r}.
$$

在超出二项式支撑之前，相邻地址之间至少相差 $c$。相应的重复信号变换保持单射；
紧致性则给出一个统一载波尺度，使任意指定列可以被选择，同时保持该行尚未处理的后缀
全部处于 ReLU 线性支路。

[`SharedBiasGridScan.lean`](OneChannelCNNUniversality/SharedBiasGridScan.lean)
在两个坐标方向分别执行同样的正累加，并证明精确的可分离地址公式

$$
C(i,j)=cP_{m_{\mathrm{row}}}(i)P_{m_{\mathrm{col}}}(j).
$$

横向再纵向的完整信号变换仍然是单射。因此，任意指定的原始寄存器都是其东南受保护
象限内具有至少 $c$ 间隙的唯一最低点。对于紧集上的连续信号族，一个共享标量偏置就能
在该寄存器实施指定 ReLU，并让该象限内其余寄存器全部保持在线性支路。

[`SharedBiasGridNetwork.lean`](OneChannelCNNUniversality/SharedBiasGridNetwork.lean)
把上述公式接回真实的共享标量偏置网络对象。它引入带显式输出尺寸的
`SharedBiasNetworkTo`，证明紧信号族上的任意有限次形式卷积都能由每层一个标量偏置的
网络精确线性化，并把完整的横向再纵向 Pascal 变换构造成固定 $2\times2$ 核形状网络。
对于非负输入，文件还给出一个完全显式的版本，其中所有 Pascal 层的偏置均为零。
最后的受保护选择恒等式也已由真实的扩张型 $2\times2$ 共享偏置卷积／ReLU 层实现，
不再只是证明层面的逐点激活公式。

定理 `exists_pascal_grid_protected_selection_layers` 现在已经把一次局部更新从头到尾接通。
对于任意紧的连续输入族和任意目标寄存器，它会选取正的常数种子 $c$ 与正的首层共享
偏置 $b$；层序列从种子状态 $V(x)+c\mathbf 1$ 开始。真实首层和后续全部零偏置 Pascal
层所产生的载波，在原始矩形内被精确计算为

$$
C(i,j)=cP_{m_{\mathrm{row}}}(i)P_{m+1}(j)
      +bP_{m_{\mathrm{row}}}(i)P_m(j).
$$

第二项沿东南方向单调，因此不会缩小第一项提供的至少为 $c$ 的间隙。Lean 随后同时验证
中间状态的精确信号—载波分解，以及真实最终扩张型共享偏置 ReLU 层在目标东南受保护
象限内的行为。
更强的定理 `exists_bundled_pascal_grid_protected_selection` 会把完整层序列作为一个
`SharedBiasNetworkTo` 网络对象返回，并证明其深度为

$$
m_{\mathrm{row}}+m_{\mathrm{col}}+2.
$$

受保护求值公式直接使用该网络的 `eval` 表述。通用组合操作
`SharedBiasNetworkTo.append` 则证明串联保持求值语义且网络深度相加。

[`SharedBiasCausality.lean`](OneChannelCNNUniversality/SharedBiasCausality.lean)
形式化了组合多次局部更新所需的“不干扰”不变量。按照本工程的卷积约定，位置 $(p,q)$
只读取它弱西北方向的输入位置。Lean 已证明：若两个状态在矩形

$$
\{(i,j):i\le p,\ j\le q\}
$$

上一致，那么这种一致性会被任意一次完整卷积、真实的共享偏置卷积／ReLU 层、任意有限
`SharedBiasNetwork`，以及显式输出尺寸的 `SharedBiasNetworkTo` 保持；受保护 Pascal
信号也满足相应结论。因此，按东南到西北的顺序扫描时，已经存放在当前西北矩形之外的
信息不会反向流入并改变当前激活。这是多次更新编译器已经验证的因果基础，但还不是完整
编译器：仍需证明早先生成的非线性特征经过后续带偏置选择块后可以恢复，并完成有限扫描
的组装。

[`SharedBiasRecovery.lean`](OneChannelCNNUniversality/SharedBiasRecovery.lean)
进一步证明了经过零偏置 Pascal 传输后的精确恢复。文件把横向再纵向的变换封装为单射
线性映射 $P$，并构造线性左逆 $R$，满足

$$
R(P(x))=x.
$$

Lean 还把每个被恢复坐标转换成普通的有限权重图像：对于任意原始位置 $(i,j)$，存在权重
数组 $W_{i,j}$，使

$$
\sum_{p,q} W_{i,j}(p,q)P(x)(p,q)=x(i,j).
$$

对于非负输入，同一等式已经直接落实到具体的 `zeroBiasPascalGridNetwork`；此时所有 ReLU
都保持在线性支路。因此，早先由 ReLU 生成的非负特征不会仅仅因为后续零偏置 Pascal
传输的扩张与混合而丢失，最终仿射读出仍能精确取回它。这里尚未证明特征经过任意后续带
偏置选择块后仍可恢复。

[`SharedBiasSupport.lean`](OneChannelCNNUniversality/SharedBiasSupport.lean)
形式化了与西北因果性互补的空间不变量。记

$$
Q_{r,s}=\{(i,j):r\le i,\ s\le j\}.
$$

若两个特征图只在 $Q_{r,s}$ 内不同，Lean 已证明：经过一次完整卷积、一次真实共享偏置
卷积／ReLU 层，或者任意有限的 `SharedBiasNetworkTo` 后，它们仍然只可能在
$Q_{r,s}$ 内不同。如果输入在根位置 $(r,s)$ 也相同，那么“去掉根点的东南象限”
$Q_{r,s}\setminus\{(r,s)\}$ 会被保持，且根位置的输出继续相同。因此，已经存放在这个
去根象限内的信息，即使经过后续非线性共享偏置层，也不会向西北泄漏或扰动下一个目标。
这个支撑定理只保护东南象限内可比较的位置；若要扫描完整矩形网格，仍需额外的布局或
次序来处理坐标不可比较的位置。

[`SharedBiasRelativeInjectivity.lean`](OneChannelCNNUniversality/SharedBiasRelativeInjectivity.lean)
补上了一个完整带偏置选择块的恢复缺口。Lean 首先证明：只知道同一个有限西北矩形上的
输出一致，就可以反演任意次横向与纵向 Pascal 累加。因此，传输信号限制在原始图像矩形
上的映射已经是单射，不需要观察扩张边缘。随后把该反演结论与东南支撑传播、封装网络的
精确求值公式结合，得到定理
`BundledPascalGridSelectionSpec.injective_on_rootPuncturedSoutheast`：若两个输入只可能在
$Q_{r,s}\setminus\{(r,s)\}$ 内不同，而真实共享偏置网络的输出相等，则两幅输入特征图
必然相等。因此，在一次局部更新所需的精确保护不变量下，共享偏置和最终 ReLU 都不会
破坏输入信息。

这些是实验性的形式化证明基础，**不是**共享偏置万能逼近定理。仓库中原有的完整万能
逼近定理仍然允许任意逐位置偏置数组；本工程目前尚未判定共享标量偏置子类究竟万能还是
不万能。
任意目标现在已经能在“保护其东南象限”的条件下端到端地被选择，这消除了原先只能选择
西北角以及只在证明层面假设载波的限制。剩余工作已经变成另一项任务：选择一种有限布局
或次序，把所需的寄存器变化都转化为受保护的可比较关系；组合已验证相对单射的局部更新；
控制更新之间的扩张边缘值；最终把这种共享偏置编译器接到适用于共享标量偏置子类的稠密性
论证上。

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
| [`SharedBias.lean`](OneChannelCNNUniversality/SharedBias.lean) | 共享标量偏置的精确语义、到一般模型的保语义嵌入，以及带类型的顺序网络组合 |
| [`SharedBiasGeometry.lean`](OneChannelCNNUniversality/SharedBiasGeometry.lean) | 使用共享偏置精确生成常数、左边界与西北角位置信号 |
| [`SharedBiasCarrier.lean`](OneChannelCNNUniversality/SharedBiasCarrier.lean) | 共享偏置紧集线性化、信号与载波非破坏性共存、单射横向差分和精确边界载波间隙 |
| [`SharedBiasSelection.lean`](OneChannelCNNUniversality/SharedBiasSelection.lean) | 从载波间隙精确选择局部 ReLU，以及从单位空间地址取得紧集统一尺度 |
| [`SharedBiasAddress.lean`](OneChannelCNNUniversality/SharedBiasAddress.lean) | 两个单射共享偏置地址层、受保护寄存器上的精确西北间隙，以及端到端西北选择层 |
| [`SharedBiasScan.lean`](OneChannelCNNUniversality/SharedBiasScan.lean) | 重复正横向累加、精确 Pascal 前缀地址、单射性与受保护行后缀选择 |
| [`SharedBiasGridScan.lean`](OneChannelCNNUniversality/SharedBiasGridScan.lean) | 单射二维 Pascal 地址，以及东南受保护象限上的任意目标选择 |
| [`SharedBiasGridNetwork.lean`](OneChannelCNNUniversality/SharedBiasGridNetwork.lean) | 真实共享偏置层、首层偏置 Pascal 载波及间隙、零偏置累加，以及封装为单一网络的端到端受保护任意目标选择 |
| [`SharedBiasCausality.lean`](OneChannelCNNUniversality/SharedBiasCausality.lean) | 完整卷积、真实共享偏置 ReLU 层、任意有限网络及受保护 Pascal 信号的西北不干扰定理 |
| [`SharedBiasRecovery.lean`](OneChannelCNNUniversality/SharedBiasRecovery.lean) | Pascal 传输的线性左逆、有限仿射读出权重的精确坐标恢复，以及非负特征上具体零偏置网络的恢复定理 |
| [`SharedBiasSupport.lean`](OneChannelCNNUniversality/SharedBiasSupport.lean) | 真实共享偏置 ReLU 层和任意有限网络中的东南支撑传播，以及去根东南象限差异下的根位置保护 |
| [`SharedBiasRelativeInjectivity.lean`](OneChannelCNNUniversality/SharedBiasRelativeInjectivity.lean) | 从受保护原始矩形反演 Pascal 传输，以及完整带偏置选择块的相对单射性 |
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
