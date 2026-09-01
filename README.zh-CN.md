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

[`SharedBiasChainLayout.lean`](OneChannelCNNUniversality/SharedBiasChainLayout.lean)
形式化了把上述保护不变量扩展为完整扫描时必须付出的几何代价。任何东南单调链都不可能
覆盖行数和列数都至少为二的矩形，因为 $(0,1)$ 与 $(1,0)$ 不可比较。更定量地，Lean
证明：若在 $R\times C$ 矩形中放置由 $N$ 个不同位置组成的单调链，则必有

$$
N\le R+C-1.
$$

因此，对当前“单调链保护”方案而言，总空间跨度随寄存器数量线性增长是内在限制，并非
证明中隐藏的偶然浪费。该文件还给出到 $1\times(d_1d_2)$ 图像的精确行主序置换，构造
左逆并证明这种链式表示不丢失任何信息。这个表示在面积上没有浪费，但长宽比很极端；更
重要的是，目前它仍是数学层面的坐标布局，尚未由共享偏置 CNN 本身实现。

[`SharedBiasChainSelection.lean`](OneChannelCNNUniversality/SharedBiasChainSelection.lean)
把单行链布局重新接回真实共享偏置网络。对于目标索引 $t$，文件证明：在包含端点的前缀

$$
\{0,\ldots,t\}
$$

上一致，等价于相对单射定理所要求的“去根东南支撑”条件。由此得到完整封装选择块的
链式版本：若两个链状态在 $t$ 之前及 $t$ 处一致，并且网络输出相等，则两条输入链完全
相等。最后，`exists_bundled_rowChain_protected_selection` 利用紧致性同时返回正种子、
首层共享偏置、真实带类型网络、精确深度、选择公式和上述前缀相对恢复保证。这已经是一
个经过认证的单次扫描步骤。

[`SharedBiasSeedTransport.lean`](OneChannelCNNUniversality/SharedBiasSeedTransport.lean)
与
[`SharedBiasSuccessorSelection.lean`](OneChannelCNNUniversality/SharedBiasSuccessorSelection.lean)
给出了首个经过验证的多步接口。真实的扩张 delta 恒等层会把任意非负中间图像 $z$ 精确
变换为

$$
\mathrm{FullConv}(\delta,z)+c\mathbf 1,
$$

因此，下一选择块所需的紧集常数种子是在 CNN 内部生成的。Lean 已验证：添加相同载体不
改变支撑关系；网络求值与后继特征保持逐坐标连续；每个正深度网络的输出非负；带种子组合
具有精确求值公式和精确深度增量。定理
`exists_two_bundled_pascal_selection_stages` 进一步返回两个由紧致性生成的受保护选择器，
它们的桥接与组合是同一个真实 `SharedBiasNetworkTo`，两块之间没有插入任何网络外操作。

[`SharedBiasTwoStageRecovery.lean`](OneChannelCNNUniversality/SharedBiasTwoStageRecovery.lean)
闭合了相应的两阶段恢复链。该文件证明扩张 delta 卷积既单射又保持去根东南支撑，然后沿
组合网络反向应用两次局部恢复定理。因此，只要一对原输入在两个被选择的自然坐标上同时
满足受保护变化条件，最终两阶段输出相等就推出原始特征图相等。这里的“双根同时保护”
假设是显式条件；如何安排有限扫描，使每一步都满足该条件，仍属于尚未完成的编译器问题。

[`SharedBiasFiniteRecovery.lean`](OneChannelCNNUniversality/SharedBiasFiniteRecovery.lean)
把上述反向论证从两阶段推广到任意有限异构链。`RelativeRecoveryStep` 记录一次局部保护
谓词及其“输出相等反射输入特征相等”定理；`RelativeRecoveryChain` 允许每个中间特征
类型变化，因此也允许扩张图像尺寸逐步变化。Lean 已证明有限链的反向归纳恢复、链拼接、
长度可加，以及拼接后的保护义务等价于两段保护义务的合取。真实 Pascal 选择器被注册为
有条件恢复步骤，扩张 delta 桥被注册为无条件恢复步骤；现有两选择器构造则被封装为三步
恢复链。这解决的是有限链的“恢复逻辑”，但该文件本身不构造依赖紧致性的参数。

[`SharedBiasFiniteSelection.lean`](OneChannelCNNUniversality/SharedBiasFiniteSelection.lean)
完成了正深度头网络之后任意有限“后继选择日程”的下一层编译。这个日程是依赖类型：每个
后续目标都按照前面所有选择块产生的新尺寸进行类型检查。Lean 在递归的每一步调用紧致
受保护选择定理，并保存正种子、正选择偏置、完整选择规格以及内部种子层的精确求值等式；
最终证书导出一个 `SharedBiasNetworkTo`。因此，任意有限预定后继序列现在对应一张真实的
组合 CNN，而不再只是元语言中分别断言存在的网络块列表。

[`SharedBiasScheduledRecovery.lean`](OneChannelCNNUniversality/SharedBiasScheduledRecovery.lean)
把这个编译证书接到了有限恢复逻辑上。每个已编译选择器都被转成一个从前级网络输出到真实
组合输出的恢复步骤，其局部义务为

$$
\mathrm{AgreeOutsideStrictSoutheast}
  \bigl(S_s(x),S_s(y);r_s,c_s\bigr),
$$

其中 $S_s$ 是第 $s$ 阶段的后继特征。Lean 把所有局部义务组成合取，并构造长度严格等于
日程长度的恢复链。因此，最终网络输出相等可以反推出头网络特征相等；若头特征映射在
$K$ 上单射，并且 $K$ 中每对输入都满足整条链的保护义务，则最终那一张 CNN 在 $K$ 上
仍然单射。

[`SharedBiasProtectionObstruction.lean`](OneChannelCNNUniversality/SharedBiasProtectionObstruction.lean)
证明上述全局成对条件不能同时支持同一目标上的非平凡选择激活。对固定根 $(r,c)$，Lean
已经证明

$$
\left(\forall x,y\in K,\;
  \mathrm{AgreeOutsideStrictSoutheast}(V(x),V(y);r,c)\right)
\Longrightarrow
\left(\forall x,y\in K,\;V(x)_{r,c}=V(y)_{r,c}\right).
$$

所以对任意阈值 $\theta$，$\mathrm{ReLU}(V(x)_{r,c}+\theta)$ 在 $K$ 上也是常数。
该结论还被专门应用到真实的追加选择器恢复步骤：只要两个输入的目标后继特征不同，其全局
成对保护前提就被形式化否定。因此，日程恢复定理是正确的状态保持结论，但它最强的全局
推论本身不是计算万能性的证明。有效编译器必须把受保护的状态副本与执行非恒定 ReLU 的
可变工作寄存器分开，或者改用不同的恢复不变量。

[`SharedBiasRedundantRecovery.lean`](OneChannelCNNUniversality/SharedBiasRedundantRecovery.lean)
已经实现并形式化验证了第一种替代方案，而且不需要复制整个网络。对特征图，只把可变
根值 $x_0$ 额外存入东侧相邻寄存器一次，即令 $x_1=x_0$；该证明现已推广到任意非空特征
矩形。若选择器的横向 Pascal 传输还
包含 `extraColSteps` 层，Lean 已证明精确的受保护边界公式

$$
S_0(x)=x_0,
\qquad
S_1(x)=x_1+(\texttt{extraColSteps}+1)x_0.
$$

所以在这个冗余子空间上，
$S_1(x)=(\texttt{extraColSteps}+2)x_0$。其系数严格为正，因此即使选择 ReLU 覆盖了
$S_0(x)$，仍能从相邻位置恢复根值。定理
`BundledPascalGridSelectionSpec.injective_on_eastRootDuplicate` 进一步验证：完整、真实的
共享标量偏置选择网络在该子空间上是单射的。特别地，目标值现在允许随输入变化，前面的
“目标必须为常数”障碍不再适用。这里的代价只是一个相邻空间寄存器，而不是增加第二通道，
也不是复制一整套等宽网络。

[`SharedBiasAdjacentCopy.lean`](OneChannelCNNUniversality/SharedBiasAdjacentCopy.lean)
现在进一步用真实 CNN 层构造了这个冗余关系。输入布局把根右侧工作位置预留为零，
$x_{0,1}=0$；非负状态随后通过一个真实的零偏置横向累加层。Lean 已验证

$$
D(x)_{0,0}=x_{0,0},
\qquad
D(x)_{0,1}=x_{0,1}+x_{0,0}=x_{0,0}.
$$

同一层在全部非负图像上是全局单射的，所以建立副本不会丢失其余状态。该副本还会穿过真实
扩张 delta 种子桥而保持。最后，`exists_injective_adjacentCopy_selection` 把复制层、正内部
种子桥和由紧致性生成的 Pascal 选择器组合成一张共享标量偏置 CNN。对任何连续、非负、
单射编码并满足“相邻位置空闲”布局的紧输入族，返回的完整 CNN 在该输入族上保持单射，
其封装规格同时执行西北根上的选定 ReLU。因此，非恒定局部计算与信息保持现在已经在一张
真实单通道网络中共存，不再只是把副本关系作为外部假设。

[`SharedBiasMonotoneCode.lean`](OneChannelCNNUniversality/SharedBiasMonotoneCode.lean)
进一步证明：不需要在每次选择后重新制造精确副本。复制层只需使用一次，用来把西北角两个
坐标初始化为

$$
x_{0,0}=f(t),\qquad x_{0,1}=g(t),
$$

其中 $f$ 关于公共潜在编码 $t$ 单调，$g$ 关于 $t$ 严格单调。经过一个选择块后，Lean
验证新的两个因子具有形式

$$
f_{\mathrm{new}}(t)=\mathrm{ReLU}(f(t)+\theta),
\qquad
g_{\mathrm{new}}(t)=g(t)+(m+1)f(t)+C,
$$

这里 $m\geq 0$ 是额外横向传输步数，$C$ 与 $t$ 无关。因此
$f_{\mathrm{new}}$ 仍然单调，$g_{\mathrm{new}}$ 仍然严格单调；东侧坐标继续能够恢复
$t$，进而由选择器输出相等恢复整个选择器输入。该不变量不仅对抽象封装的选择器成立，
也已经提升到真实 `appendWithSeed` 组合网络的求值；只要前级网络在 $K$ 上单射，真实
组合后的网络仍在 $K$ 上单射。

[`SharedBiasMonotoneSchedule.lean`](OneChannelCNNUniversality/SharedBiasMonotoneSchedule.lean)
进一步把这个不变量闭合到依赖类型的任意有限递归中。谓词
`SuccessorSelectionSchedule.NorthwestTargeted` 明确记录：一个通常允许任意空间目标的日程
中，每个请求都选择西北工作寄存器。对任何满足该谓词的已编译日程，Lean 沿真实内部种子
组合逐步归纳，同时证明每一阶段 $s$ 都满足

$$
\mathrm{NorthwestMonotoneCodeOn}(K,N_s,t)
\quad\text{和}\quad
\mathrm{InjOn}(N_s,K).
$$

端到端定理 `exists_injective_compiledNorthwestSchedule` 从真实相邻复制层开始，利用紧致性
编译任意有限西北日程，并返回一张最终共享标量偏置 CNN 以及上述两个证书。其工作坐标的
递推精确为

$$
f_{s+1}(t)=\mathrm{ReLU}(f_s(t)+\theta_s).
$$

[`SharedBiasFrontier.lean`](OneChannelCNNUniversality/SharedBiasFrontier.lean)
进一步确定了“固定西北工作位置”策略的结构性上限。西北因果性意味着：若两个输入在
$(0,0)$ 的值相同，则无论网络深度和卷积核尺寸如何，任意有限扩张型共享偏置 CNN 的
西北输出都相同。因此，若一个标量目标在同一输入根纤维内发生变化，它就不可能在西北
输出处被精确实现。这个不可实现性判据直接引用已有因果性定理推出，没有重复证明历史
结论。Lean 还证明了定量的二点误差下界

$$
|f(x)-f(y)|\leq |N(F(x))_{0,0}-f(x)|
  +|N(F(y))_{0,0}-f(y)|.
$$

因此，当两个目标值相差 $\Delta$ 时，任何这种西北读出至少会在其中一个输入上产生
$\Delta/2$ 的误差。它不仅排除了精确实现，也对一致逼近构成了直接障碍。

正向替代方案是让计算前沿移动。Lean 已验证一个真实的 $2\times2$ 共享偏置层在其东侧
前沿精确计算

$$
y_{0,1}=\mathrm{ReLU}(x_{0,0}+x_{0,1}+\theta).
$$

当 $\theta=0$ 且输入族非负时，完整层仍保持单射，并且该坐标等于
$x_{0,0}+x_{0,1}$。也就是说，这个网络能够完成真实的双寄存器算术运算，同时不丢失
其余状态。这是用“向东或向南推进计算位置”取代不可能的“把所有信息送回西北角”路线
的第一个已机器检查原语。

[`SharedBiasFrontierChain.lean`](OneChannelCNNUniversality/SharedBiasFrontierChain.lean)
进一步把这个原语闭合到任意有限个真实零偏置横向层。若西北行最初含有寄存器 $a,b$，
且其后的东侧尾部为空，则经过 $s$ 层后，Lean 验证

$$
z_{0,s}=a+s b,\qquad z_{0,s+1}=b,\qquad
z_{0,q}=0\quad(q\geq s+2).
$$

因此，“更新后的工作值／不变的备份值”这一对寄存器每层向东移动一列。在非负输入族上，
真实 CNN 的求值满足这个精确不变量并继续保持单射，所以算术推进不会丢失图像其余状态。
这已经是一张任意深度的移动前沿证书，而不再只是单层公式。

[`SharedBiasFrontierTurn.lean`](OneChannelCNNUniversality/SharedBiasFrontierTurn.lean)
随后把这条横向前沿转向南方。对东侧尾部和下方各行均为空的西北双寄存器种子，真实的
“先横向、后纵向”网络能够到达任意前沿坐标 $(r,c)$，并满足

$$
z_{r,c}=a+c b,\qquad z_{r,c+1}=b,\qquad
z_{p,c}=z_{p,c+1}=0\quad(p\geq r+1).
$$

完整网络在非负种子族上保持单射，而且其深度精确等于曼哈顿距离

$$
L=r+c.
$$

因此，活跃的工作／备份寄存器对已经能够完成一次经过验证的二维转向，同时不丢失其值，
也不丢失完整特征图所编码的信息。

[`SharedBiasFrontierRoute.lean`](OneChannelCNNUniversality/SharedBiasFrontierRoute.lean)
进一步把任意有限方向序列 $\sigma\in\{E,S\}^{L}$ 编译成每步一层的真实零偏置
共享 ReLU 网络。记 $e(\sigma)$、$s(\sigma)$ 分别为向东与向南的步数。水平和纵向
全卷积彼此可交换；形式化证明给出了交错路径与下列标准次序在零延拓后的逐点相等：

$$
V^{s(\sigma)}H^{e(\sigma)}x.
$$

因此，任意多次转向路径的深度精确为

$$
L=|\sigma|=e(\sigma)+s(\sigma),
$$

网络在非负输入族上保持单射；对西北双寄存器种子还满足

$$
z_{s(\sigma),e(\sigma)}=a+e(\sigma)b,\qquad
z_{s(\sigma),e(\sigma)+1}=b.
$$

由于这里使用的两个 Pascal 算子可交换，转向的先后顺序不会改变终态。因此，这是一条
经过验证的任意路径运输定理，但还不是“路径顺序决定不同算术”的编译器。

[`SharedBiasFrontierAffineRoute.lean`](OneChannelCNNUniversality/SharedBiasFrontierAffineRoute.lean)
在仍然使用真实空间共享标量偏置的前提下打破了这种顺序不变性。令每个向东步骤使用
非负偏置 $\alpha$，每个向南步骤使用非负偏置 $\beta$。对非负输入，ReLU 始终处于
线性支，因此所得仿射路径仍具有精确求值、每方向一步一层和单射性。然而，共享偏置载波
会与下一层卷积发生方向相关的作用。形式化证明在坐标 $(1,1)$ 给出

$$
(ES)(x)_{1,1}=C(x)+2\alpha+\beta,
\qquad
(SE)(x)_{1,1}=C(x)+\alpha+2\beta,
$$

因而

$$
(ES)(x)_{1,1}-(SE)(x)_{1,1}=\alpha-\beta.
$$

所以当 $\alpha\ne\beta$ 时，仅仅交换方向次序就会得到两个输出可证明不同的二层、
二维单通道共享偏置 ReLU CNN。这是仓库中第一条经过验证的不可交换仿射前沿原语。

[`SharedBiasSignedGate.lean`](OneChannelCNNUniversality/SharedBiasSignedGate.lean)
跨过了下一道非线性检查点。对任意满足 $|x|\le M$ 的有界标量输入，以及任意带符号
系数 $a,c\in\mathbb R$，两个真实的 $2\times2$ 共享偏置层先把 $x$ 冗余编码为
$M+|c|+x$ 与 $M+|c|-x$，随后在一个输出坐标精确计算

$$
\mathrm{ReLU}(a x+c).
$$

同一个第二层还保留两个南侧坐标，并具有精确解码公式

$$
x=\frac{z_{2,0}-z_{2,1}}{2}.
$$

因此，完整隐藏表示在任意有界单射标量族上仍保持单射。对于紧集上的连续标量族，另一个
定理利用紧致性自动选择统一的 $M$。这是严格共享偏置模型中第一条经过验证的输入相关
带符号 ReLU 门；与此前的仿射路径差不同，它的非线性输出真正依赖输入。

[`SharedBiasRowGate.lean`](OneChannelCNNUniversality/SharedBiasRowGate.lean)
把这个标量构造提升到了任意有限寄存器行。对
$x=(x_0,\ldots,x_{n-1})$ 且 $|x_j|\le M$，同一个真实的二层共享偏置 CNN 对每个
$j$ 同时满足

$$
z_{0,j}=\mathrm{ReLU}(a x_j+c),
\qquad
z_{1,j}-(M+|c|+c)=x_j.
$$

因此，每个门控坐标都保留了精确解码器；完整行表示在有界单射族上仍保持单射；对于紧集
上的连续行族，紧致性还能选择统一的 $M$。这消除了此前只能处理单个孤立标量寄存器的
限制，但尚未证明这些可恢复行能够组合成任意有限计算。

[`SharedBiasGridGate.lean`](OneChannelCNNUniversality/SharedBiasGridGate.lean)
消除了输入必须只有一行的限制，同时仍把有效门放在北侧边界。对任意满足
$|x_{r,j}|\le M$ 的 $R\times C$ 输入，令

$$
B=(1+|a|)M+|c|.
$$

同一个真实的二层共享偏置 CNN 满足

$$
z_{0,j}=\mathrm{ReLU}(a x_{0,j}+c),
\qquad
z_{r+1,j}=x_{r,j}+a x_{r+1,j}+B+c,
$$

其中零延拓边界规定 $x_{R,j}=0$。所以受保护行可以从南向北精确解码：

$$
x_{r,j}=z_{r+1,j}-(B+c)-a x_{r+1,j}.
$$

Lean 已验证该三角编码对每个实数 $a$ 都是单射，并且完整网络在一致有界的单射图像族
上仍保持单射；紧致性同样给出统一的 $M$。这里验证的解码器是数学逆映射，尚未被编译成
具有同一因果方向的共享偏置 CNN；非线性门也仍只作用于输入最北行。

[`SharedBiasGridGateComposition.lean`](OneChannelCNNUniversality/SharedBiasGridGateComposition.lean)
证明受保护表示可以直接交给下一个受保护门块，而不必先执行外部逆映射。两个二层块组成一个
真实的四层 CNN，其北侧行满足

$$
z_{0,j}=\mathrm{ReLU}\!\left(
  a_2\,\mathrm{ReLU}(a_1x_{0,j}+c_1)+c_2\right),
$$

并且完整四层表示仍保持单射。紧致性会在第一个非线性块之后重新选择统一界，而不是假设
存在一个未经证明、可供所有阶段共用的全局大常数。

[`SharedBiasGridGateSchedule.lean`](OneChannelCNNUniversality/SharedBiasGridGateSchedule.lean)
进一步闭合了有限归纳。对任意有限列表
$((a_1,c_1),\ldots,(a_L,c_L))$，存在一个精确深度为 $2L$ 的真实扩张型单通道共享偏置
CNN，其北侧行计算

$$
t_0=x_{0,j},
\qquad
t_{\ell+1}=\mathrm{ReLU}(a_{\ell+1}t_\ell+c_{\ell+1}),
\qquad
z_{0,j}=t_L,
$$

同时完整特征表示在紧输入族上仍保持单射。这是仓库中严格共享偏置模型的第一条任意深度
非线性组合定理。不过它仍是逐坐标的标量日程：同一个门作用于北侧行的每个坐标，尚不能
混合不同寄存器，也不能把更深的输入行送到北侧边界。

[`SharedBiasAffineMixGate.lean`](OneChannelCNNUniversality/SharedBiasAffineMixGate.lean)
针对至少含两个寄存器的行中的一对相邻寄存器，消除了上述第一个限制。对任意带符号权重
$\lambda\in\mathbb R$，紧集上线性化的共享偏置层形成

$$
y_{i,j}=x_{i,j}+\lambda x_{i,j-1}+b.
$$

该变换对每个实数 $\lambda$ 都是单射：第一列保持不变，其后每一列都能利用已经恢复的
西侧前驱递推恢复。再接一个受保护网格门，就得到一个真实的三层网络，并在目标北侧
寄存器精确满足

$$
z_{0,1}=\mathrm{ReLU}\!\left(
  a(x_{0,1}+\lambda x_{0,0})+c\right).
$$

与此同时，完整特征表示仍保持单射；对于连续单射的有限图像紧族，紧致性会自动选择
两个统一载波。特别地，$\lambda$ 可以为负，所以该原语既能表达求和也能表达差分；这是
仓库中第一条已经验证、会在非线性门前混合两个不同输入寄存器的定理。更强的全坐标定理
还验证了同一公式会同时作用于每个原始北侧寄存器，并在 $j=0$ 使用西侧零边界。

[`SharedBiasLocalGateSchedule.lean`](OneChannelCNNUniversality/SharedBiasLocalGateSchedule.lean)
闭合了这类空间共享局部门的有限归纳。给定日程
$((\lambda_1,a_1,c_1),\ldots,(\lambda_L,a_L,c_L))$，定义

$$
t_{0,j}=x_{0,j},
\qquad
t_{\ell+1,j}=\mathrm{ReLU}\!\left(
  a_{\ell+1}
  \bigl(t_{\ell,j}+\lambda_{\ell+1}t_{\ell,j-1}\bigr)
  +c_{\ell+1}\right),
$$

并规定 $t_{\ell,-1}=0$。Lean 现在会构造一个精确深度为 $3L$ 的真实共享偏置 CNN，
在每个原始北侧坐标满足 $z_{0,j}=t_{L,j}$，且完整特征图始终保持单射。前缀定理和
感受野定理进一步证明，第 $j$ 个坐标只依赖初始坐标
$\max(0,j-L),\ldots,j$。

[`SharedBiasAdjacentRidge.lean`](OneChannelCNNUniversality/SharedBiasAdjacentRidge.lean)
在任意一致有界输入族上消除了上述三层混合块对系数分解的限制。对于任意
$\alpha,\beta,\gamma\in\mathbb R$，一个真实的两层共享偏置网络会在每个非西侧北行
寄存器精确计算

$$
\mathrm{ReLU}(\alpha x_{0,j-1}+\beta x_{0,j}+\gamma).
$$

与此同时，每个输入坐标都会向东南移动一步，并保存在精确的三角备份编码

$$
x_{i,j}+\alpha x_{i+1,j}+\beta x_{i+1,j+1}+C
$$

中，边界使用零延拓。Lean 已通过从南到北的恢复证明该编码单射，并证明紧致性会为任意
连续单射输入族选出一个统一载波。因此，任意相邻仿射 ridge 可以在不丢失完整输入状态
的情况下加入网络；但若要反复加入彼此独立的 ridge，仍需构造符合因果方向的操作数布局。

[`SharedBiasAdjacentLattice.lean`](OneChannelCNNUniversality/SharedBiasAdjacentLattice.lean)
把上述恢复结论加强到仿射读出层面。三角备份的线性部分具有一个选定的线性左逆，因而
每个原输入坐标都能从同一个两层网络的完整输出中，由有限仿射读出精确恢复。当
$(\alpha,\beta,\gamma)=(1,-1,0)$ 时，同一个固定网络的两组不同读出分别给出

$$
\min(a,b)=a-\mathrm{ReLU}(a-b),\qquad
\max(a,b)=b+\mathrm{ReLU}(a-b).
$$

对紧的单射输入族，完整特征表示仍保持单射。这里得到的是终端仿射读出：所选左逆并非
因果卷积层，因此该结果还不能把嵌套的最小值／最大值表达式编译到隐藏网络内部。

[`SharedBiasThreePointRidge.lean`](OneChannelCNNUniversality/SharedBiasThreePointRidge.lean)
给出了本工程中第一个精确的非相邻任意仿射门。对有界的 $1\times3$ 输入和任意
$r_0,r_1,r_2,\gamma\in\mathbb R$，一个真实的两层网络会在输出坐标 $(1,2)$ 精确计算

$$
\mathrm{ReLU}(r_0x_0+r_1x_1+r_2x_2+\gamma).
$$

构造把第二个空间方向用作临时存储。北侧三个输出坐标形成对角尺度严格为正的显式三角
仿射编码，并有一个显式解码器精确恢复 $(x_0,x_1,x_2)$，所以完整输出保持单射。这是
一个精确的三寄存器扩展定理，但还不是任意维仿射 ReLU 扩展，也不是可迭代的万能编译器。

[`SharedBiasFourPointRidge.lean`](OneChannelCNNUniversality/SharedBiasFourPointRidge.lean)
验证了下一个非相邻情形。对于任意有界的 `Image 1 4` 输入以及任意
$r_0,r_1,r_2,r_3,\gamma\in\mathbb R$，一个真实的三层扩张型 $2\times2$ 单通道网络
（每层只有一个共享标量偏置）会在输出坐标 $(1,3)$ 精确计算

$$
\mathrm{ReLU}(r_0x_0+r_1x_1+r_2x_2+r_3x_3+\gamma).
$$

其北侧四个输出的变量部分由三角滤波器

$$
P(z)=(1+z)(1+2z)(1+3z)=1+6z+11z^2+6z^3
$$

给出。载波项是已知常数，因此一个显式仿射解码器可以精确恢复全部四个输入坐标；由此，
完整网络在任意紧的单射特征族上保持单射。这是第二个非相邻基例，并验证了有限多项式机制
确实能越过三寄存器情形。下面的任意宽度构造现已把三寄存器和四寄存器基例推广到所有
$m\ge 3$ 的单行输入。它仍然是单个 ridge 的扩展定理，还不是一般二维状态、重复加入 ridge
或共享偏置万能逼近的编译器。

[`SharedBiasGeneralRidgePolynomial.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgePolynomial.lean)
对任意深度 $d$ 形式化了 Lagrange 分解。它采用首一节点因子

$$
A_i(X)=X+(i+1),\qquad 0\le i<d,
$$

并定义目标多项式 $R_w$，使 $X^j$ 的系数为
$w(\mathrm{Fin.rev}(j))$；这个内置反序恰好抵消自然输出列处的卷积反序。Lean 已证明
$R_w$ 可以由节点乘积 $\prod_iA_i$ 及其逐个删去一个因子的补多项式作 Lagrange 分解。
给定满足 $\sum_i\eta_i=w_0$ 的数值 $\eta_i$，还构造了线性下因子 $B_i$，并证明

$$
[Y]\prod_{i=0}^{d-1}\bigl(A_i(X)+YB_i(X)\bigr)=R_w(X).
$$

因此，这已经是任意 $d$ 的机器检查代数定理，不是从三寄存器与四寄存器情形作出的外推。

[`SharedBiasGeneralRidgeConvolution.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeConvolution.lean)
把每个因子 $A_i(X)+YB_i(X)$ 变成真实的 $2\times2$ 卷积核

$$
K_i=
\begin{pmatrix}
i+1 & 1\\
\beta_i+\eta_i(i+1) & \eta_i
\end{pmatrix}.
$$

对于任意逐层变化的这类卷积核列表，Lean 把北侧行与第一条南侧行的递推精确对应到二元
因子乘积的系数。因此，特化后的纯完整卷积链在自然位置满足

$$
\mathrm{FullConvChain}(x)_{1,d}
  =\sum_{j=0}^{d}w_jx_j.
$$

这里非平凡的南侧目标取正深度。代数也覆盖退化情形 $d=0$；此时分配条件强制
$w_0=0$，而南侧坐标位于零深度输出之外。

北侧边界则是三角多项式传输

$$
G_d(X)\,\mathrm{Row}_0(x),\qquad
G_d(X)=\prod_{i=0}^{d-1}\bigl(X+(i+1)\bigr).
$$

该文件也把任意逐层变化的卷积核列表封装成真实的零偏置 `SharedBiasNetworkTo`，但只有在
显式 `LinearBranchAlong` 假设下——即沿途遇到的每个预激活都非负——才证明其求值等于
纯卷积链。下面的载波、分离、选择与恢复模块已经对紧输入族上的一个完整任意宽度 ridge
块消除了这一条件。

[`SharedBiasGeneralRidgeCarrier.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeCarrier.lean)
对每个 $d\ge 2$ 选择一个显式的下因子分配。若 $\beta_{d-1}$ 是最后一个 Lagrange 系数，
载波尺度取为

$$
T=\frac{|\beta_{d-1}|+d+2}{d+1},
$$

同时仍有 $\sum_i\eta_i=w_0$。
[`SharedBiasGeneralRidgeSeparation.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeSeparation.lean)
进一步证明：最后一个卷积核作用在大小为 $d\times 2d$ 的单位常值载波上时，每个北侧坐标
都至少比南侧目标 $(1,d)$ 高 $2$。

[`SharedBiasHeterogeneousCarrier.lean`](OneChannelCNNUniversality/SharedBiasHeterogeneousCarrier.lean)
把任意逐层变化的因子前缀提升为紧连续输入族上的真实共享偏置 ReLU 层。前缀最后一层中
可调的非负增量经过终端卷积后变成空间地址。
[`SharedBiasTerminalSelection.lean`](OneChannelCNNUniversality/SharedBiasTerminalSelection.lean)
利用单位地址间隙与紧致性，统一选出一个全局增量和最后一个共享标量偏置：目标进入非线性
ReLU 分支，而每个受保护的北侧坐标仍等于纯信号加一个与输入无关的固定偏移。

[`SharedBiasGeneralRidgeRecovery.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeRecovery.lean)
证明完整北侧行是单射编码。其生成多项式等于输入行多项式乘以上面的非零首一因子 $G_d$，
所以北侧行相等会强制输入相等；加上固定偏移也不改变这一结论。

最后，
[`SharedBiasGeneralRidgeNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeNetwork.lean)
把这些部件装配成真实的非线性网络定理。设 $m\ge 3$，$K$ 为紧集，且
$F:X\to\mathbb R^{1\times m}$ 在 $K$ 上逐坐标连续。对任意
$w\in\mathbb R^m$ 与 $\gamma\in\mathbb R$，Lean 构造一个采用 $2\times2$ 卷积核、
单通道、逐层共享标量偏置的扩张型 ReLU 网络 $N$，满足

$$
\mathrm{depth}(N)=m-1,
\qquad
N(F(x))\in\mathbb R^{m\times(2m-1)},
$$

并且对每个 $x\in K$ 都有

$$
N(F(x))_{1,m-1}
=\mathrm{ReLU}\!\left(\sum_{j=0}^{m-1}w_jF(x)_{0,j}+\gamma\right).
$$

对每个北侧坐标 $q$，输出还满足

$$
N(F(x))_{0,q}
=\bigl[G_{m-1}(X)\,\mathrm{Row}_0(F(x))\bigr]_q+c_q,
$$

其中 $c_q$ 与 $x$ 无关。如果 $F$ 在 $K$ 上还满足单射性，那么 $N\circ F$ 在 $K$ 上
仍然单射。也就是说，任意宽度的单个 ridge 网络提升——包括共享载波和最终 ReLU 后的
恢复论证——现已全部通过机器检查。

[`SharedBiasGeneralRidgeLState.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeLState.lean)
证明：作为逻辑状态，并不需要保留整个扩张矩形。北侧最前面的 $m$ 个坐标已经构成单射的
三角编码；再加上位于 $(1,m-1)$ 的 ridge，它们落在东南单调链

$$
(0,0),(0,1),\ldots,(0,m-1),(1,m-1)
$$

上。提取得到的 $1\times(m+1)$ 状态逐坐标连续；若输入特征映射单射，它也保持单射，且最后
一个坐标精确等于所需 ridge。不过，这种坐标限制只是对已有特征图的数学读取，并不是额外的
卷积层，也还不是能够直接作为新 CNN 模块追加的网络对象。

[`SharedBiasGeneralRidgeReadout.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeReadout.lean)
把北侧恢复与一个 ridge 组合成精确的终端格运算。给定任意两个输入仿射函数

$$
A(x)=\sum_j a_jx_j+\alpha,
\qquad
B(x)=\sum_j b_jx_j+\beta,
$$

一个深度为 $m-1$ 的真实共享偏置网络在受保护目标点计算
$\mathrm{ReLU}(A-B)$。对同一个输出使用两组普通有限仿射读出，分别从北侧编码恢复 $A$ 或
$B$，再与目标组合，就能在给定紧输入族上精确得到 $\min(A,B)$ 与 $\max(A,B)$。这里非构造性
选取且通常非局部的线性左逆只属于最终读出，并不是卷积隐藏层，所以该定理还不能编译嵌套格表达式。

[`SharedBiasGeneralRidgeCompositionObstruction.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeCompositionObstruction.lean)
精确指出当前构造为什么不能作为黑盒直接串联。对多行状态 $Z$，纯 general-ridge 因子链满足

$$
\mathrm{Row}_1(\mathrm{out})
=G_d(X)\,\mathrm{Row}_1(Z)+R_w(X)\,\mathrm{Row}_0(Z).
$$

由于首一因子 $G_d$ 非零，即使固定北侧行，输出仍不会消除对旧第二行的依赖。此外，当前
终端载波地址在第二行所有内部位置上完全相同，目标点与其前驱也不例外，所以它无法提供“保护
整条第二行但只选择一个新目标”所需的单位间隙。这些定理排除了对当前分离块的朴素复用，
并没有排除另一种多 ridge 构造，也没有否定该网络架构的万能逼近性。

[`SharedBiasGeneralRidgeIdealAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeIdealAddress.lean)
给出了修复第二行平坦地址的精确代数候选。令

$$
G_d(X)=\prod_{i=1}^{d}(X+i),
\qquad C_d(X)=1+X+\cdots+X^d.
$$

$G_d$ 从 $0$ 次到 $d$ 次的每个系数都至少为一。乘积 $G_dC_d$ 的 $d$ 次系数包含这些
系数的完整总和，而其他任何次数都至少漏掉其中一项。因此 Lean 已证明：$d$ 次位置是
具有至少单位间隙的唯一最高点；整体取负以后，它就是具有同样间隙的唯一最低点。这正是
保护完整第二行所需的空间形状。这里有意只陈述代数地址定理：下一项网络级任务仍是证明
真实共享偏置 CNN 能在保留可变信号的同时，从网络内部生成这条有限箱形载波。

[`SharedBiasGeneralRidgeAddressPlateau.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeAddressPlateau.lean)
分析了线性传播偏置 boost 的一个抽象多项式载波模型。若输入宽度为 $m$、总深度为 $L$，
并假设第 $k$ 个偏置方向具有“次数受限多项式乘指定箱形多项式”的形式，那么每个偏置方向
乃至它们的任意实线性组合，都在区间

$$
L-1\le q\le m
$$

上恒定。一个能够看到全部 $m$ 个输入的目标必须满足 $m-1\le q\le L$。Lean 已证明：
只要 $m-1\le L\le m$，这样的目标必有另一个不同位置与它地址完全相同；到 $L=m+1$
时，原共同平台才首次缩成单点 $\{m\}$。这是该多项式线性载波模型内部的锐利结论；本模块
尚未声称存在从任意真实网络到该多项式表示的定理，因此它不是对含真正非线性中间掩码的
任意共享偏置网络所作的深度下界。

[`SharedBiasGeneralRidgeLowWindow.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeLowWindow.lean)
给出了顺序多 ridge 构造所需的有限三角逆元。若 $H(0)\ne0$，那么对任意多项式 $R$
和次数预算 $d$，它会构造满足 $\deg U\le d$ 的多项式 $U$，并精确证明

$$
[X^j](UH)=[X^j]R,
\qquad 0\le j\le d.
$$

构造方法是截断形式幂级数 $RH^{-1}$，并没有声称 $H$ 存在多项式逆元。它允许后续 ridge
阶段在所需低阶窗口中精确抵消此前各阶段的已知仿射传输。因此，多 ridge 路线剩余的核心
难点已经集中到真实共享偏置载波：每次选择 ReLU 时，必须同时保护完整北侧行和第二行的
指定后缀；有限系数匹配本身已经由 Lean 闭合。

[`SharedBiasGeneralRidgeStripeAlgebra.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeAlgebra.lean)
实现了第一种两行修复方案所需的带符号因子日程。给目标权重追加一个零坐标后，该日程保持
所需的纵向一次多项式不变，同时把完整横向乘积变为

$$
-T\prod_{i=1}^{d}(X+i).
$$

当 $T\ge1$ 时，最后一个扭转因子的四个卷积 tap 全都不大于 $-1$。这正是候选终端条带门
所需的符号结构；后续载波模块会在终端门中使用这一符号结构。

[`SharedBiasGeneralRidgeStripePrefix.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripePrefix.lean)
证明了该扭转日程的每个 proper prefix 都保留正横向乘积

$$
G_k(X)=\prod_{i=1}^{k}(X+i).
$$

$G_kC_m$ 在完整支撑 $0\le q\le k+m$ 上的每个系数都至少为一，包括两侧斜坡；在完整窗口
区间上，它精确等于 $(k+1)!$。这些是前缀代数界；下一项载波定理控制第二行的纵向扰动。

[`SharedBiasGeneralRidgeStripeCarrier.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeCarrier.lean)
闭合了 proper prefix 的正性问题。它证明两行载波的精确公式

$$
\mathrm{row}_0=2G_kC_m,
\qquad
\mathrm{row}_1=2G_kC_m-2T^{-1}R_kC_m,
$$

对所有前缀及所有真实输出列建立一个有限绝对值界，并取显式向上封闭阈值
$T_0=2(B+1)$。因此每个 $T\ge T_0$ 都使常数二条带成为所有 proper 层上的
`NorthTwoUnitLowerAlong` 载波，包括最短情形和两侧边界斜坡。

[`SharedBiasGeneralRidgeStripeFinalAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeFinalAddress.lean)
计算了真实末卷积核对前一层单位常数 boost 的响应。每个北侧坐标和第二行两个端点都比目标
至少高二，而第二行每个内部坐标都与目标地址严格相同。因此这个方向提供所需的纵向和边界
分离，同时也形式化确认了它单独无法产生横向唯一性。

[`SharedBiasNorthTwoLinearization.lean`](OneChannelCNNUniversality/SharedBiasNorthTwoLinearization.lean)
证明了与之互补的真实网络不变量。对扩张型 $2\times2$ 卷积，北侧两条输出行只依赖北侧
两条输入行。因此，只要每一阶段仅在这两行上的预激活非负，真实零偏置 ReLU 网络就在这两行
与形式卷积链一致；更南侧即使发生任意非线性，也不能反向污染北侧。这显著弱化了旧的全图
线性条件，但它本身还没有给出缺失的前缀非负界。

[`SharedBiasNorthTwoCarrier.lean`](OneChannelCNNUniversality/SharedBiasNorthTwoCarrier.lean)
闭合了这些界背后的紧致性步骤。它证明：只要一个固定载波在每个前缀的北侧两行预激活上
至少贡献一，就能一次性放大它，使任意连续紧输入族满足 `NorthTwoLinearAlong`。它还证明了
一个向上封闭的 identity-seed 定理：当共享偏置 $c$ 充分大时，真实第一层 ReLU 对所有更大的
$c$ 都精确等于 identity 卷积加常数图 $c$。上面的显式载波已经提供了所需单位下界证书。

[`SharedBiasSeededNorthTwoNetwork.lean`](OneChannelCNNUniversality/SharedBiasSeededNorthTwoNetwork.lean)
把这两个组成部分封装为同一个向上封闭紧集阈值。超过该阈值后，真实 identity seed 层精确
处于仿射支路，且每个 proper factor 的北侧两行预激活都非负。因此真实 seed 加零偏置网络
在这两行上与完整形式卷积链一致；更南侧的行仍有意不作限制。

[`SharedBiasBiasedLast.lean`](OneChannelCNNUniversality/SharedBiasBiasedLast.lean)
允许任意非空异构因子块只在最后一层使用一个非负共享偏置，其余层偏置为零。在同一个北侧
两行线性证书下，真实输出在受保护两行上精确等于形式卷积链加该常数。这给出了末条带因子
所用局部载波的真实网络来源。

[`SharedBiasGeneralRidgeStripeSeedAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeSeedAddress.lean)
证明完整的带符号条带链会把 identity-seed 箱形信号变成可缩放地址，并使第二行中心成为
唯一最低点。更精确地，它给出分解

$$
A_0(q)=-T I_m(q),
\qquad
A_1(q)=-T I_m(q)+B(q),
$$

构造 $T$ 的显式向上封闭阈值，并证明第二行目标与其他每一列之间都有单位间隙。它还给出
所有北侧坐标相对目标的下界，并把固定目标扰动识别为 $B(m)=\sum_j w_j$。在接上前缀线性
桥之前，这些仍是完整链上的精确代数结论。

[`SharedBiasTwoCarrierSelection.lean`](OneChannelCNNUniversality/SharedBiasTwoCarrierSelection.lean)
形式化了组合两个互补地址方向的紧集末端掩码。一个载波可负责横向唯一性，另一个负责北侧
与边界分离；在第二类位置上允许第一个方向存在有限亏损。紧致性给出统一的正缩放，使目标点
精确施加一次指定的 ReLU，而其他每个受保护坐标都保持在线性支路。
强化接口允许预先指定种子尺度的任意下界，因此同一尺度可以同时满足此前所有线性化阈值。

[`SharedBiasGeneralRidgeStripeAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeAddress.lean)
在最终矩形上组合了两个地址方向。Lean 已证明选择器所需的精确二分：每个非目标第二行位置
都有单位 seed 地址间隙和非负局部间隙；每个北侧位置都有二单位局部间隙，而 seed 地址亏损
由有限目标扰动统一控制。

[`SharedBiasGeneralRidgeStripeProperNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeProperNetwork.lean)、
[`SharedBiasGeneralRidgeStripeRealization.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeRealization.lean)
与 [`SharedBiasGeneralRidgeStripeNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeNetwork.lean)
已闭合最后的定型网络实现桥。对宽度为 $n+2$ 的输入，构造得到一个真实的、深度为
$n+3$ 的单通道扩张型 $2\times2$ 共享标量偏置 ReLU 网络。对任意连续紧输入族，
可以统一选取正参数，使受保护坐标 $(1,n+2)$ 满足精确恒等式

$$
N_{w,\theta}(x)_{1,n+2}
=\mathrm{ReLU}\!\left(\sum_{j=0}^{n+1}w_jx_j+\theta\right).
$$

机器检查的定理比单一目标等式更强：它识别了北侧两行每个坐标的输出，并证明所有非目标
受保护坐标都保持在末层 ReLU 的线性分支。
[`SharedBiasGeneralRidgeStripeRecovery.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeRecovery.lean)
进一步证明：当 $T\ne0$ 时，完整北侧行是原输入的单射线性编码；它还构造了精确恢复
输入的线性左逆，并证明整个真实 ridge 网络在紧单射特征族上仍保持单射；此外还构造了
有限仿射读出权重，可从同一个最终特征图精确恢复任意另选的输入仿射函数。
[`SharedBiasGeneralRidgeStripeMinMax.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeMinMax.lean)
把恢复的仿射值与受保护 ridge 坐标组合起来，证明对任意两个输入仿射函数 $A,B$ 都存在
精确的终端读出：

$$
\min(A,B)=A-\mathrm{ReLU}(A-B),\qquad
\max(A,B)=B+\mathrm{ReLU}(A-B).
$$

所得完整状态仍保持单射。因此，“任意宽度单 ridge”子问题及其第一个二元格运算接口
现已完成。
[`SharedBiasGeneralRidgeStripeAffineCombination.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeAffineCombination.lean)
给出一般的精确读出推论：对任意实参数，同一个真实深度 $n+3$ 网络的一个有限仿射读出
可实现

$$
\lambda\,\mathrm{ReLU}\!\left(\sum_j w_jx_j+\theta\right)
  +\sum_j a_jx_j+\alpha,
$$

并保持状态单射。这完整覆盖了“一个隐藏 ReLU 单元加仿射跳连项”的函数类，但尚不是
有限多个隐藏单元之和。
[`SharedBiasParallelRidgeAlgebra.lean`](OneChannelCNNUniversality/SharedBiasParallelRidgeAlgebra.lean)
给出了避免朴素串接多行 ridge 输出的具体有限并行路线。对任意 $r$ 个相互独立、输入宽度
为 $m$ 的权向量，把它们的反向系数分别放入互不相交的多项式窗口

$$
sm+1,\ldots,(s+1)m,\qquad 0\le s<r.
$$

Lean 已证明：一个深度为 $rm$ 的双线性因子链，会在第二行的
$m,2m,\ldots,rm$ 列同时精确计算这 $r$ 个线性形式。因此，无碰撞的代数并行化已经
完成。要把它提升为真实的有限多 ridge CNN 定理，仍需构造紧集上一致的共享偏置载体，
在所有目标坐标施加 ReLU，同时保护可恢复的北侧编码。
[`SharedBiasMultiTargetSelection.lean`](OneChannelCNNUniversality/SharedBiasMultiTargetSelection.lean)
现已完成其中的紧集选择器部分：如果一个载体在所有目标处具有共同基线，并在每个受保护
非目标坐标处至少高出一个单位，那么一个正尺度和一个广播标量偏置就能在全部目标上同时
施加 ReLU，而所有受保护非目标坐标精确保持线性。真实最终卷积层的分解定理把这一抽象
判据直接连接到共享偏置网络层。目前剩余的是为上述等距打包目标显式构造满足判据的载体。
[`SharedBiasGeneralRidgeStripeWidthCarrier.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthCarrier.lean)
消除了该构造中最主要的尺寸错配。现在带符号条带的因子深度与种子宽度彼此独立：对任意
因子深度 $d=n+2$ 和种子宽度 $m+1$，Lean 都构造了有限误差界及显式向上闭阈值
$T_0=2(B+1)$。超过该阈值后，每个真实 proper prefix 在北侧两行和全部实际输出列上都
至少为一。因此，并行打包不再需要仅为保持前缀 ReLU 线性而把宽度 $m$ 的输入填充到
深度 $rm$。
[`SharedBiasGeneralRidgeStripeWidthProperNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthProperNetwork.lean)
进一步把这个独立宽度载体提升到了真实网络层面。对任意输入宽度 $m$ 以及由
$w:\mathrm{Fin}(n+2)\to\mathbb R$ 决定的 proper 因子块，它构造了深度恰为 $n+2$、
输出尺寸为 $(n+3)\times(m+n+2)$ 的共享偏置 ReLU 网络。对任意紧输入族，存在一个
统一种子阈值，使网络北侧两行与形式 proper 卷积状态精确一致。因此，有限多 ridge
定理现在剩下的关键不再是前缀线性化。
[`SharedBiasGeneralRidgeStripeWidthFinalAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthFinalAddress.lean)
又验证了最终共享载体的局部几何部分：当 $T\ge1$ 时，第二行所有内部坐标具有同一个
基线，而全部北行坐标以及第二行的两个端点至少高出该基线 $2$。现在尚需构造全局水平
地址，把打包的内部目标与受保护的内部非目标分开，然后完成终端仿射求和。
[`SharedBiasGeneralRidgeStripeWidthSeedAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthSeedAddress.lean)
给出了任意宽度完整链地址的精确公式

$$
A_1(q)=-T[X^q](G_{n+2}C_m)+[X^q](P_wC_m).
$$

该公式也暴露了直接复用单目标结点载体的真实障碍。在最小的双目标、宽度二实例中，
[`SharedBiasParallelStripeObstruction.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeObstruction.lean)
机器验证了

$$
[X^2](G_4C_2)=109,
\qquad [X^4](G_4C_2)=46.
$$

所以当打包权重全为零且 $T\ne0$ 时，两个目标地址分别是 $-109T$ 与 $-46T$，不可能满足
同时选择器的共同基线条件。障碍实际上比这个数值实例更强：对任意首一四次水平多项式
$Q$，若 $[X]Q\ge1$ 且两个目标窗口相等，即
$[X^2](QC_2)=[X^4](QC_2)$，那么 Lean 证明

$$
[X^2](QC_2)\le [X^3](QC_2).
$$

乘上负的正尺度条带后，中间非目标不可能比共同目标基线高出一个单位。因此，这排除了
最小双目标几何中整个“正前缀载体”模式，而不只是一组结点；它仍不否定有限多 ridge
万能逼近。下一条路线必须使用性质不同的水平载体，或采用顺序受保护调度。
[`SharedBiasParallelStripeCandidate.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeCandidate.lean)
进一步证明：一旦放弃正前缀，所需的双目标地址在代数上确实存在。首一实根多项式

$$
Q(X)=(X-1)(X-2)(X-3)\left(X+\frac14\right)
$$

满足

$$
[X^2](QC_2)=[X^4](QC_2)=\frac{19}{4},
\qquad [X^3](QC_2)=\frac12,
$$

所以目标相对中间非目标的精确间隔为 $17/4$。Lean 同时验证了代价：按上述因子顺序，
前缀 $(X+1/4)(X-1)C_2$ 的常数系数为 $-1/4$。这说明多目标分离与旧的“所有前缀
均为正”线性化机制直接冲突；剩余构造问题现在被精确压缩为如何线性化符号变化的前缀。

[`SharedBiasParallelStripeCompensation.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeCompensation.lean)
解决了这个最小前缀线性化问题。对任意尺度 $s\ge0$，依次使用因子

$$
X+\frac14,\qquad 1-X,\qquad X-2,\qquad X-3,
$$

从种子 $4sC_2$ 出发，并在前三个因子后分别加入共享标量偏置 $0$、$5s$、$13s$。
Lean 证明每个 proper 中间状态的全部系数都至少为 $s$，而完整地址满足

$$
A(2)=A(4)=-35s,
\qquad A(3)=-18s,
\qquad A(3)-A(2)=17s.
$$

因此 $s\ge1/17$ 时就得到同时选择器要求的单位间隔。这是一个实质性的正面构造：它给出
每层一个共享标量偏置的精确补偿数据，并证明载体分量具有严格的线性分支裕量。剩余工作是
用同时承载可变打包 ridge 信号的因子来特化下述紧集真实网络桥接，再与二维北侧受保护编码
组合起来；目前仍不宣称已经证明共享偏置有限 ridge 万能性。

[`SharedBiasCompensatedCarrier.lean`](OneChannelCNNUniversality/SharedBiasCompensatedCarrier.lean)
现在以通用形式证明了这条路线所需的紧集真实网络桥接。一个补偿因子步骤由一个双线性
$2\times2$ 核和一个标量载体偏置系数组成。若形式载体在整个因子链的北侧两行每个预激活
坐标都至少为一，则紧集性给出统一阈值 $s_0$。对所有 $s\ge s_0$，第 $i$ 层使用共享偏置
$sc_i$ 的真实 ReLU 网络在北侧两行满足精确逐坐标恒等式

$$
\mathrm{Net}_s(V(x)+sC)=
\mathrm{ConvChain}(V(x))+s\,\mathrm{CompCarrier}(C).
$$

该定理适用于任意有限异质因子列表和任意紧的逐坐标连续信号族。下一项特化工作已经变成
完全有限的问题：证明显式的 $(0,5,13)$ 双目标载体在同一组因子同时承载打包 ridge 信号时，
确实满足这个北侧两行单位下界假设。

[`SharedBiasParallelStripeFactorization.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeFactorization.lean)
完成了这项特化中的可变信号代数。对两个任意的宽度二权向量，将它们无碰撞地打包为

$$
P(X)=w_{0,1}X+w_{0,0}X^2+w_{1,1}X^3+w_{1,0}X^4,
$$

并为同一组四个水平因子给出显式有理数竖直抽头。Lean 逐系数证明到四次为止，乘积的
竖直一次部分恰好等于 $\varepsilon P$。因此形式卷积链在两个目标位置精确读出

$$
\varepsilon(w_{0,0}x_0+w_{0,1}x_1),\qquad
\varepsilon(w_{1,0}x_0+w_{1,1}x_1).
$$

参数 $\varepsilon$ 仍可自由选择，这正是控制补偿载体扰动所需的自由度。这已经是一条精确的
双 ridge 双线性分解，但还不是完整的共享偏置 ReLU 网络定理：下一项义务是识别并修正由权重
引起的载体偏移，同时保持受保护的单位间隔，再实例化紧集桥接。

[`SharedBiasParallelStripeCarrierCorrection.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeCarrierCorrection.lean)
解决了这个载体相互作用。对上述显式竖直抽头，未经修正的加倍载体会在两个目标处产生一个
由打包权重决定的固定线性差。在输入第二行的西南角加入一个显式修正

$$
\frac{16}{17}\varepsilon
  (w_{0,1}-w_{1,1}-w_{1,0})
$$

即可精确抵消该差异。Lean 先将其证明为生成多项式恒等式，再把它传递到真实有限卷积图像。
Lean 还证明：对任意两个权向量，都存在严格正的 $\varepsilon$，使三个 proper 层北侧两行的
全部坐标至少为一，最终两个载体目标具有完全相同的基线，并且受保护的中间位置仍比该基线
高出严格大于一。因此紧集真实网络桥所要求的完整有限载体条件已经解决。剩余步骤是完成最终
共享偏置 ReLU 选择（包括仿射 ridge 偏移），再与受保护的二维编码复合。

[`SharedBiasParallelStripeProperNetwork.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeProperNetwork.lean)
现在已经实例化紧集桥接。对任意紧的逐坐标连续两行三列信号族和任意两个宽度二权向量，
Lean 给出正打包尺度 $\varepsilon$ 与统一网络阈值 $s_0$。对所有 $s\ge s_0$，真实三层
共享偏置 ReLU 网络在北侧两行精确等于

$$
\mathrm{VariableChain}(V(x))+
s\,\mathrm{CorrectedCarrier}.
$$

同一个 $\varepsilon$ 还具有上面证明的严格最终选择间隔。

[`SharedBiasParallelStripeAffinePacking.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeAffinePacking.lean)
解决了最终共享偏置无法直接提供两个独立偏移的问题。第二输入行只使用常数项和二次项

$$
h_0=\frac{-38a-6b}{367},\qquad
h_2=\frac{4a-38b}{367},
$$

使水平乘积在第 $2$、$4$ 列分别贡献 $a$、$b$。取
$a=\varepsilon\theta_0$、$b=\varepsilon\theta_1$，完整四因子可变链就在两个目标处得到

$$
\varepsilon(w_{0,0}x_0+w_{0,1}x_1+\theta_0),\qquad
\varepsilon(w_{1,0}x_0+w_{1,1}x_1+\theta_1).
$$

Lean 已验证这两个恒等式以及该固定仿射输入填充映射的连续性。

[`SharedBiasParallelStripeAffineNetwork.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeAffineNetwork.lean)
进一步闭合了紧集上的双 ridge 模块。它把同时选择定理加强为向上封闭的尺度阈值，与前三个
proper ReLU 层的阈值取最大值，再接上第四次卷积和一个共享最终偏置，得到真实的深度四、
单通道网络。对任意两个宽度二仿射 ridge 和任意紧输入集，当网络作用于显式加载了载体的
仿射嵌入状态时，两个目标坐标精确等于

$$
\varepsilon\,\mathrm{ReLU}(w_0\mathbin{\cdot}x+\theta_0),\qquad
\varepsilon\,\mathrm{ReLU}(w_1\mathbin{\cdot}x+\theta_1),
$$

其中 $\varepsilon>0$，公共因子可由后续仿射读出消去。这是一个实质性的并行化结论：两个
具有独立偏移的非线性单元能够共存于同一个固定深度、单通道、共享偏置卷积块中。当前构造
仍假设输入状态已显式加载依赖网络参数的载体，其中包括第二行常数填充；如何从原始输入在
网络内部生成整个状态，以及如何组合任意有限多个这样的模块，仍是后续任务。

[`SharedBiasGeneralRidgeOptimality.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeOptimality.lean)
进一步证明：对一个有代表性的长程 ridge，上述线性深度并不是当前构造方法造成的偶然浪费。
令

$$
f_L(x)=\mathrm{ReLU}(x_0+x_{L+1}).
$$

任意深度不超过 $L$ 的扩张型 $2\times2$ 共享偏置网络，即使允许任意最终仿射读出，在四个
端点符号输入上的最大误差也至少为 $1/2$。因此误差严格小于 $1/2$ 必然要求深度至少为 $L+1$。
反过来，对每个 $L\ge1$，任意宽度 ridge 编译器都给出一个深度恰为 $L+1$ 的真实共享偏置
网络，其单坐标仿射读出在这四个输入上精确等于 $f_L$。所以对这族目标，上下深度界完全匹配；
空间扩张是否最优仍是另一个效率问题。

[`SharedBiasDepthLowerBound.lean`](OneChannelCNNUniversality/SharedBiasDepthLowerBound.lean)
给出了覆盖任意最终仿射读出的定量限制。深度为 $L$ 的扩张型 $2\times2$ 网络，其感受野
半径至多为 $L$。把符号 $\sigma,\tau\in\{-1,1\}$ 分别放在
$1\times(L+2)$ 输入的第 $0$ 列和第 $L+1$ 列，并用 $R_{\sigma,\tau}$ 表示最终特征图的
任意仿射读出。Lean 证明了精确的混合差恒等式

$$
R_{-1,-1}+R_{1,1}=R_{-1,1}+R_{1,-1}.
$$

连续的端点乘积目标在这个有限紧集上的取值为 $1,-1,-1,1$，所以任何深度不超过 $L$
的网络，其一致误差都至少为 $1$；若误差严格小于 $1$，网络深度就必须至少为 $L+1$。
这是长程非线性交互的深度下界，而不是对无界深度网络的非万能定理。证明只使用有限感受野
和最终读出的线性性，并不依赖偏置共享，因此不能把该下界错误归因于共享标量偏置这一限制。

[`SpatialInteractionDepthLowerBound.lean`](OneChannelCNNUniversality/SpatialInteractionDepthLowerBound.lean)
把这一限制推广到任意固定核形状和真正的二维间隔。对于整个逐坐标单位立方体上的目标

$$
F(x)=x_{0,0}x_{A,B},
$$

即使允许隐藏层使用任意逐位置偏置图像，网络也不可能以小于 $1$ 的一致误差逼近它，
除非同时满足

$$
A\le d(k_{\mathrm{rows}}-1),\qquad
B\le d(k_{\mathrm{cols}}-1).
$$

因此共享偏置子类当然也满足同一必要条件。这是锐利的固定深度局部性下界；允许深度
增长时，它并不是非万能性结论。

这个结论解决了本形式化工程中的任意宽度单 ridge 子问题，但它**不是**共享偏置万能逼近
定理。这里的宽度 $m=d+1$ 是输入行的空间长度，而不是通道数：网络始终只有一个特征通道，
采用固定的 $2\times2$ 卷积核形状，并且每层只有一个在所有空间位置共享的标量偏置。为满足
这些限制，构造使用深度 $d$，并把空间工作区扩张到 $(d+1)\times(2d+1)$。因此，它对于把
有限特征向量编码为一行后的精确表达能力和网络编译具有明确意义；但它不是关于训练效率、
固定分辨率图像架构或任意二维输入状态的结论。仓库中已有的完整万能逼近定理仍使用任意
逐位置偏置图像，而共享标量偏置子类是否万能仍然是开放问题。

当前决定性的缺口已经变成**任意有限组合**，而不是构造单个 ridge，也不是现在已经验证的
宽度二 ridge 对。新的 $L$ 状态说明无需规范化整个
$m\times(2m-1)$ 矩形：输入长度的北侧前缀再加 ridge 已经足够。但这个 $L$ 状态仍嵌在真实
矩形中，而任意宽度 ridge 定理的输入仍是单行状态；链外坐标可能继续依赖输入，坐标限制也不是
`SharedBiasNetworkTo.append` 能执行的一层网络，并且已经验证的第二行污染恒等式阻止把当前
因子链当作黑盒复用。后续编译器必须直接处理这个嵌入状态，用更丰富的载波替代平坦终端地址，让多个
彼此独立选取的 ridge 特征穿过后续共享偏置 ReLU 后仍可保留，再实现稠密性论证所需的有限格
组合。在这个有限多 ridge 编译器被证明以前，当前结果不能被称为共享偏置万能逼近定理。

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
| [`SharedBiasChainLayout.lean`](OneChannelCNNUniversality/SharedBiasChainLayout.lean) | 东南单调扫描的不可能性与长度上界，以及无损的行主序链式表示 |
| [`SharedBiasChainSelection.lean`](OneChannelCNNUniversality/SharedBiasChainSelection.lean) | 前缀／支撑等价，以及由紧致性生成且带相对恢复保证的真实行链选择块 |
| [`SharedBiasSeedTransport.lean`](OneChannelCNNUniversality/SharedBiasSeedTransport.lean) | 真实扩张恒等种子层、公共载体下的支撑不变性、连续性／非负性接口及精确带种子组合 |
| [`SharedBiasSuccessorSelection.lean`](OneChannelCNNUniversality/SharedBiasSuccessorSelection.lean) | 紧致构造后继受保护选择块，以及真实的两阶段共享偏置选择证书 |
| [`SharedBiasTwoStageRecovery.lean`](OneChannelCNNUniversality/SharedBiasTwoStageRecovery.lean) | delta 桥接的单射性／支撑保持，以及完整两阶段组合网络的相对单射性 |
| [`SharedBiasFiniteRecovery.lean`](OneChannelCNNUniversality/SharedBiasFiniteRecovery.lean) | 异构有限恢复链、反向归纳、拼接组合律，以及具体选择器／桥接适配器 |
| [`SharedBiasFiniteSelection.lean`](OneChannelCNNUniversality/SharedBiasFiniteSelection.lean) | 依赖类型有限后继日程、紧致性见证的递归构造、内部种子精确等式，以及最终单一组合 CNN 的导出 |
| [`SharedBiasScheduledRecovery.lean`](OneChannelCNNUniversality/SharedBiasScheduledRecovery.lean) | 已编译选择块的恢复适配器、等长日程恢复链、最终输出恢复，以及最终 CNN 的条件单射性 |
| [`SharedBiasProtectionObstruction.lean`](OneChannelCNNUniversality/SharedBiasProtectionObstruction.lean) | 全局成对保护导致目标常值、选择 ReLU 恒定的障碍定理，以及对追加选择器步骤的专门结论 |
| [`SharedBiasRedundantRecovery.lean`](OneChannelCNNUniversality/SharedBiasRedundantRecovery.lean) | 两个边界坐标上的精确 Pascal 公式，以及真实选择块在相邻根副本子空间上的单射性 |
| [`SharedBiasAdjacentCopy.lean`](OneChannelCNNUniversality/SharedBiasAdjacentCopy.lean) | 真实且单射的零偏置相邻根复制层、种子桥保持，以及端到端单射的复制—种子—选择 CNN |
| [`SharedBiasMonotoneCode.lean`](OneChannelCNNUniversality/SharedBiasMonotoneCode.lean) | 可重复使用的单调／严格单调双坐标编码、选择块中的保持与恢复，以及真实追加网络的单射性 |
| [`SharedBiasMonotoneSchedule.lean`](OneChannelCNNUniversality/SharedBiasMonotoneSchedule.lean) | 任意有限西北目标日程的归纳证明，以及由真实相邻复制层初始化的端到端单射编译 CNN |
| [`SharedBiasFrontier.lean`](OneChannelCNNUniversality/SharedBiasFrontier.lean) | 输入根纤维上的西北输出不可实现性，以及移动东侧前沿处真实、单射的双寄存器加法层 |
| [`SharedBiasFrontierChain.lean`](OneChannelCNNUniversality/SharedBiasFrontierChain.lean) | 非负状态上任意深度、无损的横向前沿移动，以及精确工作／备份／空尾公式 |
| [`SharedBiasFrontierTurn.lean`](OneChannelCNNUniversality/SharedBiasFrontierTurn.lean) | 无损的先东后南前沿转向、前沿下方活跃列精确为空、单射性及深度恒等式 $L=r+c$ |
| [`SharedBiasFrontierRoute.lean`](OneChannelCNNUniversality/SharedBiasFrontierRoute.lean) | 任意有限东／南路径、水平—纵向交换律、标准 Pascal 网格正规化、精确深度、终端前沿公式与单射性 |
| [`SharedBiasFrontierAffineRoute.lean`](OneChannelCNNUniversality/SharedBiasFrontierAffineRoute.lean) | 方向相关非负共享偏置、精确仿射路径求值、单射性，以及顺序敏感差值 $(ES)_{1,1}-(SE)_{1,1}=\alpha-\beta$ |
| [`SharedBiasSignedGate.lean`](OneChannelCNNUniversality/SharedBiasSignedGate.lean) | 二层输入相关带符号仿射 ReLU 门、冗余精确输入恢复、有界族上的单射性，以及紧集上的统一参数选择 |
| [`SharedBiasRowGate.lean`](OneChannelCNNUniversality/SharedBiasRowGate.lean) | 任意有限行上的二层逐点带符号 ReLU 门、逐坐标精确解码、单射性，以及紧集上的统一参数选择 |
| [`SharedBiasGridGate.lean`](OneChannelCNNUniversality/SharedBiasGridGate.lean) | 任意高度图像上的二层北侧行带符号 ReLU 门、精确的南向三角全图解码、单射性，以及紧集上的统一参数选择 |
| [`SharedBiasGridGateComposition.lean`](OneChannelCNNUniversality/SharedBiasGridGateComposition.lean) | 两个受保护网格门组成的真实四层网络、精确嵌套 ReLU 公式、逐阶段紧致界与单射性 |
| [`SharedBiasGridGateSchedule.lean`](OneChannelCNNUniversality/SharedBiasGridGateSchedule.lean) | 将任意有限带符号仿射 ReLU 日程编译成精确深度共享偏置 CNN，并验证北侧行逐点语义与完整状态单射性 |
| [`SharedBiasAffineMixGate.lean`](OneChannelCNNUniversality/SharedBiasAffineMixGate.lean) | 相邻北侧寄存器的任意带符号混合、加权水平变换的单射性、三层受保护 ReLU 门，以及紧集参数选择 |
| [`SharedBiasLocalGateSchedule.lean`](OneChannelCNNUniversality/SharedBiasLocalGateSchedule.lean) | 任意有限带符号局部门日程的精确编译、前缀依赖、深度 $3L$、逐阶段紧致载波与完整状态单射性 |
| [`SharedBiasAdjacentRidge.lean`](OneChannelCNNUniversality/SharedBiasAdjacentRidge.lean) | 两层任意相邻仿射 ridge、精确东南移位三角备份、从南到北恢复、紧集载波选择与完整状态单射性 |
| [`SharedBiasAdjacentLattice.lean`](OneChannelCNNUniversality/SharedBiasAdjacentLattice.lean) | 相邻 ridge 备份的线性左逆、仿射读出的精确坐标恢复，以及同一个两层网络的终端相邻最小值／最大值读出 |
| [`SharedBiasThreePointRidge.lean`](OneChannelCNNUniversality/SharedBiasThreePointRidge.lean) | 对 $1\times3$ 全部三坐标的两层任意仿射 ReLU、显式三角仿射恢复、紧集参数选择与完整状态单射性 |
| [`SharedBiasFourPointRidge.lean`](OneChannelCNNUniversality/SharedBiasFourPointRidge.lean) | 对有界 $1\times4$ 全部四坐标的三层任意仿射 ReLU、北侧三角滤波器 $1+6z+11z^2+6z^3$、显式仿射恢复、紧集参数选择与完整状态单射性 |
| [`SharedBiasGeneralRidgePolynomial.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgePolynomial.lean) | 任意 $d$ 的 Lagrange 分解、反序目标系数，以及从双线性因子乘积的 $Y$ 系数精确提取 $R_w$ |
| [`SharedBiasGeneralRidgeConvolution.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeConvolution.lean) | 每个因子的真实 $2\times2$ 核、在 $(1,d)$ 实现 $\sum_jw_jx_j$ 的逐层变化完整卷积链、北侧节点乘积传输，以及以 `LinearBranchAlong` 为条件的零偏置 ReLU 网络桥 |
| [`SharedBiasGeneralRidgeCarrier.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeCarrier.lean) | 任意宽度下因子的显式分配、正载波尺度、精确分配和及最后因子的分离界 |
| [`SharedBiasGeneralRidgeSeparation.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeSeparation.lean) | 前缀／末两因子拆分，以及每个北侧载波响应相对南侧 ridge 目标至少为二的统一间隙 |
| [`SharedBiasHeterogeneousCarrier.lean`](OneChannelCNNUniversality/SharedBiasHeterogeneousCarrier.lean) | 逐层变化双线性核前缀的紧集共享偏置线性化，以及可调的终端载波增量 |
| [`SharedBiasTerminalSelection.lean`](OneChannelCNNUniversality/SharedBiasTerminalSelection.lean) | 选择单个非线性目标、同时把受保护坐标保持为纯信号加固定偏移的紧集终端编译器 |
| [`SharedBiasGeneralRidgeRecovery.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeRecovery.lean) | 完整北侧节点多项式编码的单射性，以及任意固定偏移下的保持 |
| [`SharedBiasGeneralRidgeNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeNetwork.lean) | 真实的深度 $d$ 任意宽度仿射 ReLU ridge 网络、目标精确求值、北侧受保护恢复，以及紧单射特征族上的单射性 |
| [`SharedBiasGeneralRidgeLState.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeLState.lean) | 输入长度北侧前缀的单射性，以及终止于精确 ridge 坐标的连续、单射、东南单调 $L$ 状态 |
| [`SharedBiasGeneralRidgeReadout.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeReadout.lean) | 从北侧编码进行线性恢复，并用同一个共享偏置网络对任意两个输入仿射函数实现精确终端最小值／最大值读出 |
| [`SharedBiasGeneralRidgeCompositionObstruction.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeCompositionObstruction.lean) | 当前 ridge 块无法朴素黑盒组合的精确旧行污染恒等式与平坦终端地址障碍 |
| [`SharedBiasGeneralRidgeIdealAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeIdealAddress.lean) | 节点乘积系数非负性、箱形乘积的唯一中心峰，以及取负后的单位间隙唯一最低点 |
| [`SharedBiasGeneralRidgeAddressPlateau.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeAddressPlateau.lean) | 次数受限多项式线性载波模型中的精确共同平台、深度不超过 $m$ 时不可避免的同址竞争点，以及深度 $m+1$ 时的平台坍缩 |
| [`SharedBiasGeneralRidgeLowWindow.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeLowWindow.lean) | 传输多项式常数项非零时，由截断形式幂级数逆元实现的精确有限低阶系数匹配 |
| [`SharedBiasGeneralRidgeStripeAlgebra.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeAlgebra.lean) | 保持目标纵向多项式、生成横向载波 $-T G_d$ 并使末因子四个 tap 都不大于 $-1$ 的带符号倒数扭转 |
| [`SharedBiasGeneralRidgeStripePrefix.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripePrefix.lean) | 所有 proper twisted prefix 的精确正节点乘积，以及其箱形乘积在完整支撑上的逐系数单位下界 |
| [`SharedBiasGeneralRidgeStripeCarrier.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeCarrier.lean) | 两行前缀载波的精确公式，以及逐层认证单位下界预激活的显式向上封闭尺度阈值 |
| [`SharedBiasGeneralRidgeStripeFinalAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeFinalAddress.lean) | 末卷积核局部地址的精确公式：北侧和端点的二单位间隙，以及已证明的第二行内部平台 |
| [`SharedBiasNorthTwoLinearization.lean`](OneChannelCNNUniversality/SharedBiasNorthTwoLinearization.lean) | 北侧两行因果性，以及在局部非负条件下真实零偏置 ReLU 网络与形式卷积链在北侧两行的一致性 |
| [`SharedBiasNorthTwoCarrier.lean`](OneChannelCNNUniversality/SharedBiasNorthTwoCarrier.lean) | 单位下界北两行载波的紧集统一支配，以及适用于有符号紧输入族的向上封闭精确 identity-seed 阈值 |
| [`SharedBiasSeededNorthTwoNetwork.lean`](OneChannelCNNUniversality/SharedBiasSeededNorthTwoNetwork.lean) | 同一个紧集 seed 阈值给出真实 seed 层精确性、proper prefix 北侧线性化及其与形式卷积链的一致性 |
| [`SharedBiasBiasedLast.lean`](OneChannelCNNUniversality/SharedBiasBiasedLast.lean) | 仅末层带偏置的真实异构网络，在北侧两行上等于形式卷积链加该常数 |
| [`SharedBiasGeneralRidgeStripeSeedAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeSeedAddress.lean) | 完整链 identity-seed 地址分解、中心唯一最低点的显式单调尺度阈值，以及北侧亏损下界 |
| [`SharedBiasGeneralRidgeStripeAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeAddress.lean) | 把横向 seed 唯一性与北侧／边界局部分离组合起来的互补二类间隙定理 |
| [`SharedBiasTwoCarrierSelection.lean`](OneChannelCNNUniversality/SharedBiasTwoCarrierSelection.lean) | 从两个互补载波间隙得到紧集精确 ReLU 选择，并允许一个地址方向存在有界亏损 |
| [`SharedBiasGeneralRidgeStripeProperNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeProperNetwork.lean) | 真实 seed 加 proper-factor 网络：一个紧集阈值同时保证前缀线性化及其与形式状态的北侧两行一致性 |
| [`SharedBiasGeneralRidgeStripeRealization.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeRealization.lean) | 带符号条带因子对 seed 地址、局部地址和任意线性 ridge 信号的精确实现 |
| [`SharedBiasGeneralRidgeStripeNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeNetwork.lean) | 已完成的深度 $n+3$ 真实单通道共享偏置 $2\times2$ 网络：在紧输入族上精确计算任意仿射 ReLU ridge |
| [`SharedBiasGeneralRidgeStripeRecovery.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeRecovery.lean) | 北侧条带编码的单射性与线性左逆、有限读出权重的精确仿射恢复，以及整个真实 ridge 状态的单射性 |
| [`SharedBiasGeneralRidgeStripeMinMax.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeMinMax.lean) | 任意两个输入仿射函数的精确终端最小值／最大值读出，并保持真实 ridge 完整状态的单射性 |
| [`SharedBiasGeneralRidgeStripeAffineCombination.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeAffineCombination.lean) | 任意标量 ridge 倍数加任意仿射跳连项的精确有限读出，并保持真实隐藏状态的单射性 |
| [`SharedBiasParallelRidgeAlgebra.lean`](OneChannelCNNUniversality/SharedBiasParallelRidgeAlgebra.lean) | 无碰撞系数打包，以及用一个深度 $rm$ 的双线性链在分离的第二行目标上计算 $r$ 个独立的宽度 $m$ 线性形式 |
| [`SharedBiasMultiTargetSelection.lean`](OneChannelCNNUniversality/SharedBiasMultiTargetSelection.lean) | 用共同基线载体在有限目标集上同时执行紧集 ReLU 选择，并给出真实最终层的精确分解定理 |
| [`SharedBiasGeneralRidgeStripeWidthCarrier.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthCarrier.lean) | 输入宽度与因子深度独立的条带前缀载体，以及使北侧两行对任意种子宽度统一保持线性的显式阈值 |
| [`SharedBiasGeneralRidgeStripeWidthProperNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthProperNetwork.lean) | 输入宽度任意、深度恰为 $n+2$ 的真实带符号条带 proper 网络，以及紧集上一致的种子阈值和北侧两行精确形式行为 |
| [`SharedBiasGeneralRidgeStripeWidthFinalAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthFinalAddress.lean) | 任意宽度最终因子地址：第二行内部具有共同基线，全部北行坐标和两个水平端点至少高出该基线 $2$ |
| [`SharedBiasGeneralRidgeStripeWidthSeedAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthSeedAddress.lean) | 任意宽度完整链种子地址的精确分解：可缩放结点 boxcar 载体加固定打包权重扰动 |
| [`SharedBiasParallelStripeObstruction.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeObstruction.lean) | 机器检查的最小双目标反例，以及排除正前缀条带模式受保护共同基线的通用首一正线性系数定理 |
| [`SharedBiasParallelStripeCandidate.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeCandidate.lean) | 实根符号变化载体：精确共同双目标基线与 $17/4$ 间隔，以及旧线性化方法所遇到的精确负前缀障碍 |
| [`SharedBiasCompensatedCarrier.lean`](OneChannelCNNUniversality/SharedBiasCompensatedCarrier.lean) | 具有预设逐层标量偏置补偿的异质因子链通用紧集真实网络定理，以及北侧两行精确“信号加载体”语义 |
| [`SharedBiasParallelStripeCompensation.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeCompensation.lean) | 符号变化双目标载体的逐层标量偏置精确补偿：proper 前缀统一正裕量，以及最终共同基线和 $17s$ 间隔 |
| [`SharedBiasParallelStripeFactorization.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeFactorization.lean) | 显式有理数竖直抽头：在补偿条带的两个目标位置实现任意两个宽度二线性形式，并给出精确逐系数与卷积恒等式 |
| [`SharedBiasParallelStripeCarrierCorrection.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeCarrierCorrection.lean) | 精确单点修正恢复双目标载体共同基线，并证明存在正打包尺度同时满足所有 proper 北侧两行单位下界与严格最终选择间隔 |
| [`SharedBiasParallelStripeProperNetwork.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeProperNetwork.lean) | 紧集上一致的真实三层共享偏置 ReLU 修正双目标 proper 链，并给出北侧两行精确“信号加载体”语义 |
| [`SharedBiasParallelStripeAffinePacking.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeAffinePacking.lean) | 用第二输入行的两个显式系数编码两个独立仿射偏移，并证明完整四因子卷积的精确双目标恒等式 |
| [`SharedBiasParallelStripeAffineNetwork.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeAffineNetwork.lean) | 真实紧集深度四共享偏置模块，在显式加载载体的输入状态上，同时精确计算两个具有独立偏移的宽度二 ReLU ridge |
| [`SharedBiasGeneralRidgeOptimality.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeOptimality.lean) | 端点仿射 ReLU ridge 的锐利 $1/2$ 四点误差障碍，以及达到匹配精确深度的共享偏置构造 |
| [`SharedBiasDepthLowerBound.lean`](OneChannelCNNUniversality/SharedBiasDepthLowerBound.lean) | 精确的深度感受野、任意仿射读出的四点混合差恒等式、锐利误差下界 $1$，以及端点交互所需的深度 $L+1$ |
| [`SpatialInteractionDepthLowerBound.lean`](OneChannelCNNUniversality/SpatialInteractionDepthLowerBound.lean) | 普通逐位置偏置网络的二维各向异性感受野上界、两点混合差障碍，以及乘积逼近所需的行／列深度跨度 |
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
定理、约束更强的共享偏置任意宽度单 ridge 定理、宽度二仿射输入的载体加载紧集深度四双 ridge
模块及其边界／载波引理，都可由给定定义与报告中的基础推出；但这并不会把尚未解决的
共享偏置万能性问题变成定理。机器验证本身也
不等同于外部同行评审，不构成历史
优先权判断。
