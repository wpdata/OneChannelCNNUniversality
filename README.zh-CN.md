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
确实能越过三寄存器情形；但它还不是任意 $n$、一般二维特征图、可迭代格编译器或共享偏置
万能逼近定理。任意宽度的代数分解及其纯卷积实现现已在下述模块中通过机器检查；仍未完成
的是共享载波与 ReLU 网络部分。

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
纯卷积链。目前尚未证明：构造统一共享载波以保证该假设；在最终 ReLU 中保护北侧边界；
为真实 ReLU 网络证明北侧编码恢复；或得到共享偏置万能逼近定理。

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

这些是实验性的形式化证明基础，**不是**共享偏置万能逼近定理。仓库中原有的完整万能
逼近定理仍然允许任意逐位置偏置数组；本工程目前尚未判定共享标量偏置子类究竟万能还是
不万能。已经验证的三寄存器和四寄存器构造说明，共享卷积核和单一通道并不会排除这些
非局部带符号仿射 ReLU：闲置的空间方向可以充当临时代数存储。相邻格定理则给出精确的
终端最小值／最大值读出，而二维各向异性下界确定了长程交互不可避免的深度代价。

当前决定性的缺口，是把任意宽度卷积分解提升为非线性网络定理：给定一个可恢复的有限
特征图 $F$ 和任意仿射泛函 $\ell$，需要构造共享载波，使每个中间因子都处于所需线性支，
并让北侧三角编码穿过最终 ReLU 后仍受保护、可恢复，同时把
$\mathrm{ReLU}(\ell(F))$ 暴露为新的内部可恢复特征。这样的定理才能支持反复编译格表达式。
新的任意 $d$ 分解已经解决其代数与纯卷积核心，但真实共享偏置网络的载波／恢复归纳仍未完成。

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
定理和约束更强的共享偏置边界／载波引理都可由给定定义与报告中的基础推出；但这并不会把尚未
解决的共享偏置万能性问题变成定理。机器验证本身也不等同于外部同行评审，不构成历史
优先权判断。
