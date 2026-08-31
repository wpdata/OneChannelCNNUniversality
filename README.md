# Machine-Checked Universal Approximation by Two-Dimensional One-Channel Expansive ReLU CNNs

[中文说明](README.zh-CN.md)

This repository contains a Lean 4 formalization of universal approximation by
finite-depth, two-dimensional, one-channel expansive ReLU convolutional neural
networks with an affine readout.

## Main result

For positive input dimensions $d_1,d_2$, a fixed convolution shape
$k_{\mathrm{rows}}\times k_{\mathrm{cols}}$ with both sides at least two, a
compact set $K$ of real-valued input images, a continuous target
$f\colon K\to\mathbb{R}$, and any $\varepsilon>0$, the formalization constructs
a finite-depth network whose uniform approximation error on $K$ is less than
$\varepsilon$.

The exact model has:

- finite two-dimensional real inputs of size $d_1\times d_2$;
- a fixed expansive convolution shape in every hidden layer;
- one feature channel in every hidden layer;
- zero-extended full convolution, arbitrary spatial bias, and entrywise ReLU;
- an arbitrary affine readout from the final feature image.

The exported theorem is
[`OneChannelCNNUniversality.twoDimensional_oneChannel_universal_approximation`](OneChannelCNNUniversality/Main.lean):

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

## Shared-scalar-bias extension: current status

The repository also contains verified infrastructure for the stricter and
more implementation-standard hidden-layer rule

$$
H_\ell(X)=\mathrm{ReLU}\!\left(W_\ell*H_{\ell-1}(X)+b_\ell\mathbf 1\right),
$$

where each layer has only one scalar bias $b_\ell$, broadcast to every spatial
site.  [`SharedBias.lean`](OneChannelCNNUniversality/SharedBias.lean) defines
this exact network class and proves that its semantics embeds without change
into the general position-dependent-bias model.

[`SharedBiasGeometry.lean`](OneChannelCNNUniversality/SharedBiasGeometry.lean)
machine-checks exact boundary effects of zero-extended full convolution.  A
zero kernel and positive shared bias create a constant rectangle; horizontal
first differencing followed by ReLU isolates its positive left edge; vertical
first differencing then isolates its northwest corner.  These theorems cover
all finite dimensions, including empty rectangles.

[`SharedBiasCarrier.lean`](OneChannelCNNUniversality/SharedBiasCarrier.lean)
proves a first non-destructive coexistence result.  On a compact input set,
one broadcast scalar can place every site of a finite layer in ReLU's linear
region simultaneously.  If the incoming state is a variable signal plus a
fixed image, the next state is exactly the convolved variable signal plus a
fixed spatial carrier.  For the horizontal boundary kernel, the variable
transform is injective, while a constant input carrier becomes `b + c` on the
left boundary and `b` at original interior sites.

[`SharedBiasSelection.lean`](OneChannelCNNUniversality/SharedBiasSelection.lean)
turns a certified carrier gap into one exact selected ReLU.  If the target
carrier is lower than every other carrier by more than the signal variation,
the one shared bias `theta - carrier(target)` applies the requested ReLU at
the target and keeps every other protected site in the linear branch; no
condition is imposed on expansion-fringe sites that do not store registers.
Compactness machine-checkably supplies one uniform scale for any continuous
finite signal family once a unit-gap spatial address is available.

[`SharedBiasAddress.lean`](OneChannelCNNUniversality/SharedBiasAddress.lean)
constructs such an address at the northwest protected register using two
genuine shared-bias ReLU layers with positive two-tap kernels.  On the original
rectangle the carrier values are computed exactly, the northwest site is the
unique minimum with a quantitative gap, and the input-dependent two-layer
transform is injective.  The end-to-end theorem
`exists_northwest_protected_selection_layers` chooses all required amplitudes
uniformly on a compact input family and verifies a third shared-bias layer that
applies the selected ReLU at the northwest register while every other
protected register remains in the linear branch.

[`SharedBiasScan.lean`](OneChannelCNNUniversality/SharedBiasScan.lean)
extends the address mechanism along an arbitrary row.  Repeating the positive
two-tap full convolution produces the exact carrier

$$
C(i,j)=cP_m(j),\qquad
P_m(q)=\sum_{r=0}^{q}\binom{m}{r}.
$$

Before the binomial support is exhausted, successive addresses have a gap of
at least $c$.  The corresponding repeated signal transform is injective, and
compactness supplies one carrier scale that selects any requested column while
keeping the unprocessed suffix of that row in ReLU's linear branch, with its
signal retained up to a known fixed offset.

[`SharedBiasGridScan.lean`](OneChannelCNNUniversality/SharedBiasGridScan.lean)
performs the same positive accumulation in both coordinates.  It proves the
exact separable address formula

$$
C(i,j)=cP_{m_{\mathrm{row}}}(i)P_{m_{\mathrm{col}}}(j),
$$

and proves that the complete horizontal-then-vertical signal transform is
injective.  Consequently, any chosen original register is the unique minimum,
with gap at least $c$, in its southeast protected quadrant.  On a compact
continuous signal family, one shared scalar bias then performs the requested
ReLU at that register and leaves every other register in that quadrant in the
linear branch.

[`SharedBiasGridNetwork.lean`](OneChannelCNNUniversality/SharedBiasGridNetwork.lean)
connects these formulas back to genuine shared-scalar-bias network objects.
It introduces an explicitly output-typed `SharedBiasNetworkTo`, proves that
any finite repetition of a fixed formal convolution can be linearized on a compact
signal family using one scalar bias per layer, and constructs the complete
horizontal-then-vertical Pascal transform as a fixed-`2 × 2`-shape network.
For nonnegative inputs it gives a fully explicit version whose every Pascal
layer has bias zero.  It also realizes the final protected selection identity
with an actual expansive `2 × 2` shared-bias convolution/ReLU layer rather
than a proof-level pointwise activation.

The theorem `exists_pascal_grid_protected_selection_layers` now closes the
single-update path end to end.  For any compact continuous input family and
any target register, it chooses a positive seed $c$ and a positive first-layer
shared bias $b$.  The layer sequence starts from the seeded state
$V(x)+c\mathbf 1$.  The carrier produced by the genuine first layer and all
subsequent zero-bias Pascal layers is computed exactly on the original
rectangle as

$$
C(i,j)=cP_{m_{\mathrm{row}}}(i)P_{m+1}(j)
      +bP_{m_{\mathrm{row}}}(i)P_m(j).
$$

The second summand is southeast-monotone, so it cannot reduce the gap of at
least $c$ supplied by the first summand.  Lean then verifies both the exact
signal-plus-carrier middle state and the behavior of the genuine final
expansive shared-bias ReLU layer on the target's protected southeast quadrant.
The stronger theorem `exists_bundled_pascal_grid_protected_selection` returns
the complete sequence as one `SharedBiasNetworkTo` object, proves its depth is

$$
m_{\mathrm{row}}+m_{\mathrm{col}}+2,
$$

and states the protected evaluation law directly in terms of that network's
`eval`.  The generic composition operation in `SharedBiasNetworkTo.append`
proves that sequential composition preserves evaluation and adds depths.

[`SharedBiasCausality.lean`](OneChannelCNNUniversality/SharedBiasCausality.lean)
establishes the noninterference invariant needed for composing local updates.
With the convolution convention used here, the value at $(p,q)$ reads only
sites weakly northwest of $(p,q)$. Lean proves that agreement on the rectangle

$$
\{(i,j):i\le p,\ j\le q\}
$$

is preserved by an arbitrary full-convolution layer, by a genuine shared-bias
convolution/ReLU layer, and by every finite `SharedBiasNetwork` or explicitly
typed `SharedBiasNetworkTo`. It also specializes the result to the protected
Pascal signal. Hence, in a southeast-to-northwest scan, information already
stored outside the current northwest rectangle cannot flow backward and alter
the current activation. This is a verified causal foundation for a
multi-update compiler, not yet the compiler itself: recovery of earlier
nonlinear features through subsequent biased selection blocks and the finite
scan assembly remain to be proved.

[`SharedBiasRecovery.lean`](OneChannelCNNUniversality/SharedBiasRecovery.lean)
then proves exact recovery through the zero-bias Pascal transport. It packages
the horizontal-then-vertical transform as an injective linear map $P$ and
constructs a linear left inverse $R$ satisfying

$$
R(P(x))=x.
$$

Lean also converts each recovered coordinate into an ordinary finite weight
image, so for every original site $(i,j)$ there is a weight array $W_{i,j}$
with

$$
\sum_{p,q} W_{i,j}(p,q)P(x)(p,q)=x(i,j).
$$

For nonnegative inputs the same equation is proved directly for the concrete
`zeroBiasPascalGridNetwork`, whose ReLUs remain in their linear branch. Thus a
feature created by an earlier ReLU is not lost merely because later zero-bias
Pascal transport expands and mixes the feature image; it remains available to
the final affine readout. This does not yet prove recoverability through an
arbitrary later biased selection block.

[`SharedBiasSupport.lean`](OneChannelCNNUniversality/SharedBiasSupport.lean)
formalizes the complementary spatial invariant. Write

$$
Q_{r,s}=\{(i,j):r\le i,\ s\le j\}.
$$

If two feature images differ only inside $Q_{r,s}$, Lean proves that their
outputs still differ only inside $Q_{r,s}$ after one full convolution, one
genuine shared-bias convolution/ReLU layer, or an arbitrary finite
`SharedBiasNetworkTo`. If the inputs also agree at the root $(r,s)$, this
punctured-southeast condition $Q_{r,s}\setminus\{(r,s)\}$ is preserved and the
root output remains equal. Consequently, information already stored in that
punctured quadrant cannot leak toward the northwest or perturb the next target,
even through later nonlinear shared-bias layers. It protects only comparable
sites in a southeast quadrant; a scan covering an entire rectangular grid
still needs a layout or ordering that handles incomparable coordinates.

[`SharedBiasRelativeInjectivity.lean`](OneChannelCNNUniversality/SharedBiasRelativeInjectivity.lean)
closes the recovery gap for one complete biased selection block. Lean first
proves that horizontal and vertical Pascal accumulation can be inverted from
agreement on the same finite northwest rectangle. Hence the restriction of
the transported signal to the original image rectangle is already injective;
no expansion-fringe observation is needed. It then combines this inverse with
southeast support propagation and the exact bundled-network evaluation law.
The resulting theorem
`BundledPascalGridSelectionSpec.injective_on_rootPuncturedSoutheast` says that,
for two inputs differing only in
$Q_{r,s}\setminus\{(r,s)\}$, equality of the genuine shared-bias network
outputs implies equality of the input feature images. Thus the shared bias
and final ReLU do not destroy information under precisely the protected
variation invariant needed for one local update.

[`SharedBiasChainLayout.lean`](OneChannelCNNUniversality/SharedBiasChainLayout.lean)
formalizes the geometric cost of extending that invariant to a total scan.
No southeast-monotone chain can cover a rectangle with at least two rows and
two columns, because $(0,1)$ and $(1,0)$ are incomparable. More quantitatively,
every injective chain of $N$ sites in an $R\times C$ rectangle satisfies

$$
N\le R+C-1.
$$

Thus linear total spatial extent is intrinsic to the present chain-protection
strategy, rather than an artifact hidden by the proof. The file also gives an
exact row-major permutation into a $1\times(d_1d_2)$ image, proves a left
inverse, and hence proves that this chain representation loses no information.
This representation is area-efficient but has an extreme aspect ratio; more
importantly, its coordinate permutation is currently a mathematical layout,
not yet a shared-bias-CNN realization.

[`SharedBiasChainSelection.lean`](OneChannelCNNUniversality/SharedBiasChainSelection.lean)
connects the one-row layout back to genuine shared-bias networks. For a target
index $t$, it proves that agreement on the inclusive prefix

$$
\{0,\ldots,t\}
$$

is equivalent to the root-punctured southeast-support condition used by the
relative-injectivity theorem. It then specializes the complete bundled
selection block to this invariant: if two chain states agree through $t$ and
their network outputs agree, the entire input chains are equal. Finally,
`exists_bundled_rowChain_protected_selection` uses compactness to return the
positive seed, first shared bias, genuine typed network, exact depth and
selection contract together with this prefix-relative recovery guarantee.
This is a certified single scan step.

[`SharedBiasSeedTransport.lean`](OneChannelCNNUniversality/SharedBiasSeedTransport.lean)
and
[`SharedBiasSuccessorSelection.lean`](OneChannelCNNUniversality/SharedBiasSuccessorSelection.lean)
now provide the first verified multi-step interface. A genuine expansive
delta-identity layer maps every nonnegative intermediate image $z$ exactly to

$$
\mathrm{FullConv}(\delta,z)+c\mathbf 1,
$$

so it generates the fresh compactness seed required by the next selector
inside the CNN itself. Lean verifies common-carrier support invariance,
coordinatewise continuity, nonnegativity of every positive-depth network,
the exact composed evaluation law, and the exact depth increment. The theorem
`exists_two_bundled_pascal_selection_stages` then returns two compactly
generated protected selectors whose bridge and composition form one genuine
`SharedBiasNetworkTo`; no external operation is inserted between the blocks.

[`SharedBiasTwoStageRecovery.lean`](OneChannelCNNUniversality/SharedBiasTwoStageRecovery.lean)
closes the corresponding two-stage recovery loop. It proves that expansive
delta convolution is injective and preserves root-punctured southeast
support, then runs the two local recovery theorems backward through the
composed network. Consequently, if a pair of original inputs satisfies the
protected-variation hypotheses at both selected natural coordinates, equality
of the final two-stage outputs implies equality of the original feature
images. The simultaneous two-root hypothesis is explicit; arranging a finite
scan so that it holds at every step remains part of the open compiler problem.

[`SharedBiasFiniteRecovery.lean`](OneChannelCNNUniversality/SharedBiasFiniteRecovery.lean)
generalizes this backward argument from two stages to an arbitrary finite
heterogeneous chain. A `RelativeRecoveryStep` records one local protection
predicate and its equality-reflection theorem. A `RelativeRecoveryChain`
allows every intermediate feature type—and therefore every expanded image
size—to change. Lean proves recovery by backward induction, supplies chain
concatenation, proves additive length and identifies the concatenated
protection obligation with conjunction. Genuine Pascal selectors and
expansive delta bridges are registered as conditional and unconditional
steps, respectively; the existing two-selector construction is packaged as
a three-step chain. This settles the finite *recovery logic*, but does not by
itself construct the compactness-dependent parameters.

[`SharedBiasFiniteSelection.lean`](OneChannelCNNUniversality/SharedBiasFiniteSelection.lean)
adds that next compiler layer for every finite **successor-selection
schedule** following a positive-depth head network. The schedule is dependent:
each later target is typed against the dimensions produced by all earlier
blocks. Lean recursively applies the compact protected-selection theorem and
stores, at every stage, a positive seed, a positive selector bias, the full
selection specification, and the exact internal-seed evaluation equation.
The certificate exports one final `SharedBiasNetworkTo`, so an arbitrary
finite scheduled sequence is now an actual CNN rather than a metalevel list
of separately asserted blocks.

[`SharedBiasScheduledRecovery.lean`](OneChannelCNNUniversality/SharedBiasScheduledRecovery.lean)
connects that compiler certificate to the finite recovery logic. Each
compiled selector is converted into one recovery step from the preceding
network output to the genuinely composed output. Its local obligation is

$$
\mathrm{AgreeOutsideStrictSoutheast}
  \bigl(S_s(x),S_s(y);r_s,c_s\bigr),
$$

where $S_s$ is the successor feature at stage $s$. Lean forms their
conjunction through a recovery chain whose length is exactly the schedule
length. Equality of final-network outputs then recovers equality of the head
features; if the head feature map is injective on $K$ and every pair in $K$
satisfies the chain obligation, the final single CNN is injective on $K$.

[`SharedBiasProtectionObstruction.lean`](OneChannelCNNUniversality/SharedBiasProtectionObstruction.lean)
shows that this last pairwise premise cannot justify a nontrivial selected
activation at the same target. For a fixed root $(r,c)$, Lean proves

$$
\left(\forall x,y\in K,\;
  \mathrm{AgreeOutsideStrictSoutheast}(V(x),V(y);r,c)\right)
\Longrightarrow
\left(\forall x,y\in K,\;V(x)_{r,c}=V(y)_{r,c}\right).
$$

Consequently $\mathrm{ReLU}(V(x)_{r,c}+\theta)$ is constant on $K$
for every threshold $\theta$. The result is also specialized to the actual
appended-selector recovery step: two inputs with different selected successor
features formally refute its global pairwise-protection premise. Thus the
scheduled-recovery theorem is a valid state-preservation result, but its
strongest global corollary is not by itself a computational universality
argument. A useful compiler must separate protected state from the mutable
register on which a nonconstant ReLU is performed, or use a different
recovery invariant.

[`SharedBiasRedundantRecovery.lean`](OneChannelCNNUniversality/SharedBiasRedundantRecovery.lean)
implements and verifies the first such alternative without duplicating the
whole network. On any nonempty feature rectangle, it stores the mutable root
value $x_0$ once more in the adjacent eastern register, so $x_1=x_0$. If the
selector's horizontal Pascal transport has `extraColSteps` additional layers,
Lean proves the exact protected boundary formulas

$$
S_0(x)=x_0,
\qquad
S_1(x)=x_1+(\texttt{extraColSteps}+1)x_0.
$$

Hence on the redundant subspace,
$S_1(x)=(\texttt{extraColSteps}+2)x_0$, and the strictly positive coefficient
recovers the root even though the selected ReLU overwrites $S_0(x)$. The
theorem
`BundledPascalGridSelectionSpec.injective_on_eastRootDuplicate` verifies that
the complete genuine shared-scalar-bias selection network is injective on
this subspace. In particular, the selected value may vary across the input
family; the previous target-constancy obstruction no longer applies. This
costs one adjacent spatial register, not a second channel or a full-width
network copy.

[`SharedBiasAdjacentCopy.lean`](OneChannelCNNUniversality/SharedBiasAdjacentCopy.lean)
now constructs that redundancy with actual CNN layers. The input layout
reserves the eastern work site as zero, $x_{0,1}=0$, and the nonnegative state
is passed through one genuine zero-bias horizontal accumulation layer. Lean
verifies

$$
D(x)_{0,0}=x_{0,0},
\qquad
D(x)_{0,1}=x_{0,1}+x_{0,0}=x_{0,0}.
$$

The same layer is globally injective on nonnegative images, so creating the
copy does not discard the remaining state. The duplicate also survives the
genuine expansive delta seed bridge. Finally,
`exists_injective_adjacentCopy_selection` composes the copy layer, a positive
internal seed bridge, and a compactly generated Pascal selector into one
shared-scalar-bias CNN. For every compact family of continuous, nonnegative,
injectively encoded states satisfying the vacant-neighbor layout, the
returned complete CNN is injective on that family and its bundled
specification performs the selected northwest ReLU. Thus a nonconstant
selected computation and information preservation now coexist in an actual
one-channel network, rather than only under an assumed duplicate invariant.

[`SharedBiasMonotoneCode.lean`](OneChannelCNNUniversality/SharedBiasMonotoneCode.lean)
removes the need to recreate an exact duplicate after every selection.  The
copy layer is used only once, to initialize two northwest coordinates as

$$
x_{0,0}=f(t),\qquad x_{0,1}=g(t),
$$

with $f$ monotone and $g$ strictly monotone in a common latent code $t$.
After a selected block, Lean verifies that the two new factors have the form

$$
f_{\mathrm{new}}(t)=\mathrm{ReLU}(f(t)+\theta),
\qquad
g_{\mathrm{new}}(t)=g(t)+(m+1)f(t)+C,
$$

where $m\geq 0$ is the number of extra horizontal transport steps and $C$ is
independent of $t$.  Therefore $f_{\mathrm{new}}$ remains monotone and
$g_{\mathrm{new}}$ remains strictly monotone.  The eastern coordinate still
recovers $t$, so equality of selector outputs recovers the complete selector
input.  The invariant is proved both for the abstract bundled selector and
for the actual `appendWithSeed` network evaluation; if the preceding network
is injective on $K$, the genuinely composed network remains injective on
$K$.

[`SharedBiasMonotoneSchedule.lean`](OneChannelCNNUniversality/SharedBiasMonotoneSchedule.lean)
closes this invariant under dependent finite recursion.  The predicate
`SuccessorSelectionSchedule.NorthwestTargeted` records that every request in
an otherwise general spatial schedule selects the northwest work register.
For any compiled schedule satisfying that predicate, induction through the
actual internal-seed compositions proves simultaneously that

$$
\mathrm{NorthwestMonotoneCodeOn}(K,N_s,t)
\quad\text{and}\quad
\mathrm{InjOn}(N_s,K)
$$

hold at every stage $s$.  The end-to-end theorem
`exists_injective_compiledNorthwestSchedule` starts with the genuine adjacent
copy layer, uses compactness to compile an arbitrary finite northwest
schedule, and returns one final shared-scalar-bias CNN together with both
certificates.  Its work-coordinate recurrence is exactly

$$
f_{s+1}(t)=\mathrm{ReLU}(f_s(t)+\theta_s).
$$

[`SharedBiasFrontier.lean`](OneChannelCNNUniversality/SharedBiasFrontier.lean)
identifies a structural limit of keeping that work site fixed. Northwest
causality implies that inputs with the same value at $(0,0)$ have the same
northwest output after every finite expansive shared-bias CNN, independently
of depth and kernel size. Consequently, a scalar target that varies inside
one such input-root fiber cannot be realized at the northwest output. The
module derives this non-realizability criterion from the existing causality
theorem rather than reproving causality. It also proves the quantitative
two-point bound

$$
|f(x)-f(y)|\leq |N(F(x))_{0,0}-f(x)|
  +|N(F(y))_{0,0}-f(y)|.
$$

Thus, when the two target values differ by $\Delta$, every such northwest
readout has error at least $\Delta/2$ at one of the two inputs. In particular,
this is an obstruction to uniform approximation, not only to exact
realization.

The positive alternative is a moving computation frontier. One genuine
$2\times2$ shared-bias layer is verified to compute at its eastern frontier

$$
y_{0,1}=\mathrm{ReLU}(x_{0,0}+x_{0,1}+\theta).
$$

At $\theta=0$ on nonnegative input families, the complete layer remains
injective and this coordinate equals $x_{0,0}+x_{0,1}$. Thus the construction
performs a genuine two-register arithmetic operation without discarding the
rest of the state. This is the first checked primitive for replacing the
impossible “route everything back northwest” strategy by computation sites
that advance east or south.

[`SharedBiasFrontierChain.lean`](OneChannelCNNUniversality/SharedBiasFrontierChain.lean)
closes this primitive under an arbitrary finite number of genuine zero-bias
horizontal layers. If the northwest row initially contains registers
$a,b$ followed by a vacant eastern tail, then after $s$ layers Lean verifies

$$
z_{0,s}=a+s b,\qquad z_{0,s+1}=b,\qquad
z_{0,q}=0\quad(q\geq s+2).
$$

The pair consisting of the updated work value and the unchanged backup thus
moves one column east per layer. On nonnegative input families the exact CNN
evaluation satisfies this invariant and remains injective, so the arithmetic
advance does not discard the rest of the image state. This is an arbitrary-
depth moving-frontier certificate, rather than a one-layer formula.

[`SharedBiasFrontierTurn.lean`](OneChannelCNNUniversality/SharedBiasFrontierTurn.lean)
then turns this horizontal frontier south. For a northwest two-register seed
whose eastern tail and lower rows are vacant, the genuine horizontal-then-
vertical network reaches any frontier coordinate $(r,c)$ and satisfies

$$
z_{r,c}=a+c b,\qquad z_{r,c+1}=b,\qquad
z_{p,c}=z_{p,c+1}=0\quad(p\geq r+1).
$$

The complete network is injective on nonnegative seed families, and its depth
is exactly the Manhattan distance

$$
L=r+c.
$$

Thus the active work/backup pair can make one verified two-dimensional turn
without losing its values or the information stored by the full feature map.

[`SharedBiasFrontierRoute.lean`](OneChannelCNNUniversality/SharedBiasFrontierRoute.lean)
compiles an arbitrary finite direction list
$\sigma\in\{E,S\}^{L}$ to one genuine zero-bias shared-ReLU layer per step.
If $e(\sigma)$ and $s(\sigma)$ count its eastern and southern steps, then
horizontal and vertical full convolution commute, and the formalization proves
pointwise equality after zero extension between the interleaved route and

$$
V^{s(\sigma)}H^{e(\sigma)}x.
$$

Consequently every repeated-turn route has exact depth

$$
L=|\sigma|=e(\sigma)+s(\sigma),
$$

remains injective on nonnegative input families, and on northwest
two-register seeds satisfies

$$
z_{s(\sigma),e(\sigma)}=a+e(\sigma)b,\qquad
z_{s(\sigma),e(\sigma)+1}=b.
$$

The order of the turns does not affect this terminal state because these two
particular Pascal operators commute. This is a verified arbitrary-route
transport theorem, but not yet a route-dependent arithmetic compiler.

[`SharedBiasFrontierAffineRoute.lean`](OneChannelCNNUniversality/SharedBiasFrontierAffineRoute.lean)
breaks that order invariance while staying inside genuine spatially shared
scalar biases. Assign a nonnegative bias $\alpha$ to every eastern step and a
nonnegative bias $\beta$ to every southern step. ReLU remains in its linear
branch on nonnegative inputs, so the resulting affine route is still exact
and injective, with one layer per direction. Nevertheless the shared bias
carriers interact differently with the next convolution. At coordinate
$(1,1)$ the formalization proves

$$
(ES)(x)_{1,1}=C(x)+2\alpha+\beta,
\qquad
(SE)(x)_{1,1}=C(x)+\alpha+2\beta,
$$

and therefore

$$
(ES)(x)_{1,1}-(SE)(x)_{1,1}=\alpha-\beta.
$$

Thus $\alpha\ne\beta$ gives two depth-two, one-channel shared-bias ReLU CNNs
whose outputs are provably different solely because the direction order was
swapped. This is the first verified noncommuting affine frontier primitive in
the repository.

[`SharedBiasSignedGate.lean`](OneChannelCNNUniversality/SharedBiasSignedGate.lean)
crosses the next nonlinear checkpoint.  For every bounded scalar input
$|x|\le M$ and arbitrary signed coefficients $a,c\in\mathbb R$, two genuine
$2\times2$ shared-bias layers first encode $x$ redundantly as $M+|c|+x$ and
$M+|c|-x$, then compute at one output coordinate

$$
\mathrm{ReLU}(a x+c).
$$

The same second layer preserves two southern coordinates with exact decoder

$$
x=\frac{z_{2,0}-z_{2,1}}{2}.
$$

Consequently the complete hidden representation remains injective on every
bounded injective scalar family.  A compactness theorem chooses one common
$M$ for any continuous scalar family on a compact set.  This is the first
verified input-dependent signed ReLU gate in the strict model; unlike the
preceding affine route gap, its nonlinear output genuinely depends on the
input.

[`SharedBiasRowGate.lean`](OneChannelCNNUniversality/SharedBiasRowGate.lean)
lifts this scalar construction to an arbitrary finite register row.  For
$x=(x_0,\ldots,x_{n-1})$ with $|x_j|\le M$, the same depth-two genuine
shared-bias CNN simultaneously satisfies, for every $j$,

$$
z_{0,j}=\mathrm{ReLU}(a x_j+c),
\qquad
z_{1,j}-(M+|c|+c)=x_j.
$$

Thus every gated coordinate has an exact surviving decoder, the complete
row representation remains injective on bounded injective families, and
compactness selects one uniform $M$ for a continuous row family on a compact
set.  This removes the former restriction to one isolated scalar register;
it does not yet prove that such recoverable rows can be composed into an
arbitrary finite computation.

[`SharedBiasGridGate.lean`](OneChannelCNNUniversality/SharedBiasGridGate.lean)
removes the one-row input restriction while keeping the active gate on the
northern boundary.  For an arbitrary $R\times C$ input with
$|x_{r,j}|\le M$, set

$$
B=(1+|a|)M+|c|.
$$

The same depth-two genuine shared-bias CNN satisfies

$$
z_{0,j}=\mathrm{ReLU}(a x_{0,j}+c),
\qquad
z_{r+1,j}=x_{r,j}+a x_{r+1,j}+B+c,
$$

where the zero boundary convention sets $x_{R,j}=0$.  The protected rows are
therefore decoded exactly from south to north by

$$
x_{r,j}=z_{r+1,j}-(B+c)-a x_{r+1,j}.
$$

Lean verifies that this triangular code is injective for every real $a$ and
that the complete network remains injective on uniformly bounded injective
image families.  Compactness again supplies one uniform $M$.  The verified
decoder is a mathematical inverse; it is not yet compiled into a causal
shared-bias CNN, and the nonlinear gate is still confined to the northern
input row.

[`SharedBiasGridGateComposition.lean`](OneChannelCNNUniversality/SharedBiasGridGateComposition.lean)
shows that the protected representation can be consumed directly by another
protected gate block.  Two depth-two blocks form one genuine depth-four CNN
with northern-row formula

$$
z_{0,j}=\mathrm{ReLU}\!\left(
  a_2\,\mathrm{ReLU}(a_1x_{0,j}+c_1)+c_2\right),
$$

and the complete four-layer representation remains injective.  Compactness
selects a separate uniform bound after the first nonlinear block, rather than
assuming one unverified global carrier margin.

[`SharedBiasGridGateSchedule.lean`](OneChannelCNNUniversality/SharedBiasGridGateSchedule.lean)
closes the corresponding finite induction.  For every finite list
$((a_1,c_1),\ldots,(a_L,c_L))$, there is a genuine expansive one-channel
shared-bias CNN of exact depth $2L$ whose northern row evaluates

$$
t_0=x_{0,j},
\qquad
t_{\ell+1}=\mathrm{ReLU}(a_{\ell+1}t_\ell+c_{\ell+1}),
\qquad
z_{0,j}=t_L,
$$

while its complete feature representation remains injective on the compact
input family.  This is the first verified arbitrary-depth nonlinear
composition theorem for the strict shared-bias model in this repository.
It is still a coordinatewise scalar schedule: the same gate is applied to
every northern-row coordinate, and it does not yet mix different registers
or expose deeper input rows.

[`SharedBiasAffineMixGate.lean`](OneChannelCNNUniversality/SharedBiasAffineMixGate.lean)
removes the first of those two restrictions for one adjacent pair in a row
containing at least two registers.  For every
signed weight $\lambda\in\mathbb R$, a compactly linearized shared-bias layer
forms

$$
y_{i,j}=x_{i,j}+\lambda x_{i,j-1}+b.
$$

This transform is injective for every real $\lambda$: the first column is
unchanged and each later column is recovered recursively from its western
predecessor.  Appending one protected grid gate gives a genuine depth-three
network whose target northern register satisfies

$$
z_{0,1}=\mathrm{ReLU}\!\left(
  a(x_{0,1}+\lambda x_{0,0})+c\right),
$$

while the complete representation remains injective.  Compactness chooses
both required uniform carriers for any continuous injective finite-image
family.  In particular, negative $\lambda$ is allowed, so this primitive
supports differences as well as sums; it is the first verified nonlinear
gate here that mixes two distinct input registers.  The stronger all-coordinate
theorem verifies the same formula simultaneously for every original northern
register, using a zero western boundary at $j=0$.

[`SharedBiasLocalGateSchedule.lean`](OneChannelCNNUniversality/SharedBiasLocalGateSchedule.lean)
closes the finite induction for these spatially shared local gates.  For a
schedule $((\lambda_1,a_1,c_1),\ldots,(\lambda_L,a_L,c_L))$, define

$$
t_{0,j}=x_{0,j},
\qquad
t_{\ell+1,j}=\mathrm{ReLU}\!\left(
  a_{\ell+1}
  \bigl(t_{\ell,j}+\lambda_{\ell+1}t_{\ell,j-1}\bigr)
  +c_{\ell+1}\right),
$$

with $t_{\ell,-1}=0$.  Lean now constructs one genuine shared-bias CNN of
exact depth $3L$ satisfying $z_{0,j}=t_{L,j}$ at every original northern
coordinate.  The complete feature image remains injective throughout.  A
prefix and receptive-field theorems prove that coordinate $j$ depends only on
initial coordinates $\max(0,j-L),\ldots,j$.

[`SharedBiasAdjacentRidge.lean`](OneChannelCNNUniversality/SharedBiasAdjacentRidge.lean)
removes the coefficient-factorization restriction of the preceding
depth-three mixing block on every uniformly bounded input family.  Given arbitrary
$\alpha,\beta,\gamma\in\mathbb R$, a genuine depth-two shared-bias network
computes, at every nonwestern northern register,

$$
\mathrm{ReLU}(\alpha x_{0,j-1}+\beta x_{0,j}+\gamma).
$$

At the same time, every input coordinate survives one step southeast in the
exact triangular backup code

$$
x_{i,j}+\alpha x_{i+1,j}+\beta x_{i+1,j+1}+C,
$$

with zero extension at the boundary.  Lean proves that this code is
injective by south-to-north recovery and that compactness supplies one
uniform carrier for every continuous injective input family.  Thus an
arbitrary adjacent affine ridge can be added without losing the complete
input state, although iterating independently chosen ridges still requires a
causal operand layout.

[`SharedBiasAdjacentLattice.lean`](OneChannelCNNUniversality/SharedBiasAdjacentLattice.lean)
strengthens that recovery statement at the affine-readout level.  The linear
part of the triangular backup has a chosen linear left inverse, so every
original input coordinate is exactly recoverable by a finite affine readout of
the same depth-two output.  For $(\alpha,\beta,\gamma)=(1,-1,0)$, two different
readouts of one fixed network give

$$
\min(a,b)=a-\mathrm{ReLU}(a-b),\qquad
\max(a,b)=b+\mathrm{ReLU}(a-b).
$$

The complete representation remains injective on compact injective input
families.  These are terminal affine readouts: the chosen left inverse is not
a causal convolutional layer, and the result does not yet compile nested
minimum/maximum expressions inside the hidden network.

[`SharedBiasThreePointRidge.lean`](OneChannelCNNUniversality/SharedBiasThreePointRidge.lean)
gives the first exact nonadjacent arbitrary-affine gate in this development.
For a bounded $1\times3$ input and arbitrary
$r_0,r_1,r_2,\gamma\in\mathbb R$, one genuine depth-two network computes

$$
\mathrm{ReLU}(r_0x_0+r_1x_1+r_2x_2+\gamma)
$$

at output coordinate $(1,2)$.  The construction uses the second spatial
direction as temporary storage.  Three northern output coordinates form an
explicit triangular affine code with positive diagonal scale, and an explicit
decoder recovers $(x_0,x_1,x_2)$ exactly; hence the complete output remains
injective.  This is an exact three-register extension theorem, not yet an
arbitrary-dimension affine-ReLU extension or an iterable universal compiler.

[`SharedBiasFourPointRidge.lean`](OneChannelCNNUniversality/SharedBiasFourPointRidge.lean)
verifies the next nonadjacent case.  For every bounded `Image 1 4` input and
arbitrary $r_0,r_1,r_2,r_3,\gamma\in\mathbb R$, a genuine depth-three
expansive $2\times2$ one-channel network with one shared scalar bias per layer
computes

$$
\mathrm{ReLU}(r_0x_0+r_1x_1+r_2x_2+r_3x_3+\gamma)
$$

exactly at output coordinate $(1,3)$.  Its four northern outputs have variable
part given by the triangular filter

$$
P(z)=(1+z)(1+2z)(1+3z)=1+6z+11z^2+6z^3.
$$

The carrier terms are known constants, so an explicit affine decoder recovers
all four input coordinates.  Consequently the complete network remains
injective on every compact injective feature family.  This second
nonadjacent base case validates the finite polynomial mechanism beyond three
registers, but it is not yet a theorem for arbitrary $n$, general
two-dimensional feature images, an iterable lattice compiler, or shared-bias
universal approximation.  A Lagrange-based algebraic prototype for arbitrary
$n$ is under study and is not claimed here as a proved repository result.

[`SharedBiasDepthLowerBound.lean`](OneChannelCNNUniversality/SharedBiasDepthLowerBound.lean)
gives a quantitative limitation that includes the arbitrary final affine
readout.  A depth-$L$ expansive $2\times2$ network has receptive radius at
most $L$.  Put signs $\sigma,\tau\in\{-1,1\}$ in columns $0$ and $L+1$ of a
$1\times(L+2)$ input and write $R_{\sigma,\tau}$ for any affine readout of
the final feature image.  Lean proves the exact mixed-difference identity

$$
R_{-1,-1}+R_{1,1}=R_{-1,1}+R_{1,-1}.
$$

The continuous endpoint-product target has values
$1,-1,-1,1$ on this finite compact set, so every network of depth at most
$L$ has uniform error at least $1$.  Consequently, strict error below $1$
forces depth at least $L+1$.  This is a long-range interaction depth lower
bound, not a non-universality theorem for unbounded depth.  Its proof uses
finite receptive fields and linearity of the final readout; it does not rely
on bias sharing and therefore must not be attributed specifically to the
shared-scalar-bias restriction.

[`SpatialInteractionDepthLowerBound.lean`](OneChannelCNNUniversality/SpatialInteractionDepthLowerBound.lean)
generalizes this limitation to arbitrary fixed kernel shape and genuine
two-dimensional separation.  For the target

$$
F(x)=x_{0,0}x_{A,B}
$$

on the full coordinatewise unit cube, even a network with arbitrary
position-dependent hidden bias images cannot achieve uniform error below
$1$ unless

$$
A\le d(k_{\mathrm{rows}}-1),\qquad
B\le d(k_{\mathrm{cols}}-1).
$$

The same conclusion therefore holds for the shared-bias subclass.  This is a
sharp fixed-depth locality bound; it is not a non-universality result when
depth is allowed to grow.

This is experimental proof infrastructure, **not** a shared-bias universal-
approximation theorem.  The repository's existing full universal-
approximation theorem still permits arbitrary position-dependent bias images,
and it remains open in this development whether the shared-scalar-bias
subclass is universal or non-universal.  The verified three- and four-register
constructions show that shared kernels and one feature channel do not prevent
these nonlocal signed affine ReLUs: the unused spatial direction can act as
temporary algebraic storage.  The adjacent lattice theorem also supplies exact
terminal minimum/maximum readouts, while the anisotropic lower bound identifies
the unavoidable depth cost of long-range interactions.

The decisive missing theorem is now an arbitrary-dimension extension step:
given a recoverable finite feature image $F$ and an arbitrary affine
functional $\ell$, append a genuine shared-bias block that keeps $F$
recoverable and exposes $\mathrm{ReLU}(\ell(F))$ as an internal recoverable
feature.  Such a theorem would make repeated lattice compilation possible;
the present $1\times3$ and $1\times4$ constructions prove two nonadjacent
finite base cases but do not justify the general induction.

## Proof architecture

| Files | Role |
| --- | --- |
| [`Basic.lean`](OneChannelCNNUniversality/Basic.lean) | Finite-array image, convolution, ReLU-layer, network, and affine-readout semantics |
| [`Carrier.lean`](OneChannelCNNUniversality/Carrier.lean), [`Register.lean`](OneChannelCNNUniversality/Register.lean) | Exact carrier and masked-register operations |
| [`Program.lean`](OneChannelCNNUniversality/Program.lean), [`RegisterProgram.lean`](OneChannelCNNUniversality/RegisterProgram.lean), [`HybridProgram.lean`](OneChannelCNNUniversality/HybridProgram.lean) | Compilation of register programs into genuine convolution/ReLU layers |
| [`Encoder.lean`](OneChannelCNNUniversality/Encoder.lean), [`SparseEncoder.lean`](OneChannelCNNUniversality/SparseEncoder.lean) | Injective sparse convolutional encoding and the binomial/Vandermonde invertibility argument |
| [`RouteGeometry.lean`](OneChannelCNNUniversality/RouteGeometry.lean), [`Routing.lean`](OneChannelCNNUniversality/Routing.lean), [`GridRouting.lean`](OneChannelCNNUniversality/GridRouting.lean) | Exact spatial routing of encoded coordinates |
| [`GridMachine.lean`](OneChannelCNNUniversality/GridMachine.lean), [`LatticeCompiler.lean`](OneChannelCNNUniversality/LatticeCompiler.lean) | Exact evaluation of finite affine lattice expressions using ReLU min/max identities |
| [`Ridge.lean`](OneChannelCNNUniversality/Ridge.lean), [`Universal.lean`](OneChannelCNNUniversality/Universal.lean) | Density via Mathlib's lattice Stone--Weierstrass theorem |
| [`Simulation.lean`](OneChannelCNNUniversality/Simulation.lean), [`Main.lean`](OneChannelCNNUniversality/Main.lean) | Assembly of exact compilation and density into the final network theorem |
| [`SharedBias.lean`](OneChannelCNNUniversality/SharedBias.lean) | Exact shared-scalar-bias semantics, semantics-preserving embedding, and typed sequential network composition |
| [`SharedBiasGeometry.lean`](OneChannelCNNUniversality/SharedBiasGeometry.lean) | Exact constant, left-boundary, and northwest-corner position signals generated with shared biases |
| [`SharedBiasCarrier.lean`](OneChannelCNNUniversality/SharedBiasCarrier.lean) | Compact shared-bias linearization, non-destructive signal/carrier coexistence, injective horizontal differencing, and an exact boundary carrier gap |
| [`SharedBiasSelection.lean`](OneChannelCNNUniversality/SharedBiasSelection.lean) | Exact selected ReLU from a carrier gap and compact uniform scaling from a unit spatial address |
| [`SharedBiasAddress.lean`](OneChannelCNNUniversality/SharedBiasAddress.lean) | Two injective shared-bias address layers, an exact northwest gap on protected registers, and an end-to-end northwest selection layer |
| [`SharedBiasScan.lean`](OneChannelCNNUniversality/SharedBiasScan.lean) | Repeated positive horizontal accumulation, exact Pascal-prefix addresses, injectivity, and protected row-suffix selection |
| [`SharedBiasGridScan.lean`](OneChannelCNNUniversality/SharedBiasGridScan.lean) | Injective two-dimensional Pascal addresses and arbitrary-target selection on a southeast protected quadrant |
| [`SharedBiasGridNetwork.lean`](OneChannelCNNUniversality/SharedBiasGridNetwork.lean) | Explicit genuine shared-bias layers, the exact first-bias Pascal carrier and gap, zero-bias accumulation, and a bundled end-to-end protected arbitrary-target network |
| [`SharedBiasCausality.lean`](OneChannelCNNUniversality/SharedBiasCausality.lean) | Northwest noninterference for full convolution, genuine shared-bias ReLU layers, arbitrary finite networks, and the protected Pascal signal |
| [`SharedBiasRecovery.lean`](OneChannelCNNUniversality/SharedBiasRecovery.lean) | Linear left inversion of Pascal transport and exact coordinate recovery by finite affine-readout weights, including the concrete zero-bias network on nonnegative features |
| [`SharedBiasSupport.lean`](OneChannelCNNUniversality/SharedBiasSupport.lean) | Southeast-support propagation and root-punctured-quadrant protection through genuine shared-bias ReLU layers and arbitrary finite networks |
| [`SharedBiasRelativeInjectivity.lean`](OneChannelCNNUniversality/SharedBiasRelativeInjectivity.lean) | Inversion from the protected original rectangle and relative injectivity of a complete bundled biased selection block |
| [`SharedBiasChainLayout.lean`](OneChannelCNNUniversality/SharedBiasChainLayout.lean) | Impossibility and length bounds for southeast-monotone scans, plus an injective row-major chain representation |
| [`SharedBiasChainSelection.lean`](OneChannelCNNUniversality/SharedBiasChainSelection.lean) | Prefix/support equivalence and a compactly generated genuine row-chain selection block with relative recovery |
| [`SharedBiasSeedTransport.lean`](OneChannelCNNUniversality/SharedBiasSeedTransport.lean) | Genuine expansive identity seed layer, support invariance under common carriers, continuity/nonnegativity interfaces, and exact seeded composition |
| [`SharedBiasSuccessorSelection.lean`](OneChannelCNNUniversality/SharedBiasSuccessorSelection.lean) | Compact construction of a protected successor block and a genuine two-stage shared-bias selection certificate |
| [`SharedBiasTwoStageRecovery.lean`](OneChannelCNNUniversality/SharedBiasTwoStageRecovery.lean) | Injectivity/support of the delta bridge and relative injectivity of the complete two-stage composed network |
| [`SharedBiasFiniteRecovery.lean`](OneChannelCNNUniversality/SharedBiasFiniteRecovery.lean) | Heterogeneous finite recovery chains, backward induction, concatenation laws, and concrete selector/bridge adapters |
| [`SharedBiasFiniteSelection.lean`](OneChannelCNNUniversality/SharedBiasFiniteSelection.lean) | Dependent finite successor schedules, recursive compactness witness construction, exact internal-seed equations, and extraction of one final composed CNN |
| [`SharedBiasScheduledRecovery.lean`](OneChannelCNNUniversality/SharedBiasScheduledRecovery.lean) | Recovery adapters for compiled selector blocks, schedule-length recovery chains, final-output recovery, and conditional injectivity of the final CNN |
| [`SharedBiasProtectionObstruction.lean`](OneChannelCNNUniversality/SharedBiasProtectionObstruction.lean) | The target-constancy obstruction for global pairwise protection, constancy of the selected ReLU, and its specialization to appended selector steps |
| [`SharedBiasRedundantRecovery.lean`](OneChannelCNNUniversality/SharedBiasRedundantRecovery.lean) | Exact two-coordinate Pascal boundary formulas and injectivity of a genuine selected block on the adjacent-root-duplicate subspace |
| [`SharedBiasAdjacentCopy.lean`](OneChannelCNNUniversality/SharedBiasAdjacentCopy.lean) | A genuine injective zero-bias layer that creates the adjacent root copy, preservation through the seed bridge, and an end-to-end injective copy--seed--select CNN |
| [`SharedBiasMonotoneCode.lean`](OneChannelCNNUniversality/SharedBiasMonotoneCode.lean) | A reusable monotone/strictly-monotone two-coordinate code, its preservation and recovery through a selected block, and injectivity of the actual appended network |
| [`SharedBiasMonotoneSchedule.lean`](OneChannelCNNUniversality/SharedBiasMonotoneSchedule.lean) | Induction through arbitrary finite northwest-targeted schedules and an end-to-end injective compiled CNN initialized by the genuine adjacent-copy layer |
| [`SharedBiasFrontier.lean`](OneChannelCNNUniversality/SharedBiasFrontier.lean) | Northwest-output non-realizability on input-root fibers and a genuine injective two-register addition layer at a moving eastern frontier |
| [`SharedBiasFrontierChain.lean`](OneChannelCNNUniversality/SharedBiasFrontierChain.lean) | Arbitrary-depth lossless horizontal frontier motion with exact work/backup/tail formulas on nonnegative states |
| [`SharedBiasFrontierTurn.lean`](OneChannelCNNUniversality/SharedBiasFrontierTurn.lean) | A lossless east-then-south frontier turn, exact active-column vacancy below the frontier, injectivity, and the depth identity $L=r+c$ |
| [`SharedBiasFrontierRoute.lean`](OneChannelCNNUniversality/SharedBiasFrontierRoute.lean) | Arbitrary finite east/south routes, horizontal-vertical commutation, canonical Pascal-grid normalization, exact depth, terminal frontier formulas, and injectivity |
| [`SharedBiasFrontierAffineRoute.lean`](OneChannelCNNUniversality/SharedBiasFrontierAffineRoute.lean) | Direction-dependent nonnegative shared biases, exact affine route evaluation, injectivity, and the order-sensitive gap $(ES)_{1,1}-(SE)_{1,1}=\alpha-\beta$ |
| [`SharedBiasSignedGate.lean`](OneChannelCNNUniversality/SharedBiasSignedGate.lean) | A depth-two input-dependent signed affine ReLU gate, redundant exact input recovery, injectivity on bounded families, and compact uniform parameter selection |
| [`SharedBiasRowGate.lean`](OneChannelCNNUniversality/SharedBiasRowGate.lean) | A depth-two pointwise signed ReLU gate on an arbitrary finite row, coordinatewise exact decoding, injectivity, and compact uniform parameter selection |
| [`SharedBiasGridGate.lean`](OneChannelCNNUniversality/SharedBiasGridGate.lean) | A depth-two northern-row signed ReLU gate on arbitrary-height images, an exact south-triangular full-image decoder, injectivity, and compact uniform parameter selection |
| [`SharedBiasGridGateComposition.lean`](OneChannelCNNUniversality/SharedBiasGridGateComposition.lean) | A genuine depth-four composition of two protected grid gates, the exact nested ReLU formula, stagewise compact bounds, and injectivity |
| [`SharedBiasGridGateSchedule.lean`](OneChannelCNNUniversality/SharedBiasGridGateSchedule.lean) | Compilation of every finite signed affine ReLU schedule to an exact-depth shared-bias CNN with pointwise northern-row semantics and injective complete state |
| [`SharedBiasAffineMixGate.lean`](OneChannelCNNUniversality/SharedBiasAffineMixGate.lean) | Arbitrary signed mixing of adjacent northern registers, injectivity of the weighted horizontal transform, a depth-three protected ReLU gate, and compact parameter selection |
| [`SharedBiasLocalGateSchedule.lean`](OneChannelCNNUniversality/SharedBiasLocalGateSchedule.lean) | Exact compilation of arbitrary finite signed local-gate schedules, prefix dependence, depth $3L$, stagewise compact carriers, and injective complete state |
| [`SharedBiasAdjacentRidge.lean`](OneChannelCNNUniversality/SharedBiasAdjacentRidge.lean) | A depth-two arbitrary adjacent affine ridge, exact southeast-shifted triangular backup, south-to-north recovery, compact carrier selection, and injective complete state |
| [`SharedBiasAdjacentLattice.lean`](OneChannelCNNUniversality/SharedBiasAdjacentLattice.lean) | Linear left inversion of the adjacent-ridge backup, exact coordinate recovery by affine readouts, and terminal adjacent minimum/maximum readouts from one depth-two network |
| [`SharedBiasThreePointRidge.lean`](OneChannelCNNUniversality/SharedBiasThreePointRidge.lean) | A depth-two arbitrary affine ReLU of all three coordinates of a $1\times3$ input, explicit triangular affine recovery, compact parameter selection, and injective complete state |
| [`SharedBiasFourPointRidge.lean`](OneChannelCNNUniversality/SharedBiasFourPointRidge.lean) | A depth-three arbitrary affine ReLU of all four coordinates of a bounded $1\times4$ input, the triangular northern filter $1+6z+11z^2+6z^3$, explicit affine recovery, compact parameter selection, and injective complete state |
| [`SharedBiasDepthLowerBound.lean`](OneChannelCNNUniversality/SharedBiasDepthLowerBound.lean) | Exact depth-dependent receptive fields, the four-corner mixed-difference identity for arbitrary affine readouts, the sharp error lower bound $1$, and the necessary depth $L+1$ for endpoint interaction |
| [`SpatialInteractionDepthLowerBound.lean`](OneChannelCNNUniversality/SpatialInteractionDepthLowerBound.lean) | Anisotropic receptive-field bounds for ordinary position-dependent-bias networks, a two-site mixed-difference obstruction, and the necessary row/column depth spans for product approximation |
| [`Tests/`](OneChannelCNNUniversality/Tests) | Module, regression, top-level, and axiom-audit checks |

The compiler uses the exact identities
$\min(a,b)=a-\mathrm{ReLU}(a-b)$ and
$\max(a,b)=b+\mathrm{ReLU}(a-b)$.

## Environment

- Lean 4.32.1
- Mathlib v4.32.1

The toolchain is pinned by [`lean-toolchain`](lean-toolchain). The Mathlib Git
dependency and revision are pinned by [`lakefile.lean`](lakefile.lean) and
[`lake-manifest.json`](lake-manifest.json). Lake downloads dependencies into
the ignored local `.lake/packages/` directory; Mathlib source is not stored in
this repository.

## Installation

Install [elan](https://github.com/leanprover/elan), then clone the repository:

```bash
git clone git@github.com:wpdata/OneChannelCNNUniversality.git
cd OneChannelCNNUniversality
```

Download the pinned dependencies:

```bash
lake update
```

## Verification

Build the complete formalization:

```bash
lake build
```

Run every proof test:

```bash
for test_file in OneChannelCNNUniversality/Tests/*.lean; do
  lake env lean "$test_file"
done
```

Audit the top-level theorem:

```bash
lake env lean OneChannelCNNUniversality/Tests/Axioms.lean
```

The expected report is:

```text
'OneChannelCNNUniversality.twoDimensional_oneChannel_universal_approximation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

These are standard Lean/Mathlib foundations. The project contains no custom
`axiom` declaration and no `sorry` or `admit` proof placeholder. The following
source scan must return no matches:

```bash
rg -n --glob '*.lean' \
  '(^|[^[:alnum:]_])(sorry|admit|unsafe)([^[:alnum:]_]|$)|^[[:space:]]*axiom([^[:alnum:]_]|$)' \
  OneChannelCNNUniversality OneChannelCNNUniversality.lean
```

Compiler linter warnings are style diagnostics rather than unproved goals. The
verification criteria are a successful build, successful tests, an empty
forbidden-source scan, and the axiom report above.

## Scope and status

This repository publishes the Lean source and its machine-checkable results.
Lean kernel verification establishes that the position-dependent-bias
universal-approximation theorem and the narrower shared-bias boundary/carrier lemmas
follow from the stated definitions and reported foundations.  It does not
turn the unresolved shared-bias universality question into a theorem, and it
does not by itself establish external peer review or historical priority.
