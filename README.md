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
registers.  The arbitrary-width construction below now subsumes the
three- and four-register cases for every one-row input width $m\ge 3$.
It is still a single-ridge extension theorem, not yet a compiler for general
two-dimensional states, iterated ridge insertion, or shared-bias universal
approximation.

[`SharedBiasGeneralRidgePolynomial.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgePolynomial.lean)
formalizes the Lagrange factorization for every depth $d$.  It uses the monic
nodal factors

$$
A_i(X)=X+(i+1),\qquad 0\le i<d,
$$

and defines the target polynomial $R_w$ so that its coefficient of $X^j$ is
$w(\mathrm{Fin.rev}(j))$; this built-in reversal exactly matches convolution
at the natural output column.  Lean proves a Lagrange decomposition of $R_w$
into the nodal product $\prod_i A_i$ and its one-factor complements.  Given
numbers $\eta_i$ with $\sum_i\eta_i=w_0$, it then constructs linear lower
factors $B_i$ and proves

$$
[Y]\prod_{i=0}^{d-1}\bigl(A_i(X)+YB_i(X)\bigr)=R_w(X).
$$

This is an arbitrary-$d$ machine-checked algebraic theorem, rather than an
extrapolation from the three- and four-register cases.

[`SharedBiasGeneralRidgeConvolution.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeConvolution.lean)
turns every factor $A_i(X)+YB_i(X)$ into the genuine $2\times2$ kernel

$$
K_i=
\begin{pmatrix}
i+1 & 1\\
\beta_i+\eta_i(i+1) & \eta_i
\end{pmatrix}.
$$

For an arbitrary heterogeneous list of such kernels, Lean identifies the
northern and first-southern row recursions with the coefficients of the
bivariate factor product.  The specialized pure full-convolution chain
therefore satisfies

$$
\mathrm{FullConvChain}(x)_{1,d}
  =\sum_{j=0}^{d}w_jx_j.
$$

for positive depth.  The algebra also covers the degenerate case $d=0$;
there the allocation condition forces $w_0=0$, and the southern coordinate
is outside the depth-zero output.

Its northern boundary is the triangular polynomial transport

$$
G_d(X)\,\mathrm{Row}_0(x),\qquad
G_d(X)=\prod_{i=0}^{d-1}\bigl(X+(i+1)\bigr).
$$

The file also packages any heterogeneous kernel list as a genuine zero-bias
`SharedBiasNetworkTo`, but its equality with the pure convolution chain is
proved only under the explicit `LinearBranchAlong` hypothesis that every
encountered preactivation is nonnegative.  The following carrier, separation,
selection, and recovery modules discharge that condition for one complete
arbitrary-width ridge block on a compact input family.

[`SharedBiasGeneralRidgeCarrier.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeCarrier.lean)
chooses an explicit lower-factor allocation for every $d\ge 2$.  Writing
$\beta_{d-1}$ for the last Lagrange coefficient, its carrier scale is

$$
T=\frac{|\beta_{d-1}|+d+2}{d+1},
$$

and the selected allocation still satisfies $\sum_i\eta_i=w_0$.
[`SharedBiasGeneralRidgeSeparation.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeSeparation.lean)
then proves that the final kernel applied to the unit constant carrier of
size $d\times 2d$ has a uniform gap: every northern coordinate exceeds the
southern target $(1,d)$ by at least $2$.

[`SharedBiasHeterogeneousCarrier.lean`](OneChannelCNNUniversality/SharedBiasHeterogeneousCarrier.lean)
lifts an arbitrary heterogeneous factor prefix to genuine shared-bias ReLU
layers on compact continuous input families.  A tunable nonnegative boost in
the last prefix layer becomes a spatial address after the terminal
convolution.  [`SharedBiasTerminalSelection.lean`](OneChannelCNNUniversality/SharedBiasTerminalSelection.lean)
uses the unit address gap and compactness to choose one global boost and one
final shared scalar bias.  The target follows the nonlinear ReLU branch,
while every protected northern coordinate remains the pure signal plus a
fixed, input-independent offset.

[`SharedBiasGeneralRidgeRecovery.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeRecovery.lean)
proves that the complete northern row is injective.  Its generating
polynomial is the input row polynomial multiplied by the nonzero monic factor
$G_d$ above, so equality of northern rows forces equality of inputs; adding a
fixed offset preserves this conclusion.

Finally,
[`SharedBiasGeneralRidgeNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeNetwork.lean)
assembles these parts into the genuine nonlinear network theorem.  Let
$m\ge 3$, let $K$ be compact, and let
$F:X\to\mathbb R^{1\times m}$ be coordinatewise continuous on $K$.  For
arbitrary $w\in\mathbb R^m$ and $\gamma\in\mathbb R$, Lean constructs a
one-channel expansive $2\times2$ shared-bias ReLU network $N$ with

$$
\mathrm{depth}(N)=m-1,
\qquad
N(F(x))\in\mathbb R^{m\times(2m-1)},
$$

such that, for every $x\in K$,

$$
N(F(x))_{1,m-1}
=\mathrm{ReLU}\!\left(\sum_{j=0}^{m-1}w_jF(x)_{0,j}+\gamma\right).
$$

For every northern coordinate $q$, the output also satisfies

$$
N(F(x))_{0,q}
=\bigl[G_{m-1}(X)\,\mathrm{Row}_0(F(x))\bigr]_q+c_q,
$$

where $c_q$ is fixed independently of $x$.  If $F$ is additionally injective
on $K$, then $N\circ F$ remains injective there.  Thus the arbitrary-width
single-ridge network lift, including the shared carriers and the final ReLU
recovery argument, is now machine-checked.

[`SharedBiasGeneralRidgeLState.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeLState.lean)
shows that the whole expanded rectangle is not needed as a logical state.
The first $m$ northern coordinates already form an injective triangular code.
Together with the ridge at $(1,m-1)$, they occupy the southeast-monotone chain

$$
(0,0),(0,1),\ldots,(0,m-1),(1,m-1).
$$

The extracted $1\times(m+1)$ state is coordinatewise continuous and remains
injective whenever the input feature map is injective, while its last entry is
the requested ridge exactly.  This coordinate restriction is a mathematical
readout of the existing feature image, not an extra convolutional layer and
not yet an object that can be appended as a new CNN block.

[`SharedBiasGeneralRidgeReadout.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeReadout.lean)
turns the northern recovery and one ridge into an exact terminal lattice
operation.  Given arbitrary input affine functions

$$
A(x)=\sum_j a_jx_j+\alpha,
\qquad
B(x)=\sum_j b_jx_j+\beta,
$$

one depth-$(m-1)$ genuine shared-bias network computes
$\mathrm{ReLU}(A-B)$ at its protected target.  Two ordinary finite affine
readouts of that same output recover $A$ or $B$ from the northern code and
combine it with the target, exactly producing $\min(A,B)$ and $\max(A,B)$ on
the compact input family.  The noncomputably chosen, generally nonlocal linear
left inverse belongs only to the terminal readout; it is not a convolutional
hidden layer, so this theorem does not yet compile nested lattice expressions.

[`SharedBiasGeneralRidgeCompositionObstruction.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeCompositionObstruction.lean)
pinpoints why black-box appending fails for the present construction.  On a
multirow state $Z$, the pure general-ridge factor chain satisfies the exact
identity

$$
\mathrm{Row}_1(\mathrm{out})
=G_d(X)\,\mathrm{Row}_1(Z)+R_w(X)\,\mathrm{Row}_0(Z).
$$

Because the monic factor $G_d$ is nonzero, fixing the northern row does not
remove dependence on the old second row.  Moreover, the current terminal
carrier address is exactly flat at every interior site of row one, including
the target and its predecessor, so it cannot supply the unit gap needed to
protect that whole row while selecting one new target.  These theorems rule
out naive reuse of this separated block; they do not rule out a different
multi-ridge construction or universal approximation by the architecture.

[`SharedBiasGeneralRidgeIdealAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeIdealAddress.lean)
identifies an exact algebraic repair for the flat row address.  With

$$
G_d(X)=\prod_{i=1}^{d}(X+i),
\qquad C_d(X)=1+X+\cdots+X^d,
$$

every coefficient of $G_d$ from degree $0$ through $d$ is at least one.
The coefficient of $G_dC_d$ at degree $d$ contains their full sum, while
every other degree omits at least one term.  Lean therefore proves that
degree $d$ is the unique maximum with gap at least one; after negation it is
the unique minimum with the same gap.  This supplies the precise spatial
shape required by a full-row selector.  It is deliberately stated as an
algebraic address theorem: generating the finite boxcar stripe inside a
genuine shared-bias CNN, while retaining the variable signal, is the next
network-level obligation.

[`SharedBiasGeneralRidgeAddressPlateau.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeAddressPlateau.lean)
analyzes an abstract polynomial carrier model for linearly propagated bias
boosts.  In that model, if the input width is $m$, the total depth is $L$,
and the $k$-th bias direction is a degree-bounded polynomial multiplied by
its prescribed boxcar, then every bias direction—and therefore every real
linear combination of them—is constant throughout

$$
L-1\le q\le m.
$$

A target that sees all $m$ inputs must satisfy $m-1\le q\le L$.  Lean proves
that whenever $m-1\le L\le m$, such a target always has a distinct competitor
with exactly the same address.  At $L=m+1$ the former common plateau first
shrinks to the singleton $\{m\}$.  This is a sharp statement only inside that
polynomial linear-carrier model.  A network-to-polynomial representation
theorem is not asserted here, so this is not a depth lower bound for arbitrary
shared-bias networks with genuinely nonlinear intermediate masks.

[`SharedBiasGeneralRidgeLowWindow.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeLowWindow.lean)
supplies the finite triangular inverse needed by a sequential multi-ridge
design.  If $H(0)\ne0$, then for every polynomial $R$ and degree budget $d$
it constructs a polynomial $U$ with $\deg U\le d$ such that

$$
[X^j](UH)=[X^j]R,
\qquad 0\le j\le d.
$$

The construction truncates the formal power series $RH^{-1}$; it does not
claim that $H$ has a polynomial inverse.  In a later ridge stage this permits
the low-order target window to cancel all known affine transport from earlier
stages.  The remaining multi-ridge difficulty is therefore the genuine
shared-bias carrier that protects the northern row and the required suffix of
row one during each selected ReLU, not the finite coefficient matching.

[`SharedBiasGeneralRidgeStripeAlgebra.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeAlgebra.lean)
implements the signed factor schedule for the first proposed two-row repair.
After appending a zero target weight, it preserves the desired vertical
degree-one polynomial while changing the complete horizontal product to

$$
-T\prod_{i=1}^{d}(X+i).
$$

For $T\ge1$, all four taps of the final twisted factor are at most $-1$.
This is the exact sign pattern needed by the proposed terminal stripe gate;
the later carrier modules use this sign pattern in the terminal gate.

[`SharedBiasGeneralRidgeStripePrefix.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripePrefix.lean)
shows that every proper prefix of this twisted schedule retains the positive
horizontal product

$$
G_k(X)=\prod_{i=1}^{k}(X+i).
$$

Every coefficient of $G_kC_m$ on its complete support
$0\le q\le k+m$ is at least one, including both boundary ramps; on the
full-window interval it is exactly $(k+1)!$.  These are algebraic prefix
bounds; the following carrier theorem controls the lower-row perturbation.

[`SharedBiasGeneralRidgeStripeCarrier.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeCarrier.lean)
closes the proper-prefix positivity problem.  It proves the exact two-row
carrier formulas

$$
\mathrm{row}_0=2G_kC_m,
\qquad
\mathrm{row}_1=2G_kC_m-2T^{-1}R_kC_m,
$$

places one finite absolute bound over every prefix and every genuine output
column, and chooses the explicit upward-closed threshold $T_0=2(B+1)$.
For every $T\ge T_0$, the constant-two stripe is therefore a certified
`NorthTwoUnitLowerAlong` carrier for all proper layers, including the
shortest case and both boundary ramps.

[`SharedBiasGeneralRidgeStripeFinalAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeFinalAddress.lean)
computes the genuine final-kernel response to a unit constant boost at the
preceding layer.  Every northern coordinate and both row-one endpoints lie
at least two above the target, while every row-one interior coordinate has
exactly the target address.  Thus this direction supplies the required
vertical and boundary separation but formally confirms that it cannot create
horizontal uniqueness by itself.

[`SharedBiasNorthTwoLinearization.lean`](OneChannelCNNUniversality/SharedBiasNorthTwoLinearization.lean)
proves the complementary genuine-network invariant.  For expansive
$2\times2$ convolutions, the northern two output rows depend only on the
northern two input rows.  Hence a real zero-bias ReLU network agrees there
with its formal convolution chain whenever only those two rows have
nonnegative preactivations at every stage; arbitrary nonlinear behavior
farther south cannot propagate back north.  This substantially weakens the
old full-image linearity obligation, but it does not by itself establish the
missing prefix nonnegativity bounds.

[`SharedBiasNorthTwoCarrier.lean`](OneChannelCNNUniversality/SharedBiasNorthTwoCarrier.lean)
closes the compactness step behind those bounds.  It proves that any fixed
carrier contributing at least one at every northern-two-row prefix
preactivation can be scaled once so that an arbitrary continuous compact
signal family satisfies `NorthTwoLinearAlong`.  It also proves an
upward-closed identity-seed theorem: for every sufficiently large shared
bias $c$, the genuine first ReLU layer is exactly the identity convolution
plus the constant image $c$.  The remaining stripe-specific task is now
supplied by the certified unit-lower carrier above.

[`SharedBiasSeededNorthTwoNetwork.lean`](OneChannelCNNUniversality/SharedBiasSeededNorthTwoNetwork.lean)
packages these two ingredients into one upward-closed compact threshold.
Above it, a genuine identity seed layer is exactly affine and every proper
factor preactivation is nonnegative on the northern two rows.  Consequently
the actual seed-plus-zero-bias network agrees there with its full formal
convolution chain.  Rows farther south are deliberately unrestricted.

[`SharedBiasBiasedLast.lean`](OneChannelCNNUniversality/SharedBiasBiasedLast.lean)
allows the last layer of any nonempty heterogeneous factor block to carry a
nonnegative shared bias while all earlier layers keep bias zero.  Under the
same northern-two-row linearity certificate, its actual output is exactly
the formal chain plus that constant on the protected two rows.  This is the
genuine-network source of the local carrier used by the final stripe factor.

[`SharedBiasGeneralRidgeStripeSeedAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeSeedAddress.lean)
proves that the complete signed stripe chain turns the identity-seed boxcar
into a scalable address whose row-one center is the unique minimum.  More
precisely, it splits the address as

$$
A_0(q)=-T I_m(q),
\qquad
A_1(q)=-T I_m(q)+B(q),
$$

constructs an explicit upward-closed threshold for $T$, and proves a unit
gap between the row-one target and every other row-one column.  It also
bounds every northern coordinate relative to the target and identifies the
fixed target perturbation as $B(m)=\sum_j w_j$.  These remain exact algebraic
full-chain statements until the prefix linearity bridge is attached.

[`SharedBiasTwoCarrierSelection.lean`](OneChannelCNNUniversality/SharedBiasTwoCarrierSelection.lean)
formalizes the compact terminal mask used to combine complementary address
directions.  One carrier may handle horizontal uniqueness while a second
handles northern and boundary separation; a finite deficit in the first
direction is allowed on the second class.  Compactness supplies uniform
positive scales so that the target applies exactly one prescribed ReLU and
every other protected coordinate stays on its linear branch.
The strengthened interface permits an arbitrary prescribed lower bound on
the seed scale, so the same scale can satisfy all preceding linearization
thresholds.

[`SharedBiasGeneralRidgeStripeAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeAddress.lean)
combines the two address directions on the final rectangle.  Lean proves
the exact dichotomy required by the selector: every non-target row-one site
has a unit seed-address gap and a nonnegative local gap, whereas every
northern site has a two-unit local gap and a seed deficit bounded by the
finite target perturbation.

[`SharedBiasGeneralRidgeStripeProperNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeProperNetwork.lean),
[`SharedBiasGeneralRidgeStripeRealization.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeRealization.lean),
and [`SharedBiasGeneralRidgeStripeNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeNetwork.lean)
close the final typed network-realization bridge.  For an input of width
$n+2$, the construction is a genuine depth-$n+3$, one-channel expansive
$2\times2$ shared-bias ReLU network.  On every compact continuous input
family, positive parameters can be chosen uniformly so that the protected
coordinate $(1,n+2)$ satisfies the exact identity

$$
N_{w,\theta}(x)_{1,n+2}
=\mathrm{ReLU}\!\left(\sum_{j=0}^{n+1}w_jx_j+\theta\right).
$$

The machine-checked theorem is stronger than target equality: it identifies
the output at every coordinate in the northern two rows and proves that all
non-target protected coordinates remain in the linear branch of the final
ReLU.  [`SharedBiasGeneralRidgeStripeRecovery.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeRecovery.lean)
further proves that the complete northern row is an injective linear encoding
of the original input whenever $T\ne0$, constructs a linear left inverse that
recovers the input exactly, and upgrades the genuine compact ridge network to
an injective state transform on compact injective feature families.  It also
constructs finite affine-readout weights that recover any independently
chosen input affine functional from the same final feature map.
[`SharedBiasGeneralRidgeStripeMinMax.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeMinMax.lean)
uses this recovered affine value together with the protected ridge coordinate
to prove exact terminal readouts for two arbitrary affine functions $A,B$:

$$
\min(A,B)=A-\mathrm{ReLU}(A-B),\qquad
\max(A,B)=B+\mathrm{ReLU}(A-B).
$$

The resulting state is still injective.  Thus the arbitrary-width
single-ridge subproblem and its first binary lattice interface are complete.
[`SharedBiasGeneralRidgeStripeAffineCombination.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeAffineCombination.lean)
packages the general exact readout consequence: for arbitrary real data it
realizes

$$
\lambda\,\mathrm{ReLU}\!\left(\sum_j w_jx_j+\theta\right)
  +\sum_j a_jx_j+\alpha
$$

by one finite affine readout of the same genuine depth-$n+3$ network, while
retaining state injectivity.  This is the complete one-hidden-unit ReLU class
with an affine skip term, not yet a finite hidden-unit sum.
[`SharedBiasParallelRidgeAlgebra.lean`](OneChannelCNNUniversality/SharedBiasParallelRidgeAlgebra.lean)
opens a concrete route to such finite sums without naively composing
multirow ridge outputs.  For any $r$ independent weight vectors of input
width $m$, it packs their reversed coefficients into the disjoint polynomial
windows

$$
sm+1,\ldots,(s+1)m,\qquad 0\le s<r.
$$

Lean proves that one depth-$rm$ bilinear factor chain simultaneously computes
the corresponding $r$ linear forms at row-one columns
$m,2m,\ldots,rm$.  This completes the collision-free algebraic
parallelization.  A compact shared-bias carrier that applies ReLU at all of
these targets while protecting the recoverable northern code is still needed
before this becomes a genuine finite-ridge CNN theorem.
[`SharedBiasMultiTargetSelection.lean`](OneChannelCNNUniversality/SharedBiasMultiTargetSelection.lean)
now proves the compact selector half of that obligation.  If one carrier has
a common baseline on every target and a unit gap at every protected
non-target, one positive scale and one broadcast scalar bias apply ReLU at
all targets simultaneously while every protected non-target remains exactly
linear.  A final-layer convolutional decomposition theorem connects this
abstract criterion directly to a genuine shared-bias layer.  What remains is
the explicit carrier realizing this criterion for the equally spaced packed
ridge targets.
[`SharedBiasGeneralRidgeStripeWidthCarrier.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthCarrier.lean)
removes the main size mismatch in that construction.  The signed-stripe
factor depth and seed width are now independent: for arbitrary factor depth
$d=n+2$ and seed width $m+1$, Lean constructs the finite error bound and the
explicit upward-closed threshold $T_0=2(B+1)$.  Above it, every genuine
proper prefix is at least one on both northern rows and every actual output
column.  Thus parallel packing no longer needs to pad a width-$m$ input to
the depth-$rm$ factor length merely to keep the prefix ReLUs linear.
[`SharedBiasGeneralRidgeStripeWidthProperNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthProperNetwork.lean)
now lifts this independent-width carrier into a genuine network theorem.  For
arbitrary input width $m$ and a proper factor block determined by
$w:\mathrm{Fin}(n+2)\to\mathbb R$, it constructs a shared-bias ReLU
network of exact depth $n+2$ and output size
$(n+3)\times(m+n+2)$.  On every compact input family, one uniform seed
threshold makes its northern two rows agree exactly with the formal proper
convolution state.  The remaining finite-ridge step is no longer prefix
linearization.  The local geometric part of its final shared carrier is also
now verified in
[`SharedBiasGeneralRidgeStripeWidthFinalAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthFinalAddress.lean):
all row-one interior sites have one common baseline, while every northern
site and both row-one endpoints lie at least two above it when $T\ge1$.
What remains is the global horizontal address that separates the packed
interior targets from the protected interior non-targets, followed by the
terminal affine sum.
[`SharedBiasGeneralRidgeStripeWidthSeedAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthSeedAddress.lean)
derives the exact arbitrary-width complete-chain address

$$
A_1(q)=-T[X^q](G_{n+2}C_m)+[X^q](P_wC_m).
$$

This formula also exposes a genuine obstruction to directly reusing the
single-target nodal carrier.  In the minimal two-target width-two instance,
[`SharedBiasParallelStripeObstruction.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeObstruction.lean)
machine-checks

$$
[X^2](G_4C_2)=109,
\qquad [X^4](G_4C_2)=46,
$$

and hence, for zero packed weights and every $T\ne0$, the two target
addresses are $-109T$ and $-46T$.  They cannot meet the selector's common-
baseline hypothesis.  The obstruction is stronger than this numerical
instance.  For any monic degree-four horizontal polynomial $Q$ with
$[X]Q\ge1$, equality of the target windows
$[X^2](QC_2)=[X^4](QC_2)$ forces

$$
[X^2](QC_2)\le [X^3](QC_2).
$$

After multiplication by a negative positive-scale stripe, the intervening
non-target can therefore never lie one unit above the common target
baseline.  This rules out the full positive-prefix carrier pattern in the
minimal two-target geometry, not finite-ridge universality; the next
construction must use a qualitatively different horizontal carrier or a
sequential protected schedule.
[`SharedBiasParallelStripeCandidate.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeCandidate.lean)
shows that the desired two-target address itself is algebraically possible
once positive prefixes are abandoned.  The real-rooted monic polynomial

$$
Q(X)=(X-1)(X-2)(X-3)\left(X+\frac14\right)
$$

satisfies

$$
[X^2](QC_2)=[X^4](QC_2)=\frac{19}{4},
\qquad [X^3](QC_2)=\frac12,
$$

giving the exact target-to-middle gap $17/4$.  Lean also verifies the
precise cost: in the displayed factor order, the prefix
$(X+1/4)(X-1)C_2$ has constant coefficient $-1/4$.  Thus multi-target
separation and the old all-prefix-positive linearization mechanism are in
direct conflict.  The remaining constructive problem is now sharply
localized to linearizing sign-changing prefixes.

[`SharedBiasParallelStripeCompensation.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeCompensation.lean)
closes that minimal prefix-linearization problem.  For any scale $s\ge0$,
use the ordered factors

$$
X+\frac14,\qquad 1-X,\qquad X-2,\qquad X-3,
$$

start from the seed $4sC_2$, and add the shared scalar biases $0$, $5s$,
and $13s$ after the first three factors.  Lean proves that every coefficient
of every proper state is at least $s$, while the complete address satisfies

$$
A(2)=A(4)=-35s,
\qquad A(3)=-18s,
\qquad A(3)-A(2)=17s.
$$

Consequently $s\ge1/17$ gives the selector's normalized unit gap.  This is
a substantive constructive result: it supplies exact one-scalar-per-layer
compensation data whose carrier component has a positive linear-branch
margin.  The remaining work is to instantiate the compact genuine-network
bridge below with factors that also carry the variable packed-ridge signal,
and then combine it with the two-dimensional protected northern code; the
finite-ridge shared-bias universality theorem is not yet claimed.

[`SharedBiasCompensatedCarrier.lean`](OneChannelCNNUniversality/SharedBiasCompensatedCarrier.lean)
now proves the compact genuine-network bridge needed by this strategy in a
general form.  A compensated factor step consists of one bilinear
$2\times2$ kernel and one scalar carrier-bias coefficient.  If its formal
carrier preactivation is at least one at every coordinate of the northern
two rows throughout the chain, then compactness produces a common threshold
$s_0$.  For every $s\ge s_0$, the actual shared-bias ReLU network, using
layer bias $s c_i$ at step $i$, satisfies the exact coordinate identity

$$
\mathrm{Net}_s(V(x)+sC)=
\mathrm{ConvChain}(V(x))+s\,\mathrm{CompCarrier}(C)
$$

on both northern rows.  The theorem handles arbitrary finite heterogeneous
factor lists and arbitrary compact coordinatewise-continuous signal
families.  The next specialization obligation is entirely finite: prove
that the explicit $(0,5,13)$ two-target carrier meets this two-row unit-lower
hypothesis when the same factors also carry the packed ridge signal.

[`SharedBiasParallelStripeFactorization.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeFactorization.lean)
completes the variable-signal algebra for that specialization. Given two
arbitrary width-two weight vectors, it packs them into

$$
P(X)=w_{0,1}X+w_{0,0}X^2+w_{1,1}X^3+w_{1,0}X^4
$$

and supplies explicit rational vertical taps for the same four horizontal
factors. Lean proves coefficientwise through degree four that the
vertical-degree-one product is exactly $\varepsilon P$. Hence the formal
convolution chain reads, at its two target sites, precisely

$$
\varepsilon(w_{0,0}x_0+w_{0,1}x_1),\qquad
\varepsilon(w_{1,0}x_0+w_{1,1}x_1).
$$

The parameter $\varepsilon$ remains free, which is the degree of freedom
needed to control the perturbation of the compensated carrier. This is an
exact two-ridge bilinear factorization, not yet the full shared-bias ReLU
network theorem: the next obligation is to identify and correct the induced
weight-dependent carrier shift while retaining a protected unit gap, and then
instantiate the compact bridge.

[`SharedBiasParallelStripeCarrierCorrection.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeCarrierCorrection.lean)
resolves that carrier interaction. For the explicit vertical taps, the raw
doubled carrier targets differ by a fixed linear functional of the packed
weights. A single explicit correction at the southwest site of the second
input row,

$$
\frac{16}{17}\varepsilon
  (w_{0,1}-w_{1,1}-w_{1,0}),
$$

cancels the discrepancy exactly. Lean proves this first as a generating-
polynomial identity and then transports it to the actual finite convolution
images. It also proves that, for every pair of weight vectors, there exists
a strictly positive $\varepsilon$ for which all coordinates in both northern
rows of all three proper layers are at least one, the two final carrier
targets have exactly one common baseline, and the protected middle site
remains more than one above that baseline. Thus the complete finite carrier
hypothesis of the compact genuine-network bridge is now discharged. The
remaining step is the terminal shared-bias ReLU selection, including the
affine ridge offsets, followed by composition with the protected 2D code.

[`SharedBiasParallelStripeProperNetwork.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeProperNetwork.lean)
now instantiates the compact bridge. For every compact coordinatewise-
continuous family of two-row, width-three signals and every pair of width-two
weights, Lean produces a positive packing scale $\varepsilon$ and a common
network threshold $s_0$. For every $s\ge s_0$, the genuine three-layer
shared-bias ReLU network agrees exactly on both northern rows with

$$
\mathrm{VariableChain}(V(x))+
s\,\mathrm{CorrectedCarrier}.
$$

The same $\varepsilon$ has the strict final selector gap proved above. This
closes the proper-network realization; only the terminal selective ReLU and
its affine-offset bookkeeping remain before obtaining the two-ridge block.

[`SharedBiasGeneralRidgeOptimality.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeOptimality.lean)
shows that the linear depth of this construction is unavoidable for a
representative long-range ridge.  For

$$
f_L(x)=\mathrm{ReLU}(x_0+x_{L+1}),
$$

every depth-at-most-$L$ expansive $2\times2$ shared-bias network, even with an
arbitrary final affine readout, has maximum error at least $1/2$ on the four
endpoint sign inputs.  Therefore error strictly below $1/2$ forces depth at least
$L+1$.  Conversely, for every $L\ge1$, the arbitrary-width ridge compiler
produces a genuine shared-bias network of exact depth $L+1$ whose
single-coordinate affine readout equals $f_L$ on those four inputs.  Hence the
upper and lower depth bounds match exactly for this family; spatial expansion
remains a separate efficiency question.

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

This result closes the arbitrary-width single-ridge subproblem in this
formalization, but it is **not** a shared-bias universal-approximation theorem.
Here the width $m=d+1$ is the spatial length of the input row, not a channel
count: the network still has exactly one feature channel, a fixed $2\times2$
kernel shape, and one scalar bias shared across all spatial positions in each
layer.  The construction pays for those restrictions with depth $d$ and an
expansive output workspace of size $(d+1)\times(2d+1)$.  It is therefore an
exact expressivity and compilation result for finite feature vectors embedded
as one row, not a claim about training efficiency, fixed-resolution image
architectures, or arbitrary two-dimensional input states.  The repository's
existing full universal-approximation theorem still permits arbitrary
position-dependent bias images, and universality of the shared-scalar-bias
subclass remains open.

The decisive remaining gap is **composition**, not construction or recovery of one
ridge.  The new $L$-state shows that the complete $m\times(2m-1)$ rectangle
need not be normalized: an input-length northern prefix plus the ridge is
already sufficient.  However, that $L$-state is still embedded in the physical
rectangle, whereas the arbitrary-width ridge theorem starts from a one-row
state; off-chain sites may still depend on the input, coordinate restriction
is not a layer that `SharedBiasNetworkTo.append` can execute, and the verified
row-one contamination identity prevents black-box reuse of the current
factor chain.  A future compiler must operate directly on this embedded state,
replace the flat terminal address by a richer carrier, retain several
independently chosen ridge features through later shared-bias ReLUs, and then
implement the finite lattice combinations used by the density argument.
Until that finite multi-ridge compiler is proved, the present result must not
be described as a shared-bias universal-approximation theorem.

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
| [`SharedBiasGeneralRidgePolynomial.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgePolynomial.lean) | Arbitrary-$d$ Lagrange decomposition with reversed target coefficients and exact extraction of $R_w$ as the $Y$ coefficient of a product of bilinear factors |
| [`SharedBiasGeneralRidgeConvolution.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeConvolution.lean) | Genuine $2\times2$ kernels for every factor, heterogeneous full-convolution chains realizing $\sum_j w_jx_j$ at $(1,d)$, northern nodal-product transport, and a zero-bias ReLU-network bridge conditional on `LinearBranchAlong` |
| [`SharedBiasGeneralRidgeCarrier.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeCarrier.lean) | Explicit arbitrary-width lower-factor allocation, positive carrier scale, exact allocation sum, and the separated last-factor bound |
| [`SharedBiasGeneralRidgeSeparation.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeSeparation.lean) | Prefix/final-factor splitting and a uniform gap of at least two between every northern carrier response and the southern ridge target |
| [`SharedBiasHeterogeneousCarrier.lean`](OneChannelCNNUniversality/SharedBiasHeterogeneousCarrier.lean) | Compact shared-bias linearization for heterogeneous bilinear-kernel prefixes and a tunable terminal carrier boost |
| [`SharedBiasTerminalSelection.lean`](OneChannelCNNUniversality/SharedBiasTerminalSelection.lean) | Compact terminal compiler selecting one nonlinear target while preserving protected coordinates as pure signal plus a fixed offset |
| [`SharedBiasGeneralRidgeRecovery.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeRecovery.lean) | Injectivity of the complete northern nodal-polynomial code, including preservation under an arbitrary fixed offset |
| [`SharedBiasGeneralRidgeNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeNetwork.lean) | A genuine depth-$d$ arbitrary-width affine-ReLU ridge network, exact target evaluation, protected northern recovery, and injectivity on compact injective feature families |
| [`SharedBiasGeneralRidgeLState.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeLState.lean) | Injectivity of the input-length northern prefix and a continuous injective southeast-monotone $L$-state ending at the exact ridge coordinate |
| [`SharedBiasGeneralRidgeReadout.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeReadout.lean) | Linear recovery from the northern code and exact terminal min/max readouts for any two input affine functions using one shared-bias network |
| [`SharedBiasGeneralRidgeCompositionObstruction.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeCompositionObstruction.lean) | The exact old-row contamination identity and flat terminal-address obstruction to naive black-box composition of the present ridge block |
| [`SharedBiasGeneralRidgeIdealAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeIdealAddress.lean) | Nonnegative nodal-product coefficients and the boxcar product's unique central maximum, or unique unit-gap minimum after negation |
| [`SharedBiasGeneralRidgeAddressPlateau.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeAddressPlateau.lean) | The exact common plateau in the degree-bounded polynomial linear-carrier model, its unavoidable tied competitor through depth $m$, and its collapse at depth $m+1$ |
| [`SharedBiasGeneralRidgeLowWindow.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeLowWindow.lean) | Truncated formal-power-series inversion giving exact finite low-order coefficient matching whenever the transport polynomial has nonzero constant term |
| [`SharedBiasGeneralRidgeStripeAlgebra.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeAlgebra.lean) | A signed reciprocal factor twist preserving the target vertical polynomial, producing horizontal carrier $-T G_d$, and forcing all four final taps to be at most $-1$ |
| [`SharedBiasGeneralRidgeStripePrefix.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripePrefix.lean) | Exact positive nodal products for all proper twisted prefixes and a unit lower bound for every coefficient of their boxcar products on the complete support |
| [`SharedBiasGeneralRidgeStripeCarrier.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeCarrier.lean) | Exact two-row prefix-carrier formulas and an explicit upward-closed scale threshold certifying unit-lower preactivations at every proper layer |
| [`SharedBiasGeneralRidgeStripeFinalAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeFinalAddress.lean) | Exact final-kernel local address: two-unit northern and endpoint gaps together with a proved row-one interior plateau |
| [`SharedBiasNorthTwoLinearization.lean`](OneChannelCNNUniversality/SharedBiasNorthTwoLinearization.lean) | Northern-two-row causality and equality of a genuine zero-bias ReLU network with its formal convolution chain under row-local nonnegativity |
| [`SharedBiasNorthTwoCarrier.lean`](OneChannelCNNUniversality/SharedBiasNorthTwoCarrier.lean) | Compact domination by any unit-lower northern-two-row carrier and an upward-closed exact identity-seed threshold for signed compact inputs |
| [`SharedBiasSeededNorthTwoNetwork.lean`](OneChannelCNNUniversality/SharedBiasSeededNorthTwoNetwork.lean) | One common compact seed threshold giving an exact genuine seed layer, proper-prefix northern linearity, and agreement with the formal chain |
| [`SharedBiasBiasedLast.lean`](OneChannelCNNUniversality/SharedBiasBiasedLast.lean) | A genuine heterogeneous network biased only at its last layer, equal on the northern two rows to the formal chain plus that constant |
| [`SharedBiasGeneralRidgeStripeSeedAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeSeedAddress.lean) | Full-chain identity-seed address decomposition, an explicit monotone scale threshold for a unique row-one center, and a northern deficit bound |
| [`SharedBiasGeneralRidgeStripeAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeAddress.lean) | The complementary two-class gap theorem combining horizontal seed uniqueness with northern and boundary local separation |
| [`SharedBiasTwoCarrierSelection.lean`](OneChannelCNNUniversality/SharedBiasTwoCarrierSelection.lean) | Compact exact ReLU selection from two complementary carrier gaps, allowing a bounded deficit in one address direction |
| [`SharedBiasGeneralRidgeStripeProperNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeProperNetwork.lean) | A genuine seed-plus-proper-factor network with one compact threshold and exact northern-two-row agreement with its formal state |
| [`SharedBiasGeneralRidgeStripeRealization.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeRealization.lean) | Exact realization of the seed address, local address, and arbitrary linear ridge signal by the signed stripe factors |
| [`SharedBiasGeneralRidgeStripeNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeNetwork.lean) | The completed depth-$n+3$ genuine one-channel shared-bias $2\times2$ network computing an arbitrary affine ReLU ridge exactly on compact input families |
| [`SharedBiasGeneralRidgeStripeRecovery.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeRecovery.lean) | Injectivity and a linear left inverse for the northern stripe code, exact affine recovery by finite readout weights, and injectivity of the complete genuine ridge state |
| [`SharedBiasGeneralRidgeStripeMinMax.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeMinMax.lean) | Exact terminal affine readouts for the minimum and maximum of two arbitrary input affine functions, with the genuine ridge state still injective |
| [`SharedBiasGeneralRidgeStripeAffineCombination.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeAffineCombination.lean) | Exact finite readout of an arbitrary scalar ridge multiple plus an arbitrary affine skip term, with the genuine hidden state still injective |
| [`SharedBiasParallelRidgeAlgebra.lean`](OneChannelCNNUniversality/SharedBiasParallelRidgeAlgebra.lean) | Collision-free coefficient packing and one depth-$rm$ bilinear chain computing $r$ independent width-$m$ linear forms at separated row-one targets |
| [`SharedBiasMultiTargetSelection.lean`](OneChannelCNNUniversality/SharedBiasMultiTargetSelection.lean) | Compact simultaneous ReLU selection on a finite target set from one common-baseline carrier, including the exact genuine final-layer decomposition theorem |
| [`SharedBiasGeneralRidgeStripeWidthCarrier.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthCarrier.lean) | Independent-width signed-stripe prefix carrier, with one explicit threshold keeping both northern rows uniformly linear for arbitrary seed width |
| [`SharedBiasGeneralRidgeStripeWidthProperNetwork.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthProperNetwork.lean) | Genuine arbitrary-input-width signed-stripe proper network of exact depth $n+2$, with compact-uniform seed threshold and exact northern-two-row formal behavior |
| [`SharedBiasGeneralRidgeStripeWidthFinalAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthFinalAddress.lean) | Arbitrary-width final-factor address: a common row-one interior baseline and a gap of at least two at every northern site and both horizontal endpoints |
| [`SharedBiasGeneralRidgeStripeWidthSeedAddress.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeStripeWidthSeedAddress.lean) | Exact arbitrary-width full-chain seed-address decomposition into the scalable nodal boxcar carrier and the fixed packed-weight perturbation |
| [`SharedBiasParallelStripeObstruction.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeObstruction.lean) | Machine-checked minimal two-target counterexample and a generic monic positive-linear-coefficient theorem ruling out a protected common baseline for the positive-prefix stripe pattern |
| [`SharedBiasParallelStripeCandidate.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeCandidate.lean) | A real-rooted sign-changing carrier with exact common two-target baseline and gap $17/4$, together with the exact negative-prefix obstruction to the old linearization method |
| [`SharedBiasCompensatedCarrier.lean`](OneChannelCNNUniversality/SharedBiasCompensatedCarrier.lean) | General compact genuine-network theorem for heterogeneous factor chains with prescribed layerwise scalar-bias compensation and exact northern-two-row signal-plus-carrier semantics |
| [`SharedBiasParallelStripeCompensation.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeCompensation.lean) | Exact layerwise scalar-bias compensation for the sign-changing two-target carrier: uniform proper-prefix margin and final common baseline with gap $17s$ |
| [`SharedBiasParallelStripeFactorization.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeFactorization.lean) | Explicit rational vertical taps realizing two arbitrary width-two linear forms at the compensated stripe's two target sites, with exact coefficientwise and convolution identities |
| [`SharedBiasParallelStripeCarrierCorrection.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeCarrierCorrection.lean) | Exact one-site correction restoring the two-target carrier baseline, plus existence of a positive packed scale satisfying every proper northern-two-row unit-lower condition and a strict final selector gap |
| [`SharedBiasParallelStripeProperNetwork.lean`](OneChannelCNNUniversality/SharedBiasParallelStripeProperNetwork.lean) | Compact-uniform genuine three-layer shared-bias ReLU realization of the corrected two-target proper chain, with exact northern-two-row signal-plus-carrier semantics |
| [`SharedBiasGeneralRidgeOptimality.lean`](OneChannelCNNUniversality/SharedBiasGeneralRidgeOptimality.lean) | A sharp $1/2$ four-corner error obstruction for the endpoint affine-ReLU ridge and a matching exact-depth shared-bias construction |
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
universal-approximation theorem and the narrower shared-bias arbitrary-width
single-ridge theorem with its supporting boundary/carrier lemmas
follow from the stated definitions and reported foundations.  It does not
turn the unresolved shared-bias universality question into a theorem, and it
does not by itself establish external peer review or historical priority.
