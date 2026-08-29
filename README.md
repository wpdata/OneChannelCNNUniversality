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
\operatorname{FullConv}(\delta,z)+c\mathbf 1,
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
\operatorname{AgreeOutsideStrictSoutheast}
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
  \operatorname{AgreeOutsideStrictSoutheast}(V(x),V(y);r,c)\right)
\Longrightarrow
\left(\forall x,y\in K,\;V(x)_{r,c}=V(y)_{r,c}\right).
$$

Consequently $\operatorname{ReLU}(V(x)_{r,c}+\theta)$ is constant on $K$
for every threshold $\theta$. The result is also specialized to the actual
appended-selector recovery step: two inputs with different selected successor
features formally refute its global pairwise-protection premise. Thus the
scheduled-recovery theorem is a valid state-preservation result, but its
strongest global corollary is not by itself a computational universality
argument. A useful compiler must separate protected state from the mutable
register on which a nonconstant ReLU is performed, or use a different
recovery invariant.

This is experimental proof infrastructure, **not** a shared-bias universal-
approximation theorem. The repository's existing full universal-approximation
theorem still permits arbitrary position-dependent bias images. It remains
open in this development whether the shared-scalar-bias subclass is universal
or non-universal. Arbitrary
targets can now be selected end to end under southeast-quadrant protection,
which removes the earlier northwest-only and proof-level-carrier restrictions.
What remains is substantially different: realize a protected-state copy and
a mutable work copy inside one spatial channel, route and recombine them with
explicit depth/area bounds, replace the now-refuted global same-root premise
by an invariant for that duplicated state, and connect the resulting compiler
to a density argument for the shared-scalar-bias subclass.

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
