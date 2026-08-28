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
nonlinear features after subsequent transports and the finite scan assembly
remain to be proved.

This is experimental proof infrastructure, **not** a shared-bias universal-
approximation theorem. The repository's existing full universal-approximation
theorem still permits arbitrary position-dependent bias images. It remains
open in this development whether the shared-scalar-bias subclass is universal
or non-universal. Arbitrary
targets can now be selected end to end under southeast-quadrant protection,
which removes the earlier northwest-only and proof-level-carrier restrictions.
What remains is substantially different: compose many such local updates
while preserving registers outside the active quadrant, control
expansion-fringe sites between updates, and connect that compiler to a density
argument for the shared-scalar-bias subclass.

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
