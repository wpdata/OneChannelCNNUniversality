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

This is experimental proof infrastructure, **not** a shared-bias universal-
approximation theorem.  The verified theorem above still permits an arbitrary
position-dependent bias image.  It remains open in this development whether
the shared-scalar-bias subclass is universal or non-universal: the boundary
seed alone does not yet provide the independently separated carrier values
needed to preserve arbitrary input registers while applying a local ReLU.

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
| [`SharedBias.lean`](OneChannelCNNUniversality/SharedBias.lean) | Exact shared-scalar-bias semantics and semantics-preserving embedding into the general model |
| [`SharedBiasGeometry.lean`](OneChannelCNNUniversality/SharedBiasGeometry.lean) | Exact constant, left-boundary, and northwest-corner position signals generated with shared biases |
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
universal-approximation theorem and the narrower shared-bias boundary lemmas
follow from the stated definitions and reported foundations.  It does not
turn the unresolved shared-bias universality question into a theorem, and it
does not by itself establish external peer review or historical priority.
