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
[`ICM2022NumCS97.twoDimensional_oneChannel_universal_approximation`](ICM2022NumCS97/Main.lean):

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

## Proof architecture

| Files | Role |
| --- | --- |
| [`Basic.lean`](ICM2022NumCS97/Basic.lean) | Finite-array image, convolution, ReLU-layer, network, and affine-readout semantics |
| [`Carrier.lean`](ICM2022NumCS97/Carrier.lean), [`Register.lean`](ICM2022NumCS97/Register.lean) | Exact carrier and masked-register operations |
| [`Program.lean`](ICM2022NumCS97/Program.lean), [`RegisterProgram.lean`](ICM2022NumCS97/RegisterProgram.lean), [`HybridProgram.lean`](ICM2022NumCS97/HybridProgram.lean) | Compilation of register programs into genuine convolution/ReLU layers |
| [`Encoder.lean`](ICM2022NumCS97/Encoder.lean), [`SparseEncoder.lean`](ICM2022NumCS97/SparseEncoder.lean) | Injective sparse convolutional encoding and the binomial/Vandermonde invertibility argument |
| [`RouteGeometry.lean`](ICM2022NumCS97/RouteGeometry.lean), [`Routing.lean`](ICM2022NumCS97/Routing.lean), [`GridRouting.lean`](ICM2022NumCS97/GridRouting.lean) | Exact spatial routing of encoded coordinates |
| [`GridMachine.lean`](ICM2022NumCS97/GridMachine.lean), [`LatticeCompiler.lean`](ICM2022NumCS97/LatticeCompiler.lean) | Exact evaluation of finite affine lattice expressions using ReLU min/max identities |
| [`Ridge.lean`](ICM2022NumCS97/Ridge.lean), [`Universal.lean`](ICM2022NumCS97/Universal.lean) | Density via Mathlib's lattice Stone--Weierstrass theorem |
| [`Simulation.lean`](ICM2022NumCS97/Simulation.lean), [`Main.lean`](ICM2022NumCS97/Main.lean) | Assembly of exact compilation and density into the final network theorem |
| [`Tests/`](ICM2022NumCS97/Tests) | Module, regression, top-level, and axiom-audit checks |

The compiler uses the exact identities
$\min(a,b)=a-\operatorname{ReLU}(a-b)$ and
$\max(a,b)=b+\operatorname{ReLU}(a-b)$.

## Environment

- Lean 4.32.1
- Mathlib v4.32.1

The toolchain is pinned by [`lean-toolchain`](lean-toolchain). The Mathlib
revision is recorded by [`lake-manifest.json`](lake-manifest.json) and the
[`vendor/mathlib`](vendor/mathlib) submodule.

## Installation

Install [elan](https://github.com/leanprover/elan), then clone the repository
with its Mathlib submodule:

```bash
git clone --recurse-submodules git@github.com:wpdata/machine-checked-2d-one-channel-relu-cnn-universality.git
cd machine-checked-2d-one-channel-relu-cnn-universality
```

If the repository was cloned without submodules, initialize Mathlib with:

```bash
git submodule update --init --recursive
```

## Verification

Build the complete formalization:

```bash
lake build
```

Run every proof test:

```bash
for test_file in ICM2022NumCS97/Tests/*.lean; do
  lake env lean "$test_file"
done
```

Audit the top-level theorem:

```bash
lake env lean ICM2022NumCS97/Tests/Axioms.lean
```

The expected report is:

```text
'ICM2022NumCS97.twoDimensional_oneChannel_universal_approximation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

These are standard Lean/Mathlib foundations. The project contains no custom
`axiom` declaration and no `sorry` or `admit` proof placeholder. The following
source scan must return no matches:

```bash
rg -n --glob '*.lean' \
  '(^|[^[:alnum:]_])(sorry|admit|unsafe)([^[:alnum:]_]|$)|^[[:space:]]*axiom([^[:alnum:]_]|$)' \
  ICM2022NumCS97 ICM2022NumCS97.lean
```

Compiler linter warnings are style diagnostics rather than unproved goals. The
verification criteria are a successful build, successful tests, an empty
forbidden-source scan, and the axiom report above.

## Scope and status

This repository publishes the Lean source and its machine-checkable theorem.
Lean kernel verification establishes that the theorem follows from the stated
definitions and reported foundations; it does not by itself establish external
peer review or historical priority.
