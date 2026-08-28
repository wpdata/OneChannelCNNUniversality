# Lean formalization of two-dimensional one-channel universality

This Lean 4 project proves universal approximation for the following exact
model:

- finite two-dimensional real inputs of positive size `d₁ × d₂`;
- a fixed expansive convolution shape `kRows × kCols`, with both sides at
  least `2`;
- one feature channel in every hidden layer;
- zero-extended full convolution, an arbitrary spatial bias, and entrywise
  ReLU at every layer;
- an arbitrary affine readout from the final feature image.

The exported theorem is
`ICM2022NumCS97.twoDimensional_oneChannel_universal_approximation` in
[`ICM2022NumCS97/Main.lean`](ICM2022NumCS97/Main.lean). It states that, on
every compact input set, these finite-depth networks uniformly approximate
every continuous real-valued target to every positive tolerance.

## Proof architecture

1. `Basic` defines the original finite-array CNN semantics.
2. `Carrier`, `Register`, `Program`, and `HybridProgram` compile exact
   masked register operations into genuine convolution/ReLU layers.
3. `Encoder` and `SparseEncoder` build an injective sparse convolutional
   encoding. The required binomial sampling matrix is proved invertible in
   Lean via polynomial bases and a Vandermonde argument.
4. `GridRouting`, `GridMachine`, and `LatticeCompiler` route encoded
   coordinates and exactly evaluate finite affine lattice expressions using
   `min(a,b) = a - ReLU(a-b)` and
   `max(a,b) = b + ReLU(a-b)`.
5. `Universal` applies Mathlib's lattice Stone--Weierstrass theorem to the
   injective encoded coordinates.
6. `Simulation` and `Main` combine exact compilation and density to return an
   actual network in the original semantics.

## Reproduce the verification

The project pins Lean `4.32.1` and Mathlib `v4.32.1`. Mathlib is recorded as
a Git submodule, so clone with:

```sh
git clone --recurse-submodules git@github.com:wpdata/lean-2d-one-channel-universality.git
cd lean-2d-one-channel-universality
```

If the repository was cloned without submodules, initialize Mathlib with:

```sh
git submodule update --init --recursive
```

Then run:

```sh
lake build
```

Run every proof test:

```sh
for test_file in ICM2022NumCS97/Tests/*.lean; do
  lake env lean "$test_file"
done
```

Audit the top theorem's axioms:

```sh
lake env lean ICM2022NumCS97/Tests/Axioms.lean
```

The expected report is:

```text
'ICM2022NumCS97.twoDimensional_oneChannel_universal_approximation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

There is no `sorryAx` and no project-defined axiom. The following source scan
must return no matches:

```sh
rg -n --glob '*.lean' \
  '(^|[^[:alnum:]_])(sorry|admit|unsafe)([^[:alnum:]_]|$)|^[[:space:]]*axiom([^[:alnum:]_]|$)' \
  ICM2022NumCS97 ICM2022NumCS97.lean
```

Compiler linter warnings do not represent unproved goals; the completion
criteria are a successful build, successful tests, an empty forbidden-source
scan, and the axiom report above.
