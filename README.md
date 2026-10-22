# Parabolic rectifiability

[![Build and axiom audit](https://github.com/robertkoirala/parabolic-rectifiability/actions/workflows/build.yml/badge.svg)](https://github.com/robertkoirala/parabolic-rectifiability/actions/workflows/build.yml)
[![Comparator](https://github.com/robertkoirala/parabolic-rectifiability/actions/workflows/comparator.yml/badge.svg)](https://github.com/robertkoirala/parabolic-rectifiability/actions/workflows/comparator.yml)
![Lean](https://img.shields.io/badge/Lean-v4.35.0--rc4-blue)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue)](LICENSE)

A Lean 4 + mathlib formalization of decomposition and regular rectifiability
results for measures on parabolic space $\mathbb R^n\times\mathbb R$, by Robert
Koirala. The library develops horizontal and regular vertical graph covers,
square-energy (beta-number) criteria, a rectifiable Reifenberg decomposition of an
arbitrary Radon measure, a canonical decomposition into horizontal, vertical
and graph-pure parts, fifteen integral rectifiability criteria, a quantitative
characterization by Carleson energies and uniform coverings, and beta-$p$
versions of the support theorem with their exponent restrictions.

- **About 176,000 lines of Lean** in 957 modules, built on [mathlib](https://github.com/leanprover-community/mathlib4).
- **No `sorry` and no custom `axiom`.** Every declaration of the library uses only `propext`,
  `Classical.choice` and `Quot.sound`, checked by [`verification/AxiomAudit.lean`](verification/AxiomAudit.lean).
- **Statements checked against a Mathlib-only specification.** The statements of all checked
  results, together with every definition they depend on, are restated in
  [`verification/Spec.lean`](verification/Spec.lean), which imports only Mathlib.
  [Comparator](https://github.com/leanprover/comparator) checks that the library proves exactly
  these statements, and the proofs are replayed in Lean's kernel and in the independent checker
  [nanoda](https://github.com/ammkrn/nanoda_lib).
- **Builds without warnings.** Pinned to Lean `v4.35.0-rc4` and a fixed mathlib revision.

## Setting

The ambient space is $\mathbb R^n\times\mathbb R$ with the parabolic metric and
dilations

$$
d_P((x,t),(y,s))=\max\{\lVert x-y\rVert,\sqrt{|t-s|}\},
\qquad \delta_r(x,t)=(rx,r^2t).
$$

Write $P(a,R)$ for an open parabolic ball and $\mathcal H_P^k$ for Hausdorff
measure in this metric. The principal results concern $n\ge1$ and integer
$1\le k\le n+2$. Horizontal models (affine spatial $k$-planes at a fixed time)
are available for $1\le k\le n$; vertical models (affine spatial
$(k-2)$-planes times all of time) for $2\le k\le n+2$. A fixed-family statement
requires that family to be available.

For a measure $\mu$, a family $T$ of models, a center $z$ and a radius $r>0$,
the beta number is

$$
\beta_{\mu,T}^2(z,r)=r^{-k-2}\inf_{L}\int_{P(z,r)}d_P(w,L)^2\,d\mu(w),
$$

with no division by the mass of the ball, and the square energy is
$S^R_{\mu,T}(z)=\int_0^R\beta_{\mu,T}^2(z,r)\,dr/r$ (the superscript is the scale endpoint, not an exponent). Both are computed from the
whole source measure. Measures are nonnegative; "locally Radon" means finite on
compact sets and inner regular. Densities are $\mu(P(z,r))/r^k$. The exact
graph classes, including the half-time derivative and BMO conditions for
regular vertical graphs, are part of the Lean definitions; see
[docs/definitions.md](docs/definitions.md).

## Formalized results

Every result listed here, and every other result in [docs/theorems.md](docs/theorems.md),
is proved without `sorry` and uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Each statement is also restated in the [specification](verification/Spec.lean)
and checked against the library with Comparator (see [Verifying](#verifying)).
Unless noted, $n\ge1$, $1\le k\le n+2$, and $\mu$ is a locally Radon measure on
$\mathbb R^n\times\mathbb R$.

- [**Parabolic rectifiable Reifenberg theorem**](ParabolicRectifiability/Main.lean#L135): if
  $\mu(P(0,1)\cap\{S^{2}_{\mu}>M\})\le\Gamma$, then $\mu=\mu_++\mu_H+\mu_V$, where $\mu_H$ and
  $\mu_V$ are restrictions of $\mu$ with compact supports covered, at every tolerance, by
  horizontal and regular vertical graphs (modulo $\mathcal H_P^k$-null sets), with content,
  packing and tube bounds, and the remainder satisfies $\mu_+(P(0,1))\le C(n)M+\Gamma$. No
  density, doubling or finite-mass assumption is made. Variants: a
  [version uniform over all families](ParabolicRectifiability/Main.lean#L88), the
  [fixed-family version](ParabolicRectifiability/Main.lean#L157), the [ambient case $k=n+2$](ParabolicRectifiability/Main.lean#L164), the
  [scaled version on any ball $P(a,R)$](ParabolicRectifiability/Enhancements/Theorems/ScalingRates.lean#L18),
  [graph-domain covers](ParabolicRectifiability/Enhancements/Theorems/GraphDomains.lean#L30),
  [density bounds](ParabolicRectifiability/Enhancements/Theorems/Density.lean#L35), and
  [power](ParabolicRectifiability/Enhancements/Theorems/ScalingRates.lean#L23) and
  [gauge](ParabolicRectifiability/Enhancements/Theorems/ScalingRates.lean#L29) energy rates.
- [**Qualitative characterization**](ParabolicRectifiability/Characterization/Theorems/Main.lean#L31): for an available
  family $T$, $\mu$ is regularly type-$T$ rectifiable if and only if $0<\Theta^{k,*}<\infty$ and
  $S^R_{\mu,T}<\infty$ hold $\mu$-almost everywhere, for one (equivalently every) $R>0$; with the
  positive-upper/finite-lower density and intrinsic-source forms. Related results:
  [fifteen integral criteria](ParabolicRectifiability/IntegralCanonical/Theorems/Integral.lean#L36) (three source
  conditions, five integral tests), the [canonical decomposition](ParabolicRectifiability/IntegralCanonical/Theorems/Canonical.lean#L44)
  into horizontal rectifiable, regular vertical rectifiable and graph-pure parts (unique and
  independent of the energy endpoint), and [type separation](ParabolicRectifiability/IntegralCanonical/Theorems/Canonical.lean#L51).
- [**Quantitative characterization**](ParabolicRectifiability/QuantitativeCharacterization/Theorems/Characterization.lean#L24):
  for $\mu\neq0$ with unbounded support that is $A$-Ahlfors regular at all scales, a finite mixed
  square-energy Carleson bound is equivalent to absolute continuity with respect to
  $\mathcal H_P^k$ together with uniform regular mixed coverings, with explicit forward and reverse
  constants. Related results: [measure approximants](ParabolicRectifiability/QuantitativeCharacterization/Theorems/Approximants.lean#L22),
  the [local](ParabolicRectifiability/QuantitativeCharacterization/Theorems/Approximants.lean#L26) and
  [bounded-support](ParabolicRectifiability/QuantitativeCharacterization/Theorems/Approximants.lean#L30) versions, and the
  [beta-$p$ Carleson comparison](ParabolicRectifiability/QuantitativeCharacterization/Theorems/Characterization.lean#L31).
- [**Beta-$p$ support theorem**](ParabolicRectifiability/BetaP/Theorems/Main.lean#L35): the decomposition holds with
  remainder $C(n,p)M^{p/2}R^k+\Gamma$ for the energy $S_p$, $p\ge2$, and $C(n,p)MR^k+\Gamma$ for
  $T_p$, $0<p\le2$. Related results: the [complete necessity/sufficiency classification](ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L145),
  [sharpness of the integrated rates](ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L57), and
  [explicit witnesses](ParabolicRectifiability/BetaP/Theorems/Failures.lean#L55) for the failing exponent ranges.
- **Examples**: a [lacunary graph](ParabolicRectifiability/Examples/Theorems/Lacunary.lean#L49) of positive finite
  $\mathcal H_P^2$ measure, covered by ordinary graphs at every slope, whose measure is null on every
  regular vertical graph; [dense atomic sources](ParabolicRectifiability/Examples/Theorems/DensityExamples.lean#L27); and
  the [flat, diffuse and atomic density tests](ParabolicRectifiability/Examples/Theorems/DensityExamples.lean#L34).

Precise statements, all further results and remarks on what the statements do and do not
assert are in [docs/theorems.md](docs/theorems.md).

## Building

Install [elan](https://github.com/leanprover/elan), then from a checkout:

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
lake build
```

The pins are Lean `leanprover/lean4:v4.35.0-rc4` and mathlib at the revision in
[lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json).
`lake exe cache get` downloads prebuilt mathlib objects; `lake build` builds
the whole library through the single root import. A downstream project can use
the library through that one import:

```lean
import ParabolicRectifiability

#check ParabolicRectifiability.rectifiable_reifenberg
#check ParabolicRectifiability.Characterization.qualitative_characterization
#check ParabolicRectifiability.IntegralCanonical.canonical_decomposition
#check ParabolicRectifiability.QuantitativeCharacterization.quantitative_characterization
```

## Verifying

After building, three checks are available.

1. **Build.** `lake build` compiles every module and checks every proof with Lean's kernel. The
   build produces no errors and no warnings.
2. **Axiom audit.** The following checks every declaration of the library, not only the listed
   results, and fails if any uses an axiom other than `propext`, `Classical.choice` and
   `Quot.sound` (a `sorry` would appear as the axiom `sorryAx`):

   ```sh
   lake env lean verification/AxiomAudit.lean
   ```
3. **Comparator.** The [specification](verification/Spec.lean) restates, with `sorry` proofs, every
   checked result together with all definitions their statements depend on, copied from the
   library. [Comparator](https://github.com/leanprover/comparator) checks that the library proves
   exactly these statements over exactly these definitions, using only the three axioms above, and
   replays the proofs in Lean's kernel and in the independent checker
   [nanoda](https://github.com/ammkrn/nanoda_lib):

   ```sh
   lake comparator            # Linux, with bubblewrap installed
   ```

   Comparator builds and exports the code inside a `bubblewrap` sandbox, which exists only on Linux.
   On macOS it can be run without the sandbox (`lake comparator --inadvisably-no-sandbox`); the kernel
   checks are the same, but the build is then not isolated from the rest of the machine.

The continuous integration runs all three on Linux: [build and axiom audit](.github/workflows/build.yml) and [Comparator](.github/workflows/comparator.yml). Details, including
what each check does and does not establish, are in
[verification/README.md](verification/README.md).

## Library structure

- [`Metric`](ParabolicRectifiability/Metric), [`Geometry`](ParabolicRectifiability/Geometry),
  [`Measure`](ParabolicRectifiability/Measure), [`Analysis`](ParabolicRectifiability/Analysis): the
  parabolic metric and its measures, affine and graph models, beta numbers and square energies,
  neck constructions, the half-time derivative, BMO, and the trace and regular-extension theory.
- [`Foundations`](ParabolicRectifiability/Foundations): density bridges, graph envelopes, high-pass
  estimates, similarity transport and the ambient endpoint, shared by the main results.
- [`Specifications`](ParabolicRectifiability/Specifications),
  [`Decomposition`](ParabolicRectifiability/Decomposition),
  [`Composition`](ParabolicRectifiability/Composition) and [`Main.lean`](ParabolicRectifiability/Main.lean):
  the parabolic rectifiable Reifenberg theorem; [`Enhancements`](ParabolicRectifiability/Enhancements):
  its scaled, graph-domain, density and rate versions.
- [`Characterization`](ParabolicRectifiability/Characterization) and
  [`IntegralCanonical`](ParabolicRectifiability/IntegralCanonical): the qualitative characterization,
  integral criteria and canonical decomposition.
- [`QuantitativeCharacterization`](ParabolicRectifiability/QuantitativeCharacterization): the
  quantitative characterization.
- [`BetaP`](ParabolicRectifiability/BetaP): beta-$p$ theory; [`Examples`](ParabolicRectifiability/Examples):
  examples and counterexamples.

Each result area is organized as `Statements/` (the statements, as `Prop`-valued definitions),
`Proofs/` (by topic), `Assembly/` (the reduction of each main statement to the proved parts) and
`Theorems/` (the public results). [docs/architecture.md](docs/architecture.md) describes every
folder. `verification/` holds the specification and the axiom audit, and `docs/` the documentation.

## Documentation

- [docs/overview.md](docs/overview.md): the setting, notation and the main results in words, and how the Lean encoding differs from paper conventions.
- [docs/theorems.md](docs/theorems.md): every checked result, grouped by main theorem, with the main theorems stated precisely.
- [docs/definitions.md](docs/definitions.md): the definitions a reader must trust.
- [verification/README.md](verification/README.md): the verification checks in detail.
- [docs/architecture.md](docs/architecture.md): the module map and how the main proofs are assembled.

## Citation

See [CITATION.cff](CITATION.cff). Please cite the tagged version of the
software that you use.

## License

Apache-2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE). Dependencies retain
their own licenses.

