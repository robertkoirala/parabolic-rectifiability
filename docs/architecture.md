# Architecture

The library is the Lean package `ParabolicRectifiability`: 958 modules under
[`ParabolicRectifiability/`](../ParabolicRectifiability), plus the import root
[`ParabolicRectifiability.lean`](../ParabolicRectifiability.lean), which imports
every other module. A downstream project needs only
`import ParabolicRectifiability`. The statement specification is the separate
Lean library `Spec` ([`verification/Spec.lean`](../verification/Spec.lean) and
[`verification/Spec/`](../verification/Spec)); see
[definitions.md](definitions.md).

## Layout convention

Every result area (`BetaP`, `Characterization`, `Enhancements`, `Examples`, `Foundations`, `IntegralCanonical`, `QuantitativeCharacterization`) is organized in the same way.

- `Statements/`: the statements as `Prop`-valued definitions, named `…Statement` (and the data structures such as `IsCanonicalDecomposition` that they refer to), together with named intermediate statements. A `Statements` module contains no proofs of the main results.
- `Assembly/`: modules that derive the main results from the intermediate statements and from the proofs in `Proofs/`, and that package auxiliary results.
- `Theorems/`: the final named theorems, each of the form `theorem name : …Statement`, which are the public interface of the area (for example `Characterization/Theorems/Main.lean` contains `qualitative_characterization`).
- `Proofs/<topic>/`: the supporting proof modules, grouped by topic.

An area may also have top-level files holding its definitions (for example
`IntegralCanonical/Defs.lean`, `QuantitativeCharacterization/Coverings.lean`).

## Module map

Counts are numbers of `.lean` files in the folder, including subfolders.

### Basic space and measure theory

- [`Basic.lean`](../ParabolicRectifiability/Basic.lean): the space `Space n`, its coordinates and `point`.
- [`Metric/`](../ParabolicRectifiability/Metric) (6): the parabolic metric and coordinates, properness, coordinate and parabolic volume, parabolic Hausdorff measure, similarities (translation and scaling).
- [`Measure/`](../ParabolicRectifiability/Measure) (54): beta numbers and scale energies. Top-level files define the natural beta square, scale energies and countable fitting families and prove their laws (monotonicity, homogeneity, measurability), tail and level-set estimates, barycenter transfer to atomic measures, and spatial moments. `Measure/Neck/` (42 files) is the measure-side construction of *necks*: a recursive source construction with a decomposition tree, certificates, node charges, contracting steps and density selection, used to prove the decomposition theorems.

### Analysis

- [`Analysis/`](../ParabolicRectifiability/Analysis) (89): the analytic input for regular vertical graphs. Subfolders:
  - `HalfTimeDerivative/` (10): the half-time derivative on Schwartz tests and as a distribution, local representation by compactly supported tests, and an $`L^2`$ inverse representative.
  - `FractionalKernel/` (11): kernels and multipliers for the half-time derivative, high-pass kernels, moments of frequency cutoffs, and one-dimensional weighted and unweighted estimates.
  - `FourierAffine/` (4): the Fourier-affine square-integral bound, a parabolic smoothing kernel and pointwise control by the affine error.
  - `SmoothCutoff/` (3): the fixed profiles of the smooth parabolic partition and normalized weights.
  - `RegularExtension/` (16): extension of regular functions from a trace, with affine-error and cutoff comparisons and the bound that the half-time derivative of a function with an affine Carleson bound is in BMO.
  - `TraceExtension/` (41): construction of the extension of a trace on a compact set (Whitney boxes and cutoffs, Hall-type allocation of mass among cells, reservoirs, trace pieces, affine Carleson bounds).
  - Top-level files: Euclidean analytic coordinates, local mean oscillation, parabolic BMO on a vertical base, and a quantitative inverse on a ball.

### Geometry

- [`Geometry/`](../ParabolicRectifiability/Geometry) (55): affine spatial planes, horizontal, vertical and mixed models and their distances and topology, the graph classes used by the decomposition theorem, coherent projections, the smooth parabolic partition, covariance and minimizing planes, and intrinsic coordinates on vertical bases.
  - `Chart/` (5): the coherent chart construction and its induction estimates and coverage.
  - `Horizontal/` (4): the horizontal core graph cover and spatial graph pieces of a bi-Lipschitz chart.
  - `Neck/` (27): the geometric side of necks (regions, coherent charts, buffered reference measures, charging and collapse, local content, the neck structure theorem and the six neck theorems).

### Foundations

- [`Foundations/`](../ParabolicRectifiability/Foundations) (110): definitions and general facts shared by the main results. Top-level files define Ahlfors regularity, the beta-$`p`$ numbers and energies, sigma-finite Hausdorff carriers and intrinsic sources, lower and upper densities and density conditions, graph-domain covers, general regular graphs, typed covers and the classes of rectifiable sets and measures, the half-time derivative representation, and the bundle of support conclusions. Besides `Statements/`, `Assembly/` and `Theorems/`, the topics in `Proofs/` are the ambient case $`k=n+2`$ (`Ambient/`), density bridges (`DensityBridges/`), the envelope and Borel properties of graphs (`GraphEnvelope/`), high-pass estimates for BMO functions (`HighPass/`, `HighPassBracket/`), the beta-$`p`$ laws (`BetaPowLaws/`), covariance under similarities (`Similarity/`) and typed rectifiability under sums (`Rectifiability/`).

### Decomposition and the first main result

- [`Specifications/Rectifiability.lean`](../ParabolicRectifiability/Specifications/Rectifiability.lean): the public specification of the rectifiable Reifenberg theorem (`RetainedSets`, `HasRectifiabilityContentBounds`, `IsRectifiabilityDecomposition`, and the statements `MainRectifiabilityStatement`, `FixedFamilyRectifiabilityStatement`, `AmbientRectifiabilityStatement`).
- [`Decomposition/`](../ParabolicRectifiability/Decomposition) (17): the proof of the decomposition theorem: source localization, geometric extraction, density refinement, compact typed pieces, the positive-threshold, zero-threshold and ambient branches, and the final assembly. `Decomposition/Carrier/` (7) builds the regular vertical carrier.
- [`Main.lean`](../ParabolicRectifiability/Main.lean): exports `family_rectifiable_reifenberg`, `rectifiable_reifenberg`, `main_rectifiability`, `fixed_family_rectifiability` and `ambient_rectifiability`.
- [`Composition/`](../ParabolicRectifiability/Composition) (1): `MainTheoremOne.lean` assembles the rectifiable Reifenberg theorem with the general graph classes from the decomposition, a compact-to-general bridge for regular vertical graphs and local scaling.
- [`Enhancements/`](../ParabolicRectifiability/Enhancements) (30): the enhancements of the rectifiable Reifenberg theorem (`Decomposition.lean` defines the decomposition predicates): graph-domain covers on fixed carriers and on the supports, scaling, power-energy and gauge-energy rates, density corollaries. Contains `Statements/`, `Assembly/`, `Theorems/` and `Proofs/` (domination, graph domains, scaling).

### Characterizations

- [`Characterization/`](../ParabolicRectifiability/Characterization) (91): the qualitative characterization. `Statements/`, `Assembly/` and `Theorems/` hold the statement, the branches (finite-Hausdorff criterion, intrinsic sufficiency and necessity, graph-source finiteness, typed refinements) and the source-transfer results. `Proofs/` (79 files) has the topics `FiniteHausdorff/`, `Fourier/` (the parabolic Fourier affine-square inequality and its multipliers), `GraphSource/` (Ahlfors-regular carriers and graph sources), `NestedPartitions/`, `Replacement/` and `SourceTransfer/`, plus a Vitali selection lemma and Radon approximation.
- [`IntegralCanonical/`](../ParabolicRectifiability/IntegralCanonical) (25): `Defs.lean` defines the finite-energy sets, the canonical parts, graph purity, the three structural conditions and the five integral tests; `Statements/`, `Assembly/`, `Theorems/` and `Proofs/` (`Canonical/`, `Integral/`) hold the canonical decomposition, the density bridge, type separation, the guards, the integral equivalences and the integral criterion.
- [`QuantitativeCharacterization/`](../ParabolicRectifiability/QuantitativeCharacterization) (199): the quantitative characterization. `References.lean` defines horizontal, vertical and ambient reference models; `Coverings.lean` defines the Carleson energy, regular mixed coverings, approximants and quantitative rectifiability. `Statements/`, `Assembly/` and `Theorems/` carry the statements and final theorems. `Proofs/` (166 files) is the longest part of the library; its topics include the forward covering (`Forward/`, with stopping, terminal, last-witness, partition-energy, projection-energy, coverage and completion steps), the reverse bound (`Reverse/`), reference estimates (`Reference/`), Whitney plateau completion (`Plateau/`), trace and multiplicity (`Trace/`), approximants (`Approximants/`), pieces (`Pieces/`), the ambient and bounded-support cases (`Ambient/`, `BoundedSupport/`).

### Beta-p

- [`BetaP/`](../ParabolicRectifiability/BetaP) (89): the beta-$`p`$ support theorem and its consequences. `Statements/`, `Assembly/` and `Theorems/` hold the statements and final theorems (`betaP_support_theorem` is in `Theorems/Main.lean`); the topics in `Proofs/` are `Laws/` (conventions and laws of $`B_p`$), `Comparison/` (comparison with the quadratic energy), `Packing/` (active-radius packing), `Localization/`, `Carrier/`, `Support/` and `Corollaries/` (graph enhancement, integrated rates, classification), and `Counterexamples/` (19 files), which constructs witnesses showing that implications fail outside the favorable exponent ranges.

### Examples

- [`Examples/`](../ParabolicRectifiability/Examples) (188): concrete measures and graphs used for the counterexamples and exponent witnesses: dense atoms, lacunary space-time graphs, dispersed digit graphs, decorated segments, diffuse measures, planar slices, stationary graphs and time-slice reductions. Each example has its own topic folder in `Proofs/` (`DenseAtoms/`, `Lacunary/`, `DigitGraph/`, `DecoratedSegment/`, `DiffuseMeasures/`, `PlanarSlices/`, `StationaryGraphs/`, `TimeSlices/`, `ExponentBelow/`, …), beside `Statements/`, `Assembly/` and `Theorems/`.

## How the main results are assembled

1. **Definitions.** `Basic`, `Metric/`, `Geometry/` (models and graphs), `Measure/` (beta numbers and energies) and `Foundations/` define the vocabulary of [definitions.md](definitions.md).
2. **Decomposition.** The rectifiable Reifenberg theorem is proved in `Decomposition/`, which imports `Measure/` and `Geometry/` (including the neck constructions), `Analysis/` and the specification in `Specifications/Rectifiability.lean`. `Main.lean` imports `Decomposition/Assembly` and `Decomposition/ZeroThresholdAndAmbientBranches` and exports the decomposition theorems.
3. **Enhancements.** `Enhancements/` imports `Main`, `Composition/` and parts of `Characterization/` and `Foundations/`; `Composition/MainTheoremOne.lean` assembles the rectifiable Reifenberg theorem with the general graph classes.
4. **Characterizations.** `IntegralCanonical/` imports `Characterization/` and `Foundations/`. `QuantitativeCharacterization/` imports `Characterization/`, `IntegralCanonical/`, `BetaP/`, `Analysis/`, `Geometry/`, `Foundations/` and `Measure/`.
5. **Beta-p.** `BetaP/` imports `Enhancements/`, `Decomposition/`, `Composition/`, `Characterization/`, `Foundations/` and `Examples/` (for the witnesses).
6. **Public interface.** In each area the `Theorems/` modules contain the final theorems, each stated by a `…Statement` from the corresponding `Statements/` module. The twelve headline theorems are listed in [theorems.md](theorems.md). `verification/Spec.lean` restates them over the definitions in `verification/Spec/`.

The module graph is not layered by folder: for example some `Foundations/` modules
import `Decomposition/` and `Main`, and `Characterization/` modules import
`Enhancements/` and `QuantitativeCharacterization/` modules. The list above
records the top-level imports between areas; the Lean imports are
authoritative, and the root file `ParabolicRectifiability.lean` imports all
modules in a single acyclic graph.
