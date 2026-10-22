# What a reader must trust

A Lean proof is checked by the kernel, so the proofs in this library need no
trust beyond Lean, mathlib and the three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). What a reader must examine is the
*meaning* of the statements: the definitions that the headline theorems unfold
to. This page lists them.

## The specification

[`verification/Spec.lean`](../verification/Spec.lean) imports the folder
[`verification/Spec/`](../verification/Spec), which contains one file per library module that
holds a definition or a result the specification needs, at the same relative path (for example
`ParabolicRectifiability/Foundations/ADR.lean` has the specification copy
`verification/Spec/Foundations/ADR.lean`). Each specification file contains, copied from the
library:

- the definitions of that module that the checked results depend on, unchanged;
- the statements of the checked results (every theorem in a `Theorems/` folder and in
  `Main.lean`, listed in [theorems.md](theorems.md)), with `sorry` proofs;
- the few instances and elementary facts that those definitions need to be well formed
  (for example second-countability of model spaces), also with `sorry` proofs.

[`comparator.json`](../comparator.json) names `Spec` as the challenge and
`ParabolicRectifiability` as the solution, lists every theorem of the specification, and
permits only the three standard axioms. `lake comparator` then checks that the library proves
exactly these statements, over exactly these definitions (see
[verification/README.md](../verification/README.md)).

The sections below describe the core definitions: those that the main theorems unfold to. The
last section lists the further definitions used only by the other checked results. Links point to
the library declaration (`#L` gives the line). Where a bullet says "Derived members", the linked
names are projections or accessors defined next to the structure.

The mathematical conventions that these definitions encode, and the places where they differ from
the usual paper conventions, are discussed in [overview.md](overview.md).

## Ambient space, metric and measure

### `ParabolicRectifiability.Basic`

Source: [ParabolicRectifiability/Basic.lean](../ParabolicRectifiability/Basic.lean). Specification copy: [verification/Spec/Basic.lean](../verification/Spec/Basic.lean).

- [`Spatial`](../ParabolicRectifiability/Basic.lean#L23) (abbrev): Euclidean `n`-space with its `ℓ²` norm, including the one-point space at `n = 0`.
- [`Time`](../ParabolicRectifiability/Basic.lean#L26) (abbrev): Time with the square-root metric, as a distinct type.
- [`Space`](../ParabolicRectifiability/Basic.lean#L29) (abbrev): The product metric is the maximum of the spatial and snowflaked time metrics.
- [`point`](../ParabolicRectifiability/Basic.lean#L32) (def): Insert ordinary spatial and time coordinates into the parabolic metric space.

### `ParabolicRectifiability.Metric.Space`

Source: [ParabolicRectifiability/Metric/Space.lean](../ParabolicRectifiability/Metric/Space.lean). Specification copy: [verification/Spec/Metric/Space.lean](../verification/Spec/Metric/Space.lean).

- [`Coordinates`](../ParabolicRectifiability/Metric/Space.lean#L20) (abbrev): Ordinary space-time coordinates, with the library product structures.
- [`instMeasurableSpaceTime`](../ParabolicRectifiability/Metric/Space.lean#L22) (instance): The Borel sigma-algebra on the snowflaked time line.
- [`coordinatesHomeomorph`](../ParabolicRectifiability/Metric/Space.lean#L27) (def): Forget the snowflaked time metric while preserving the topology.

### `ParabolicRectifiability.Metric.Measure`

Source: [ParabolicRectifiability/Metric/Measure.lean](../ParabolicRectifiability/Metric/Measure.lean). Specification copy: [verification/Spec/Metric/Measure.lean](../verification/Spec/Metric/Measure.lean).

- [`coordinateVolume`](../ParabolicRectifiability/Metric/Measure.lean#L22) (def): Product of ordinary Euclidean spatial volume and one-dimensional Lebesgue time measure; the coordinate dimension is `n + 1`.
- [`parabolicVolume`](../ParabolicRectifiability/Metric/Measure.lean#L28) (def): Coordinate Lebesgue volume transported to `Space n`.
- [`fourierToParabolic`](../ParabolicRectifiability/Metric/Measure.lean#L44) (def): Map from analytic Euclidean coordinates to parabolic space.
- [`coordinateDilationHomeomorph`](../ParabolicRectifiability/Metric/Measure.lean#L238) (def): Coordinate form of the parabolic dilation as a homeomorphism.
- [`dilationHomeomorph`](../ParabolicRectifiability/Metric/Measure.lean#L244) (def): The invertible version of the existing parabolic dilation.

### `ParabolicRectifiability.Metric.Hausdorff`

Source: [ParabolicRectifiability/Metric/Hausdorff.lean](../ParabolicRectifiability/Metric/Hausdorff.lean). Specification copy: [verification/Spec/Metric/Hausdorff.lean](../verification/Spec/Metric/Hausdorff.lean).

- [`hausdorffP`](../ParabolicRectifiability/Metric/Hausdorff.lean#L26) (def): Unnormalized `k`-dimensional Hausdorff measure for the parabolic metric.

### `ParabolicRectifiability.Metric.Similarity`

Source: [ParabolicRectifiability/Metric/Similarity.lean](../ParabolicRectifiability/Metric/Similarity.lean). Specification copy: [verification/Spec/Metric/Similarity.lean](../verification/Spec/Metric/Similarity.lean).

- [`translationHomeomorph`](../ParabolicRectifiability/Metric/Similarity.lean#L15) (def): Subtract a space-time center through ordinary coordinates.
- [`similarity`](../ParabolicRectifiability/Metric/Similarity.lean#L35) (def): `T(q,a)(x,t) = ((x-qₓ)/a,(t-qₜ)/a²)` for a positive real scale.

## Analysis: half-time derivative and BMO

### `ParabolicRectifiability.Analysis.Coordinates`

Source: [ParabolicRectifiability/Analysis/Coordinates.lean](../ParabolicRectifiability/Analysis/Coordinates.lean). Specification copy: [verification/Spec/Analysis/Coordinates.lean](../verification/Spec/Analysis/Coordinates.lean).

- [`FourierSpace`](../ParabolicRectifiability/Analysis/Coordinates.lean#L23) (abbrev): Ordinary Euclidean analytic space, with the L² product inner product.
- [`fourierCoordinatesHomeomorph`](../ParabolicRectifiability/Analysis/Coordinates.lean#L26) (def): Ordinary spatial and time coordinates of the Euclidean L² product.

### `ParabolicRectifiability.Analysis.HalfTimeDerivative.Basic`

Source: [ParabolicRectifiability/Analysis/HalfTimeDerivative/Basic.lean](../ParabolicRectifiability/Analysis/HalfTimeDerivative/Basic.lean). Specification copy: [verification/Spec/Analysis/HalfTimeDerivative/Basic.lean](../verification/Spec/Analysis/HalfTimeDerivative/Basic.lean).

- [`HalfTimeDerivative.timeCoordinate`](../ParabolicRectifiability/Analysis/HalfTimeDerivative/Basic.lean#L20) (def): The real continuous linear time coordinate of the canonical Euclidean product.
- [`HalfTimeDerivative.symbol`](../ParabolicRectifiability/Analysis/HalfTimeDerivative/Basic.lean#L55) (def): The nonsmooth, nonnegative half-time frequency symbol.
- [`HalfTimeDerivative.polynomialWeight`](../ParabolicRectifiability/Analysis/HalfTimeDerivative/Basic.lean#L74) (def): Smooth polynomial majorant; this, rather than `symbol`, multiplies Schwartz maps.
- [`HalfTimeDerivative.polynomialMul`](../ParabolicRectifiability/Analysis/HalfTimeDerivative/Basic.lean#L102) (def): Continuous complex-linear multiplication by the proved smooth polynomial.
- [`HalfTimeDerivative.weightedLp`](../ParabolicRectifiability/Analysis/HalfTimeDerivative/Basic.lean#L123) (def): Frequency-side L² class, constructed using actual membership of the weighted function.
- [`HalfTimeDerivative.weightedLinearMap`](../ParabolicRectifiability/Analysis/HalfTimeDerivative/Basic.lean#L137) (def): Linear-map form of multiplication by the half-time symbol on Schwartz functions.
- [`HalfTimeDerivative.weightedLpCLM`](../ParabolicRectifiability/Analysis/HalfTimeDerivative/Basic.lean#L154) (def): The continuous complex-linear frequency weighting on the actual Schwartz topology.
- [`HalfTimeDerivative.halfTimeDeriv`](../ParabolicRectifiability/Analysis/HalfTimeDerivative/Basic.lean#L172) (def): Half-time derivative on complex Schwartz tests, valued in L², using the inverse L² Fourier map.

### `ParabolicRectifiability.Analysis.HalfTimeDerivative.LocalRepresentation`

Source: [ParabolicRectifiability/Analysis/HalfTimeDerivative/LocalRepresentation.lean](../ParabolicRectifiability/Analysis/HalfTimeDerivative/LocalRepresentation.lean). Specification copy: [verification/Spec/Analysis/HalfTimeDerivative/LocalRepresentation.lean](../verification/Spec/Analysis/HalfTimeDerivative/LocalRepresentation.lean).

- [`HalfTimeDerivative.compactTest`](../ParabolicRectifiability/Analysis/HalfTimeDerivative/LocalRepresentation.lean#L20) (def): A complex smooth compact test, with its genuine Schwartz membership.
- [`HalfTimeDerivative.realCompactTest`](../ParabolicRectifiability/Analysis/HalfTimeDerivative/LocalRepresentation.lean#L28) (def): Complexification of a real smooth compact test.
- [`HalfTimeDerivative.RepHalf`](../ParabolicRectifiability/Analysis/HalfTimeDerivative/LocalRepresentation.lean#L60) (def): Real compact-test representation of the half derivative on an open set.

### `ParabolicRectifiability.Analysis.ParabolicBMO`

Source: [ParabolicRectifiability/Analysis/ParabolicBMO.lean](../ParabolicRectifiability/Analysis/ParabolicBMO.lean). Specification copy: [verification/Spec/Analysis/ParabolicBMO.lean](../verification/Spec/Analysis/ParabolicBMO.lean).

- [`parabolicBallAverage`](../ParabolicRectifiability/Analysis/ParabolicBMO.lean#L22) (def): The vector average on an intrinsic parabolic ball.
- [`HasParabolicBMOBound`](../ParabolicRectifiability/Analysis/ParabolicBMO.lean#L29) (def): A bound on vector-valued mean oscillation, with local integrability stated explicitly.
- [`normalFourierComponent`](../ParabolicRectifiability/Analysis/ParabolicBMO.lean#L38) (def): One scalar normal component in ordinary Fourier coordinates.
- [`RepresentsHalfTimeDerivative`](../ParabolicRectifiability/Analysis/ParabolicBMO.lean#L46) (def): Representation of the half-time derivative in every orthonormal normal component.
- [`IsRegularVerticalFunction`](../ParabolicRectifiability/Analysis/ParabolicBMO.lean#L59) (def): The constructed regular class: `G = c + H` with compactly supported `H`, a parabolic Lipschitz bound `L`, and a vector-valued representative `g` of the half-time derivative of `H` with BMO bound `B`, where `L + B ≤ ε`.

## Geometry: models and graphs

### `ParabolicRectifiability.Geometry.AffinePlane`

Source: [ParabolicRectifiability/Geometry/AffinePlane.lean](../ParabolicRectifiability/Geometry/AffinePlane.lean). Specification copy: [verification/Spec/Geometry/AffinePlane.lean](../verification/Spec/Geometry/AffinePlane.lean).

- [`AffineSpatialPlane`](../ParabolicRectifiability/Geometry/AffinePlane.lean#L19) (structure): An affine spatial plane, anchored at its point closest to the origin. Derived members: [`toSet`](../ParabolicRectifiability/Geometry/AffinePlane.lean#L30), [`linearProjection`](../ParabolicRectifiability/Geometry/AffinePlane.lean#L34).

### `ParabolicRectifiability.Geometry.AdmissibleModels`

Source: [ParabolicRectifiability/Geometry/AdmissibleModels.lean](../ParabolicRectifiability/Geometry/AdmissibleModels.lean). Specification copy: [verification/Spec/Geometry/AdmissibleModels.lean](../verification/Spec/Geometry/AdmissibleModels.lean).

- [`HorizontalModel`](../ParabolicRectifiability/Geometry/AdmissibleModels.lean#L25) (structure): An affine spatial `k`-plane at the recorded fixed time, with `k ≥ 1`. Derived members: [`toSet`](../ParabolicRectifiability/Geometry/AdmissibleModels.lean#L56).
- [`VerticalModel`](../ParabolicRectifiability/Geometry/AdmissibleModels.lean#L32) (structure): An affine spatial plane times all time, with parabolic dimension `k`. Derived members: [`toSet`](../ParabolicRectifiability/Geometry/AdmissibleModels.lean#L102).
- [`AdmissibleModel`](../ParabolicRectifiability/Geometry/AdmissibleModels.lean#L39) (abbrev): Tagged union of horizontal and vertical models of the same parabolic dimension.
- [`FamilyKind`](../ParabolicRectifiability/Geometry/AdmissibleModels.lean#L42) (inductive): Choice of horizontal, vertical or mixed planes in a fitting problem.
- [`Models`](../ParabolicRectifiability/Geometry/AdmissibleModels.lean#L48) (def): The actual type of fitting models for the selected family; empty dimensions give an empty type rather than a fictitious zero-rank model.
- [`AdmissibleModel.toSet`](../ParabolicRectifiability/Geometry/AdmissibleModels.lean#L155) (def): The represented subset of an admissible (horizontal or vertical) model.
- [`modelSet`](../ParabolicRectifiability/Geometry/AdmissibleModels.lean#L196) (def): The represented set, uniformly across the three family choices.

### `ParabolicRectifiability.Geometry.ModelDistance`

Source: [ParabolicRectifiability/Geometry/ModelDistance.lean](../ParabolicRectifiability/Geometry/ModelDistance.lean). Specification copy: [verification/Spec/Geometry/ModelDistance.lean](../verification/Spec/Geometry/ModelDistance.lean).

- [`modelCost`](../ParabolicRectifiability/Geometry/ModelDistance.lean#L20) (def): Squared distance to the represented set in the parabolic metric.

### `ParabolicRectifiability.Geometry.SubspaceCoordinates`

Source: [ParabolicRectifiability/Geometry/SubspaceCoordinates.lean](../ParabolicRectifiability/Geometry/SubspaceCoordinates.lean). Specification copy: [verification/Spec/Geometry/SubspaceCoordinates.lean](../verification/Spec/Geometry/SubspaceCoordinates.lean).

- [`subspaceCoordinates`](../ParabolicRectifiability/Geometry/SubspaceCoordinates.lean#L23) (def): Orthonormal coordinates constructed on the intrinsic spatial subspace.
- [`normalCoordinates`](../ParabolicRectifiability/Geometry/SubspaceCoordinates.lean#L39) (def): Orthonormal coordinates constructed on the actual normal subspace.
- [`subspaceCoordinatesHomeomorph`](../ParabolicRectifiability/Geometry/SubspaceCoordinates.lean#L47) (def): Coordinates on the vertical base `W x R`: homeomorphism with a standard coordinate space.
- [`subspaceToFourierHomeomorph`](../ParabolicRectifiability/Geometry/SubspaceCoordinates.lean#L71) (def): Homeomorphism from the vertical base `W x R` to analytic (L2-product) coordinates.
- [`subspaceToFourier`](../ParabolicRectifiability/Geometry/SubspaceCoordinates.lean#L75) (def): The underlying map of `subspaceToFourierHomeomorph`.
- [`SubspaceSpace`](../ParabolicRectifiability/Geometry/SubspaceCoordinates.lean#L117) (abbrev): The intrinsic vertical base with the inherited maximum parabolic metric.
- [`subspaceTimeHomeomorph`](../ParabolicRectifiability/Geometry/SubspaceCoordinates.lean#L166) (def): Homeomorphism splitting the vertical base into its spatial and time factors.
- [`subspaceTimeMeasurableEquiv`](../ParabolicRectifiability/Geometry/SubspaceCoordinates.lean#L169) (def): The same splitting as a measurable equivalence.
- [`intrinsicParabolicVolume`](../ParabolicRectifiability/Geometry/SubspaceCoordinates.lean#L182) (def): Intrinsic reference volume: spatial inner-product volume times real time volume, transported only through the inverse snowflake time coordinate map.
- [`subspaceFourierToParabolic`](../ParabolicRectifiability/Geometry/SubspaceCoordinates.lean#L207) (def): Map from analytic coordinates back to the parabolic vertical base.

### `ParabolicRectifiability.Geometry.Graphs`

Source: [ParabolicRectifiability/Geometry/Graphs.lean](../ParabolicRectifiability/Geometry/Graphs.lean). Specification copy: [verification/Spec/Geometry/Graphs.lean](../verification/Spec/Geometry/Graphs.lean).

- [`HorizontalGraph`](../ParabolicRectifiability/Geometry/Graphs.lean#L21) (structure): A graph over an arbitrary subset of a spatial `k`-plane, with normal and time maps satisfying `max ‖normal u-normal v‖ (sqrt |time u-time v|) ≤ ε * ‖u-v‖`. Derived members: [`image`](../ParabolicRectifiability/Geometry/Graphs.lean#L34).
- [`RegularVerticalGraph`](../ParabolicRectifiability/Geometry/Graphs.lean#L41) (structure): A full regular vertical graph. Derived members: [`image`](../ParabolicRectifiability/Geometry/Graphs.lean#L51).
- [`HasHorizontalGraphCover`](../ParabolicRectifiability/Geometry/Graphs.lean#L58) (def): A countable horizontal cover with a Hausdorff-null exception.
- [`HasRegularVerticalGraphCover`](../ParabolicRectifiability/Geometry/Graphs.lean#L64) (def): A countable cover by full regular vertical graphs, using the same outer Hausdorff-null convention, including for nonmeasurable graph images.

## Beta numbers and square energies

### `ParabolicRectifiability.Measure.CountableFitting`

Source: [ParabolicRectifiability/Measure/CountableFitting.lean](../ParabolicRectifiability/Measure/CountableFitting.lean). Specification copy: [verification/Spec/Measure/CountableFitting.lean](../verification/Spec/Measure/CountableFitting.lean).

- [`fit`](../ParabolicRectifiability/Measure/CountableFitting.lean#L19) (def): Unnormalized integral of the already squared geometric distance.

### `ParabolicRectifiability.Measure.Beta`

Source: [ParabolicRectifiability/Measure/Beta.lean](../ParabolicRectifiability/Measure/Beta.lean). Specification copy: [verification/Spec/Measure/Beta.lean](../verification/Spec/Measure/Beta.lean).

- [`betaSq`](../ParabolicRectifiability/Measure/Beta.lean#L73) (def): Natural squared beta number: for `r > 0`, this is `r^(-k-2) * inf_L ∫_{ball z r} dist(w,L)^2 dμ(w)`, valued in `ℝ≥0∞`.

### `ParabolicRectifiability.Measure.ScaleEnergy`

Source: [ParabolicRectifiability/Measure/ScaleEnergy.lean](../ParabolicRectifiability/Measure/ScaleEnergy.lean). Specification copy: [verification/Spec/Measure/ScaleEnergy.lean](../verification/Spec/Measure/ScaleEnergy.lean).

- [`scaleMeasure`](../ParabolicRectifiability/Measure/ScaleEnergy.lean#L16) (def): Lebesgue measure on positive radii with exactly the density `1/r`.
- [`squareEnergy`](../ParabolicRectifiability/Measure/ScaleEnergy.lean#L102) (def): The extended nonnegative scale integral of `betaSq` against `dr/r` on `0 < r < R`.
- [`exceptionalSet`](../ParabolicRectifiability/Measure/ScaleEnergy.lean#L117) (def): Points in the open unit parabolic ball where the mixed-family energy of the original source, integrated over `0 < r < 2`, exceeds `ofReal M`.

### `ParabolicRectifiability.Measure.BetaLaws`

Source: [ParabolicRectifiability/Measure/BetaLaws.lean](../ParabolicRectifiability/Measure/BetaLaws.lean). Specification copy: [verification/Spec/Measure/BetaLaws.lean](../verification/Spec/Measure/BetaLaws.lean).

- [`rescaledSource`](../ParabolicRectifiability/Measure/BetaLaws.lean#L103) (def): The original source rescaled by its model dimension k, not ambient dimension.

## Foundations: classes of measures, graphs and densities

### `ParabolicRectifiability.Foundations.HalfTimeDerivative`

Source: [ParabolicRectifiability/Foundations/HalfTimeDerivative.lean](../ParabolicRectifiability/Foundations/HalfTimeDerivative.lean). Specification copy: [verification/Spec/Foundations/HalfTimeDerivative.lean](../verification/Spec/Foundations/HalfTimeDerivative.lean).

- [`Foundations.halfTimeSpatialIntegrand`](../ParabolicRectifiability/Foundations/HalfTimeDerivative.lean#L47) (def): The spatial integrand of the ordered pairing at time `t`: `u ↦ G(u,t) (|D_t|^{1/2}ψ)(u,t)` on `ℝ^m`.
- [`Foundations.halfTimeSpatialBracket`](../ParabolicRectifiability/Foundations/HalfTimeDerivative.lean#L52) (def): The spatial bracket of the ordered pairing: `t ↦ ∫_{ℝ^m} G(u,t) (|D_t|^{1/2}ψ)(u,t) du`.
- [`Foundations.halfTimeWindowPairing`](../ParabolicRectifiability/Foundations/HalfTimeDerivative.lean#L60) (def): The ordered windowed pairing, before the limit: `∫_{[-R,R]} [∫_{ℝ^m} G(u,t) (|D_t|^{1/2}ψ)(u,t) du] dt`.
- [`Foundations.RepresentsHomogeneousHalfTimeDerivative`](../ParabolicRectifiability/Foundations/HalfTimeDerivative.lean#L78) (def): Scalar representation of the homogeneous half-time derivative in ordinary coordinates: `g` is locally integrable and, for every real compact smooth test `φ` of total integral zero, * for a.e.
- [`Foundations.RepresentsGeneralHalfTimeDerivative`](../ParabolicRectifiability/Foundations/HalfTimeDerivative.lean#L91) (def): Vector representation on a vertical base: each orthonormal normal component of `g` represents the homogeneous derivative of the same component of `G`, in the ordinary coordinates of `SubspaceSpace W`.
- [`Foundations.IsGeneralRegularVerticalFunction`](../ParabolicRectifiability/Foundations/HalfTimeDerivative.lean#L101) (def): General regular vertical function on the vertical base `W × ℝ`: a parabolic Lipschitz bound `L`, a representative `g` of the homogeneous derivative with vector parabolic BMO bound `B`, and `L + B ≤ ε`.
- [`Foundations.standardBallAverage`](../ParabolicRectifiability/Foundations/HalfTimeDerivative.lean#L116) (def): The average of a real function over a parabolic ball of `Space m`.
- [`Foundations.HasStandardParabolicBMOBound`](../ParabolicRectifiability/Foundations/HalfTimeDerivative.lean#L122) (def): A real parabolic BMO bound on the standard base, with local integrability stated explicitly (the seminorm over unrestricted centres and positive radii).
- [`Foundations.RepresentsStandardHalfTimeDerivative`](../ParabolicRectifiability/Foundations/HalfTimeDerivative.lean#L130) (def): Representation of the homogeneous half-time derivative of a real function on the standard base, read in ordinary coordinates.
- [`Foundations.HasHalfTimeBMOBound`](../ParabolicRectifiability/Foundations/HalfTimeDerivative.lean#L142) (def): `[|D_t|^{1/2}F]_{BMO_P} ≤ B` for a real function on the standard base: `F` is parabolic Lipschitz with some constant, and some representative of the homogeneous derivative has real parabolic BMO bound `B`.
- [`Foundations.HasCoordinateHalfTimeBMOBound`](../ParabolicRectifiability/Foundations/HalfTimeDerivative.lean#L151) (def): `max_α [|D_t|^{1/2}F^α]_{BMO_P} ≤ B` for the Euclidean coordinates of `F : ℝ^m × ℝ → ℝ^d`: every coordinate satisfies the real bound, so in particular every coordinate is parabolic Lipschitz (with its own existential constant, not charged against `B`).

### `ParabolicRectifiability.Foundations.Graphs`

Source: [ParabolicRectifiability/Foundations/Graphs.lean](../ParabolicRectifiability/Foundations/Graphs.lean). Specification copy: [verification/Spec/Foundations/Graphs.lean](../verification/Spec/Foundations/Graphs.lean).

- [`Foundations.GeneralRegularVerticalGraph`](../ParabolicRectifiability/Foundations/Graphs.lean#L35) (structure): A full general regular vertical graph `{(a + u + G(u,t), t) : (u,t) ∈ W × ℝ}` with `dim W + 2 = k`. Derived members: [`direction`](../ParabolicRectifiability/Foundations/Graphs.lean#L48), [`map`](../ParabolicRectifiability/Foundations/Graphs.lean#L48), [`image`](../ParabolicRectifiability/Foundations/Graphs.lean#L52).
- [`Foundations.HasGeneralRegularVerticalGraphCover`](../ParabolicRectifiability/Foundations/Graphs.lean#L62) (def): A countable cover of `K` by full general regular vertical graph images of total seminorm at most `ε`, with a remainder of zero `H_P^k` outer measure.
- [`Foundations.OrdinaryVerticalGraph`](../ParabolicRectifiability/Foundations/Graphs.lean#L68) (structure): An ordinary full vertical graph: the fields of a full vertical graph with only a parabolic Lipschitz bound at most `L`.
- [`Foundations.HasTypedGraphCover`](../ParabolicRectifiability/Foundations/Graphs.lean#L94) (def): Typed set cover at tolerance `ε`, modulo Hausdorff outer measure.
- [`Foundations.IsCarriedByFiniteNormGraphs`](../ParabolicRectifiability/Foundations/Graphs.lean#L119) (def): `μ` is carried by countably many typed graphs of finite norm: every graph has its own finite slope or regular norm `ε i`, and `μ` vanishes on the complement of the union of their images.
- [`Foundations.IsRegularlyRectifiableMeasure`](../ParabolicRectifiability/Foundations/Graphs.lean#L137) (def): Regular measure rectifiability of type `T`: `μ ≪ H_P^k` and a countable typed graph carrier, with each graph allowed its own finite slope or total regular seminorm.
- [`Foundations.HasTypedMeasureCover`](../ParabolicRectifiability/Foundations/Graphs.lean#L147) (def): A countable typed graph carrier at a prescribed bound `ε`: `μ((⋃ images)ᶜ) = 0`.

### `ParabolicRectifiability.Foundations.BetaPow`

Source: [ParabolicRectifiability/Foundations/BetaPow.lean](../ParabolicRectifiability/Foundations/BetaPow.lean). Specification copy: [verification/Spec/Foundations/BetaPow.lean](../verification/Spec/Foundations/BetaPow.lean).

- [`Foundations.fitPow`](../ParabolicRectifiability/Foundations/BetaPow.lean#L38) (def): The unnormalized `p`-fitting integral `∫_{P(z,r)} d_P(w,L)^p dμ(w)` of one model, with the parabolic distance raised to the real power `p` in `ℝ≥0∞`.
- [`Foundations.betaPow`](../ParabolicRectifiability/Foundations/BetaPow.lean#L45) (def): The beta-`p` fitting quantity `B_p(z,r) = r^{-k-p} inf_{L ∈ T} ∫_{P(z,r)} d_P(w,L)^p dμ(w)` for `r > 0`, and `0` for `r ≤ 0` (the `betaSq` convention).
- [`Foundations.energyS`](../ParabolicRectifiability/Foundations/BetaPow.lean#L61) (def): The quadratic beta-`p` energy `S_p^a(z) = ∫_{(0,a)} B_p(z,r)^{2/p} dr/r`, valued in `ℝ≥0∞`.
- [`Foundations.energyT`](../ParabolicRectifiability/Foundations/BetaPow.lean#L70) (def): The `p`-power beta-`p` energy `T_p^a(z) = ∫_{(0,a)} B_p(z,r) dr/r`, valued in `ℝ≥0∞` and using the full measure argument.

### `ParabolicRectifiability.Foundations.Density`

Source: [ParabolicRectifiability/Foundations/Density.lean](../ParabolicRectifiability/Foundations/Density.lean). Specification copy: [verification/Spec/Foundations/Density.lean](../verification/Spec/Foundations/Density.lean).

- [`Foundations.densityRatio`](../ParabolicRectifiability/Foundations/Density.lean#L27) (def): The ball-mass ratio `r^{-k} μ(P(z,r)) = μ(P(z,r)) / r^k`, in `ℝ≥0∞`.
- [`Foundations.lowerDensity`](../ParabolicRectifiability/Foundations/Density.lean#L31) (def): Lower `k`-density `Θ_*^k(μ,z) = liminf_{r↓0} r^{-k} μ(P(z,r))`.
- [`Foundations.upperDensity`](../ParabolicRectifiability/Foundations/Density.lean#L35) (def): Upper `k`-density `Θ^{k,*}(μ,z) = limsup_{r↓0} r^{-k} μ(P(z,r))`.

### `ParabolicRectifiability.Foundations.DensityConditions`

Source: [ParabolicRectifiability/Foundations/DensityConditions.lean](../ParabolicRectifiability/Foundations/DensityConditions.lean). Specification copy: [verification/Spec/Foundations/DensityConditions.lean](../verification/Spec/Foundations/DensityConditions.lean).

- [`Foundations.HasPositiveUpperFiniteLowerDensity`](../ParabolicRectifiability/Foundations/DensityConditions.lean#L26) (def): Structural condition (a) of the integral criterion: `Θ^{k,*}(μ,·) > 0` and `Θ_*^k(μ,·) < ∞` at `μ`-almost every point.
- [`Foundations.HasPositiveFiniteUpperDensity`](../ParabolicRectifiability/Foundations/DensityConditions.lean#L32) (def): Structural condition (b) of the integral criterion: `0 < Θ^{k,*}(μ,·) < ∞` at `μ`-almost every point.

### `ParabolicRectifiability.Foundations.Carriers`

Source: [ParabolicRectifiability/Foundations/Carriers.lean](../ParabolicRectifiability/Foundations/Carriers.lean). Specification copy: [verification/Spec/Foundations/Carriers.lean](../verification/Spec/Foundations/Carriers.lean).

- [`Foundations.HasBorelSigmaFiniteHausdorffCarrier`](../ParabolicRectifiability/Foundations/Carriers.lean#L28) (def): `μ` has a Borel sigma-finite `H_P^k` carrier: countably many Borel sets of finite `H_P^k` measure whose union `E` carries `μ`, i.e.
- [`Foundations.IsIntrinsicSource`](../ParabolicRectifiability/Foundations/Carriers.lean#L37) (def): The intrinsic source class: `μ ≪ H_P^k` and a Borel carrier `E = ⋃_j E_j` with `μ(X \ E) = 0` and `H_P^k(E_j) < ∞` for every `j`.

### `ParabolicRectifiability.Foundations.ADR`

Source: [ParabolicRectifiability/Foundations/ADR.lean](../ParabolicRectifiability/Foundations/ADR.lean). Specification copy: [verification/Spec/Foundations/ADR.lean](../verification/Spec/Foundations/ADR.lean).

- [`Foundations.IsADR`](../ParabolicRectifiability/Foundations/ADR.lean#L53) (def): Global `A`-Ahlfors–David regularity in dimension `k`: `A⁻¹ r^k ≤ μ(P(z,r)) ≤ A r^k` for every `z ∈ E = supp μ` and every `r > 0`.

### `ParabolicRectifiability.Foundations.SupportBounds`

Source: [ParabolicRectifiability/Foundations/SupportBounds.lean](../ParabolicRectifiability/Foundations/SupportBounds.lean). Specification copy: [verification/Spec/Foundations/SupportBounds.lean](../verification/Spec/Foundations/SupportBounds.lean).

- [`Foundations.HasRegularSupportBounds`](../ParabolicRectifiability/Foundations/SupportBounds.lean#L43) (structure): The bundle of support conclusions at center `a`, scale `R` and constant `C` for typed supports `K_H`, `K_V`: compactness, containment in the closed ball, empty supports for empty types, typed graph covers at every tolerance, and the global and local Hausdorff, separated-set, tube and packing bounds.

### `ParabolicRectifiability.Foundations.GraphDomainCover`

Source: [ParabolicRectifiability/Foundations/GraphDomainCover.lean](../ParabolicRectifiability/Foundations/GraphDomainCover.lean). Specification copy: [verification/Spec/Foundations/GraphDomainCover.lean](../verification/Spec/Foundations/GraphDomainCover.lean).

- [`Foundations.horizontalGraphMap`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L33) (def): The graph map `u ↦ (a + u + g(u), h(u))` of a horizontal subset graph, on its actual domain.
- [`Foundations.horizontalPreimage`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L38) (def): `Φ⁻¹(S)` for a horizontal graph, as a subset of the full base `U`.
- [`Foundations.horizontalPatch`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L43) (def): The horizontal patch `Φ(D ∩ B(p,ρ))`, with trace preimage `D = Φ⁻¹(F)`.
- [`Foundations.verticalPatch`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L49) (def): The vertical patch `Φ(B(p,ρ))`, using the whole parabolic base ball.
- [`Foundations.HorizontalDomainData`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L60) (structure): The horizontal data of a graph-domain cover of the carrier `K`, at tolerance `ε` and mesh `δ`: countably many graph maps, pairwise disjoint Borel traces in `K` covering it modulo `H_P^k`, Borel trace preimages in the full bases, and countably many patches ... Derived members: [`graph`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L139), [`patchIndex`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L135), [`patchGraph`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L139), [`centerPoint`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L135), [`baseBall`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L139), [`patch`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L143), [`charge`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L148), [`traceVolume`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L152), [`localIndex`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L157), [`totalCharge`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L161), [`localCharge`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L164).
- [`Foundations.VerticalDomainData`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L97) (structure): The vertical data of a graph-domain cover of the carrier `K`, at tolerance `ε` and mesh `δ`. Derived members: [`graph`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L139), [`patchIndex`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L135), [`patchGraph`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L139), [`centerPoint`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L173), [`baseBall`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L177), [`patch`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L181), [`charge`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L185), [`traceVolume`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L191), [`localIndex`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L196), [`totalCharge`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L200), [`localCharge`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L203).
- [`Foundations.GraphDomainCover`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L214) (structure): A graph-domain cover of the carriers `(K_H, K_V)` with bound `C`, tolerance `ε` and mesh `δ`: typed graph maps, disjoint traces, patches of radius at most `δ`, a trace estimate for Borel sets, and total and local charge bounds in terms of `H_P^k`. Described in [theorems.md](theorems.md) (item 10).

## Decomposition outputs

### `ParabolicRectifiability.Specifications.Rectifiability`

Source: [ParabolicRectifiability/Specifications/Rectifiability.lean](../ParabolicRectifiability/Specifications/Rectifiability.lean). Specification copy: [verification/Spec/Specifications/Rectifiability.lean](../verification/Spec/Specifications/Rectifiability.lean).

- [`RetainedSets`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L30) (structure): Retained Borel pieces of the original source inside the open unit ball. Derived members: [`horizontalMeasure`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L44), [`verticalMeasure`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L48), [`remainderMeasure`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L53), [`horizontalSupport`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L58), [`verticalSupport`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L63), [`supportUnion`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L68).
- [`HasRectifiabilityContentBounds`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L80) (structure): Five quantitative bounds with one constant `C`: local `k`-dimensional Hausdorff measure, finite separated sets, ambient tubular volume, and finite or countable disjoint-ball packing with individually varying radii.
- [`IsRectifiabilityDecomposition`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L106) (structure): The output of the rectifiable Reifenberg decomposition for retained sets `D`: the measure identity, the remainder bound `C M + Γ` in the unit ball, compact supports in the closed unit ball, vanishing for empty types, typed graph covers of the supports at every tolerance, and the content bounds. See [theorems.md](theorems.md) (Part I).
- [`MainRectifiabilityStatement`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L127) (def): The mixed-family rectifiable Reifenberg statement: a constant `C(n)` is chosen before `k`, the source and the thresholds, and the retained sets are chosen before any graph tolerance. See [theorems.md](theorems.md) (item 3).
- [`FixedFamilyRectifiabilityStatement`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L139) (def): The fixed-family rectifiable Reifenberg statement for a family `T`, with availability `Nonempty (Models n k T)` as a hypothesis and the opposite retained measure and support zero. See [theorems.md](theorems.md) (item 4).
- [`AmbientRectifiabilityStatement`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L152) (def): The ambient statement at `k = n + 2`: remainder zero in the unit ball, with no energy hypothesis. See [theorems.md](theorems.md) (item 5).

### `ParabolicRectifiability.Decomposition.Interfaces`

Source: [ParabolicRectifiability/Decomposition/Interfaces.lean](../ParabolicRectifiability/Decomposition/Interfaces.lean). Specification copy: [verification/Spec/Decomposition/Interfaces.lean](../verification/Spec/Decomposition/Interfaces.lean).

- [`HasFamilyDecomposition`](../ParabolicRectifiability/Decomposition/Interfaces.lean#L171) (def): The family-specific rectifiable Reifenberg output: retained sets `D` with `IsRectifiabilityDecomposition` and the opposite type vanishing for a fixed family.

### `ParabolicRectifiability.Enhancements.Decomposition`

Source: [ParabolicRectifiability/Enhancements/Decomposition.lean](../ParabolicRectifiability/Enhancements/Decomposition.lean). Specification copy: [verification/Spec/Enhancements/Decomposition.lean](../verification/Spec/Enhancements/Decomposition.lean).

- [`Enhancements.HasScaledGraphDomainCover`](../ParabolicRectifiability/Enhancements/Decomposition.lean#L64) (def): A graph-domain cover whose total charge is at most `C R^k` and whose local charge at `(q,s)`, `0 < s ≤ R`, is at most `C s^k`, for the union and each typed subfamily.
- [`Enhancements.IsLocalEnhancedDecomposition`](../ParabolicRectifiability/Enhancements/Decomposition.lean#L85) (structure): The enhanced restriction decomposition on `P(a,R)` for a family `T`, without its loss bound: disjoint Borel sets `E_H, E_V`, the restriction identity, unavailable and disallowed types vanish, `HasRegularSupportBounds` for the actual supports, and graph-domain covers at every tolerance and mesh. See [theorems.md](theorems.md) (item 11).

## Statements: integral criteria and canonical decomposition

### `ParabolicRectifiability.IntegralCanonical.Defs`

Source: [ParabolicRectifiability/IntegralCanonical/Defs.lean](../ParabolicRectifiability/IntegralCanonical/Defs.lean). Specification copy: [verification/Spec/IntegralCanonical/Defs.lean](../verification/Spec/IntegralCanonical/Defs.lean).

- [`IntegralCanonical.finiteEnergySet`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L50) (def): The full-source finite-energy set `E_T = {z : S^R_{μ,T}(z) < ∞}`: horizontal, vertical, and mixed choices give `E_H`, `E_V`, and `G`.
- [`IntegralCanonical.pureSet`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L55) (def): The infinite-mixed-energy set `E_+ = X \ G`, `G = {S^R_{μ,mix} < ∞}`.
- [`IntegralCanonical.horizontalPart`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L61) (def): The canonical horizontal restriction `μ_H = μ⌊{S^R_{μ,H} < ∞}`.
- [`IntegralCanonical.verticalPart`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L67) (def): The canonical vertical restriction `μ_V = μ⌊{S^R_{μ,V} < ∞}`, selected using the full original source.
- [`IntegralCanonical.purePart`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L71) (def): The canonical pure part `μ_+ = μ⌊E_+`.
- [`IntegralCanonical.IsGraphPure`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L77) (def): Graph purity: outer measure zero on every horizontal graph of finite slope and on every full general regular vertical graph of finite total seminorm.
- [`IntegralCanonical.StructuralCondition`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L87) (def): The three structural conditions (a), (b), (c) of the integral criterion, indexed by `Fin 3` in this order.
- [`IntegralCanonical.boundedCylinders`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L97) (def): The bounded cylinders `P(z,r)`, `z ∈ X`, `0 < r < ∞`: open parabolic balls of positive real radius.
- [`IntegralCanonical.originCylinders`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L101) (def): The reduced testing family `P(0,j)`, `j ∈ ℕ`, `j ≥ 1`.
- [`IntegralCanonical.CappedTailTest`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L108) (def): Test (1), the vanishing capped tail: on every tested set `A`, `lim_{ρ↓0} ∫_A min{1, T_ρ} dμ = 0`, where `T_ρ = S^ρ_{μ,T}`.
- [`IntegralCanonical.CappedValueTest`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L116) (def): Test (2), the vanishing normalized capped energy: on every tested set `A`, `lim_{L→∞} L^{-1} ∫_A min{S, L} dμ = 0`, where `S = S^R_{μ,T}`.
- [`IntegralCanonical.CompactExhaustionTest`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L126) (def): Test (3), the compact integrable exhaustion: increasing compact sets `K_j` with `μ(X \ ⋃_j K_j) = 0` and `∫_{K_j} S dμ < ∞` for every `j`, where `S = S^R_{μ,T}`.
- [`IntegralCanonical.PositiveWeightTest`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L134) (def): Test (4), the strictly positive weight: a Borel `w : X → (0,1]` with `∫_A w S dμ < ∞` on every tested set `A`, where `S = S^R_{μ,T}`.
- [`IntegralCanonical.IsAdmissibleGauge`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L142) (def): An admissible gauge `Φ : [0,∞) → [0,∞)` of test (5): continuous, nondecreasing, concave and unbounded on `[0,∞)`, with `Φ(0) = 0` and nonnegative values.
- [`IntegralCanonical.extendedGauge`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L148) (def): The extension of a gauge to `[0,∞]` with `Φ(∞) = ∞`: a finite value `x` is sent to `Φ(x)` and `⊤` to `⊤`.
- [`IntegralCanonical.AdaptiveGaugeTest`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L154) (def): Test (5), the adaptive concave gauge: for every tested set `A` there is an admissible gauge `Φ_A` with `∫_A Φ_A(S) dμ < ∞`, where `S = S^R_{μ,T}` and `Φ_A(∞) = ∞`.
- [`IntegralCanonical.IntegralTest`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L162) (def): The five integral tests (1)–(5) of the integral equivalences, indexed by `Fin 5` in this order (index `j` is test `(j+1)`), for the family `T`, the endpoint `R` of `S = S^R_{μ,T}`, and the family `𝒜` of tested sets.

### `ParabolicRectifiability.IntegralCanonical.Statements.Canonical`

Source: [ParabolicRectifiability/IntegralCanonical/Statements/Canonical.lean](../ParabolicRectifiability/IntegralCanonical/Statements/Canonical.lean). Specification copy: [verification/Spec/IntegralCanonical/Statements/Canonical.lean](../verification/Spec/IntegralCanonical/Statements/Canonical.lean).

- [`IntegralCanonical.IsCanonicalDecomposition`](../ParabolicRectifiability/IntegralCanonical/Statements/Canonical.lean#L51) (structure): The conclusions of the canonical decomposition theorem for the source `μ`, dimension `k` and endpoint `R`.
- [`IntegralCanonical.CanonicalDecompositionStatement`](../ParabolicRectifiability/IntegralCanonical/Statements/Canonical.lean#L97) (def): The canonical decomposition theorem: for a locally Radon source that is intrinsic or has positive finite upper density a.e., every `R > 0` gives `IsCanonicalDecomposition k μ R`. See [theorems.md](theorems.md) (item 7).

### `ParabolicRectifiability.IntegralCanonical.Statements.Integral`

Source: [ParabolicRectifiability/IntegralCanonical/Statements/Integral.lean](../ParabolicRectifiability/IntegralCanonical/Statements/Integral.lean). Specification copy: [verification/Spec/IntegralCanonical/Statements/Integral.lean](../verification/Spec/IntegralCanonical/Statements/Integral.lean).

- [`IntegralCanonical.IntegralCriterionStatement`](../ParabolicRectifiability/IntegralCanonical/Statements/Integral.lean#L70) (def): The fifteen integral criteria: each structural condition (a), (b), (c) paired with each integral test (1) to (5) characterizes regular type-`T` rectifiability, with reduced testing and density and cover consequences. See [theorems.md](theorems.md) (item 8).

## Statements: characterizations, enhancements and beta-p

### `ParabolicRectifiability.Characterization.Statements.Main`

Source: [ParabolicRectifiability/Characterization/Statements/Main.lean](../ParabolicRectifiability/Characterization/Statements/Main.lean). Specification copy: [verification/Spec/Characterization/Statements/Main.lean](../verification/Spec/Characterization/Statements/Main.lean).

- [`Characterization.QualitativeCharacterizationStatement`](../ParabolicRectifiability/Characterization/Statements/Main.lean#L55) (def): The qualitative characterization of regularly rectifiable measures by square energies and density or carrier conditions, with one- and every-endpoint forms. See [theorems.md](theorems.md) (item 6).

### `ParabolicRectifiability.QuantitativeCharacterization.References`

Source: [ParabolicRectifiability/QuantitativeCharacterization/References.lean](../ParabolicRectifiability/QuantitativeCharacterization/References.lean). Specification copy: [verification/Spec/QuantitativeCharacterization/References.lean](../verification/Spec/QuantitativeCharacterization/References.lean).

- [`QuantitativeCharacterization.dyadicCube`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L45) (def): The closed cube of side `λ 2^j` of the dyadic grid with origin `c` and scale `λ`: `{x : c_α + λ 2^j m_α ≤ x_α ≤ c_α + λ 2^j (m_α + 1) for every coordinate α}`.
- [`QuantitativeCharacterization.setDist`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L54) (def): The distance `dist(Q,D) = inf_{x ∈ Q} dist(x,D)` from a set `Q` to a set `D`.
- [`QuantitativeCharacterization.HorizontalReference`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L60) (structure): A horizontal `L`-reference with all of its data. Derived members: [`map`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L114), [`measure`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L118), [`carrier`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L123).
- [`QuantitativeCharacterization.VerticalReference`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L133) (structure): A vertical `L`-reference: a spatial rank `m` with `m + 2 = k < n + 2`, and `F : ℝ^m × ℝ → ℝ^n` such that `Φ(u,t) = (F(u,t),t)` is `L`-bi-Lipschitz for the max parabolic metrics of `Space m` and `X`, and every Euclidean coordinate of `F` has a pure-time ... Derived members: [`spatialRank`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L152), [`map`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L152), [`carrier`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L160).
- [`QuantitativeCharacterization.Reference`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L167) (inductive): A typed `L`-reference: horizontal, vertical, or the ambient reference `(X, L^{n+1})` at `k = n + 2`. Derived members: [`carrier`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L189).

### `ParabolicRectifiability.QuantitativeCharacterization.Coverings`

Source: [ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean). Specification copy: [verification/Spec/QuantitativeCharacterization/Coverings.lean](../verification/Spec/QuantitativeCharacterization/Coverings.lean).

- [`QuantitativeCharacterization.rootCarlesonSup`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L42) (def): The normalized root supremum `sup_{a ∈ S, R > 0} R^{-k} ∫_{P(a,R)} f(R,z) dμ(z)` of a scale-dependent energy `f(R,·)`, in `ℝ≥0∞`.
- [`QuantitativeCharacterization.carlesonEnergy`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L50) (def): The Carleson energy `M_β(μ) = sup_{a ∈ E, R > 0} R^{-k} ∫_{P(a,R)} ∫_0^R β_μ(z,r)² dr/r dμ(z)`, with the natural mixed-family beta of the whole original source.
- [`QuantitativeCharacterization.pointScaleMeasure`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L70) (def): The point–scale measure `dμ dr/r` on `X × ℝ`.
- [`QuantitativeCharacterization.rootPairs`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L74) (def): The tested point–scale pairs `(P₀ ∩ E) × (0,R)` of the root `P₀ = P(a,R)`.
- [`QuantitativeCharacterization.RegularMixedCovering`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L83) (structure): A `(K,L)`-regular mixed parabolic covering of `μ` on `P₀ = P(a,R)`.
- [`QuantitativeCharacterization.IsQuantitativelyMixedRectifiable`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L205) (def): `(K,L)`-quantitative mixed parabolic rectifiability: `μ ≪ H_P^k` and every support-centred root `P(a,R)`, `a ∈ supp μ`, `R > 0`, has a `(K,L)`-regular mixed parabolic covering.

### `ParabolicRectifiability.QuantitativeCharacterization.Statements.Characterization`

Source: [ParabolicRectifiability/QuantitativeCharacterization/Statements/Characterization.lean](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Characterization.lean). Specification copy: [verification/Spec/QuantitativeCharacterization/Statements/Characterization.lean](../verification/Spec/QuantitativeCharacterization/Statements/Characterization.lean).

- [`QuantitativeCharacterization.MainTheoremBounds`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Characterization.lean#L39) (def): For given constants `L₀, C`: for every `μ ≠ 0` Radon with unbounded support and `A`-ADR, `M_β(μ) < ∞` iff `μ` is `(K,L₀)`-quantitatively mixed rectifiable for some `K ≥ 1`, with the forward bound `K ≤ C(1+M_β)` and the reverse bound `M_β ≤ C K`.
- [`QuantitativeCharacterization.QuantitativeCharacterizationStatement`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Characterization.lean#L63) (def): The quantitative characterization: for `n ≥ 1`, `1 ≤ k ≤ n + 2` and `A ≥ 1`, constants `L₀, C` and `C_rev` exist, fixed before the measure, with the properties stated in [theorems.md](theorems.md) (item 9).

### `ParabolicRectifiability.Enhancements.Statements.GraphDomains`

Source: [ParabolicRectifiability/Enhancements/Statements/GraphDomains.lean](../ParabolicRectifiability/Enhancements/Statements/GraphDomains.lean). Specification copy: [verification/Spec/Enhancements/Statements/GraphDomains.lean](../verification/Spec/Enhancements/Statements/GraphDomains.lean).

- [`Enhancements.FixedCarrierGraphDomainStatement`](../ParabolicRectifiability/Enhancements/Statements/GraphDomains.lean#L41) (def): Graph-domain covers on a compact carrier of finite `H_P^k` measure with typed graph covers at every tolerance, with the local-growth charge bound. See [theorems.md](theorems.md) (item 10).

### `ParabolicRectifiability.Enhancements.Statements.ScalingRates`

Source: [ParabolicRectifiability/Enhancements/Statements/ScalingRates.lean](../ParabolicRectifiability/Enhancements/Statements/ScalingRates.lean). Specification copy: [verification/Spec/Enhancements/Statements/ScalingRates.lean](../verification/Spec/Enhancements/Statements/ScalingRates.lean).

- [`Enhancements.ScalingIdentitiesStatement`](../ParabolicRectifiability/Enhancements/Statements/ScalingRates.lean#L36) (def): The scaling identities: for the rescaled source `ν = R^{-k}(F^{-1})_# μ` with `F(y) = a + δ_R y`, `β²_ν(y,s) = β²_μ(F y, R s)` and `S²_ν(y) = S^{2R}_μ(F y)`.
- [`Enhancements.ScaledThresholdProperty`](../ParabolicRectifiability/Enhancements/Statements/ScalingRates.lean#L59) (def): The scaled threshold decomposition with constant `C` in dimension `n`: from `μ(P(a,R) ∩ {S^{2R}_{μ,T} > M}) ≤ Γ` one obtains sets `E_H, E_V` with `IsLocalEnhancedDecomposition` and loss at most `C M R^k + Γ` in `P(a,R)`.
- [`Enhancements.ScaledRectifiableReifenbergStatement`](../ParabolicRectifiability/Enhancements/Statements/ScalingRates.lean#L73) (def): Full scaling contract: the scaling identities, and, for each `n ≥ 1`, one constant `C > 0` (chosen before `k`, `μ`, `a`, `R`, `T`, `M`, `Γ`, every tolerance and every mesh) for the scaled threshold decomposition.

### `ParabolicRectifiability.BetaP.Statements.Main`

Source: [ParabolicRectifiability/BetaP/Statements/Main.lean](../ParabolicRectifiability/BetaP/Statements/Main.lean). Specification copy: [verification/Spec/BetaP/Statements/Main.lean](../verification/Spec/BetaP/Statements/Main.lean).

- [`BetaP.IsBetaPDecomposition`](../ParabolicRectifiability/BetaP/Statements/Main.lean#L46) (structure): The conclusion of the beta-`p` support theorem at center `a` and radius `R`: a decomposition `μ = μ₊ + μ_H + μ_V` into nonnegative measures with the stated loss bound, `μ_H, μ_V` carried by `P(a,R)`, unavailable and disallowed types vanishing, and `HasRegularSupportBounds` for their actual supports.
- [`BetaP.BetaPSupportStatement`](../ParabolicRectifiability/BetaP/Statements/Main.lean#L79) (def): The beta-`p` support theorem: unit, localized and ambient clauses with loss `C M^{p/2} R^k + Γ` for `p ≥ 2` (energy `S_p`) and `C M R^k + Γ` for `0 < p ≤ 2` (energy `T_p`). See [theorems.md](theorems.md) (item 12).

## Further definitions

Definitions used by the statements of the other checked results (examples, beta-p theory, quantitative constructions), grouped by module. They are part of the specification in the same way.

### `BetaP.Proofs.Counterexamples.Euclidean`

- [`BetaP.IsPurelyUnrectifiable`](../ParabolicRectifiability/BetaP/Proofs/Counterexamples/Euclidean.lean#L57): Pure one-unrectifiability in `ℝ²`: `E` meets every Lipschitz image `f(A)`, `A ⊆ ℝ`, in an `H¹`-null set.
- [`BetaP.Plane`](../ParabolicRectifiability/BetaP/Proofs/Counterexamples/Euclidean.lean#L41): The Euclidean plane `ℝ²` (reducibly `Spatial 2`).
- [`BetaP.horizontalSegment`](../ParabolicRectifiability/BetaP/Proofs/Counterexamples/Euclidean.lean#L61): The closed horizontal segment `[u,v] × {b}` of `ℝ²` (first coordinate horizontal).
- [`BetaP.planarDensityRatio`](../ParabolicRectifiability/BetaP/Proofs/Counterexamples/Euclidean.lean#L44): The planar one-dimensional ball ratio `ν(B(z,r))/r`, in `ℝ≥0∞`.
- [`BetaP.planarLowerDensity`](../ParabolicRectifiability/BetaP/Proofs/Counterexamples/Euclidean.lean#L52): The planar lower one-density `liminf_{r↓0} ν(B(z,r))/r`.
- [`BetaP.planarUpperDensity`](../ParabolicRectifiability/BetaP/Proofs/Counterexamples/Euclidean.lean#L48): The planar upper one-density `limsup_{r↓0} ν(B(z,r))/r`.
- [`BetaP.timeSlice`](../ParabolicRectifiability/BetaP/Proofs/Counterexamples/Euclidean.lean#L65): The constant-time embedding `x ↦ (x,0)` of `ℝ²` into `X = ℝ² × ℝ` at `n = 2`.

### `BetaP.Statements.Corollaries`

- [`BetaP.BetaPClassificationStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L306): **Qualitative implications, sharp ranges and failure dimensions**: the ten table entries for `k < n+2` (each "yes" an implication for all sources with the density hypothesis, each "no" a …
- [`BetaP.BetaPEndpointInvarianceStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L296): Endpoint invariance of finiteness (from the finite annuli of `BetaPowAnnulusStatement`): for a locally Radon source, every family, every `p > 0` and every centre, finiteness of `S_p^a` and of …
- [`BetaP.BetaPGraphEnhancementStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L58): **Graph-domain enhancement of the support theorem.**  Same quantifiers and hypotheses as `BetaPSupportStatement`, with one constant `C = C(n,p)`.
- [`BetaP.BetaPIntegratedRateStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L116): **Integrated rates.** For `n ≥ 1` and `0 < p < ∞` there is `C = C(n,p) > 0` such that for `1 ≤ k ≤ n+2`, every mixed or available fixed family, every locally Radon `μ`, every centre `q` and radius …
- [`BetaP.BetaPIntegratedSharpnessStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L148): **Sharp amplitude powers.** Formulated as a negative statement about the diffuse witness `ω = L^{n+1}⌊P(0,1/4)` (`parabolicVolume n` restricted to the open ball `P(0,1/4)`) and its amplitudes `μ_c …
- [`BetaP.ClassificationAmbientStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L277): The ambient endpoint of the classification.
- [`BetaP.HasGraphDomainCostBounds`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L40): The graph-domain conclusions of the enhancement for the supports `(K_H, K_V)` at parent radius `R`, with constant `C`: for every tolerance `ε > 0` and absolute mesh `δ > 0` there is one …
- [`BetaP.IsRegularlyRectifiableWithCovers`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L180): Mixed regular measure rectifiability together with measure covers of every prescribed positive slope or regular norm: the conclusion of every sufficiency entry.
- [`BetaP.SpAboveTwoNotNecessaryStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L232): Table row `S_p^a`, `2 < p < ∞`, "necessary: no, `n = 2`, `k = 1`".
- [`BetaP.SpAboveTwoSufficientStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L221): Table row `S_p^a`, `2 < p < ∞`, "sufficient: yes".
- [`BetaP.SpBelowTwoNecessaryStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L185): Table row `S_p^a`, `0 < p < 2`, "necessary: yes".
- [`BetaP.SpBelowTwoNotSufficientStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L195): Table row `S_p^a`, `0 < p < 2`, "sufficient: no, `n = 2`, `k = 1`".
- [`BetaP.SquareNecessaryStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L214): Table row `S_2^a = T_2^a`, "necessary: yes".
- [`BetaP.SquareSufficientStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L204): Table row `S_2^a = T_2^a`, "sufficient: yes".
- [`BetaP.TpAboveTwoNecessaryStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L266): Table row `T_p^a`, `2 < p < ∞`, "necessary: yes".
- [`BetaP.TpAboveTwoNotSufficientStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L259): Table row `T_p^a`, `2 < p < ∞`, "sufficient: no, `n = 1`, `k = 2`".
- [`BetaP.TpBelowTwoNotNecessaryStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L250): Table row `T_p^a`, `0 < p < 2`, "necessary: no, `n = 1`, `k = 2`".
- [`BetaP.TpBelowTwoSufficientStatement`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L239): Table row `T_p^a`, `0 < p < 2`, "sufficient: yes".
- [`BetaP.integratedEnergyS`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L97): The integrated quadratic beta-`p` energy `ℰ_{p,q,R} = ∫_{P(q,R)} S_{p,μ,T}^{2R} dμ`, in `ℝ≥0∞`.
- [`BetaP.integratedEnergyT`](../ParabolicRectifiability/BetaP/Statements/Corollaries.lean#L103): The integrated `p`-power beta-`p` energy `𝒯_{p,q,R} = ∫_{P(q,R)} T_{p,μ,T}^{2R} dμ`, in `ℝ≥0∞`.

### `BetaP.Statements.Failures`

- [`BetaP.BetaPFailuresStatement`](../ParabolicRectifiability/BetaP/Statements/Failures.lean#L170): **Remainder failures outside the support ranges**: the three negative statements, each in its stated dimension.
- [`BetaP.DirectWitnessMinusStatement`](../ParabolicRectifiability/BetaP/Statements/Failures.lean#L73): The direct witness below two (part (a)).
- [`BetaP.DirectWitnessPlusStatement`](../ParabolicRectifiability/BetaP/Statements/Failures.lean#L94): The direct witness above two (part (b)).
- [`BetaP.DirectWitnessesStatement`](../ParabolicRectifiability/BetaP/Statements/Failures.lean#L108): **Direct Hausdorff-source counterexamples**: the two witnesses and the constant-time transfer.
- [`BetaP.SpBelowTwoNoVanishingRemainderStatement`](../ParabolicRectifiability/BetaP/Statements/Failures.lean#L118): First failure.
- [`BetaP.TimeSliceTransferStatement`](../ParabolicRectifiability/BetaP/Statements/Failures.lean#L53): The constant-time transfer.
- [`BetaP.TpAboveTwoNoIntegratedRemainderStatement`](../ParabolicRectifiability/BetaP/Statements/Failures.lean#L154): Third failure.
- [`BetaP.TpAboveTwoNoVanishingRemainderStatement`](../ParabolicRectifiability/BetaP/Statements/Failures.lean#L136): Second failure.

### `BetaP.Statements.Laws`

- [`BetaP.BetaPowAnnulusStatement`](../ParabolicRectifiability/BetaP/Statements/Laws.lean#L79): Finite annuli: for a given family and a locally Radon source, both scale integrands have finite integral over every positive finite annulus `(u,v)`, `0 < u < v`, at every centre.
- [`BetaP.BetaPowClampingStatement`](../ParabolicRectifiability/BetaP/Statements/Laws.lean#L145): Density-free clamping comparisons: `B_2 ≤ 2^{2-p} B_p` for `0 < p ≤ 2` and `B_p ≤ 2^{p-2} B_2` for `2 ≤ p`, at every centre and radius, for every family and every source;
- [`BetaP.BetaPowHolderStatement`](../ParabolicRectifiability/BetaP/Statements/Laws.lean#L132): Hölder with the density factor.
- [`BetaP.BetaPowMeasurabilityStatement`](../ParabolicRectifiability/BetaP/Statements/Laws.lean#L57): Borel measurability: for a given family and a locally Radon source, `(z,r) ↦ B_p(z,r)` is jointly Borel, and `S_p^a`, `T_p^a` are Borel in the centre for every positive endpoint.
- [`BetaP.BetaPowRescalingStatement`](../ParabolicRectifiability/BetaP/Statements/Laws.lean#L99): Dilation law: for `μ^{q,R} = R^{-k}(z ↦ δ_{1/R}(z-q))_# μ`, which is the existing `rescaledSource μ k q R hR` (the point `δ_{1/R}(z-q)` is `similarity q R hR z`), `B_{p,μ^{q,R}}(δ_{1/R}(z-q), s) = …
- [`BetaP.BetaPowRestrictionStatement`](../ParabolicRectifiability/BetaP/Statements/Laws.lean#L67): Restriction: for a given family, `B_p`, `S_p^a` and `T_p^a` decrease when the source is restricted to any set.
- [`BetaP.BetaPowSmulStatement`](../ParabolicRectifiability/BetaP/Statements/Laws.lean#L90): Amplitude law of the fitting quantity: `B_{p,cμ} = c B_{p,μ}` for a real `c > 0`, at every centre and radius, for every family.
- [`BetaP.BetaPowZeroSourceStatement`](../ParabolicRectifiability/BetaP/Statements/Laws.lean#L114): Zero source: for a given family the zero source has `B_p = 0` and zero energies `S_p^a = T_p^a = 0`.
- [`BetaP.EmptyTestingBallStatement`](../ParabolicRectifiability/BetaP/Statements/Laws.lean#L39): Empty testing ball: for a nonempty family, a testing ball of zero source mass has `B_p = 0`.
- [`BetaP.UnavailableFamilyStatement`](../ParabolicRectifiability/BetaP/Statements/Laws.lean#L48): Empty family: for an empty family `B_p = +∞` at every positive radius and `S_p^a = T_p^a = +∞` at every positive endpoint, for every source.

### `BetaP.Statements.Main`

- [`BetaP.ActiveRadiusPackingExceptionalStatement`](../ParabolicRectifiability/BetaP/Statements/Main.lean#L180): Active-radius packing, exceptional indices: if the all-scale tail hypothesis for the full source `σ` holds at every index outside a set `E` of indices of total weight `Σ_{i ∈ E} b_i r_i^k ≤ Γ`, …
- [`BetaP.ActiveRadiusPackingStatement`](../ParabolicRectifiability/BetaP/Statements/Main.lean#L138): Active-radius packing, main assertion.
- [`BetaP.ActiveRadiusPackingTruncatedStatement`](../ParabolicRectifiability/BetaP/Statements/Main.lean#L152): Active-radius packing, truncated testing sources: the same conclusion when, at each scale `s`, the testing source is `σ_s`, which retains only the indices `r_j ≤ s`.
- [`BetaP.ActiveRadiusPackingUnitParentExceptionalStatement`](../ParabolicRectifiability/BetaP/Statements/Main.lean#L195): Active-radius packing, exceptional indices for the unit-parent form (this adds exactly `Γ` to either conclusion): for packings of `P(q,1)` and tails over `(r_i, 2)` holding outside indices of …
- [`BetaP.ActiveRadiusPackingUnitParentStatement`](../ParabolicRectifiability/BetaP/Statements/Main.lean#L165): Active-radius packing, unit parent with endpoint two: for packings of a unit ball `P(q,1)`, the tail hypothesis integrated only over `(r_i, 2)` gives `σ(X) ≤ C (b + B^{p/2})`.
- [`BetaP.IsWeightedPacking`](../ParabolicRectifiability/BetaP/Statements/Main.lean#L125): The hypotheses on the finite family in the packing statements: finitely many pairwise disjoint open balls `P(z_i,r_i) ⊆ P(q,R)` of positive radii, with weights `0 < b_i ≤ b`.
- [`BetaP.atomicSource`](../ParabolicRectifiability/BetaP/Statements/Main.lean#L112): The atomic source `σ = Σ_i b_i r_i^k δ_{z_i}` of a finite weighted family.
- [`BetaP.truncatedAtomicSource`](../ParabolicRectifiability/BetaP/Statements/Main.lean#L118): The testing source at scale `s` retaining only the indices with `r_j ≤ s`: `σ_s = Σ_{r_j ≤ s} b_j r_j^k δ_{z_j}`.

### `Characterization.Carriers`

- [`Characterization.adrGoodSet`](../ParabolicRectifiability/Characterization/Carriers.lean#L33): The good set `G_A = {z ∈ Γ : ν(P(z,r)) ≤ A r^k for every r > 0}` The balls are the ambient open balls;

### `Characterization.Partitions`

- [`Characterization.IsExactNestedBorelPartitions`](../ParabolicRectifiability/Characterization/Partitions.lean#L24): `P j` (`j : ℕ`) is a sequence of countable exact nested Borel partitions of `R`: in each generation the cells are Borel, pairwise disjoint and have union exactly `R`, and every cell of generation …
- [`Characterization.partitionCell`](../ParabolicRectifiability/Characterization/Partitions.lean#L35): The cell of the partition `P` containing `z`, i.e.

### `Characterization.Statements.Branches`

- [`Characterization.FiniteHausdorffCriterionStatement`](../ParabolicRectifiability/Characterization/Statements/Branches.lean#L47): **Finite-Hausdorff criterion.**  First clause: for `n ≥ 1`, `1 ≤ k ≤ n + 2`, a given family `T`, and a Borel `E` with `H_P^k(E) < ∞`, put `η = H_P^k⌊E`.
- [`Characterization.GraphSourceStatement`](../ParabolicRectifiability/Characterization/Statements/Branches.lean#L84): **Graph-source finiteness.**  For `n ≥ 1` and `1 ≤ k ≤ n + 2`: for every individual horizontal subset graph of finite slope (arbitrary domain) and every individual full general regular vertical …
- [`Characterization.IntrinsicSufficiencyStatement`](../ParabolicRectifiability/Characterization/Statements/Branches.lean#L64): **Intrinsic sufficiency.**  For `n ≥ 1`, `1 ≤ k ≤ n + 2`, a given family `T` and a locally Radon `μ` with `μ ≪ H_P^k` and a Borel sigma-finite `H_P^k` carrier: if `S^R_{μ,T} < ∞` `μ`-a.e.
- [`Characterization.NecessityStatement`](../ParabolicRectifiability/Characterization/Statements/Branches.lean#L108): **Necessity.**  For `n ≥ 1`, `1 ≤ k ≤ n + 2`, a given family `T` and a locally Radon `μ` that is regularly `k`-rectifiable in the finite-norm definition with graphs of type `T`: `μ` has a …
- [`Characterization.TypedRefinementMeasureStatement`](../ParabolicRectifiability/Characterization/Statements/Branches.lean#L159): **Typed refinement, measure version.**  For `n ≥ 1`, `1 ≤ k ≤ n + 2` and a locally Radon, regularly rectifiable `μ` (finite-norm mixed definition), there are disjoint Borel source pieces `E_H, …
- [`Characterization.TypedRefinementSetStatement`](../ParabolicRectifiability/Characterization/Statements/Branches.lean#L126): **Typed refinement, set version.**  For `n ≥ 1`, `1 ≤ k ≤ n + 2` and a Borel `E` with `η = H_P^k⌊E` finite (`H_P^k(E) < ∞`) and `S^1_{η,𝒜_k} < ∞` `η`-a.e., there are Borel sets `E_H, E_V ⊆ E`, …

### `Characterization.Statements.SourceTransfer`

- [`Characterization.CoordinateDifferentiationStatement`](../ParabolicRectifiability/Characterization/Statements/SourceTransfer.lean#L82): **Coordinate differentiation.** Let `R` be a bounded Borel subset of `X` or of a closed subspace (`Y` with closed isometric embedding into `X`), let `λ` be a finite Radon source on `R` (a finite …
- [`Characterization.FivefoldSelectionStatement`](../ParabolicRectifiability/Characterization/Statements/SourceTransfer.lean#L43): **Fivefold selection.** In a separable metric space, every family of open balls `P(z_i, r_i)` with positive, uniformly bounded radii has a countable pairwise disjoint subfamily (indexed by `J`) …
- [`Characterization.GoodDominationStatement`](../ParabolicRectifiability/Characterization/Statements/SourceTransfer.lean#L99): **Good-set domination.** Under the reference hypotheses (`IsADRCarrier k c C Γ σ`), let `ν` be a finite Borel measure carried by `Γ` and `A > 0`.
- [`Characterization.RadonApproximationStatement`](../ParabolicRectifiability/Characterization/Statements/SourceTransfer.lean#L57): **Radon approximation.** Let `λ` be a locally finite Radon measure (finite on compacts and inner regular) on `X` or on a closed subspace of `X` (the space `Y` with closed isometric embedding `e`), …
- [`Characterization.ReplacementStatement`](../ParabolicRectifiability/Characterization/Statements/SourceTransfer.lean#L119): **Bad-region replacement.** There are constants `C₀, C₁ > 0` depending only on `k, c, C` such that, under the reference hypotheses and for `ν` and `A` as in `GoodDominationStatement`, with `Ω_A = …
- [`Characterization.SourceTransferStatement`](../ParabolicRectifiability/Characterization/Statements/SourceTransfer.lean#L146): **ADR source transfer.** Under the reference hypotheses (`IsADRCarrier k c C Γ σ`), let `T` be a given fixed horizontal or vertical model family, or their mixed family (`Nonempty (Models n k …

### `Decomposition.ZeroThresholdAndAmbientBranches`

- [`ambientRetainedSets`](../ParabolicRectifiability/Decomposition/ZeroThresholdAndAmbientBranches.lean#L69): At ambient dimension retain the whole original source inside the unit ball.

### `Enhancements.Decomposition`

- [`Enhancements.IsRectifiableReifenbergDecomposition`](../ParabolicRectifiability/Enhancements/Decomposition.lean#L42): The conclusions of the parabolic rectifiable Reifenberg theorem for the retained sets `D`, with constant `C`, threshold `M` and allowance `Γ`: the restriction decomposition `μ = μ⁺ + μ_H + μ_V`;
- [`Enhancements.gaugeEnergy`](../ParabolicRectifiability/Enhancements/Decomposition.lean#L114): `Λ_Φ = ∫_{P(a,R)} Φ(S^{2R}_{μ,T}) dμ`, for a gauge `Φ : [0,∞] → [0,∞]`.
- [`Enhancements.localSquareEnergy`](../ParabolicRectifiability/Enhancements/Decomposition.lean#L124): `𝓔_{q,R} = ∫_{P(q,R)} S^{2R}_{μ,T} dμ`, the local integrated energy.
- [`Enhancements.powerEnergy`](../ParabolicRectifiability/Enhancements/Decomposition.lean#L109): `Λ_q = ∫_{P(a,R)} (S^{2R}_{μ,T})^q dμ`, an extended nonnegative integral of the `ℝ≥0∞` real power of the full-source square energy with endpoint `2R`.
- [`Enhancements.unitSquareEnergy`](../ParabolicRectifiability/Enhancements/Decomposition.lean#L120): `𝓔 = ∫_U S²_{μ,T} dμ` with `U = P(0,1)` and the whole original `μ` in the energy.
- [`Enhancements.upperDensityLevelSet`](../ParabolicRectifiability/Enhancements/Decomposition.lean#L130): The upper-density level set `O ∩ {z : Θ^{k,*}(μ,z) ≥ a}`, with the density of the original measure `μ`.

### `Enhancements.Statements.Density`

- [`Enhancements.DensityRectifiableReifenbergStatement`](../ParabolicRectifiability/Enhancements/Statements/Density.lean#L101): **Rectifiable Reifenberg density bounds.**  For each `n ≥ 1` there is `C > 0` such that, for `1 ≤ k ≤ n+2`, locally Radon `μ`, `U = P(0,1)` and real `M, Γ ≥ 0` with `μ(U ∩ {S²_{μ,A_k} > M}) ≤ Γ` …
- [`Enhancements.DensityScalingStatement`](../ParabolicRectifiability/Enhancements/Statements/Density.lean#L144): **All local scales and their exact normalization.**  For each `n ≥ 1` there is `C > 0` such that, for `1 ≤ k ≤ n+2`, locally Radon `μ`, `q ∈ X`, `R > 0`, and with `F_{q,R} = P(q,R) ∩ {Θ^{k,*} ≥ …
- [`Enhancements.DensityThreePartsStatement`](../ParabolicRectifiability/Enhancements/Statements/Density.lean#L50): **All three density conclusions.**  For each `n ≥ 1` there is `C > 0` (depending only on `n` and the fixed Hausdorff normalization, so chosen before `k`, `μ`, `A` and `a`) such that, for `1 ≤ k ≤ …

### `Enhancements.Statements.GraphDomains`

- [`Enhancements.GraphEnhancedRectifiableReifenbergStatement`](../ParabolicRectifiability/Enhancements/Statements/GraphDomains.lean#L69): **Graph-domain enhancement on the same supports.**  Quantifier order: `∃ C ∀ k, μ, M, Γ ∃ E_H, E_V (hence K_H, K_V) ∀ ε, δ > 0 ∃ cover`.

### `Enhancements.Statements.MainTheorem`

- [`Enhancements.RectifiableReifenbergTheoremStatement`](../ParabolicRectifiability/Enhancements/Statements/MainTheorem.lean#L46): **The parabolic rectifiable Reifenberg theorem.**  For each `n ≥ 1` there is one constant `C > 0` such that:  * **mixed**: for every integer `1 ≤ k ≤ n+2`, every locally Radon `μ` and all real `M, …

### `Enhancements.Statements.ScaledCore`

- [`Enhancements.IsLocalCoreDecomposition`](../ParabolicRectifiability/Enhancements/Statements/ScaledCore.lean#L46): The restriction decomposition on the cylinder `P(a,R)` for the family `T`, without its loss and **without graph-domain covers**.
- [`Enhancements.ScaledRectifiableReifenbergCoreStatement`](../ParabolicRectifiability/Enhancements/Statements/ScaledCore.lean#L93): **Scaling contract without graph-domain covers**: the scaling identities, and, for each `n ≥ 1`, one constant `C > 0` (chosen before `k`, `μ`, `a`, `R`, `T`, `M`, `Γ` and every cover tolerance) …
- [`Enhancements.ScaledThresholdCoreProperty`](../ParabolicRectifiability/Enhancements/Statements/ScaledCore.lean#L74): The scaled threshold decomposition without graph-domain covers, with constant `C` in dimension `n`.

### `Enhancements.Statements.ScalingRates`

- [`Enhancements.GaugeRateProperty`](../ParabolicRectifiability/Enhancements/Statements/ScalingRates.lean#L133): The gauge rate with core constant `C₀`: for `1 ≤ k ≤ n+2`, locally Radon `μ`, `a ∈ X`, `R > 0`, and a gauge `Φ : [0,∞] → [0,∞]` that is nondecreasing, Borel and finite on finite inputs, with `Λ_Φ …
- [`Enhancements.GaugeRateStatement`](../ParabolicRectifiability/Enhancements/Statements/ScalingRates.lean#L156): **Gauge rate and an approximated numerical infimum.** As for the power rate, `C₀` is one constant per `n` for which the scaled threshold decomposition holds, chosen before `k`, `μ`, `a`, `R`, `Φ`, …
- [`Enhancements.PowerRateProperty`](../ParabolicRectifiability/Enhancements/Statements/ScalingRates.lean#L90): The power-energy rate with core constant `C₀`:  * for `1 ≤ k ≤ n+2`, locally Radon `μ`, `a ∈ X`, `R > 0`, the mixed family or a given fixed family `T` (the given fixed-family version with …
- [`Enhancements.PowerRateStatement`](../ParabolicRectifiability/Enhancements/Statements/ScalingRates.lean#L114): **Power-energy rate, including zero energy.**  Here `C₀` is the unchanged core threshold constant, independent of `q`: for each `n ≥ 1` there is one `C₀ > 0`, chosen before `k`, `μ`, `a`, `R`, `T` …

### `Examples.DenseAtoms`

- [`Examples.denseAtomMeasure`](../ParabolicRectifiability/Examples/DenseAtoms.lean#L38): The dense-atom measure `μ = Σ_j w_j δ_{z_j}`.
- [`Examples.denseAtomWeight`](../ParabolicRectifiability/Examples/DenseAtoms.lean#L31): The dense-atom weights `w`, in the Lean index: `w j = 2^{-(j+1)} / (1 + Σ_{i<j} w i · (d_P(z i, z j)^k)⁻¹)`.

### `Examples.Lacunary`

- [`Examples.IsLacunaryData`](../ParabolicRectifiability/Examples/Lacunary.lean#L53): The standing amplitude and frequency hypotheses of the lacunary construction, with the Lean index `j` standing for the mathematical index `j + 1`: `0 < a_j ≤ 1`, positive integer frequencies, and …
- [`Examples.IsLebesgueDensityPoint`](../ParabolicRectifiability/Examples/Lacunary.lean#L95): `t` is a Lebesgue density point of `E ⊆ ℝ`: `|E ∩ [t-r,t+r]| / |[t-r,t+r]| → 1` as `r ↓ 0`.
- [`Examples.LacunaryConvergenceStatement`](../ParabolicRectifiability/Examples/Lacunary.lean#L73): Convergence of the lacunary primitive series.
- [`Examples.exponentAmplitude`](../ParabolicRectifiability/Examples/Lacunary.lean#L105): The amplitudes `a_j = c₀ / (√j log(j+1))` of the exponent witness below `p = 2`, in the Lean index: `a j = c₀ / (√(j+1) log(j+2))`.
- [`Examples.lacunaryFunction`](../ParabolicRectifiability/Examples/Lacunary.lean#L65): The lacunary function `f(t) = ε Σ_j a_j N_j^{-1/2} cos(N_j t)`, as a `tsum`.
- [`Examples.lacunaryGraphMap`](../ParabolicRectifiability/Examples/Lacunary.lean#L83): The graph map `F(t) = (f(t), t) ∈ Space 1`.
- [`Examples.lacunaryInterval`](../ParabolicRectifiability/Examples/Lacunary.lean#L87): The parameter interval `J = [-1,1]`.
- [`Examples.lacunarySource`](../ParabolicRectifiability/Examples/Lacunary.lean#L90): The restricted graph source `ν_E = F_#(L¹⌊E)`.
- [`Examples.nonregularAmplitude`](../ParabolicRectifiability/Examples/Lacunary.lean#L101): The amplitudes `a_j = j^{-1/2}` of the nonregular lacunary example, in the Lean index: `a j = (j + 1)^{-1/2}`.
- [`Examples.zeroBaseLift`](../ParabolicRectifiability/Examples/Lacunary.lean#L116): A real function `h` of time, read as the normal-valued function `(0, t) ↦ h(t) e₁` on the vertical base `zeroDirection × ℝ`, with values in `zeroDirectionᗮ = ℝ¹`.
- [`Examples.zeroDirection`](../ParabolicRectifiability/Examples/Lacunary.lean#L110): The zero spatial subspace of `ℝ¹`: the direction of every vertical model and full vertical graph at `n = 1`, `k = 2` (spatial rank zero).

### `Examples.Statements.DensityExamples`

- [`Examples.AtomTestStatement`](../ParabolicRectifiability/Examples/Statements/DensityExamples.lean#L119): Density tests, atom.
- [`Examples.DenseAtomsStatement`](../ParabolicRectifiability/Examples/Statements/DensityExamples.lean#L50): **Dense atoms.** For `n ≥ 1`, `1 ≤ k < n + 2` and distinct points `z_i` dense in `D = \overline{P(0,1/4)}` (values in `D`, `D ⊆ closure {z_i}`), the measure `μ = Σ_j w_j δ_{z_j}` of …
- [`Examples.DensityTestsStatement`](../ParabolicRectifiability/Examples/Statements/DensityExamples.lean#L132): The density tests: the flat, diffuse and atomic tests.
- [`Examples.DiffuseTestStatement`](../ParabolicRectifiability/Examples/Statements/DensityExamples.lean#L97): Density tests, diffuse source.
- [`Examples.FlatPatchTestStatement`](../ParabolicRectifiability/Examples/Statements/DensityExamples.lean#L77): Density tests, flat patch.

### `Examples.Statements.Lacunary`

- [`Examples.ExponentWitnessAboveCarrierStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L203): **Exponent-free part for `p > 2`.** With `a_j = j^{-1/2}` and `ν_ε = F_#(L¹⌊[-1/4,1/4])`: the support of `ν_ε` lies in `P(0,1)`, its mass is `1/2`, and every countably regular carrier with a …
- [`Examples.ExponentWitnessAboveEnergyStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L217): **Energy part for `p > 2`.** For every `p > 2` there is `C_p > 0`, independent of `ε` and `N`, with `sup_{supp ν_ε} T²_{p,ν_ε} ≤ C_p ε^p` and `0 < ∫ T²_{p,ν_ε} dν_ε ≤ C_p ε^p / 2`.
- [`Examples.ExponentWitnessBelowStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L241): **Exponents below `2`.** There is a universal `C > 0` such that for every `c₀ > 0` with `a_j = c₀/(√j log(j+1)) ≤ 1` (`exponentAmplitude c₀`, the bound being part of `IsLacunaryData`) and every …
- [`Examples.ExponentWitnessesStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L269): **The exponent witnesses:** the complementary exponent witnesses, `p > 2` and `p < 2`.
- [`Examples.LacunaryBallMeasureStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L55): **Exact ball identity.** `ν_E(P(F(t),r)) = |E ∩ (t-r², t+r²)|` for every measurable `E ⊆ J`, every `t ∈ ℝ` and every `r > 0`.
- [`Examples.LacunaryDensityLimitStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L74): **Density limit.** For almost every `t ∈ E`, the ratio `ν_E(P(F(t),r)) / r²` tends to `2` as `r ↓ 0`.
- [`Examples.LacunaryEstimatesStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L141): **The lacunary estimates.** The conjunction of every displayed claim of the lemma: isometry, exact ball identity, Hausdorff identity, density limit, full-interval regularity, upper and lower …
- [`Examples.LacunaryFullIntervalStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L85): **Full-interval regularity.** `ν_J` is two-Ahlfors regular at the points `F(t)`, `t ∈ J`, of its support for `0 < r ≤ 1` (some constant `C ≥ 1` with `r²/C ≤ ν_J(P(F(t),r)) ≤ C r²`), and at every …
- [`Examples.LacunaryHausdorffStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L65): **Hausdorff identity.** There is a positive normalization constant `c_H`, chosen before all data, with `H_P²(F(E)) = c_H |E|` for every measurable `E ⊆ J`.
- [`Examples.LacunaryIsometryStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L49): **Isometry.** `F` is an isometry from `(ℝ, √|t-s|)` onto its image in `(Space 1, d_P)`.
- [`Examples.LacunaryLowerEnergyStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L112): **Restriction-stable lower energy.** There are coefficients `c_q > 0` (`q > 0`) such that, for every measurable `E ⊆ J`, every Lebesgue density point `t ∈ E ∩ (-1,1)` of `E` and every `R > 0`, …
- [`Examples.LacunarySmallSlopeStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L130): **Small slopes.** If `a_j → 0`, then for every `η > 0` the fixed graph `F(J)` is covered by finitely many restrictions of full ordinary vertical graphs of slope at most `η`.
- [`Examples.LacunaryUpperEnergyStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L97): **All-scale upper energy.** For every `q ≥ 1` there is `C_q > 0` such that `sup_{t ∈ ℝ} T^∞_{q,ν_E}(F(t)) ≤ C_q ε^q Σ_j a_j^q` for every measurable `E ⊆ J`.
- [`Examples.NonregularQualitativeStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L160): **Nonregular example, qualitative part.** With `a_j = j^{-1/2}` (`nonregularAmplitude`), every admissible `ε`, `N`: * the single graph `F(J)` is compact;
- [`Examples.NonregularStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L193): **The nonregular example:** ordinarily rectifiable, but no regular graph cover.
- [`Examples.NonregularUpperEnergyStatement`](../ParabolicRectifiability/Examples/Statements/Lacunary.lean#L184): **The `T_p` bound for `p > 2`.** For every fixed `p > 2` there is `C_p > 0`, independent of `ε` and `N`, with `sup_t T^∞_{p,ν_J}(F(t)) ≤ C_p ε^p`.

### `Examples.Statements.Reductions`

- [`Examples.ReductionsStatement`](../ParabolicRectifiability/Examples/Statements/Reductions.lean#L116): The exact reductions: the time-slice identity and its tube identity, the stationary-product comparison, and the stationary graph extensions.
- [`Examples.StationaryGraphExtensionStatement`](../ParabolicRectifiability/Examples/Statements/Reductions.lean#L98): Reductions, stationary graphs.
- [`Examples.StationaryProductStatement`](../ParabolicRectifiability/Examples/Statements/Reductions.lean#L70): Reductions, stationary product.
- [`Examples.TimeSliceStatement`](../ParabolicRectifiability/Examples/Statements/Reductions.lean#L39): Reductions, time slice.
- [`Examples.TimeSliceTubeStatement`](../ParabolicRectifiability/Examples/Statements/Reductions.lean#L60): Reductions, tube identity: for every spatial set `A`, every `t₀` and every `r > 0`, `|{z : d_P(z, A × {t₀}) < r}| = 2 r² |{y : dist(y,A) < r}|`, with ambient volume `L^{n+1} = parabolicVolume n` …

### `Foundations.ADR`

- [`Foundations.IsADRCarrier`](../ParabolicRectifiability/Foundations/ADR.lean#L38): The reference carrier of the source-transfer argument: `Γ ⊆ X` is nonempty and closed, `σ` is a Radon measure (finite on compacts and inner regular, the project's convention) with `supp σ = Γ`, …

### `Foundations.EuclideanBeta`

- [`Foundations.euclideanBetaPow`](../ParabolicRectifiability/Foundations/EuclideanBeta.lean#L38): The Euclidean beta-`p` quantity `b^E_{p,λ,m}(x,r) = r^{-m-p} inf_{U^m} ∫_{B(x,r)} dist(y,U)^p dλ(y)` for `r > 0`, and `0` for `r ≤ 0`.
- [`Foundations.euclideanEnergyS`](../ParabolicRectifiability/Foundations/EuclideanBeta.lean#L46): The Euclidean quadratic energy `S^{a,E}_p(x) = ∫_{(0,a)} b^E_p(x,r)^{2/p} dr/r`.
- [`Foundations.euclideanEnergyT`](../ParabolicRectifiability/Foundations/EuclideanBeta.lean#L51): The Euclidean `p`-power energy `T^{a,E}_p(x) = ∫_{(0,a)} b^E_p(x,r) dr/r`.

### `Foundations.GraphDomainCover`

- [`Foundations.GraphDomainCover.horizontal`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L242): `(K_H, K_V)` admits a graph-domain cover with bound `C`, tolerance `ε` and mesh `δ`.
- [`Foundations.GraphDomainCover.vertical`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L242): `(K_H, K_V)` admits a graph-domain cover with bound `C`, tolerance `ε` and mesh `δ`.
- [`Foundations.HorizontalDomainData.center`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L97): The vertical data of a graph-domain cover of the carrier `K`, at tolerance `ε` and mesh `δ`.
- [`Foundations.HorizontalDomainData.graphIndex`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L97): The vertical data of a graph-domain cover of the carrier `K`, at tolerance `ε` and mesh `δ`.
- [`Foundations.HorizontalDomainData.radius`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L97): The vertical data of a graph-domain cover of the carrier `K`, at tolerance `ε` and mesh `δ`.
- [`Foundations.HorizontalDomainData.trace`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L97): The vertical data of a graph-domain cover of the carrier `K`, at tolerance `ε` and mesh `δ`.
- [`Foundations.VerticalDomainData.center`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L135): The patch centre `z_α = Φ(p_α)` in `X`.
- [`Foundations.VerticalDomainData.graphIndex`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L135): The patch centre `z_α = Φ(p_α)` in `X`.
- [`Foundations.VerticalDomainData.radius`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L135): The patch centre `z_α = Φ(p_α)` in `X`.
- [`Foundations.VerticalDomainData.trace`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L135): The patch centre `z_α = Φ(p_α)` in `X`.

### `Foundations.Graphs`

- [`Foundations.GeneralRegularVerticalGraph.function`](../ParabolicRectifiability/Foundations/Graphs.lean#L48): The graph map `(u,t) ↦ (a + u + G(u,t), t)` on the whole base `W × ℝ`.
- [`Foundations.GeneralRegularVerticalGraph.offset`](../ParabolicRectifiability/Foundations/Graphs.lean#L48): The graph map `(u,t) ↦ (a + u + G(u,t), t)` on the whole base `W × ℝ`.
- [`Foundations.IsOrdinarilyRectifiableSet`](../ParabolicRectifiability/Foundations/Graphs.lean#L111): Ordinary mixed parabolic set rectifiability: at every positive tolerance, horizontal graphs of slope at most `ε` and ordinary full vertical graphs of Lipschitz bound at most `ε` cover `E` modulo …
- [`Foundations.IsRegularlyRectifiableSet`](../ParabolicRectifiability/Foundations/Graphs.lean#L105): Regular set rectifiability of type `T`: for every prescribed `ε > 0`, `E` has a countable typed graph cover with bound `ε` modulo `H_P^k` outer measure.
- [`Foundations.OrdinaryVerticalGraph.function`](../ParabolicRectifiability/Foundations/Graphs.lean#L81): The graph map `(u,t) ↦ (a + u + G(u,t), t)` on the whole base `W × ℝ`.
- [`Foundations.OrdinaryVerticalGraph.offset`](../ParabolicRectifiability/Foundations/Graphs.lean#L81): The graph map `(u,t) ↦ (a + u + G(u,t), t)` on the whole base `W × ℝ`.

### `Foundations.Statements.Ambient`

- [`Foundations.AmbientAbsolutelyContinuousDensityStatement`](../ParabolicRectifiability/Foundations/Statements/Ambient.lean#L120): Fourth clause: differentiation with respect to volume.
- [`Foundations.AmbientCharacterizationStatement`](../ParabolicRectifiability/Foundations/Statements/Ambient.lean#L105): Third clause: for a locally Radon `μ` on `X`, at `k = n + 2` the following are equivalent: * regular `(n + 2)`-rectifiability of `μ`, of mixed type and, equally, of vertical type …
- [`Foundations.AmbientEnergyZeroArbitrarySourceStatement`](../ParabolicRectifiability/Foundations/Statements/Ambient.lean#L73): Generalization of the first clause to an **arbitrary** measure: the same conclusions as `AmbientEnergyZeroStatement`, with no hypothesis on `μ`.
- [`Foundations.AmbientEnergyZeroStatement`](../ParabolicRectifiability/Foundations/Statements/Ambient.lean#L58): First clause, form for locally Radon sources: at `k = n + 2`, for every locally Radon `μ` and every family available there (`Nonempty (Models n (n + 2) T)`, i.e.
- [`Foundations.AmbientLocalCoreStatement`](../ParabolicRectifiability/Foundations/Statements/Ambient.lean#L144): Fifth clause: the ambient core has zero remainder, without an energy assumption, on every cylinder `P(q,R)`.
- [`Foundations.AmbientZeroGraphCoverStatement`](../ParabolicRectifiability/Foundations/Statements/Ambient.lean#L87): Second clause: every set has the zero-graph cover.

### `Foundations.Statements.CompactBridge`

- [`Foundations.CompactBridgeCoverStatement`](../ParabolicRectifiability/Foundations/Statements/CompactBridge.lean#L51): Cover inclusion without loss of tolerance: every countable cover modulo `H_P^k` by core regular vertical graphs of norm at most `ε` is a cover by full general regular vertical graphs of norm at …
- [`Foundations.CompactBridgeFunctionStatement`](../ParabolicRectifiability/Foundations/Statements/CompactBridge.lean#L44): Function inclusion at the same tolerance: every function of the existing compact-perturbation class with `Lip_P G + [g]_BMO ≤ ε` is general regular with the same bound `ε`.
- [`Foundations.CompactBridgeRepresentativeStatement`](../ParabolicRectifiability/Foundations/Statements/CompactBridge.lean#L35): Representative identification: if `g` represents the existing `L²` half derivative of `H` in every normal component, then, for every constant `c`, the same `g` represents the general homogeneous …

### `Foundations.Statements.DensityBridges`

- [`Foundations.ACBridgeStatement`](../ParabolicRectifiability/Foundations/Statements/DensityBridges.lean#L88): The absolute-continuity bridge: finite lower density and finite energy imply absolute continuity.
- [`Foundations.PackingMassStatement`](../ParabolicRectifiability/Foundations/Statements/DensityBridges.lean#L43): Packing turns lower density into retained mass.
- [`Foundations.UpperDensityDominationStatement`](../ParabolicRectifiability/Foundations/Statements/DensityBridges.lean#L68): Pointwise positive upper density gives Hausdorff domination.

### `Foundations.Statements.Measurability`

- [`Foundations.AnnulusBoundStatement`](../ParabolicRectifiability/Foundations/Statements/Measurability.lean#L70): The finite-annulus bound: for a given family, a locally Radon source and `0 < a < b < ∞`, `∫_a^b b_{μ,T}(z,r) dr/r ≤ a^{-k} μ(closed P(z,b)) log(b/a) < ∞`.
- [`Foundations.BetaEnergyDominationStatement`](../ParabolicRectifiability/Foundations/Statements/Measurability.lean#L57): Domination: if `ν ≤ c μ` with a real `c > 0`, then `b_ν ≤ c b_μ` at every centre and positive radius, and `S_ν^R ≤ c S_μ^R` at every centre and positive endpoint.
- [`Foundations.BetaPowTwoStatement`](../ParabolicRectifiability/Foundations/Statements/Measurability.lean#L116): Compatibility with `p = 2`: at `p = 2` the beta-`p` fitting quantity is literally the natural `betaSq`, at every centre, radius and family (both vanish at nonpositive radii).
- [`Foundations.DensityMeasurabilityStatement`](../ParabolicRectifiability/Foundations/Statements/Measurability.lean#L38): Density part of the measurability clause: for a locally Radon source both densities are Borel functions of the centre.
- [`Foundations.EnergyPowSmulStatement`](../ParabolicRectifiability/Foundations/Statements/Measurability.lean#L133): Amplitude laws of the beta-`p` energies: for real `p > 0` and real `c > 0`, `S_{p,cμ}^a = c^{2/p} S_{p,μ}^a` and `T_{p,cμ}^a = c T_{p,μ}^a`, for every positive endpoint `a` and every family (an …
- [`Foundations.EnergyTwoStatement`](../ParabolicRectifiability/Foundations/Statements/Measurability.lean#L123): Compatibility with `p = 2`: `S_2^a = T_2^a = S^a`, the existing `squareEnergy`, for every positive endpoint `a` and every family.
- [`Foundations.RestrictLocallyRadonStatement`](../ParabolicRectifiability/Foundations/Statements/Measurability.lean#L46): The restriction of a locally Radon source to a Borel set is locally Radon (finite on compacts and inner regular).
- [`Foundations.SquareEnergyRescalingStatement`](../ParabolicRectifiability/Foundations/Statements/Measurability.lean#L97): Dilation law of the square function: for `μ_{q,R} = R^{-k} (δ_{1/R}(· - q))_# μ`, which is the existing `rescaledSource μ k q R hR`, `S_{μ_{q,R}}^A(z) = S_μ^{RA}(q + δ_R z)`.
- [`Foundations.SquareEnergySmulStatement`](../ParabolicRectifiability/Foundations/Statements/Measurability.lean#L109): Scalar law of the square function: `S_{cμ}^A = c S_μ^A` for a real `c > 0`, every family and every positive endpoint.
- [`Foundations.SquareFinitenessEndpointStatement`](../ParabolicRectifiability/Foundations/Statements/Measurability.lean#L85): Endpoint independence: finiteness of the square energy at a centre does not depend on the finite positive endpoint.

### `Geometry.AdmissibleModels`

- [`FamilyKind.casesOn`](../ParabolicRectifiability/Geometry/AdmissibleModels.lean#L42): Choice of horizontal, vertical or mixed planes in a fitting problem.
- [`HorizontalModel.spatial`](../ParabolicRectifiability/Geometry/AdmissibleModels.lean#L32): An affine spatial plane times all time, with parabolic dimension `k`.
- [`HorizontalModel.time`](../ParabolicRectifiability/Geometry/AdmissibleModels.lean#L32): An affine spatial plane times all time, with parabolic dimension `k`.
- [`VerticalModel.spatial`](../ParabolicRectifiability/Geometry/AdmissibleModels.lean#L39): Tagged union of horizontal and vertical models of the same parabolic dimension.
- [`instDecidableEqFamilyKind`](../ParabolicRectifiability/Geometry/AdmissibleModels.lean#L48): The actual type of fitting models for the selected family;

### `Geometry.AffinePlane`

- [`AffineSpatialPlane.anchor`](../ParabolicRectifiability/Geometry/AffinePlane.lean#L30): The represented affine set.

### `Geometry.Graphs`

- [`HorizontalGraph.domain`](../ParabolicRectifiability/Geometry/Graphs.lean#L34): Space-time image of the partial horizontal graph, including its spatial offset, normal displacement and varying time coordinate.
- [`HorizontalGraph.normal`](../ParabolicRectifiability/Geometry/Graphs.lean#L34): Space-time image of the partial horizontal graph, including its spatial offset, normal displacement and varying time coordinate.
- [`HorizontalGraph.offset`](../ParabolicRectifiability/Geometry/Graphs.lean#L34): Space-time image of the partial horizontal graph, including its spatial offset, normal displacement and varying time coordinate.
- [`HorizontalGraph.time`](../ParabolicRectifiability/Geometry/Graphs.lean#L34): Space-time image of the partial horizontal graph, including its spatial offset, normal displacement and varying time coordinate.
- [`RegularVerticalGraph.function`](../ParabolicRectifiability/Geometry/Graphs.lean#L51): Image of the full time-preserving graph over the intrinsic vertical base;
- [`RegularVerticalGraph.offset`](../ParabolicRectifiability/Geometry/Graphs.lean#L51): Image of the full time-preserving graph over the intrinsic vertical base;

### `Geometry.SubspaceCoordinates`

- [`subspaceCoordinatesMeasurableEquiv`](../ParabolicRectifiability/Geometry/SubspaceCoordinates.lean#L51)

### `IntegralCanonical.Statements.Canonical`

- [`IntegralCanonical.CanonicalGuardsStatement`](../ParabolicRectifiability/IntegralCanonical/Statements/Canonical.lean#L136): **Guards**, precise claims only.
- [`IntegralCanonical.IntrinsicSourceOfDensityStatement`](../ParabolicRectifiability/IntegralCanonical/Statements/Canonical.lean#L29): **Density bridge.** For a locally Radon `μ`, `0 < Θ^{k,*}(μ,z) < ∞` at `μ`-almost every `z` implies the intrinsic source class.
- [`IntegralCanonical.TypeSeparationStatement`](../ParabolicRectifiability/IntegralCanonical/Statements/Canonical.lean#L114): **Type separation.** The geometric separation of types.

### `IntegralCanonical.Statements.Integral`

- [`IntegralCanonical.IntegralEquivalencesStatement`](../ParabolicRectifiability/IntegralCanonical/Statements/Integral.lean#L36): **Exact integral tests** for square finiteness.

### `QuantitativeCharacterization.Coverings`

- [`QuantitativeCharacterization.RegularMixedCovering.HasCanonicalLimits`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L181): The canonical conclusions of the approximants for a typed split: every `μ^N_H` is horizontally rectifiable and every `μ^N_V` regularly vertically rectifiable (`IsRegularlyRectifiableMeasure` of …
- [`QuantitativeCharacterization.RegularMixedCovering.IsTypedTraceSplit`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L152): The typed split of the root: disjoint Borel `F_H, F_V ⊂ P₀`, each inside the union of the typed traces of its type, carrying `μ ⌊ P₀`.
- [`QuantitativeCharacterization.RegularMixedCovering.MeasureIdentity`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L164): The measure identity at every level: `μ ⌊ P₀ = μ^N_H + μ^N_V + e^N` for every `N ≥ 0`.
- [`QuantitativeCharacterization.RegularMixedCovering.RelativeTail`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L170): The relative residual tail at every level, with tail constant `C_tail` and the covering constant `K`: `e^N(P₀) ≤ 2 exp(-N / (C_tail K)) μ(P₀)` for every `N ≥ 0`.
- [`QuantitativeCharacterization.RegularMixedCovering.approximant`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L143): The retained approximant `μ^N_{T,P₀} = μ ⌊ (F_T ∩ {m ≤ N})`, for a given typed set `F = F_T`.
- [`QuantitativeCharacterization.RegularMixedCovering.ball`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L131): The model ball `P_i = P(a_i, R_i)`.
- [`QuantitativeCharacterization.RegularMixedCovering.center`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L131): The model ball `P_i = P(a_i, R_i)`.
- [`QuantitativeCharacterization.RegularMixedCovering.index`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L131): The model ball `P_i = P(a_i, R_i)`.
- [`QuantitativeCharacterization.RegularMixedCovering.multiplicity`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L135): The multiplicity `m(z) = Σ_i 1_{P_i}(z) ∈ ℕ∞`, the number of model balls containing `z`.
- [`QuantitativeCharacterization.RegularMixedCovering.radius`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L131): The model ball `P_i = P(a_i, R_i)`.
- [`QuantitativeCharacterization.RegularMixedCovering.reference`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L131): The model ball `P_i = P(a_i, R_i)`.
- [`QuantitativeCharacterization.RegularMixedCovering.residual`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L147): The residual `e^N_{P₀} = μ ⌊ (P₀ ∩ {m > N})`.
- [`QuantitativeCharacterization.RegularMixedCovering.typedTrace`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L139): The union of the typed traces `P_i ∩ Γ_i` over the references of type `T`.
- [`QuantitativeCharacterization.carlesonEnergyS`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L55): `M_{S_p} = sup_{a ∈ E, R > 0} R^{-k} ∫_{P(a,R)} S^R_{p,μ} dμ`, with the Foundations energy `energyS` of the mixed family.
- [`QuantitativeCharacterization.carlesonEnergyT`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L60): `M_{T_p} = sup_{a ∈ E, R > 0} R^{-k} ∫_{P(a,R)} T^R_{p,μ} dμ`, with the Foundations energy `energyT` of the mixed family.

### `QuantitativeCharacterization.References`

- [`QuantitativeCharacterization.HorizontalReference.height`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L114): The map `(F,T) : ℝ^k → X`, `u ↦ (F(u), T(u))`.
- [`QuantitativeCharacterization.HorizontalReference.spatialMap`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L114): The map `(F,T) : ℝ^k → X`, `u ↦ (F(u), T(u))`.
- [`QuantitativeCharacterization.Reference.casesOn`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L167): A typed `L`-reference: horizontal, vertical, or the ambient reference `(X, L^{n+1})` at `k = n + 2`.
- [`QuantitativeCharacterization.Reference.kind`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L177): The type of a reference.
- [`QuantitativeCharacterization.VerticalReference.spatialMap`](../ParabolicRectifiability/QuantitativeCharacterization/References.lean#L152): The time-preserving embedding `Φ(u,t) = (F(u,t),t)`.

### `QuantitativeCharacterization.Statements.Approximants`

- [`QuantitativeCharacterization.AmbientEndpointStatement`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Approximants.lean#L166): **The ambient case.** Let `k = n + 2` and `μ` be locally Radon.
- [`QuantitativeCharacterization.BoundedSupportBounds`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Approximants.lean#L112): The conclusion of the bounded-support statement for given constants `C(A,k) = Cabs`, `L₀` and `C`;
- [`QuantitativeCharacterization.BoundedSupportStatement`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Approximants.lean#L155): **The bounded-support case.** For `μ ≠ 0` locally Radon with `0 < D_E = diam_P E < ∞`, upper growth `μ(P(z,r)) ≤ A r^k` for `z ∈ E` and all `r > 0`, and lower growth `A⁻¹ r^k ≤ μ(P(z,r))` for `z ∈ …
- [`QuantitativeCharacterization.LocalForwardBounds`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Approximants.lean#L63): The forward part of the local statement for given constants `B_loc`, `L₀` and `C`: for a locally Radon `μ`, a root `P₀ = P(a,R)` with `a ∈ E`, `R > 0`, and a finite `M ≥ 0`, the local ADR and …
- [`QuantitativeCharacterization.MeasureApproximantsStatement`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Approximants.lean#L46): **Approximants of a covering.** Under the global hypotheses of the quantitative characterization (`μ ≠ 0` Radon, unbounded support, `A`-ADR) and the equivalent condition `M_β(μ) < ∞`: for every …
- [`QuantitativeCharacterization.QuantitativeCommonConstantsStatement`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Approximants.lean#L202): **Common constants of the quantitative characterization and its corollaries**.
- [`QuantitativeCharacterization.UniformLocalStatement`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Approximants.lean#L93): **The local forward and converse clauses.** 1.

### `QuantitativeCharacterization.Statements.Characterization`

- [`QuantitativeCharacterization.BetaPowCarlesonComparisonStatement`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Characterization.lean#L96): **The beta-`p` comparison.** On the global `A`-ADR class of the quantitative characterization, with `M_{S_p}`, `M_{T_p}` the root energies of the mixed-family beta-`p` energies of the source: 1.
- [`QuantitativeCharacterization.BetaPowForwardBounds`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Characterization.lean#L78): The forward clause of the beta-`p` comparison for given constants `L₀` and `C`: on the global `A`-ADR class, finiteness of `M_{S_p}` (`p ≥ 2`) or of `M_{T_p}` (`0 < p ≤ 2`) gives `M_β < ∞` and the …

### `QuantitativeCharacterization.Statements.Geometry`

- [`QuantitativeCharacterization.BetaScalingStatement`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Geometry.lean#L37): **The scaling identity.** For `S_{a,R}(z) = δ_{1/R}(z - a)` and `μ_{a,R} = R^{-k} (S_{a,R})_# μ`, which is the existing `rescaledSource μ k a R hR`, `β_{μ_{a,R}}(z,r)² = β_μ(a + δ_R z, R r)²` for …
- [`QuantitativeCharacterization.QuantitativeRectifiabilityMonoStatement`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Geometry.lean#L46): **Monotonicity**: increasing either constant preserves the `(K,L)`-quantitative mixed parabolic rectifiability of a locally Radon measure.

### `QuantitativeCharacterization.Statements.Pieces`

- [`QuantitativeCharacterization.AnyCoverRectifiableStatement`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Pieces.lean#L31): **A measure with a quantitative covering is rectifiable**: a locally Radon measure with the `(K,L)` property for some finite `K, L ≥ 1` is regularly mixed parabolically `k`-rectifiable.
- [`QuantitativeCharacterization.CountableQuantitativePiecesStatement`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Pieces.lean#L42): **Countable quantitative pieces.** With `K_* = 2^k` and `L_* = max {2, √(1+n)}`, a locally Radon `μ` is regularly mixed parabolically `k`-rectifiable if and only if there are pairwise disjoint …

### `Specifications.Rectifiability`

- [`RetainedSets.horizontal`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L44): Restriction of the original source to the retained horizontal Borel set.
- [`RetainedSets.vertical`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L44): Restriction of the original source to the retained horizontal Borel set.
