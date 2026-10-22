import ParabolicRectifiability.Examples.Proofs.PlanarSlices.SlopeGraph
import ParabolicRectifiability.Examples.Proofs.PlanarSlices.SliceSource
import ParabolicRectifiability.Examples.Proofs.PlanarSlices.SliceGraphNull
import ParabolicRectifiability.Examples.Proofs.PlanarSlices.LipschitzExtend
import ParabolicRectifiability.Examples.Proofs.PlanarSlices.SliceHausdorff
import ParabolicRectifiability.Examples.Proofs.PlanarSlices.SmallSlopePieces
import ParabolicRectifiability.Examples.Proofs.DigitGraph.Purity
import ParabolicRectifiability.Examples.Proofs.PlanarSlices.ZeroDerivImage
import ParabolicRectifiability.Examples.Proofs.PlanarSlices.LipschitzNondiff
import ParabolicRectifiability.Examples.Proofs.DigitGraph.PureUnrectifiabilityStatements
import ParabolicRectifiability.Characterization.Statements.Branches
import ParabolicRectifiability.BetaP.Statements.Failures
import ParabolicRectifiability.Foundations.Statements.Measurability

/-! # Graph necessity and pure unrectifiability for the digit graph: composed lemmas

The theorems here delegate to their corresponding proofs `<name>_proof`, which have exactly the
displayed type and are proved in separate modules (prefix `e2_`).

The graph-source statement enters only `E2sbSliceGraphNull`, as hypotheses:
`Characterization.GraphSourceStatement` (proved as
`Characterization.graph_source_square_finite`), `BetaP.TimeSliceTransferStatement` (proved as
`c2_timeSliceTransfer`) and `Foundations.EnergyTwoStatement`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- **The finite source is locally Radon.** Route: `timeSlice`
is continuous (`isometry_point_zero`, or
`continuous_point`), so `ν.map timeSlice` is finite (`Measure.isFiniteMeasure_map`), hence
`IsFiniteMeasureOnCompacts`; inner regularity: `ν` is a finite measure on the Polish plane, so
`InnerRegular` (`InnerRegularCompactLTTop` instance for complete second-countable spaces plus
the `SigmaFinite` upgrade), then `Measure.InnerRegular.map_of_continuous`. -/
theorem e2_sb_sliceSource : E2sbSliceSource := by
  exact @e2_sb_sliceSource_proof

/-- **Graph-source nullity of the divergence set.** Route: put `μ = ν.map timeSlice` (finite on compacts and inner regular
by `hSrc`). For `z ∈ S`: `hTS.1 ν 2 two_pos .horizontal (Or.inl rfl) z` gives
`energyS μ 1 .horizontal 2 1 (ι z) = euclideanEnergyS ν 1 2 1 z = ⊤`, and
`(hE2 2 _ 1 _ _ .horizontal μ 1 one_pos (ι z)).1` turns it into
`squareEnergy μ 1 .horizontal 1 (ι z) = ⊤`. So `ι(S) ∩ Γ ⊆ Γ ∩ {S^1_{μ,H} = ∞}`, which is
`H_P^1`-null by `(hGS 2 _ 1 _ _).1 ε Γ μ _ _ 1 one_pos` (`measure_mono_null`). -/
theorem e2_sb_sliceGraphNull (hGS : Characterization.GraphSourceStatement)
    (hTS : BetaP.TimeSliceTransferStatement) (hE2 : EnergyTwoStatement) (hSrc : E2sbSliceSource) :
    E2sbSliceGraphNull := by
  exact @e2_sb_sliceGraphNull_proof hGS hTS hE2 hSrc

/-- **The slice preserves `H¹`.** Route: `timeSlice` is an
isometry (`ParabolicRectifiability.isometry_point_zero`;
or `Isometry.of_dist_eq` with `dist_point`), and
`Isometry.hausdorffMeasure_image` with `hausdorffP_eq`. (The null rest could also be obtained from
the Hausdorff clause of the time-slice transfer; for sets this is the same isometry fact, and no
transfer input is needed. `c2_timeSlice_hausdorff` reduces to the same fact.) -/
theorem e2_sb_sliceHausdorff : E2sbSliceHausdorff := by
  exact @e2_sb_sliceHausdorff_proof

/-- **Lipschitz extension from a subset of `ℝ`.**
Route: transport to `Fin 2 → ℝ` by `EuclideanSpace.equiv`/`WithLp.ofLp` (Lipschitz both ways),
`LipschitzOnWith.extend_pi` (mathlib), and back; the
constant may grow by a fixed factor. A narrow adapter; no orthogonal extension construction is needed. -/
theorem e2_sb_lipschitzExtend : E2sbLipschitzExtend := by
  exact @e2_sb_lipschitzExtend_proof

/-- **Rademacher for a Lipschitz curve.** A narrow
adapter of named mathlib results. Route: Rademacher
`LipschitzWith.ae_differentiableAt_real`  makes the
nondifferentiability set Lebesgue-null; `MeasureTheory.hausdorffMeasure_real` (`μH[1] = volume`
on `ℝ`) and the Hausdorff-image bound
`LipschitzWith.hausdorffMeasure_image_le` give `μH[1](F '' N) ≤ K · 0`. -/
theorem e2_sb_lipschitzNondiff : E2sbLipschitzNondiff := by
  exact @e2_sb_lipschitzNondiff_proof

/-- **The zero-derivative image is null.** Route
(a covering-free variant; a fivefold selection argument is an
alternative): fix `ε > 0` and `M`; the sets
`Z_m = {s ∈ Z ∩ [-M,M) : ‖F t - F s‖ ≤ ε|t - s| for |t - s| < 1/m}`, `m ≥ 1`, increase to
`Z ∩ [-M,M)` (uniform radius `1/m`); on each grid interval `[k/m, (k+1)/m)` the restriction
`F|_{Z_m}` is `ε`-Lipschitz, so `μH[1](F(Z_m)) ≤ 2Mε` (`LipschitzOnWith.hausdorffMeasure_image_le`,
`hausdorffMeasure_real`, finitely many grid intervals); continuity from below for this monotone
family of arbitrary sets (`Monotone.measure_iUnion`), then `ε ↓ 0`, then the countable union over
`M`. -/
theorem e2_sb_zeroDerivImage : E2sbZeroDerivImage := by
  exact @e2_sb_zeroDerivImage_proof

/-- **Small-slope pieces.** Route: `ε ∈ (0,1/4)`
with `2ε/(1-2ε) ≤ θ`; index pieces by a unit vector `e` of a countable dense subset of the
circle, `m ≥ 1` and `k ∈ ℤ`: `s ∈ [k/m,(k+1)/m)` with `HasDerivAt F v s`, `v ≠ 0`,
`‖v/‖v‖ - e‖ ≤ ε` and `‖F t - F s - (t - s) • v‖ ≤ ε‖v‖|t - s|` for `|t - s| < 1/m`
(`hasDerivAt_iff_isLittleO`); `V = span{e}`; along `e` the difference is `≥ (1-2ε)‖v‖|t-s|`,
normal to it `≤ 2ε‖v‖|t-s|`; re-index by `ℕ` (`Encodable`/`Denumerable`). -/
theorem e2_sb_smallSlopePieces : E2sbSmallSlopePieces := by
  exact @e2_sb_smallSlopePieces_proof

/-- **A planar small-slope set is a horizontal graph at time
zero.** Route: a short adapter of the proved
`ParabolicRectifiability.exists_horizontalGraph_of_flat_slope` with
`n = 2`, `k = 1`, `W = V`, `Z = timeSlice '' S`, `s = ε = θ`, `ε₀ = 0`: `θ ≤ θ`, `0 ≤ 0`,
`0 * (1 + θ) ≤ θ` (from `0 ≤ θ`); the slope hypothesis is the given one because
`(timeSlice x).1 - (timeSlice y).1 = x - y`; the time hypothesis is `√|0 - 0| ≤ 0`. The
graph is not rebuilt. -/
theorem e2_sb_slopeGraph : E2sbSlopeGraph := by
  exact @e2_sb_slopeGraph_proof

/-- **Pure one-unrectifiability from graph nullity.** Route: for `f` Lipschitz on `A` take a global extension `F` (`E2sbLipschitzExtend`); every `s` is
nondifferentiable, has `F'(s) = 0`, or has `F'(s) ≠ 0` (`DifferentiableAt.hasDerivAt`); the
first two images are null (`E2sbLipschitzNondiff`, `E2sbZeroDerivImage`); the third is covered by `F(P i)` with `θ = 1` (`E2sbSmallSlopePieces`),
each inside a time-zero graph `Γ i` (`E2sbSlopeGraph`); `μH[1](E ∩ F(P i)) = H_P^1(ι(E ∩ F(P i)))` (`E2sbSliceHausdorff`)
`≤ H_P^1(ι(E) ∩ Γ i) = 0`; countable subadditivity (`measure_iUnion_null`, `measure_union_null`). -/
theorem e2_sb_purity (hH : E2sbSliceHausdorff) (hX : E2sbLipschitzExtend)
    (hN : E2sbLipschitzNondiff) (hZ : E2sbZeroDerivImage) (hP : E2sbSmallSlopePieces)
    (hG : E2sbSlopeGraph) : E2sbPurity := by
  exact @e2_sb_purity_proof hH hX hN hZ hP hG

end ParabolicRectifiability.Examples
