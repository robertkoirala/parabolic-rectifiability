import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.Weights
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.WeightsDiverge
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.FitTilted
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.Fit
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.LevelMeasure
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.Segment
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.PairCost
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.BallContain
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.Cell
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.BandBeta
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.BandEnergy
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.LabelBounds
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.Generation
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SetBasic
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.Cover
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.TreeLength
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.Mass
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.Divergence
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.Levels
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.LevelPoint
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.LevelAE
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.Density
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # The decorated-segment witness: intermediate lemmas

One theorem for each intermediate statement of `AboveTwoSegmentStatements`, each delegating to
the corresponding `<name>_proof`. Lemmas that depend on other intermediate statements (or on
`E2PlanarLine`, `E2sbSlopeGraph`) take them as hypotheses (implication form); the hypotheses are
discharged in `AboveTwoSegmentGlue`. Each docstring sketches the proof.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-! ## Weights -/

/-- **The weights: bounds and sum.** Proof:
`δ_j > 0` since `log(j+1) ≥ 0`; `δ_j ≤ δ_0 = 1/100 < 1/4` (the denominator is increasing).
With `f(x) = 1/(x (1 + log x)^2)`, antitone on `[1, ∞)` with antiderivative `-1/(1 + log x)`:
`δ_{j+1} = f(j+2)/100 ≤ (1/100) ∫_{j+1}^{j+2} f`, so partial sums are at most
`(1/100) ∫_1^∞ f = 1/100` (`AntitoneOn.sum_le_integral`, `integral_eq_sub_of_hasDerivAt`);
summability from bounded nonnegative partial sums (`summable_of_sum_range_le`,
`tsum_le_of_sum_range_le`). -/
theorem e2_sap_weights : E2sapWeights := by
  exact @e2_sap_weights_proof

/-- **The weights: divergence for `q < 1`.**
Proof: for `q < q' < 1`, `(1 + log(j+1))^{2q} ≤ C (j+1)^{q'-q}` (`isLittleO_log_rpow_atTop`), so
`δ_j^q ≥ c (j+1)^{-q'}` eventually; `Σ (j+1)^{-q'} = ∞` (`Real.summable_one_div_nat_rpow`,
`q' ≤ 1`); comparison in `ℝ≥0∞` (`ENNReal.tsum_coe_ne_top_iff_summable`,
`Summable.of_nonneg_of_le`). A dyadic count is an equivalent route. -/
theorem e2_sap_weightsDiverge : E2sapWeightsDiverge := by
  exact @e2_sap_weightsDiverge_proof

/-! ## The fitting lemma -/

/-- **The fitting lemma, tilted lines.** Proof: the
reflection `s ↦ -s` preserves `Icc (-h) h` and Lebesgue measure, so the integral equals the
average of `|αs - c|^p` and `|αs + c|^p`; convexity of `t ↦ |t|^p` for `p ≥ 1`
(`convexOn_rpow`, `abs`) gives `(|x - c|^p + |x + c|^p)/2 ≥ |x|^p`; then
`∫_{-h}^{h} |α|^p |s|^p ds = 2|α|^p h^{p+1}/(p+1)` (`integral_rpow`, symmetry) and
`|α|^p ≥ 4^{-p}`. Pass between `ofReal |·| ^ p` and `ofReal (|·|^p)` by
`ENNReal.ofReal_rpow_of_nonneg`, and between lintegral and integral by
`ofReal_integral_eq_lintegral_ofReal`. -/
theorem e2_sap_fitTilted : E2sapFitTilted := by
  exact @e2_sap_fitTilted_proof

/-- **The fitting lemma, all lines.** Proof: three
cases. `|α| ≥ 1/4`: `E2sapFitTilted`, and `2·4^{-p}/(p+1) ≥ c_p δ` since `δ ≤ 1`. `|α| < 1/4`,
`|c| ≥ h/2`: on `[-h,h]`, `|αs - c| ≥ h/4`, so the baseline costs `≥ 2h (h/4)^p ≥ c_p δ h^{p+1}`.
`|α| < 1/4`, `|c| < h/2`: `|β| ≥ √15/4`, the satellite has `|s| ≤ 5h/8`, so
`|αs + βh - c| ≥ (√15/4 - 5/32 - 1/2) h > h/4`, and the satellite (length `δh`) costs
`≥ δh (h/4)^p ≥ c_p δ h^{p+1}`. No minimizing line is used. -/
theorem e2_sap_fit (hT : E2sapFitTilted) : E2sapFit := by
  exact @e2_sap_fit_proof hT

/-! ## Horizontal segments are intervals -/

/-- **Arclength on one level.** Proof: `s ↦ (s, c)` is an
isometry `ℝ → ℝ²` (`EuclideanSpace.dist_eq`, `Fin.sum_univ_two`) and a measurable embedding
(closed embedding); `Isometry.hausdorffMeasure_image` and `hausdorffMeasure_real` (`μH[1] = volume`
on `ℝ`) give `μH[1] (ι '' B) = volume B`; compare both measures on Borel sets
(`Measure.ext`, `MeasurableEmbedding.map_apply`, `Measure.restrict_apply`). -/
theorem e2_sap_levelMeasure : E2sapLevelMeasureStatement := by
  exact @e2_sap_levelMeasure_proof

/-- **Segments.** Proof: set extensionality
for the image (`e2_sapPt s b 0 = s`, `e2_sapPt s b 1 = b`, and `w = e2_sapPt (w 0) (w 1)`);
`E2sapLevelMeasureStatement` with `A = Icc u v`, then `Measure.map_apply`/`Real.volume_Icc` for the value and
`MeasurableEmbedding.lintegral_map` for the integral (valid for every `f`). -/
theorem e2_sap_segment (hL : E2sapLevelMeasureStatement) : E2sapSegment := by
  exact @e2_sap_segment_proof hL

/-! ## The band lower bound -/

/-- **The translated pair cost.** Proof:
`E2PlanarLine` writes `dist(w, U) = |α w₀ + β w₁ - c|` with `α^2 + β^2 = 1`; `E2sapSegment` turns
both `H¹`-integrals into parameter integrals over `[x-h, x+h]` and
`[x+ξ-δh/2, x+ξ+δh/2]`; translate by `x` (`lintegral_comp_add_right` / `map_add_right_eq_self`
with `Measure.restrict` of a translated interval); the offset becomes `c' = c - αx - βy`;
apply `E2sapFit`. -/
theorem e2_sap_pairCost (hL : E2PlanarLine) (hS : E2sapSegment) (hF : E2sapFit) :
    E2sapPairCost := by
  exact @e2_sap_pairCost_proof hL hS hF

/-- **Both segments lie in the ball.** Proof:
`EuclideanSpace.dist_eq` with two coordinates; on the baseline the distance is `|s - x| ≤ h < 2h`;
on the satellite `|s - x| ≤ |ξ| + δh/2 ≤ 5h/8` and the vertical offset is `h`, so the distance is
at most `h √(1 + 25/64) < 2h ≤ r`. -/
theorem e2_sap_ballContain : E2sapBallContain := by
  exact @e2_sap_ballContain_proof

/-- **The band bound for the full measure.**
Proof: unfold `euclideanBetaPow` at `r > 0`; for every line `U`,
`∫_{B} dist^p d(H¹⌊E) ≥ ∫ dist^p d(H¹⌊(I ∪ J))` (`Measure.restrict_restrict` with the open ball,
`Measure.restrict_mono_set`, `I ∪ J ⊆ E ∩ B` by `E2sapBallContain`); `I` and `J` are disjoint (heights `y`
and `y + h`) and `J` is closed, so `H¹⌊(I ∪ J) = H¹⌊I + H¹⌊J` (`Measure.restrict_union`);
`E2sapPairCost` bounds the sum below by `c_p δ h^{p+1}` (lower bound before the infimum, `le_iInf`); finally
`r^{-1-p} ≥ (4h)^{-1-p}`. The measure is the complete `H¹⌊E`, not a reassigned one. -/
theorem e2_sap_bandBeta (hP : E2sapPairCost) (hB : E2sapBallContain) : E2sapBandBeta := by
  exact @e2_sap_bandBeta_proof hP hB

/-! ## The divergence -/

/-- **The nearest cell midpoint.** Proof: with
`h = L/N_j > 0`, take `m = ⌊(x - a)/h⌋₊`; `0 ≤ (x-a)/h < N_j` gives `m < N_j`, and
`m ≤ (x-a)/h < m + 1` gives `|(m + 1/2)h - (x - a)| ≤ h/2` (`Nat.floor_le`, `Nat.lt_floor_add_one`). -/
theorem e2_sap_cell : E2sapCell := by
  exact @e2_sap_cell_proof

/-- **Divergence on disjoint bands (generic).**
Proof: with `h_j = H/N_j`, `h_{j+1} = h_j/8`, so the closed bands `[2h_j, 4h_j]` are pairwise
disjoint; choose `j₁ ≥ j₀` with `4h_{j₁} < a`; `∫_{Ioo 0 a} ≥ Σ_{j ≥ j₁} ∫_{band_j}`
(`Measure.restrict_iUnion`/`lintegral_iUnion` on measurable disjoint sets, no measurability of
`f` needed, then monotonicity); on a band, `f^{2/p} ≥ (A d_j)^{2/p}` and the `dr/r`-mass is
`log 2` by `ParabolicRectifiability.scaleMeasure_Icc_two_mul` at `s = 2H/N_j`, rewriting
`2 * (2 * (H/N_j)) = 4 * (H/N_j)`; `Σ_{j ≥ j₁} d_j^{2/p} = ∞` since the
omitted head is finite (`ENNReal.tsum_eq_add_tsum_ite` or `sum_add_tsum_nat_add`). -/
theorem e2_sap_bandEnergy : E2sapBandEnergy := by
  exact @e2_sap_bandEnergy_proof

/-- **Divergence of the energy off the endpoints.** Proof: let
`z ∈ E \ Z`; pick `n ∈ I` with `z ∈ [a, a+L] × {b}` (the segment of `n`); `z` is not an
endpoint, so `a < z₀ < a + L` and `z = (z₀, b)`. Choose `j₀ ≥ 1` with `L/N_j ≤ min(z₀ - a,
a + L - z₀)` for `j ≥ j₀`. For each such `j`, `E2sapCell` gives `m < N_j` with
`ξ = a + (m+1/2)h_j - z₀`, `|ξ| ≤ h_j/2`; the child label `(j,m) :: label n` is valid, its code
`Encodable.encode ((j,m) :: label n)` lies in `I` (`Denumerable.ofNat_encode`), and its segment
is exactly `[z₀+ξ-δ_jh_j/2, z₀+ξ+δ_jh_j/2] × {b + h_j}`; the baseline
`[z₀-h_j, z₀+h_j] × {b}` lies in the parent. `E2sapBandBeta` (`δ_j ≤ 1/4` by `E2sapWeights`)
gives `β^p ≥ A_p δ_j` on `[2h_j, 4h_j]` with `A_p = c_p 4^{-p-1} > 0`, and `E2sapBandEnergy` with
`d = δ`, `H = L` and `E2sapWeightsDiverge` at `q = 2/p ∈ (0,1)` gives `S^a = ∞` for every
`a > 0`. The same `Z` serves every `p` and `a`. -/
theorem e2_sap_divergence (hW : E2sapWeights) (hD : E2sapWeightsDiverge)
    (hG : E2sapLabelBounds) (hB : E2sapBandBeta) (hC : E2sapCell) (hE : E2sapBandEnergy) :
    E2sapDivergenceOff := by
  exact @e2_sap_divergence_proof hW hD hG hB hC hE

/-! ## The mass -/

/-- **Bounds of every labelled segment.**
Proof: induction on the label with the invariant `L > 0`, `0 ≤ a`, `a + L ≤ 1`, `0 ≤ b` and
`b + (4/255) L ≤ 4/255`: a child has `L' = δ_j L/N_j ≤ L/256` (`δ_j < 1/4`, `N_j ≥ 64`),
`a' ≥ a`, `a' + L' ≤ a + (m+1)h ≤ a + L` (`m < N_j`), and `b' = b + L/N_j ≤ b + L/64`. -/
theorem e2_sap_labelBounds (hW : E2sapWeights) : E2sapLabelBounds := by
  exact @e2_sap_labelBounds_proof hW

/-- **`E` is Borel and bounded.** Proof:
each `horizontalSegment` is closed (preimages under the continuous coordinates
`EuclideanSpace.proj`), the index type is countable, `MeasurableSet.iUnion`; by
`E2sapLabelBounds`,
`E ⊆ [0,1]²`, which lies in `closedBall 0 2` (`Metric.isBounded_closedBall.subset`). -/
theorem e2_sap_setBasic (hG : E2sapLabelBounds) : E2sapSetBasic := by
  exact @e2_sap_setBasic_proof hG

/-- **Generation lengths.** Proof: induction on
`g`; the valid labels of length `g+1` are `(j,m) :: l` with `l` valid of length `g`, `j ≥ 1`,
`m < N_j` (an equivalence with a sigma type); in `ℝ≥0∞`,
`Σ_{j≥1} Σ_{m<N_j} ofReal(δ_j L/N_j) = ofReal L · Σ_{j≥0} ofReal δ_{j+1}`
(`ENNReal.tsum_sigma'`, `ENNReal.tsum_mul_left`, `Finset.sum_const`, `ENNReal.ofReal_mul`,
positivity from `E2sapWeights` and `L ≥ 0` along the induction). -/
theorem e2_sap_generation (hW : E2sapWeights) : E2sapGeneration := by
  exact @e2_sap_generation_proof hW

/-- **Total labelled length.** Proof: the codes
in `I` are in bijection with valid labels (`Denumerable.eqv`, `Equiv.tsum_eq`); split by length
(`Equiv.sigmaFiberEquiv`, `ENNReal.tsum_sigma'`); `E2sapGeneration` gives `Σ_g D'^g` with
`D' = Σ_j ofReal δ_{j+1} = ofReal D ≤ ofReal (1/100)` (`ENNReal.ofReal_tsum_of_nonneg`,
`E2sapWeights`); `ENNReal.tsum_geometric` and `(1 - 1/100)⁻¹ = 100/99`. -/
theorem e2_sap_treeLength (hW : E2sapWeights) (hGen : E2sapGeneration) : E2sapTreeLength := by
  exact @e2_sap_treeLength_proof hW hGen

/-- **`1 ≤ H¹(E) ≤ 100/99`.** Proof: lower
bound: the root label `[]` is valid, its code `Encodable.encode []` lies in `I`, its segment is
`[0,1] × {0}` and has `H¹ = 1` (`E2sapSegment`), `measure_mono`. Upper bound: `measure_iUnion_le`,
`E2sapSegment` for each segment (`u ≤ v` by `E2sapLabelBounds`), and `E2sapTreeLength`. Labels
are counted with multiplicity; no equality with the labelled sum is used. -/
theorem e2_sap_mass (hS : E2sapSegment) (hG : E2sapLabelBounds) (hT : E2sapTreeLength) :
    E2sapMass := by
  exact @e2_sap_mass_proof hS hG hT

/-! ## The density -/

/-- **Decomposition into levels.** Proof: the
heights `{b i}` are countable; choose an injective `c : ℕ → ℝ` whose range contains them (e.g. a
bijection of `ℕ` with the countably infinite set `range b ∪ range (Nat.cast)`); let
`A_k = ⋃_{i : b i = c k} [u i, v i]` (Borel). The lines `ℝ × {c_k}` are disjoint and closed,
`F ⊆ ⋃_k ℝ × {c_k}` and `F ∩ (ℝ × {c_k}) = (s ↦ (s,c_k))(A_k)`; hence
`H¹⌊F = Σ_k H¹⌊(F ∩ ℝ × {c_k})` (`Measure.restrict_iUnion`, then `Measure.restrict_restrict`) and
`E2sapLevelMeasureStatement` on each level. -/
theorem e2_sap_levels (hL : E2sapLevelMeasureStatement) : E2sapLevels := by
  exact @e2_sap_levels_proof hL

/-- **Density at a good point.** Proof: put
`z = (s, c_m)`. Lower bound: `ν(B(z,r)) ≥ |A_m ∩ (s-r, s+r)|`, whose ratio to `r` tends to `2` (the
density point, `closedBall` versus `Ioo` differ by a null set). Upper bound, for `N ≥ m`: the
levels `k ≤ N`, `k ≠ m`, are at positive distance `|c_k - c_m|` (injectivity), so for small `r`
they miss `B(z,r)`; every level contributes at most `|A_k ∩ (s-r, s+r)|`, and the levels `k > N`
contribute at most `∫_{closedBall s r} g_N` (`lintegral_tsum`, `lintegral_indicator`); hence
`limsup ν(B(z,r))/r ≤ 2 (1 + g_N(s))`; let `N → ∞`. -/
theorem e2_sap_levelPoint : E2sapLevelPoint := by
  exact @e2_sap_levelPoint_proof

/-- **Lebesgue differentiation on the levels.**
Proof: density points: `Besicovitch.ae_tendsto_measure_inter_div volume (A m)` (exactly the
`IsLebesgueDensityPoint` form). Lebesgue points: each `g_N` is measurable with
`∫ g_N ≤ Σ_k |A_k| < ∞` (`lintegral_tsum`), so the Besicovitch Vitali family gives the
`closedBall` averages a.e. (`VitaliFamily.ae_tendsto_lintegral_div` for `Besicovitch.vitaliFamily
volume`, composed with `Besicovitch.tendsto_filterAt volume s` to pass to `closedBall s r`,
`r ↓ 0`); countably many `N` (`ae_all_iff`). Tails: `g_0 < ∞` a.e.
(`ae_lt_top`), so `g_N(s) → 0` (`ENNReal.tendsto_tsum_compl_atTop_zero` or
`ENNReal.tendsto_sum_nat_add`). Restrict from `volume` to `volume.restrict (A m)`
(`ae_restrict_of_ae`). -/
theorem e2_sap_levelAE : E2sapLevelAE := by
  exact @e2_sap_levelAE_proof

/-- **Density of countable unions of horizontal segments.** Proof:
`E2sapLevels` gives `H¹⌊F = ν = Σ_k (s ↦ (s,c_k))_#(L¹⌊A_k)`; `Σ_k |A_k| = ν(ℝ²) = H¹(F) < ∞`
(`Measure.sum_apply`, `Measure.map_apply`); `E2sapLevelAE` for each level, transported to `ν` by
`Measure.ae_sum_eq` and `MeasurableEmbedding.ae_map_iff` (no measurability of the property is
needed); `E2sapLevelPoint` at each good point. -/
theorem e2_sap_density (hLv : E2sapLevels) (hP : E2sapLevelPoint) (hAE : E2sapLevelAE) :
    E2sapDensity := by
  exact @e2_sap_density_proof hLv hP hAE

/-! ## The zero-slope cover -/

/-- **Exact zero-slope cover.** Proof: take
`V = span {e₀}` (`finrank = 1`, `finrank_span_singleton`); two points of one horizontal segment
differ by a multiple of `e₀`, so `Vᗮ.starProjection (x - y) = 0` and the slope condition holds with
`θ = 0` (`Submodule.starProjection_orthogonal_eq_zero_iff` or `starProjection_eq_zero_of_mem`);
`E2sbSlopeGraph` gives one graph `Γ_i : HorizontalGraph 2 1 0` with
`ι([a_i, a_i + L_i] × {b_i}) ⊆ Γ_i.image` for each `i ∈ I` (`Classical.choose`); then
`Set.image_iUnion`. -/
theorem e2_sap_cover (hSG : E2sbSlopeGraph) : E2sapCover := by
  exact @e2_sap_cover_proof hSG

end ParabolicRectifiability.Examples
