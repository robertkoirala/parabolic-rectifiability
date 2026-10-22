import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyStatements
import ParabolicRectifiability.Examples.Proofs.Reductions.ReductionStatements
import ParabolicRectifiability.Examples.Proofs.Lacunary.Support
import ParabolicRectifiability.Examples.Proofs.DiffuseMeasures.BetaPowBand
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.CosinePlateau
import ParabolicRectifiability.Examples.Proofs.Lacunary.Frequencies.KernelJensen
import ParabolicRectifiability.Examples.Proofs.Lacunary.Frequencies.KernelLogIntegral
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.BallPullback
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.DensityLimit
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.FullInterval
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.HausdorffExact
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.InteriorDensity
import ParabolicRectifiability.Examples.Proofs.Lacunary.Frequencies.InvSqrtDecay
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.Isometry
import ParabolicRectifiability.Examples.Proofs.Lacunary.Frequencies.KernelBound
import ParabolicRectifiability.Examples.Proofs.Lacunary.Frequencies.KernelSum
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.LittleHolder
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.LowerFirst
import ParabolicRectifiability.Examples.Proofs.Lacunary.Frequencies.Occupancy
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.PlateauBeta
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.PlateauError
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.PlateauLower
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.SmallSlope
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.TestBound
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.UpperEnergy
import ParabolicRectifiability.Examples.Proofs.StationaryGraphs.SnowflakeExtension
import ParabolicRectifiability.Examples.Proofs.StationaryGraphs.TimeHausdorff

/-! # Lacunary estimates: composed lemmas

The theorems delegate to their corresponding proofs `<name>_proof`, which have exactly the type
below (in modules with prefix `e2_`). A statement that needs the result of another takes the
other's named statement as a hypothesis (implication form), so that the proofs are independent.

Target: `Examples.lacunary_estimates_bundle : LacunaryEstimatesStatement` (internal facts:
`b_{j+1} ≤ b_j/4`; continuity is obtained from the isometry, periodicity is not needed here).

Inputs (taken as hypotheses, never restated or reproved): `E2LacunaryWeightStatement`
(`w_j > 0`, `w_{j+1} ≤ w_j/1000`, `w_j ≤ w_0 1000^{-j}`, `Σ w` summable,
`Σ_{i>j} w_i ≤ w_j/999`, with `w_j = a_j/√N_j`) and `E2StationaryLengthStatement`
(`r²/2 ≤ |(t-r², t+r²) ∩ [-1,1]| ≤ 2r²` for `t ∈ [-1,1]`, `0 < r ≤ 2`).

The shared facts live once, in the support module imported here: the snowflake isometry adapter
`e2_isometry_time_of_dist` and the source mass `e2_lacunarySource_univ`. Continuity of `F` is
`(e2_isometry_time_of_dist h).continuous.comp Metric.Snowflaking.continuous_toSnowflaking`; source
masses use `Measure.map_apply` and the restriction API directly; the empty horizontal family at
`n = 1`, `k = 2` is `HorizontalModel.isEmpty_of_not_available`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-! ## Modulus and isometry -/

/-- **Reciprocal-frequency decay.**
Route: `16 N_j ≤ N_{j+1}` (field `frequency_growth`) and `0 < N_j` give
`4 √N_j = √(16 N_j) ≤ √N_{j+1}` (`Real.sqrt_le_sqrt`, `Real.sqrt_mul_self`), then
`inv_le_inv₀` / `div_eq_mul_inv`. Inputs: `IsLacunaryData` (fields
`IsLacunaryData.frequency_growth`, `IsLacunaryData.frequency_pos`). -/
theorem e2_lacunary_invSqrtDecay : E2InvSqrtDecayStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_invSqrtDecay_proof

/-- **Lacunary kernel sum `≤ 8/3`.**
Route: `b_j ≤ b_0 4^{-j}` and `b_j ≥ 4^{J-j} b_J` (`j ≤ J`) by induction from the decay. Summability:
`K_{b_j}(r) ≤ b_j/r ≤ (b_0/r) 4^{-j}` (`Summable.of_nonneg_of_le`, `summable_geometric_of_lt_one`).
Bound: if `r > b_0`, every term is `b_j/r < 4^{-j}`, total `< 4/3`. Otherwise let `J` be the last
index with `r ≤ b_J` (the set is finite and nonempty since `b_j → 0`; `Nat.find` on `b_j < r`):
for `j ≤ J`, `r/b_j ≤ 4^{-(J-j)}`, sum `≤ 4/3` (`geom_sum_eq`); for `j > J`,
`b_j/r < 4^{-(j-J-1)}`, sum `≤ 4/3` (`Summable.sum_add_tsum_nat_add`, `tsum_geometric_of_lt_one`).
Inputs: mathlib only. -/
theorem e2_kernelSum_le : E2KernelSumStatement := by
  exact ParabolicRectifiability.Examples.e2_kernelSum_le_proof

/-- **Modulus kernel bound.**
Implication form over `E2LacunaryWeightStatement`.
Route: summability of `w_j cos(N_j t)` from `Σ w` (`E2LacunaryWeightStatement`, 4th conjunct); `f t - f s =
ε Σ' w_j (cos N_j t - cos N_j s)` (`Summable.tsum_sub`); `|cos x - cos y| ≤ min(2, |x - y|)`
(`Real.abs_cos_sub_cos_le`, `Real.abs_cos_le_one`); with `|t-s| ≤ r²`,
`w_j min(2, N_j r²) = min(2 a_j r/(r√N_j), a_j r · r√N_j) ≤ 2 a_j r K_{b_j}(r)`; summability of
`a_j K_{b_j}(r) ≤ w_j/r`; `norm_tsum_le_tsum_norm`, `Summable.tsum_le_tsum`, `tsum_mul_left`.
Inputs: `E2LacunaryWeightStatement`; mathlib. -/
theorem e2_lacunary_kernelBound : E2LacunaryWeightStatement → E2KernelBoundStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_kernelBound_proof

/-- **The isometry.**
Implication form over the kernel bound, the kernel-sum bound, the frequency decay.
Route: for `t ≠ s` put `r = √|t-s| > 0` (so `|t-s| = r²`); the kernel bound gives
`|f t - f s| ≤ 2εr Σ a_j K_j ≤ 2εr Σ K_j` (`a_j ≤ 1`, `Summable.tsum_le_tsum` with the kernel-sum bound's summability)
`≤ 2εr · 8/3 ≤ r` (the kernel-sum bound with `b = e2_invSqrtFreq N`, positive by `frequency_pos`, decaying by the frequency decay;
`ε ≤ 3/16`). Then `dist_point` and `‖single 0 x - single 0 y‖ = |x - y|`
(`EuclideanSpace.single` is `PiLp.single 2`: `PiLp.single_sub`, `PiLp.norm_single`,
`Real.norm_eq_abs`) give `max(|f t - f s|, √|t-s|) =
√|t-s|`; `t = s` is trivial. Inputs: `dist_point`. -/
theorem e2_lacunary_isometry :
    E2KernelBoundStatement → E2KernelSumStatement → E2InvSqrtDecayStatement →
      LacunaryIsometryStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_isometry_proof

/-! ## Ball pullback -/

/-- **Ball pullback.**
Implication form over the isometry.
Route: `F` is continuous, hence measurable, by the support adapter:
`(e2_isometry_time_of_dist (hiso ε a N hε hε' hd)).continuous.comp
Metric.Snowflaking.continuous_toSnowflaking`. `setLIntegral_map`
(`Metric.isOpen_ball.measurableSet`, `hg`, `hF`) turns the left side into
`∫⁻ s in F⁻¹(P(F t, r)), g(F s) ∂(volume.restrict E)`; `Measure.restrict_restrict` (measurable
preimage) gives `volume.restrict (F⁻¹(P) ∩ E)`; the isometry gives
`F⁻¹(P(F t, r)) = Ioo (t - r²) (t + r²)` (`Real.sqrt_lt'`, `abs_sub_lt_iff`); `Set.inter_comm`.
No measurability of `E` is needed. Inputs: `LacunaryIsometryStatement`; support
`e2_isometry_time_of_dist`. -/
theorem e2_lacunary_ballPullback : LacunaryIsometryStatement → E2BallPullbackStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_ballPullback_proof

/-! ## Hausdorff identity -/

/-- **Hausdorff measure of the snowflake line.**
Route: `toSnowflaking : ℝ → Time` is `HolderWith 1 (1/2)` and `ofSnowflaking : Time → ℝ` is
`HolderWith 1 2` (`Metric.Snowflaking.edist_toSnowflaking_toSnowflaking`,
`Metric.Snowflaking.edist_ofSnowflaking_ofSnowflaking`); `HolderOnWith.hausdorffMeasure_image_le` gives
`μH[2](toSnow '' E) ≤ μH[1] E` and `μH[1] E = μH[1](ofSnow '' (toSnow '' E)) ≤ μH[2](toSnow '' E)`
(`Metric.Snowflaking.image_ofSnowflaking_image_toSnowflaking`); finally
`MeasureTheory.hausdorffMeasure_real : μH[1] = volume`. Valid for every set `E`.
Inputs: mathlib (Hausdorff measure and snowflaking API). -/
theorem e2_time_hausdorff : E2TimeHausdorffStatement := by
  exact ParabolicRectifiability.Examples.e2_time_hausdorff_proof

/-- **Exact Hausdorff identity `H_P²(F(E)) = |E|`.** Implication form over the snowflake Hausdorff measure and the isometry.
Route: `G = fun τ : Time => F τ.val` is an `Isometry` by the support adapter
`e2_isometry_time_of_dist` applied to the isometry clause;
`F '' E = G '' (toSnow '' E)` (`Set.image_image`, `τ.val` of `toSnowflaking t` is `t` by `rfl`);
`Isometry.hausdorffMeasure_image (Or.inl zero_le_two)`; `hausdorffP_eq`
then the snowflake Hausdorff measure. Inputs: the snowflake Hausdorff measure statement, the isometry, support
`e2_isometry_time_of_dist`. -/
theorem e2_lacunary_hausdorffExact :
    E2TimeHausdorffStatement → LacunaryIsometryStatement → E2HausdorffExactStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_hausdorffExact_proof

/-! ## Density limit -/

/-- **Density limit `2`.**
Implication form over the ball identity.
Route: `Besicovitch.ae_tendsto_measure_inter_div volume E` gives, for `volume.restrict E`-a.e.
`t`, `|E ∩ [t-ρ,t+ρ]| / (2ρ) → 1` as `ρ → 0+` (`Real.volume_closedBall`). By the ball identity,
`densityRatio ν_E 2 (F t) r = |E ∩ (t-r², t+r²)| / r²`; open and closed intervals differ by two
null points (`measure_union_le`, `Real.volume_singleton`); compose with `r ↦ r²`, which maps
`𝓝[>] 0` to `𝓝[>] 0`; the factor `2` comes from `|[t-r², t+r²]| = 2r²` (`ENNReal.div_eq_inv_mul`,
`ENNReal.Tendsto.const_mul`). Inputs: `LacunaryBallMeasureStatement`. -/
theorem e2_lacunary_densityLimit :
    LacunaryBallMeasureStatement → LacunaryDensityLimitStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_densityLimit_proof

/-! ## Full interval -/

/-- **Full-interval regularity.** Implication form over the ball identity and `E2StationaryLengthStatement`.
Route: with `C = 2`, the ball identity at `E = J` gives `ν_J(P(F t, r)) = |J ∩ (t-r², t+r²)|`
(`Set.inter_comm`), and `E2StationaryLengthStatement` (`r ≤ 1 ≤ 2`) bounds it between `r²/2` and `2r²`. For `-1 < t < 1`
and `r² < min(1+t, 1-t)` (`eventually_nhdsWithin_of_forall`, `Metric.eventually_nhds_iff`), the
interval lies inside `J`, so the ball mass is `2r²` (`Real.volume_Ioo`) and the ratio is exactly
`ofReal (2r²) / ofReal r ^ 2 = 2` (`ENNReal.ofReal_pow`, `ENNReal.mul_div_cancel_right`).
Inputs: `LacunaryBallMeasureStatement`, `E2StationaryLengthStatement`. -/
theorem e2_lacunary_fullInterval :
    LacunaryBallMeasureStatement → E2StationaryLengthStatement →
      LacunaryFullIntervalStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_fullInterval_proof

/-! ## Upper energy -/

/-- **Single-scale test bound.**
Implication form over the ball pullback and the kernel bound.
Route: `betaPow` at `r > 0` (`ite_eq_left`; `if_pos` is deprecated in the pin); bound the infimum by the
vertical model
`Sum.inr ⟨0, le_rfl, rfl, ⟨⊥, finrank_bot, single 0 (f t), _⟩⟩` (`iInf_le`); its distance
`infEDist (F s) (modelSet L) ≤ edist (F s) (point (single 0 (f t)) s) = ofReal |f s - f t|`
(`Metric.infEDist_le_edist_of_mem`, `edist_dist`, `dist_point`). the ball pullback turns the fit into
`∫⁻ s in E ∩ (t-r², t+r²), …`; the kernel bound gives `|f s - f t| ≤ 2εr S(r)` there; the interval has
measure `≤ 2r²` (`measure_mono`, `Real.volume_Ioo`); then
`r^{-(2+q)} · 2r² · (2εrS)^q = 2^{q+1} ε^q S^q` (`ENNReal.ofReal_rpow_of_nonneg`,
`ENNReal.rpow_add`, `Real.mul_rpow`). Measurability of `w ↦ infEDist w L ^ q`:
`(Metric.continuous_infEDist).measurable.pow_const`. Inputs: the ball pullback, the kernel bound statements;
`VerticalModel.mem_toSet_point`. -/
theorem e2_lacunary_testBound :
    E2BallPullbackStatement → E2KernelBoundStatement → E2TestBoundStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_testBound_proof

/-- **Weighted Jensen for kernel sums.**
Route: summability by comparison (`x_j K_j ≤ K_j`, `x_j^q K_j ≤ K_j` from `0 ≤ x ≤ 1`,
`Real.rpow_le_one`). `q = 1`: equality with `M^0 = 1`. `q > 1`: Hölder
`Real.inner_le_Lp_mul_Lq_tsum_of_nonneg` with
`f = x K^{1/q}`, `g = K^{1-1/q}`, conjugate exponents `q, q/(q-1)`, gives
`Σ x K ≤ (Σ x^q K)^{1/q} (Σ K)^{1-1/q}`; raise to `q` (`Real.rpow_le_rpow`, `Real.rpow_mul`) and
use `Σ K ≤ M` (`Real.rpow_le_rpow` with exponent `q-1 ≥ 0`). Inputs: mathlib only. -/
theorem e2_kernelJensen : E2KernelJensenStatement := by
  exact ParabolicRectifiability.Examples.e2_kernelJensen_proof

/-- **`∫_0^∞ K_b(r) dr/r = 2`.**
Route: split `Ioi 0 = Ioc 0 b ∪ Ioi b` (`lintegral_union`); on `(0,b]` the kernel is `r/b`, and
`setLIntegral_scaleMeasure` gives `∫_0^b (1/r)(r/b) dr = 1`;
on `(b,∞)` it is `b/r = b · (ofReal r)⁻¹ ^ 1`, and `lintegral_inv_pow_Ioi_scaleMeasure 1`
gives `b · (1/b) = 1`. Inputs: `setLIntegral_scaleMeasure`,
`lintegral_inv_pow_Ioi_scaleMeasure`. -/
theorem e2_kernelLogIntegral : E2KernelLogIntegralStatement := by
  exact ParabolicRectifiability.Examples.e2_kernelLogIntegral_proof

/-- **All-scale upper energy.**
Implication form over the single-scale test bound, the weighted Jensen inequality, the logarithmic kernel integral, the kernel-sum bound, the frequency decay.
Route: `C_q = 2^{q+2} (8/3)^{q-1}`. For every `R`, `energyT … R ≤ ∫⁻ r in Ioi 0, B_q(F t, r)`
(`lintegral_mono_set`, `Ioo 0 R ⊆ Ioi 0`; `R ≤ 0` gives `0`), so the supremum is bounded
(`iSup_le`). Pointwise in `r > 0`: the single-scale test bound, then the weighted Jensen inequality with `x = a`, `K_j = K_{b_j}(r)`, `M = 8/3`
(the kernel-sum bound with the frequency decay), giving `B_q ≤ ofReal(2^{q+1} ε^q (8/3)^{q-1}) · Σ' ofReal(a_j^q K_j(r))`
(`ENNReal.ofReal_tsum_of_nonneg`). Tonelli (`lintegral_tsum`, each term continuous in `r` on
`Ioi 0`, hence a.e.-measurable) and the logarithmic kernel integral give `Σ' ofReal(a_j^q) · 2`.
Inputs: the single-scale test bound, the weighted Jensen inequality, the logarithmic kernel integral, the kernel-sum bound, the frequency decay statements. -/
theorem e2_lacunary_upperEnergy :
    E2TestBoundStatement → E2KernelJensenStatement → E2KernelLogIntegralStatement →
      E2KernelSumStatement → E2InvSqrtDecayStatement → LacunaryUpperEnergyStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_upperEnergy_proof

/-! ## Plateaus and lower energy -/

/-- **Plateau decomposition.**
Implication form over `E2LacunaryWeightStatement`.
Route: split `Σ' i, w_i cos(N_i s) = Σ_{i<j} + w_j cos(N_j s) + Σ' i, w_{j+1+i} cos(…)`
(`Summable.sum_add_tsum_nat_add`, `Finset.sum_range_succ`; summability from `E2LacunaryWeightStatement`). Low part:
`|Σ_{i<j} w_i (cos N_i s - cos N_i t)| ≤ Σ_{i<j} w_i N_i |s-t| ≤ (π/N_j) Σ_{i<j} a_i √N_i ≤ w_j/100`
(`Real.abs_cos_sub_cos_le`, `w_i N_i = a_i √N_i`, field `IsLacunaryData.low_frequency` divided by
`√N_j`).
High part: `≤ Σ' w_{j+1+i} ≤ w_j/999` (`E2LacunaryWeightStatement`, 5th conjunct). `1/100 + 1/999 ≤ 1/50`.
Inputs: `E2LacunaryWeightStatement` statement, `IsLacunaryData`. -/
theorem e2_plateau_error : E2LacunaryWeightStatement → E2PlateauErrorStatement := by
  exact ParabolicRectifiability.Examples.e2_plateau_error_proof

/-- **Cosine plateaus over one period.**
Route: `volume (S ∩ Ioo …) = ∫ indicator` over the interval; substitute `u = ω s`
(`intervalIntegral.integral_comp_mul_left`, factor `1/ω`); the indicator of `{1/2 ≤ cos u}` is
`2π`-periodic (`Real.cos_periodic`), so its integral over `(ωt - π, ωt + π)` equals that over
`(-π, π)` (`Function.Periodic.intervalIntegral_add_eq`,
), which is
`|[-π/3, π/3]| = 2π/3` (`Real.cos_le_cos_of_nonneg_of_le_pi`, `Real.cos_pi_div_three`). The second
set is the first shifted by `π` (`Real.cos_add_pi`). Inputs: mathlib only. -/
theorem e2_cosPlateau : E2CosPlateauStatement := by
  exact ParabolicRectifiability.Examples.e2_cosPlateau_proof

/-- **Plateaus survive measurable deletion.** Implication form over the plateau decomposition and the cosine plateaus.
Route: put `A = ε w_j ≥ 0`, `P± = {±cos(N_j s) ≥ 1/2} ∩ W_j(t)`. the cosine plateaus with `ω = N_j` gives
`|P±| ≥ |W|/3`; occupancy and `NullMeasurableSet E` give `|W \ E| ≤ |W|/12`
(`measure_sdiff_null'`/`measure_sdiff`), so `|E ∩ P±| ≥ |W|/4 = π/(2N_j)`. the plateau decomposition (`|s - t| < π/N_j`
on `W`) gives `f ≥ c_{j,t} + 12A/25` on `P+` and `f ≤ c_{j,t} - 12A/25` on `P-`. For
`c ≤ c_{j,t}` use `P+`, otherwise `P-`: `|f s - c|^q ≥ (12A/25)^q` there (`Real.rpow_le_rpow`),
then `lintegral_mono_set` and `setLIntegral_const`. Inputs: the plateau decomposition, the cosine plateaus statements. -/
theorem e2_plateau_lower :
    E2PlateauErrorStatement → E2CosPlateauStatement → E2PlateauLowerStatement := by
  exact ParabolicRectifiability.Examples.e2_plateau_lower_proof

/-- **Beta lower bound at the plateau radius.** Implication form over the ball pullback and the plateau lower bound.
Route: at `n = 1`, `k = 2` the horizontal family is empty (`HorizontalModel.isEmpty_of_not_available`),
so every mixed model is `Sum.inr L` with `L : VerticalModel 1 2` of spatial rank `0`; its distance
is `infEDist (point y s) L.toSet = ofReal ‖y - L.spatial.anchor‖`
(`VerticalModel.infEDist_eq_projection`, `VerticalModel.dist_projection_sq`
with direction `⊥`), i.e. `ofReal |f s - c|` for
`c = L.spatial.anchor 0`. the ball pullback at `r = r_j` (`r_j² = π/N_j`, `Real.sq_sqrt`) turns `fitPow` into
`∫⁻ s in E ∩ W_j(t), ofReal |f s - c| ^ q` (`ENNReal.ofReal_rpow_of_nonneg`); the plateau lower bound bounds it below
uniformly in `L` (`le_iInf`); multiply by `r_j^{-(2+q)} = (π/N_j)^{-1-q/2}` and simplify.
Inputs: the ball pullback, the plateau lower bound statements. -/
theorem e2_plateau_beta :
    E2BallPullbackStatement → E2PlateauLowerStatement → E2PlateauBetaStatement := by
  exact ParabolicRectifiability.Examples.e2_plateau_beta_proof

/-- **One logarithmic band.**
Route: for `ρ ≤ r ≤ 2ρ`, `fitPow μ q L z ρ ≤ fitPow μ q L z r` for every model
(`Metric.ball_subset_ball`, `lintegral_mono_set`), so the infimum is monotone; with
`r^{-(k+q)} ≥ (2ρ)^{-(k+q)}` this gives `B_q(z,r) ≥ 2^{-(k+q)} B_q(z,ρ)` on the band (both
`ofReal` radii positive). Then `setLIntegral_mono'`/`lintegral_mono` (no measurability of
`r ↦ B_q` is needed for the lower bound by a constant), `setLIntegral_const`, and the proved
`ParabolicRectifiability.scaleMeasure_Icc_two_mul : 0 < s → scaleMeasure (Icc s (2 * s)) =
ofReal (log 2)` (reused, not recomputed).
Inputs: defs `betaPow`, `fitPow`; `scaleMeasure_Icc_two_mul`. -/
theorem e2_betaPow_band : E2BandStatement := by
  exact ParabolicRectifiability.Examples.e2_betaPow_band_proof

/-- **Eventual occupancy at a density point.**
Route: `N_j ≥ 16^j` (fields `frequency_pos`, `frequency_growth`), so `π/N_j → 0+` and
`√(π/N_j) → 0`. `IsLebesgueDensityPoint E t` composed with `ρ_j = π/N_j`
(`tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`) makes
`|E ∩ [t-ρ_j, t+ρ_j]| / (2ρ_j)` eventually `> 11/12`; replace the closed by the open interval
(two null endpoints, `measure_union_le`); take `j₀` from `Filter.eventually_atTop` for both
conditions. Inputs: `IsLacunaryData`, def `IsLebesgueDensityPoint`. -/
theorem e2_lacunary_occupancy : E2OccupancyStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_occupancy_proof

/-- **Restriction-stable lower energy, first clause.** Implication form over the beta lower bound at the plateau radius, the logarithmic band bound, the occupancy statement, the frequency decay.
Route: `c q = log 2 · 2^{-(2+q)} · (1/2) π^{-q/2} (12/25)^q > 0`. Given `t`, `E`, `R`, take `j₀`
from the occupancy statement (independent of `q`). For `j ≥ j₀`, the bands `Icc r_j (2r_j)` lie in `Ioo 0 R` and are
pairwise disjoint (`r_{j+1} ≤ r_j/4` from the frequency decay times `√π`); `energyT … R ≥ Σ'_{j} ∫_{band_{j + j₀}}`
(index the bands directly by `j + j₀`; `lintegral_iUnion`, `lintegral_mono_set`); each band
integral is `≥ log 2 · 2^{-(2+q)} · B_q(F t, r_j)` (the logarithmic band bound) `≥ c q ε^q a_j^q` (the beta lower bound at the plateau radius with the
the occupancy statement). Inputs: the beta lower bound at the plateau radius, the logarithmic band bound, the occupancy statement, the frequency decay statements. -/
theorem e2_lacunary_lowerFirst :
    E2PlateauBetaStatement → E2BandStatement → E2OccupancyStatement →
      E2InvSqrtDecayStatement → E2LowerEnergyFirstStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_lowerFirst_proof

/-- **Interior points of `J` are density points.**
Route: for `0 < ρ < min (1+t) (1-t)`, `closedBall t ρ ⊆ [-1,1]`, so the ratio is
`volume (closedBall t ρ) / volume (closedBall t ρ) = 1` (`ENNReal.div_self`, positive and finite
by `Real.volume_closedBall`); `tendsto_const_nhds` with `Filter.Tendsto.congr'` on `𝓝[>] 0`. Inputs: def
`IsLebesgueDensityPoint`. -/
theorem e2_interior_densityPoint : E2InteriorDensityPointStatement := by
  exact ParabolicRectifiability.Examples.e2_interior_densityPoint_proof

/-! ## Small slopes -/

/-- **Little half-Hölder modulus.**
Implication form over the kernel bound, the kernel-sum bound, the frequency decay.
Route: `ε = 0` and `t = s` are trivial. Given `η`, choose `J₀` with `a_j ≤ δ` for `j ≥ J₀`
(`Metric.tendsto_atTop`), with **`δ = 3η/(32(ε+1))`** (the choice
`δ = 3η/(16(ε+1))` would give only `3εη/(2(ε+1))`, which exceeds `η` for `ε > 2`); split
`S(r) = Σ_{j<J₀} a_j K_j + Σ_{j≥J₀} a_j K_j`. Tail: `≤ δ Σ_j K_j ≤ (8/3)δ = η/(4(ε+1))` (the kernel-sum bound with
the frequency decay). Head: `≤ Σ_{j<J₀} r √N_j` (`K_j ≤ r/b_j`, `a_j ≤ 1`); choose `h` so that the head is
`≤ η/(4(ε+1))` for `r ≤ √h`. Apply the kernel bound with `r = √|t-s|`:
`|f t - f s| ≤ 2εr (η/(4(ε+1)) + η/(4(ε+1))) = (ε/(ε+1)) η r ≤ η √|t-s|`. No amplitude-smallness
hypothesis is used. Inputs: the kernel bound, the kernel-sum bound, the frequency decay statements. -/
theorem e2_lacunary_littleHolder :
    E2KernelBoundStatement → E2KernelSumStatement → E2InvSqrtDecayStatement →
      E2LittleHolderStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_littleHolder_proof

/-- **Snowflake extension to a full ordinary vertical graph.** Route: on `Time` (`dist = √|t-s|`), `g ∘ ofSnowflaking` is
`LipschitzOnWith ⟨η, _⟩` on `toSnowflaking '' A`; `LipschitzOnWith.extend_real`
(the McShane extension) gives `g̃ : Time → ℝ`,
`LipschitzWith ⟨η, _⟩`, equal to `g` there. The graph: direction `⊥` (`finrank_bot`, `0 + 2 = 2`),
offset `0`, function `zeroBaseLift (g̃ ∘ toSnowflaking)`, Lipschitz
constant `η` (`dist` in `⊥ᗮ` is `|g̃ τ - g̃ τ'|` by `PiLp.dist_single_same` and `Real.dist_eq`,
`EuclideanSpace.single` being `PiLp.single 2`; and `dist τ τ' ≤ dist p p'` on
`SubspaceSpace ⊥ = ⊥ × Time`, which carries the max product metric, by `Prod.dist_eq` and
`le_max_right`; `dist_snd_le` is for `WithLp` products only). Image:
`G.map (0, toSnow t) = point (single 0 (g t)) t`
for `t ∈ A`. Inputs: `zeroBaseLift`, `OrdinaryVerticalGraph`. -/
theorem e2_snowflake_extension : E2SnowflakeExtensionStatement := by
  exact ParabolicRectifiability.Examples.e2_snowflake_extension_proof

/-- **Small-slope covers of `F(J)`.** Implication form over the little half-Hölder modulus and the snowflake extension.
Route: given `η`, the little half-Hölder modulus gives `h`; take `m = ⌈2/h⌉₊ + 1` and `A_ℓ = J ∩ [-1 + 2ℓ/m, -1 + 2(ℓ+1)/m]`
(`ℓ : Fin m`), each of diameter `≤ 2/m ≤ h`; the snowflake extension with `g = f` on each `A_ℓ` gives `G ℓ`
(`choose`); every `t ∈ J` lies in `A_ℓ` for `ℓ = min (⌊(t+1)m/2⌋₊) (m-1)` (`Nat.floor_le`,
`Nat.lt_floor_add_one`). Inputs: the little half-Hölder modulus, the snowflake extension statements. -/
theorem e2_lacunary_smallSlope :
    E2LittleHolderStatement → E2SnowflakeExtensionStatement →
      LacunarySmallSlopeStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_smallSlope_proof

end ParabolicRectifiability.Examples
