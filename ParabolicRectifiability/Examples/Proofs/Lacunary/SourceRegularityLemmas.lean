import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyStatements
import ParabolicRectifiability.Examples.Proofs.Lacunary.Support
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.QuarterBall
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.QuarterLower
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.QuarterPositive
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.Restriction
import ParabolicRectifiability.Examples.Proofs.Lacunary.Graphs.SourceRegularity

/-! # Lacunary graph: intermediate results on sources, restriction, ball and energy

Implication-form intermediate results used by `e2_lacunarySource_finite_innerRegular_ac`,
`e2_exists_restriction_carried_by_graph`, `e2_lacunaryGraphMap_mem_ball_of_quarter` and
`e2_lintegral_energyT_quarter_pos`. Each theorem is obtained from the corresponding `…_proof`
theorem. The hypotheses are the lacunary estimates `E2HausdorffExactStatement`,
`E2PlateauBetaStatement`, `E2BandStatement`, the isometry `LacunaryIsometryStatement` and the
weight estimate `E2LacunaryWeightStatement`; after the hypotheses each type is the type of the
corresponding target statement.

Two auxiliary facts are shared (see `e2_isometry_time_of_dist` and `e2_lacunarySource_univ`).
Continuity of `F` is
`(e2_isometry_time_of_dist (hiso ε a N hε hε' hd)).continuous.comp
Metric.Snowflaking.continuous_toSnowflaking : Continuous F`
(used for the source regularity, the carried restriction and the positive energy). The
source-mass identity `ν_E(X) = |E|` is `e2_lacunarySource_univ` and is used only for the carried
restriction; source regularity does not need it (finiteness comes from instances).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-! ## Regularity of the sources -/

/-- **Restricted sources are finite, inner regular and `≪ H_P²`.**
Implication form over the exact Hausdorff identity and the isometry.
Proof: `F` is continuous (support adapter `e2_isometry_time_of_dist` composed with
`Metric.Snowflaking.continuous_toSnowflaking`), hence measurable. Finite, with no source-mass
identity: `volume.restrict E` is finite since `|E| ≤ |J| = 2 < ∞` (`isFiniteMeasure_restrict`,
`measure_mono`, `Real.volume_Icc`), and a pushforward of a finite measure is finite
(`Measure.isFiniteMeasure_map`). Inner regular:
`Space 1` is proper, hence σ-compact and metrizable, so the mathlib
instance for σ-finite measures applies
(`inferInstance` after `haveI : IsFiniteMeasure _`). Absolute continuity: for `H_P²(A) = 0` take a
measurable null hull `A' ⊇ A` (`exists_measurable_superset_of_null`), put
`E' = E ∩ F⁻¹(A')`; `F(E') ⊆ A'` so the exact Hausdorff identity gives `|E'| = H_P²(F(E')) = 0`,
and `ν_E(A) ≤ ν_E(A') = |F⁻¹(A') ∩ E| = 0` (`Measure.map_apply`, `Measure.restrict_apply`). -/
theorem e2_lacunarySource_finite_ac :
    E2HausdorffExactStatement → LacunaryIsometryStatement →
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ lacunaryInterval →
      IsFiniteMeasure (lacunarySource ε a N E) ∧ (lacunarySource ε a N E).InnerRegular ∧
        lacunarySource ε a N E ≪ hausdorffP 1 2 := by
  exact ParabolicRectifiability.Examples.e2_lacunarySource_finite_ac_proof

/-! ## Restriction carried by a regular graph -/

/-- **The restriction carried by a regular graph.** Implication form over the isometry.
Proof: `E = E₀ ∩ F⁻¹(G.image)`. The image is Borel by
`Foundations.fgenv_vertical_image_measurableSet_proof`, and `F` is measurable (continuous by the support adapter
`e2_isometry_time_of_dist` and `Metric.Snowflaking.continuous_toSnowflaking`), so the preimage is
measurable and `E` is null-measurable. `ν_E univ = |E| = |E₀ ∩ F⁻¹ G|` by the source-mass
identity `e2_lacunarySource_univ`, and
`ν_{E₀}(G) = |F⁻¹ G ∩ E₀|` (`Measure.map_apply`, `Measure.restrict_apply`); further
`ν_E(Gᶜ) = |F⁻¹(Gᶜ) ∩ E₀ ∩ F⁻¹ G| = 0` (`Measure.map_apply`, `Measure.restrict_apply`,
`Set.inter_comm`). -/
theorem e2_restriction_carried :
    LacunaryIsometryStatement →
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ E₀ : Set ℝ, NullMeasurableSet E₀ volume → E₀ ⊆ lacunaryInterval →
    ∀ (η : ℝ) (G : GeneralRegularVerticalGraph 1 2 η),
      ∃ E : Set ℝ, NullMeasurableSet E volume ∧ E ⊆ E₀ ∧
        lacunarySource ε a N E univ = lacunarySource ε a N E₀ G.image ∧
        lacunarySource ε a N E (G.image)ᶜ = 0 := by
  exact ParabolicRectifiability.Examples.e2_restriction_carried_proof

/-! ## The quarter graph lies in the unit ball -/

/-- **The quarter graph lies in `P(0,1)`.** Implication form over the weight estimate
`E2LacunaryWeightStatement`.
Proof: `|f t| ≤ ε Σ' w_j` (`norm_tsum_le_tsum_norm`, `|cos| ≤ 1`, summability from the weight
estimate) and `Σ' w_j = w_0 + Σ' w_{1+i} ≤ w_0 (1 + 1/999)` (`Summable.tsum_eq_zero_add`, the
tail bound of the weight estimate at `j = 0`);
`w_0 = a_0/√N_0 ≤ 1` (`a_0 ≤ 1`, `N_0 ≥ 1`); so `|f t| ≤ (3/16)(1000/999) < 1`. Time part:
`√|t| ≤ √(1/4) = 1/2 < 1`. Conclude with `dist_point` and `PiLp.norm_single`
(`EuclideanSpace.single` is `PiLp.single 2`), `Real.norm_eq_abs`. -/
theorem e2_quarter_mem_ball :
    E2LacunaryWeightStatement →
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ t ∈ Icc (-1 / 4 : ℝ) (1 / 4), lacunaryGraphMap ε a N t ∈ Metric.ball (point 0 0) 1 := by
  exact ParabolicRectifiability.Examples.e2_quarter_mem_ball_proof

/-! ## Positive integrated energy -/

/-- **Uniform energy lower bound on `F([-1/8,1/8])`.**
Implication form over the plateau beta bound `E2PlateauBetaStatement` and the one-band estimate
`E2BandStatement`.
Proof: fix `j` with `N_j > 8π` (`N_j ≥ 16^j`: `j = 2` suffices). For `t ∈ [-1/8,1/8]`,
`W_j(t) ⊆ [-1/4,1/4]` (`π/N_j < 1/8`), so `|Q ∩ W_j(t)| = |W_j(t)| ≥ (11/12)|W_j(t)|`
(`Set.inter_eq_right`); the plateau bound gives
`B_p(F t, r_j) ≥ β₀ := (1/2) π^{-p/2} (12/25)^p ε^p a_j^p > 0`;
`2 r_j < 2` puts `Icc r_j (2r_j) ⊆ Ioo 0 2`, so `energyT … p 2 ≥ ∫_{band} ≥ log 2 · 2^{-(2+p)} β₀`
(the one-band estimate, `lintegral_mono_set`). Take `b` that product (positive real). -/
theorem e2_quarter_energyLower :
    E2PlateauBetaStatement → E2BandStatement → E2QuarterEnergyLowerStatement := by
  exact ParabolicRectifiability.Examples.e2_quarter_energyLower_proof

/-- **Positive integrated energy.** Implication form over the uniform lower bound
`E2QuarterEnergyLowerStatement` and the isometry.
Proof: `K = F([-1/8,1/8])` is compact (`isCompact_Icc.image`, `F` continuous by
`e2_isometry_time_of_dist` and `Metric.Snowflaking.continuous_toSnowflaking`), hence measurable;
the uniform lower bound gives
`ofReal b · 1_K ≤ T²_{p,ν}` pointwise (`Set.indicator_le`), so
`∫⁻ T dν ≥ ofReal b · ν(K)` (`lintegral_mono`, `lintegral_indicator_const`; no measurability of
the energy is needed). `ν(K) = |Q ∩ F⁻¹(K)| ≥ |[-1/8,1/8]| = 1/4 > 0` (`Measure.map_apply`,
`Measure.restrict_apply`, `measure_mono`). -/
theorem e2_quarter_energyPos :
    E2QuarterEnergyLowerStatement → LacunaryIsometryStatement →
    ∀ p : ℝ, 0 < p → ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 →
    IsLacunaryData a N →
      0 < ∫⁻ z, energyT (lacunarySource ε a N (Icc (-1 / 4) (1 / 4))) 2 .mixed p 2 z
        ∂(lacunarySource ε a N (Icc (-1 / 4) (1 / 4))) := by
  exact ParabolicRectifiability.Examples.e2_quarter_energyPos_proof

end ParabolicRectifiability.Examples
