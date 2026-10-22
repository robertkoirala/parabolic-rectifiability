import ParabolicRectifiability.Examples.Proofs.Lacunary.Estimates
import ParabolicRectifiability.Examples.Proofs.Lacunary.SourceRegularityLemmas

/-! # Lacunary graph: source regularity, restriction, ball containment and positive energy

Four properties of the lacunary graph `F = lacunaryGraphMap ε a N` and of the sources
`ν_E = lacunarySource ε a N E`, each with a type identical to the corresponding statement:
* `e2_lacunarySource_finite_innerRegular_ac` (`lacunarySource_finite_innerRegular_ac`): `ν_E` is
  finite, inner regular and absolutely continuous with respect to `H_P²`;
* `e2_exists_restriction_carried_by_graph` (`exists_restriction_carried_by_graph`): the part of
  `ν_{E₀}` on a regular vertical graph is the source of a subset `E ⊆ E₀`;
* `e2_lacunaryGraphMap_mem_ball_of_quarter` (`lacunaryGraphMap_mem_ball_of_quarter`): `F` maps
  `[-1/4, 1/4]` into the unit ball `P(0, 1)`;
* `e2_lintegral_energyT_quarter_pos` (`lintegral_energyT_quarter_pos`): the integrated energy of
  `ν_{[-1/4,1/4]}` is positive.
The `…_of` forms take the weight estimate `E2LacunaryWeightStatement` as a hypothesis.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-! ## Regularity of the sources -/

/-- Regularity of the sources, assuming the weight estimate: follows from the exact Hausdorff
identity and the isometry property of `F`. -/
theorem e2_lacunarySource_finite_innerRegular_ac_of (hW : E2LacunaryWeightStatement) :
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ lacunaryInterval →
      IsFiniteMeasure (lacunarySource ε a N E) ∧ (lacunarySource ε a N E).InnerRegular ∧
        lacunarySource ε a N E ≪ hausdorffP 1 2 :=
  e2_lacunarySource_finite_ac (e2_hausdorffExact_of hW) (e2_isometry_of hW)

/-- The restricted sources `ν_E` are finite, inner regular and `≪ H_P²`; the type is that of
`lacunarySource_finite_innerRegular_ac`. -/
theorem e2_lacunarySource_finite_innerRegular_ac :
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ lacunaryInterval →
      IsFiniteMeasure (lacunarySource ε a N E) ∧ (lacunarySource ε a N E).InnerRegular ∧
        lacunarySource ε a N E ≪ hausdorffP 1 2 :=
  e2_lacunarySource_finite_innerRegular_ac_of e2_lacunaryWeight

/-! ## Restriction carried by a regular graph -/

/-- The restriction carried by a regular graph, assuming the weight estimate (through the
isometry property of `F`). -/
theorem e2_exists_restriction_carried_by_graph_of (hW : E2LacunaryWeightStatement) :
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ E₀ : Set ℝ, NullMeasurableSet E₀ volume → E₀ ⊆ lacunaryInterval →
    ∀ (η : ℝ) (G : GeneralRegularVerticalGraph 1 2 η),
      ∃ E : Set ℝ, NullMeasurableSet E volume ∧ E ⊆ E₀ ∧
        lacunarySource ε a N E univ = lacunarySource ε a N E₀ G.image ∧
        lacunarySource ε a N E (G.image)ᶜ = 0 :=
  e2_restriction_carried (e2_isometry_of hW)

/-- For a regular vertical graph `G` there is `E ⊆ E₀` with `ν_E(X) = ν_{E₀}(G)` and
`ν_E(Gᶜ) = 0`; the type is that of `exists_restriction_carried_by_graph`. -/
theorem e2_exists_restriction_carried_by_graph :
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ E₀ : Set ℝ, NullMeasurableSet E₀ volume → E₀ ⊆ lacunaryInterval →
    ∀ (η : ℝ) (G : GeneralRegularVerticalGraph 1 2 η),
      ∃ E : Set ℝ, NullMeasurableSet E volume ∧ E ⊆ E₀ ∧
        lacunarySource ε a N E univ = lacunarySource ε a N E₀ G.image ∧
        lacunarySource ε a N E (G.image)ᶜ = 0 :=
  e2_exists_restriction_carried_by_graph_of e2_lacunaryWeight

/-! ## The quarter graph lies in the unit ball -/

/-- `F(t) ∈ P(0, 1)` for `t ∈ [-1/4, 1/4]`; the type is that of
`lacunaryGraphMap_mem_ball_of_quarter`. Obtained from `e2_quarter_mem_ball` and the weight
estimate `e2_lacunaryWeight`. -/
theorem e2_lacunaryGraphMap_mem_ball_of_quarter :
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ t ∈ Icc (-1 / 4 : ℝ) (1 / 4), lacunaryGraphMap ε a N t ∈ Metric.ball (point 0 0) 1 :=
  e2_quarter_mem_ball e2_lacunaryWeight

/-! ## Positive integrated energy -/

/-- Positive integrated energy, assuming the weight estimate: the uniform lower bound
`e2_quarter_energyLower` (from the plateau beta bound and the one-band estimate) together with the
isometry property of `F`. -/
theorem e2_lintegral_energyT_quarter_pos_of (hW : E2LacunaryWeightStatement) :
    ∀ p : ℝ, 0 < p → ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 →
    IsLacunaryData a N →
      0 < ∫⁻ z, energyT (lacunarySource ε a N (Icc (-1 / 4) (1 / 4))) 2 .mixed p 2 z
        ∂(lacunarySource ε a N (Icc (-1 / 4) (1 / 4))) :=
  e2_quarter_energyPos (e2_quarter_energyLower (e2_plateauBeta_of hW) e2_betaPow_band)
    (e2_isometry_of hW)

/-- `0 < ∫ T²_{p,ν}(z) dν(z)` for `ν = ν_{[-1/4,1/4]}` and every `p > 0`; the type is that of
`lintegral_energyT_quarter_pos`. -/
theorem e2_lintegral_energyT_quarter_pos :
    ∀ p : ℝ, 0 < p → ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 →
    IsLacunaryData a N →
      0 < ∫⁻ z, energyT (lacunarySource ε a N (Icc (-1 / 4) (1 / 4))) 2 .mixed p 2 z
        ∂(lacunarySource ε a N (Icc (-1 / 4) (1 / 4))) :=
  e2_lintegral_energyT_quarter_pos_of e2_lacunaryWeight

end ParabolicRectifiability.Examples
