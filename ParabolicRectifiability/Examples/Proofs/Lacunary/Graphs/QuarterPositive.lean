import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import ParabolicRectifiability.Examples.Proofs.Lacunary.Support

/-! Positive integrated quarter energy from a uniform lower bound on a compact graph image. -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The inner quarter has positive source mass, and its compact image carries a constant
positive lower bound. The lower Lebesgue integral comparison needs no energy measurability. -/
theorem e2_quarter_energyPos_proof :
    E2QuarterEnergyLowerStatement → LacunaryIsometryStatement →
    ∀ p : ℝ, 0 < p → ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 →
    IsLacunaryData a N →
      0 < ∫⁻ z, energyT (lacunarySource ε a N (Icc (-1 / 4) (1 / 4))) 2 .mixed p 2 z
        ∂(lacunarySource ε a N (Icc (-1 / 4) (1 / 4))) := by
  intro hlower hiso p hp ε a N hε hε' hd
  obtain ⟨b, hb, hlower⟩ := hlower p hp ε a N hε hε' hd
  let F := lacunaryGraphMap ε a N
  let ν := lacunarySource ε a N (Icc (-1 / 4) (1 / 4))
  let K := F '' Icc (-1 / 8 : ℝ) (1 / 8)
  have hF : Continuous F :=
    (e2_isometry_time_of_dist (hiso ε a N hε hε' hd)).continuous.comp
      Metric.Snowflaking.continuous_toSnowflaking
  have hK : MeasurableSet K := (isCompact_Icc.image hF).measurableSet
  have hmass : ENNReal.ofReal (1 / 4 : ℝ) ≤ ν K := by
    change ENNReal.ofReal (1 / 4 : ℝ) ≤
      Measure.map F (volume.restrict (Icc (-1 / 4) (1 / 4))) K
    rw [Measure.map_apply hF.measurable hK,
      Measure.restrict_apply (hF.measurable hK)]
    calc
      ENNReal.ofReal (1 / 4 : ℝ) = volume (Icc (-1 / 8 : ℝ) (1 / 8)) := by
        rw [Real.volume_Icc]
        norm_num
      _ ≤ volume (F ⁻¹' K ∩ Icc (-1 / 4) (1 / 4)) := by
        apply measure_mono
        intro t ht
        exact ⟨mem_image_of_mem F ht, by constructor <;> linarith [ht.1, ht.2]⟩
  have hbound : K.indicator (fun _ : Space 1 => ENNReal.ofReal b) ≤
      fun z => energyT ν 2 .mixed p 2 z := by
    intro z
    by_cases hz : z ∈ K
    · obtain ⟨t, ht, rfl⟩ := hz
      have htK : F t ∈ K := mem_image_of_mem F ht
      rw [Set.indicator_of_mem htK]
      exact hlower t ht
    · simp only [Set.indicator_of_notMem hz]
      exact zero_le
  have hpos : 0 < ENNReal.ofReal b * ν K := by
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hb).ne'
      (lt_of_lt_of_le (by norm_num) hmass).ne'
  apply lt_of_lt_of_le hpos
  calc
    ENNReal.ofReal b * ν K = ∫⁻ z, K.indicator (fun _ => ENNReal.ofReal b) z ∂ν :=
      (lintegral_indicator_const hK _).symm
    _ ≤ ∫⁻ z, energyT ν 2 .mixed p 2 z ∂ν := lintegral_mono hbound

end ParabolicRectifiability.Examples
