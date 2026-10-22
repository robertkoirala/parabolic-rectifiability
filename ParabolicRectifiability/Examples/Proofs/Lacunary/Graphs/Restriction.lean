import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import ParabolicRectifiability.Examples.Proofs.Lacunary.Support
import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.GraphImageBorel

/-! # Restricting a lacunary source to a regular graph

Pull the Borel graph image back along the continuous lacunary map, and intersect
with the original null-measurable source set. The pushforward mass is exactly
the old mass on the graph, and the complementary preimage misses the new set.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The source restricted to the preimage of a regular graph carries precisely
its original mass on that graph. The source set need only be null-measurable. -/
theorem e2_restriction_carried_proof :
    LacunaryIsometryStatement →
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ E₀ : Set ℝ, NullMeasurableSet E₀ volume → E₀ ⊆ lacunaryInterval →
    ∀ (η : ℝ) (G : GeneralRegularVerticalGraph 1 2 η),
      ∃ E : Set ℝ, NullMeasurableSet E volume ∧ E ⊆ E₀ ∧
        lacunarySource ε a N E univ = lacunarySource ε a N E₀ G.image ∧
        lacunarySource ε a N E (G.image)ᶜ = 0 := by
  intro hiso ε a N hε hε' hd E₀ hE₀ _hE₀J η G
  have hF : Measurable (lacunaryGraphMap ε a N) :=
    ((e2_isometry_time_of_dist (hiso ε a N hε hε' hd)).continuous.comp
      Metric.Snowflaking.continuous_toSnowflaking).measurable
  have hG : MeasurableSet G.image :=
    fgenv_vertical_image_measurableSet_proof 1 2 η G
  have hpre : MeasurableSet (lacunaryGraphMap ε a N ⁻¹' G.image) := hG.preimage hF
  refine ⟨E₀ ∩ lacunaryGraphMap ε a N ⁻¹' G.image,
    hE₀.inter hpre.nullMeasurableSet, inter_subset_left, ?_, ?_⟩
  · rw [e2_lacunarySource_univ hF, lacunarySource, Measure.map_apply hF hG,
      Measure.restrict_apply hpre, inter_comm]
  · rw [lacunarySource, Measure.map_apply hF hG.compl,
      Measure.restrict_apply (hG.compl.preimage hF)]
    have hempty : (lacunaryGraphMap ε a N ⁻¹' G.imageᶜ) ∩
        (E₀ ∩ lacunaryGraphMap ε a N ⁻¹' G.image) = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false]
      exact fun h => h.1 h.2.2
    rw [hempty, measure_empty]

end ParabolicRectifiability.Examples
