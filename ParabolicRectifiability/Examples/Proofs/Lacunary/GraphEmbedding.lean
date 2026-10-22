import ParabolicRectifiability.Examples.Proofs.Lacunary.GraphEmbeddingStatements

/-! # The lacunary graph map is a measurable embedding

Proof of `E2LacunaryGraphEmbeddingStatement`: `Measurable.tsum` gives measurability of the
series; the graph map is `measurable_point` of a measurable pair; the left inverse is
`measurable_time`; the range is `{z | F z.2.val = z}`. -/

open MeasureTheory

namespace ParabolicRectifiability.Examples

theorem e2_lacunaryGraphMap_measurableEmbedding_proof : E2LacunaryGraphEmbeddingStatement := by
  intro ε a N
  have hf : Measurable (lacunaryFunction ε a N) := by
    unfold lacunaryFunction
    refine measurable_const.mul (Measurable.tsum fun j => ?_)
    exact measurable_const.mul (Real.measurable_cos.comp (measurable_const.mul measurable_id))
  have hF : Measurable (lacunaryGraphMap ε a N) := by
    unfold lacunaryGraphMap
    have hc : Continuous fun x : ℝ => (EuclideanSpace.single (0 : Fin 1) x : Spatial 1) := by
      exact (EuclideanSpace.equiv (Fin 1) ℝ).symm.continuous.comp
          (continuous_pi fun i => continuous_id.congr (by intro x; fin_cases i; simp))
    have hs : Measurable fun t : ℝ => (EuclideanSpace.single (0 : Fin 1)
        (lacunaryFunction ε a N t) : Spatial 1) := hc.measurable.comp hf
    exact measurable_point.comp (hs.prodMk measurable_id)
  have hinv : Function.LeftInverse (fun z : Space 1 => z.2.val) (lacunaryGraphMap ε a N) :=
    fun t => rfl
  have hrange : Set.range (lacunaryGraphMap ε a N) =
      {z : Space 1 | lacunaryGraphMap ε a N (z.2.val) = z} := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      simp only [Set.mem_ofPred_eq, hinv t]
    · intro h
      exact ⟨z.2.val, h⟩
  refine MeasurableEmbedding.of_measurable_inverse hF ?_ measurable_time hinv
  rw [hrange]
  exact measurableSet_eq_fun (hF.comp measurable_time) measurable_id

end ParabolicRectifiability.Examples
