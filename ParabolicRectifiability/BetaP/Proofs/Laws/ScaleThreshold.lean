import ParabolicRectifiability.BetaP.Proofs.Laws.Rescaling
import ParabolicRectifiability.Enhancements.Proofs.Scaling.RescaledCoreDecomposition

/-! # Rescaled source and both thresholds

`cscale_rescaledSource_betaP_threshold_proof` proves `rescaledSource_betaP_threshold`: the
thresholds `S_p^2 > M` and `T_p^2 > M` of a rescaled source pull back to the thresholds at
scale `2R` of the original source. It uses the rescaling law
`claws_rescaling_proof : BetaPowRescalingStatement` directly, at `a = 2`, so it takes no
hypothesis beyond those of `rescaledSource_betaP_threshold`.

`ν = rescaledSource μ k q R hR = R^{-k} S_# μ` is finite on compacts (instance) and inner
regular (`Measure.InnerRegular.map` for the homeomorphism `S`); for every set `A`,
`ν(A) = R^{-k} μ(S⁻¹' A)` (`sc2c_measure_rescaledSource_apply`, outer measure);
`S⁻¹' P(0,1) = P(q,R)` (`sc2c_preimage_similarity_unitBall`) and, by the Rescaling law,
`S⁻¹' {S_{p,ν}^2 > M} = {S_{p,μ}^{2R} > M}`, the same for `T_p`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.Enhancements.ScaledCoreTree

/-- **Thresholds of a rescaled source**: the statement `rescaledSource_betaP_threshold`; the
rescaling law enters as `claws_rescaling_proof`. -/
theorem cscale_rescaledSource_betaP_threshold_proof {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) (T : FamilyKind) (μ : Measure (Space n)) (hμ : IsFiniteMeasureOnCompacts μ)
    (hreg : μ.InnerRegular) (q : Space n) (R : ℝ) (hR : 0 < R) (p : ℝ) (hp : 0 < p) (M : ℝ) :
    IsFiniteMeasureOnCompacts (rescaledSource μ k q R hR) ∧
      (rescaledSource μ k q R hR).InnerRegular ∧
      (rescaledSource μ k q R hR) (Metric.ball (point 0 0) 1 ∩
          {z | ENNReal.ofReal M < energyS (rescaledSource μ k q R hR) k T p 2 z}) =
        (ENNReal.ofReal R)⁻¹ ^ k *
          μ (Metric.ball q R ∩ {z | ENNReal.ofReal M < energyS μ k T p (2 * R) z}) ∧
      (rescaledSource μ k q R hR) (Metric.ball (point 0 0) 1 ∩
          {z | ENNReal.ofReal M < energyT (rescaledSource μ k q R hR) k T p 2 z}) =
        (ENNReal.ofReal R)⁻¹ ^ k *
          μ (Metric.ball q R ∩ {z | ENNReal.ofReal M < energyT μ k T p (2 * R) z}) := by
  have hlaw : ∀ w : Space n,
      energyS (rescaledSource μ k q R hR) k T p 2 (similarity q R hR w) =
          energyS μ k T p (2 * R) w ∧
        energyT (rescaledSource μ k q R hR) k T p 2 (similarity q R hR w) =
          energyT μ k T p (2 * R) w :=
    fun w => (claws_rescaling_proof n hn k hk hkn T μ p hp q R hR w).2 2 two_pos
  have hS : similarity q R hR ⁻¹'
      {z | ENNReal.ofReal M < energyS (rescaledSource μ k q R hR) k T p 2 z} =
        {z | ENNReal.ofReal M < energyS μ k T p (2 * R) z} := by
    ext w
    simp only [mem_preimage, mem_ofPred_eq]
    rw [(hlaw w).1]
  have hT : similarity q R hR ⁻¹'
      {z | ENNReal.ofReal M < energyT (rescaledSource μ k q R hR) k T p 2 z} =
        {z | ENNReal.ofReal M < energyT μ k T p (2 * R) z} := by
    ext w
    simp only [mem_preimage, mem_ofPred_eq]
    rw [(hlaw w).2]
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · have : (μ.map (similarity q R hR)).InnerRegular :=
      Measure.InnerRegular.map (similarity q R hR)
    unfold rescaledSource
    infer_instance
  · rw [sc2c_measure_rescaledSource_apply, preimage_inter, sc2c_preimage_similarity_unitBall, hS]
  · rw [sc2c_measure_rescaledSource_apply, preimage_inter, sc2c_preimage_similarity_unitBall, hT]

end ParabolicRectifiability.BetaP
