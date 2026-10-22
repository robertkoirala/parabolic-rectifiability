import ParabolicRectifiability.Foundations.Statements.Measurability
import ParabolicRectifiability.Analysis.TraceExtension.TracePieces.Normalize

/-! # Proof of the dilation law of the square energy

`SquareEnergyRescalingStatement`. The beta identity `betaSq_rescaledSource`, valid for every
family, turns the integrand into `betaSq μ k T w (R * r)` at `w = (similarity q R hR).symm z`
for `r ∈ Ioo 0 A`; the change of scale `t = R r` for `dr/r`
(`setLIntegral_Ioo_scaleMeasure_comp_const_mul`) turns the integral over `Ioo 0 A` into the one over
`Ioo 0 (R * A)`. The dimension and `k` guards are not used.
-/

namespace ParabolicRectifiability.Foundations

open MeasureTheory Set

theorem squareEnergy_rescaledSource_eq_proof : SquareEnergyRescalingStatement := by
  intro n _ k _ _ T μ q R hR A _ z
  unfold squareEnergy
  have hRA : R * A / R = A := mul_div_cancel_left₀ A hR.ne'
  have h1 : ∫⁻ r in Ioo 0 A, betaSq (rescaledSource μ k q R hR) k T z r ∂scaleMeasure =
      ∫⁻ r in Ioo 0 A, betaSq μ k T ((similarity q R hR).symm z) (R * r) ∂scaleMeasure := by
    refine setLIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    have h := betaSq_rescaledSource μ k T q R hR ((similarity q R hR).symm z) hr.1
    rwa [Homeomorph.apply_symm_apply] at h
  rw [h1]
  have h2 := setLIntegral_Ioo_scaleMeasure_comp_const_mul hR
    (fun t => betaSq μ k T ((similarity q R hR).symm z) t) (R * A)
  rw [hRA] at h2
  exact h2

end ParabolicRectifiability.Foundations
