import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Lemmas
import ParabolicRectifiability.Foundations.Statements.HighPassBracket

/-! # The exponent witness below `p = 2`: assembly

`e2_exponent_witness_below_of` proves `ExponentWitnessBelowStatement` from the intermediate
results on the amplitudes, the half-Hölder modulus, the periodic half derivative, its BMO bound
and the representation identity. The lacunary estimates (`LacunaryLowerEnergyStatement`, the
kernel bounds, `LacunaryConvergenceStatement`) and the bracket integrability
`HalfTimeBracketIntegrableStatement` remain explicit hypotheses. The constant is `C = 16`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The exponent witness below `p = 2`, assuming the lacunary lower energy bound, the kernel
estimates, the convergence of the lacunary series and the bracket integrability of
half-time test kernels. -/
theorem e2_exponent_witness_below_of (hLE : LacunaryLowerEnergyStatement)
    (hKB : E2KernelBoundStatement) (hKS : E2KernelSumStatement) (hID : E2InvSqrtDecayStatement)
    (hConv : LacunaryConvergenceStatement) (hBI : HalfTimeBracketIntegrableStatement) :
    ExponentWitnessBelowStatement := by
  have hPL : E2PeriodicLocalStatement := e2_periodic_local
  refine ⟨16, by norm_num, fun c₀ hc₀ ε N hε hε' hD => ?_⟩
  have hsq : Summable (fun j => exponentAmplitude c₀ j ^ 2) :=
    e2_exponentAmplitude_sq_summable c₀
  obtain ⟨h, hP⟩ := e2_periodic_halfDerivative ε (exponentAmplitude c₀) N hD hsq
  have hmod := e2_sup_modulus hKB hKS hID ε (exponentAmplitude c₀) N hε.le hD
  obtain ⟨L, hL, hLle⟩ := e2_zeroBase_lipschitz (lacunaryFunction ε (exponentAmplitude c₀) N)
    (16 * ε * ⨆ j, exponentAmplitude c₀ j) hmod
  obtain ⟨B, hB, hBle⟩ := e2_zeroBase_bmo h
    (16 * ε * Real.sqrt (∑' j, exponentAmplitude c₀ j ^ 2))
    (e2_below_intervalBMO e2_lowFrequency_oscillation
      (e2_highFrequency_limit (e2_highFrequency_L2 e2_cosProduct_mean) hPL) hPL
      ε (exponentAmplitude c₀) N hε hD hsq h hP)
  have hRep : RepresentsGeneralHalfTimeDerivative zeroDirection
      (zeroBaseLift (lacunaryFunction ε (exponentAmplitude c₀) N)) (zeroBaseLift h) :=
    e2_zeroBase_representation (lacunaryFunction ε (exponentAmplitude c₀) N) h
      (e2_zeroDim_representation hBI (lacunaryFunction ε (exponentAmplitude c₀) N) h
        (16 * ε * ⨆ j, exponentAmplitude c₀ j) hmod (hPL ε (exponentAmplitude c₀) N h hP).1
        (e2_series_pairing hConv e2_cosine_kernelPairing hPL ε (exponentAmplitude c₀) N hε hε'
          hD h hP))
  refine ⟨hsq, e2_exponentAmplitude_not_summable c₀ hc₀,
    ⟨h, L, B, hL, hB, hRep, hLle, hBle, hP.2.1, hP.2.2⟩,
    ⟨zeroBaseLift h, L, B, hL, hB, hRep, ?_⟩,
    fun p hp hp2 R hR t ht => e2_below_divergence hLE ε (exponentAmplitude c₀) N hε hε' hD p hp
      (e2_exponentAmplitude_not_summable c₀ hc₀ p hp hp2) R hR t ht⟩
  rw [mul_add]
  exact add_le_add hLle hBle

end ParabolicRectifiability.Examples
