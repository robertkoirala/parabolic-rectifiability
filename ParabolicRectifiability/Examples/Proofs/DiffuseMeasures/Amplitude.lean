import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTestStatements
import ParabolicRectifiability.Measure.BetaLaws
import ParabolicRectifiability.Geometry.AdmissibleModels

/-! # Quadratic energy of the scaled diffuse measures

There are `C, κ > 0` with `S²_{μ_c} ≤ C c` everywhere and `∫_{P(0,1)} S²_{μ_c} dμ_c = κ c²`
for every `c > 0`, where `μ_c = c ω` (`e2_diffuse_amplitude_proof`). Take `C = A`, `κ = E_0.toReal`; the square energy of `c ω` is `c` times that of `ω`
(`squareEnergy_smul`), and the outer integral against `c ω` adds a second factor `c`. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

theorem e2_diffuse_amplitude_proof : E2DiffuseAmplitudeStatement := by
  intro n k hn hk hkn hbase
  obtain ⟨A, hA, hbd, hpos, hfin⟩ := hbase
  have : Nonempty (Models n k .mixed) :=
    AdmissibleModel.nonempty_of_range hn hk (by omega)
  set E0 : ℝ≥0∞ := ∫⁻ z in Metric.ball (point 0 0) 1,
    squareEnergy (e2_diffuseBase n) k .mixed 2 z ∂(e2_diffuseBase n) with hE0
  have hE0ne : E0 ≠ ⊤ := hfin.ne
  have hκ : 0 < E0.toReal := ENNReal.toReal_pos hpos.ne' hE0ne
  refine ⟨A, E0.toReal, hA, hκ, fun c hc => ?_⟩
  have hcne : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsm : ∀ z, squareEnergy (ENNReal.ofReal c • e2_diffuseBase n) k .mixed 2 z =
      ENNReal.ofReal c * squareEnergy (e2_diffuseBase n) k .mixed 2 z :=
    fun z => squareEnergy_smul _ _ hcne k .mixed 2 z
  refine ⟨fun z => ?_, ?_⟩
  · rw [hsm z, mul_comm A c, ENNReal.ofReal_mul hc.le]
    gcongr
    exact hbd z
  · simp_rw [hsm]
    rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
      lintegral_const_mul' _ _ hcne, ← hE0, ENNReal.ofReal_mul hκ.le,
      ENNReal.ofReal_pow hc.le, ENNReal.ofReal_toReal hE0ne]
    ring

end ParabolicRectifiability.Examples
