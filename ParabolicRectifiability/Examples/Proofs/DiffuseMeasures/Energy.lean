import ParabolicRectifiability.Examples.Proofs.DensityTests.DiffuseEstimateStatements

/-! # Pointwise and integrated energy bounds for the diffuse measures (`e2_diffuse_energy_proof`)

Proof of `E2DiffuseEnergyStatement`. The source-ball bound, the scale integral, the pointwise
upper estimates and the lower estimates enter only as hypotheses of the statement.

Route. A generic assembly `e2d7_assemble` takes an integrand
`f z r` with a majorant `C r^γ` on `(0,2)` and a minorant `m` on `D × I`, and an exact value
`K` of `∫_{(0,2)} r^γ dr/r`. It produces `A > 0` with `∫_{(0,2)} f z ≤ A` at every point,
finite outer integral over `P(0,1)`, and positivity through `I ⊆ (0,2)` and `D ⊆ P(0,1)`
using monotonicity of lower integrals only (no measurability of the integrand). It is applied
to `f = B_p` (`C = 2ω_n`, `γ = α`) and to `f = B_p^{2/p}` (`C = (2ω_n)^{2/p}`, `γ = α·2/p`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- Generic assembly: majorant `C r^γ` on `(0,2)` and minorant `m` on `D × I` give a real
pointwise bound, a finite outer integral, and a positive outer integral. -/
theorem e2d7_assemble {n : ℕ} (ω : Measure (Space n)) [IsFiniteMeasure ω]
    (D : Set (Space n)) (hDm : MeasurableSet D) (hDω : 0 < ω D)
    (hDsub : D ⊆ Metric.ball (point 0 0) 1)
    (I : Set ℝ) (hIm : MeasurableSet I) (hIsub : I ⊆ Ioo (0 : ℝ) 2) (hI0 : 0 < scaleMeasure I)
    (f : Space n → ℝ → ℝ≥0∞) (C m K : ℝ≥0∞) (γ : ℝ)
    (hC : C ≠ ⊤) (hC0 : C ≠ 0) (hK : ∫⁻ r in Ioo (0 : ℝ) 2, ENNReal.ofReal r ^ γ ∂scaleMeasure = K)
    (hK0 : K ≠ 0) (hKt : K ≠ ⊤) (hm : m ≠ 0)
    (hup : ∀ z, ∀ r ∈ Ioo (0 : ℝ) 2, f z r ≤ C * ENNReal.ofReal r ^ γ)
    (hlow : ∀ z ∈ D, ∀ r ∈ I, m ≤ f z r) :
    ∃ A : ℝ, 0 < A ∧ (∀ z, ∫⁻ r in Ioo (0 : ℝ) 2, f z r ∂scaleMeasure ≤ ENNReal.ofReal A) ∧
      (0 < ∫⁻ z in Metric.ball (point 0 0) 1, (∫⁻ r in Ioo (0 : ℝ) 2, f z r ∂scaleMeasure) ∂ω ∧
        ∫⁻ z in Metric.ball (point 0 0) 1, (∫⁻ r in Ioo (0 : ℝ) 2, f z r ∂scaleMeasure) ∂ω
          < ⊤) := by
  have hU : C * K ≠ ⊤ := ENNReal.mul_ne_top hC hKt
  have hU0 : C * K ≠ 0 := mul_ne_zero hC0 hK0
  have hpt : ∀ z, ∫⁻ r in Ioo (0 : ℝ) 2, f z r ∂scaleMeasure ≤ C * K := by
    intro z
    calc ∫⁻ r in Ioo (0 : ℝ) 2, f z r ∂scaleMeasure
        ≤ ∫⁻ r in Ioo (0 : ℝ) 2, C * ENNReal.ofReal r ^ γ ∂scaleMeasure :=
          setLIntegral_mono' measurableSet_Ioo (hup z)
      _ = C * K := by rw [lintegral_const_mul' C _ hC, hK]
  refine ⟨(C * K).toReal, ENNReal.toReal_pos hU0 hU, fun z => ?_, ?_, ?_⟩
  · rw [ENNReal.ofReal_toReal hU]
    exact hpt z
  · set c : ℝ≥0∞ := m * scaleMeasure I with hc
    have hc0 : c ≠ 0 := mul_ne_zero hm hI0.ne'
    have hlowz : ∀ z ∈ D, c ≤ ∫⁻ r in Ioo (0 : ℝ) 2, f z r ∂scaleMeasure := by
      intro z hz
      calc c = ∫⁻ _r in I, m ∂scaleMeasure := by rw [setLIntegral_const]
        _ ≤ ∫⁻ r in I, f z r ∂scaleMeasure := setLIntegral_mono' hIm (hlow z hz)
        _ ≤ ∫⁻ r in Ioo (0 : ℝ) 2, f z r ∂scaleMeasure := lintegral_mono_set hIsub
    calc (0 : ℝ≥0∞) < c * ω D := ENNReal.mul_pos hc0 hDω.ne'
      _ = ∫⁻ _z in D, c ∂ω := by rw [setLIntegral_const]
      _ ≤ ∫⁻ z in D, (∫⁻ r in Ioo (0 : ℝ) 2, f z r ∂scaleMeasure) ∂ω :=
          setLIntegral_mono' hDm hlowz
      _ ≤ _ := lintegral_mono_set hDsub
  · calc ∫⁻ z in Metric.ball (point 0 0) 1, (∫⁻ r in Ioo (0 : ℝ) 2, f z r ∂scaleMeasure) ∂ω
        ≤ ∫⁻ _z in Metric.ball (point 0 0) 1, C * K ∂ω := lintegral_mono fun z => hpt z
      _ = C * K * ω (Metric.ball (point 0 0) 1) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hU) (measure_lt_top _ _)

/-- Pointwise and integrated energy bounds for the diffuse measures (`E2DiffuseEnergyStatement`). -/
theorem e2_diffuse_energy_proof : E2DiffuseEnergyStatement := by
  intro hS hU hI n k T p hk hne hp hb
  obtain ⟨b, hbpos, hblow⟩ := hb
  obtain ⟨hfin, hDpos, -⟩ := hS n
  obtain ⟨hint, hI0, -⟩ := hI
  have : IsFiniteMeasure (e2_diffuseBase n) := hfin
  have hα : 0 < (n : ℝ) + 2 - k := by
    have : (k : ℝ) < n + 2 := by exact_mod_cast hk
    linarith
  have hp2 : 0 < 2 / p := div_pos two_pos hp
  have hγ : 0 < ((n : ℝ) + 2 - k) * (2 / p) := mul_pos hα hp2
  have hbo : (0 : ℝ≥0∞) < ENNReal.ofReal b := ENNReal.ofReal_pos.mpr hbpos
  have hDm : MeasurableSet (e2_diffuseBox n) := Metric.isOpen_ball.measurableSet
  have hDsub : e2_diffuseBox n ⊆ Metric.ball (point 0 0) 1 :=
    Metric.ball_subset_ball (by norm_num)
  have hIm : MeasurableSet e2_diffuseBand := measurableSet_Icc
  have hIsub : e2_diffuseBand ⊆ Ioo (0 : ℝ) 2 := by
    intro r hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have h2ω0 : (2 : ℝ≥0∞) * omega n ≠ 0 :=
    mul_ne_zero two_ne_zero (omega_pos n).ne'
  have h2ωt : (2 : ℝ≥0∞) * omega n ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (omega_lt_top n).ne
  -- the `T` energy
  obtain ⟨AT, hAT, hTup, hTint⟩ := e2d7_assemble (e2_diffuseBase n) (e2_diffuseBox n) hDm
    hDpos hDsub e2_diffuseBand hIm hIsub hI0
    (fun z r => betaPow (e2_diffuseBase n) k T p z r) (2 * omega n) (ENNReal.ofReal b)
    (ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) + 2 - k) / ((n : ℝ) + 2 - k))) ((n : ℝ) + 2 - k)
    h2ωt h2ω0 (hint _ hα)
    (ENNReal.ofReal_pos.mpr (div_pos (Real.rpow_pos_of_pos two_pos _) hα)).ne'
    ENNReal.ofReal_ne_top hbo.ne'
    (fun z r hr => hU n k T hne p hp z r hr.1)
    (fun z hz r hr => hblow z hz r hr)
  -- the `S` energy
  obtain ⟨AS, hAS, hSup, hSint⟩ := e2d7_assemble (e2_diffuseBase n) (e2_diffuseBox n) hDm
    hDpos hDsub e2_diffuseBand hIm hIsub hI0
    (fun z r => betaPow (e2_diffuseBase n) k T p z r ^ (2 / p)) ((2 * omega n) ^ (2 / p))
    (ENNReal.ofReal b ^ (2 / p))
    (ENNReal.ofReal ((2 : ℝ) ^ (((n : ℝ) + 2 - k) * (2 / p)) / (((n : ℝ) + 2 - k) * (2 / p))))
    (((n : ℝ) + 2 - k) * (2 / p))
    (ENNReal.rpow_ne_top_of_nonneg hp2.le h2ωt)
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr h2ω0) h2ωt).ne' (hint _ hγ)
    (ENNReal.ofReal_pos.mpr
      (div_pos (Real.rpow_pos_of_pos two_pos _) hγ)).ne'
    ENNReal.ofReal_ne_top (ENNReal.rpow_pos hbo ENNReal.ofReal_ne_top).ne'
    (fun z r hr => by
      calc betaPow (e2_diffuseBase n) k T p z r ^ (2 / p)
          ≤ (2 * omega n * ENNReal.ofReal r ^ ((n : ℝ) + 2 - k)) ^ (2 / p) :=
            ENNReal.rpow_le_rpow (hU n k T hne p hp z r hr.1) hp2.le
        _ = (2 * omega n) ^ (2 / p) * (ENNReal.ofReal r ^ ((n : ℝ) + 2 - k)) ^ (2 / p) :=
            ENNReal.mul_rpow_of_nonneg _ _ hp2.le
        _ = (2 * omega n) ^ (2 / p) * ENNReal.ofReal r ^ (((n : ℝ) + 2 - k) * (2 / p)) := by
            rw [ENNReal.rpow_mul])
    (fun z hz r hr => ENNReal.rpow_le_rpow (hblow z hz r hr) hp2.le)
  exact ⟨AS, AT, hAS, hAT, fun z => ⟨hSup z, hTup z⟩, hSint, hTint⟩

end ParabolicRectifiability.Examples
