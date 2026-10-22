import ParabolicRectifiability.Analysis.RegularExtension.NaturalBridge
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Recentering

/-! # The half-density bridge integrated below the density radius

`lintegral_Ioc_traceErrorSq_le_betaSq_proof` bounds the integral of the trace error over the
scales below the density radius by the corresponding beta integral.

Route: restriction monotonicity `γ_P ≤ γ_K` (`affineErrorSq_mono_measure`); the bridge
`traceErrorSq_le_vertical_betaSq_small` on `K`, at each `r ∈ (0, ρ]`, using
the half density **of `K`** at `p`; the change of scale `t = 2r` of `dr/r`
(`setLIntegral_scaleMeasure_comp_const_mul`, valid for every integrand); and
`(0, 2ρ] ⊆ (0, 2)` since `ρ ≤ 1/2`. `L₀` and `C` are those of `traceErrorSq_le_vertical_betaSq_small`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-- The preimage of `(0, 2ρ]` under `s ↦ 2s` is `(0, ρ]`. -/
theorem rx1_preimage_two_mul_Ioc (ρ : ℝ) :
    (fun s : ℝ => 2 * s) ⁻¹' Ioc 0 (2 * ρ) = Ioc 0 ρ := by
  ext r
  simp only [mem_preimage, mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- **Trace error below the density radius** (`lintegral_Ioc_traceErrorSq_le_betaSq`). -/
theorem lintegral_Ioc_traceErrorSq_le_betaSq_proof (m : ℕ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ L₀ ≤ 1 ∧ ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (W : Submodule ℝ (Spatial n)),
      Module.finrank ℝ W = m → Module.finrank ℝ W.orthogonal = d →
      ∀ (K P : Set (SubspaceSpace W)) (f : SubspaceSpace W → W.orthogonal) (L : ℝ≥0),
        IsCompact K → LipschitzOnWith L f K → (L : ℝ) ≤ L₀ → P ⊆ K →
        ∀ p ∈ P, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 →
          (∀ r : ℝ, 0 < r → r ≤ ρ →
            intrinsicParabolicVolume W (Metric.ball p r) ≤
              2 * intrinsicParabolicVolume W (K ∩ Metric.ball p r)) →
          ∫⁻ r in Ioc 0 ρ, traceErrorSq (intrinsicParabolicVolume W) P f p r ∂scaleMeasure ≤
            ENNReal.ofReal C *
              ∫⁻ r in Ioo 0 2,
                betaSq ((hausdorffP n (m + 2)).restrict
                    ((fun q : SubspaceSpace W =>
                      (((q.1 : Spatial n) + (f q : Spatial n), q.2) : Space n)) '' K))
                  (m + 2) .vertical
                  (((p.1 : Spatial n) + (f p : Spatial n), p.2) : Space n) r ∂scaleMeasure := by
  obtain ⟨L₀, hL₀, hL₀1, hbridge⟩ := traceErrorSq_le_vertical_betaSq_small m
  refine ⟨L₀, hL₀, hL₀1, fun d => ?_⟩
  obtain ⟨C, hC, hb⟩ := hbridge d
  refine ⟨C, hC, ?_⟩
  intro n W hW hd K P f L hK hf hL hPK p hp ρ hρ hρ2 hdens
  set g : ℝ → ℝ≥0∞ := fun s =>
    betaSq ((hausdorffP n (m + 2)).restrict
        ((fun q : SubspaceSpace W =>
          (((q.1 : Spatial n) + (f q : Spatial n), q.2) : Space n)) '' K))
      (m + 2) .vertical
      (((p.1 : Spatial n) + (f p : Spatial n), p.2) : Space n) s with hg
  have hscale := setLIntegral_scaleMeasure_comp_const_mul (c := 2) two_pos g (Ioc 0 (2 * ρ))
  rw [rx1_preimage_two_mul_Ioc] at hscale
  calc ∫⁻ r in Ioc 0 ρ, traceErrorSq (intrinsicParabolicVolume W) P f p r ∂scaleMeasure
      ≤ ∫⁻ r in Ioc 0 ρ, ENNReal.ofReal C * g (2 * r) ∂scaleMeasure := by
        refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
        calc traceErrorSq (intrinsicParabolicVolume W) P f p r
            ≤ traceErrorSq (intrinsicParabolicVolume W) K f p r :=
              affineErrorSq_mono_measure (Measure.restrict_mono hPK le_rfl) f p r
          _ ≤ ENNReal.ofReal C * g (2 * r) :=
              hb W hW hd K f L hK hf hL p (hPK hp) r hr.1 (hdens r hr.1 hr.2)
    _ = ENNReal.ofReal C * ∫⁻ r in Ioc 0 ρ, g (2 * r) ∂scaleMeasure :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal C * ∫⁻ t in Ioc 0 (2 * ρ), g t ∂scaleMeasure := by rw [hscale]
    _ ≤ ENNReal.ofReal C * ∫⁻ t in Ioo 0 2, g t ∂scaleMeasure := by
        refine mul_le_mul' le_rfl (lintegral_mono_set fun t ht => ⟨ht.1, ?_⟩)
        linarith [ht.2]

end ParabolicRectifiability
