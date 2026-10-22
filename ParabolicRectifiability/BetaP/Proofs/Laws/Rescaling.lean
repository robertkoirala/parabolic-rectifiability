import ParabolicRectifiability.BetaP.Proofs.Laws.Basic
import ParabolicRectifiability.Analysis.TraceExtension.TracePieces.Normalize

/-! # Dilation law of `B_p` and of the two beta-`p` energies

`BetaPowRescalingStatement`.
The proof follows `fit_rescaledSource` / `betaSq_rescaledSource` with
the exponent `p` in place of `2`: the parabolic distance to the transported model scales by
`R⁻¹` (`claws_infEDist_modelSimilarity`), so for a fixed model the fitting integral of the
rescaled source is `R^{-k-p}` times the original one at radius `R s`; the model bijection
`modelSimilarity` transports the infimum and `s^{-k-p} R^{-k-p} = (R s)^{-k-p}`. The energies
follow from the change of scale `t = R r` for `dr/r`
(`setLIntegral_Ioo_scaleMeasure_comp_const_mul`). Every family; no
regularity of `μ`; the guards on `n`, `k` and `p` other than `0 < p` are not used.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- The parabolic distance to a transported model scales by `a⁻¹`. -/
theorem claws_infEDist_modelSimilarity {n k : ℕ} {T : FamilyKind} (q : Space n) (a : ℝ)
    (ha : 0 < a) (L : Models n k T) (z : Space n) :
    Metric.infEDist (similarity q a ha z) (modelSet (modelSimilarity T q a ha L)) =
      (ENNReal.ofReal a)⁻¹ * Metric.infEDist z (modelSet L) := by
  have h0 : (ENNReal.ofReal a)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have ht : (ENNReal.ofReal a)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr ha).ne'
  simp only [modelSet_modelSimilarity, Metric.infEDist, iInf_image, edist_similarity,
    ← ENNReal.mul_iInf_of_ne h0 ht]

/-- The fixed-model pushforward identity for the `p`-fitting integral. -/
theorem claws_fitPow_rescaledSource {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n))
    {p : ℝ} (hp : 0 ≤ p) (q : Space n) (a : ℝ) (ha : 0 < a) (L : Models n k T)
    (z : Space n) (s : ℝ) :
    fitPow (rescaledSource μ k q a ha) p (modelSimilarity T q a ha L) (similarity q a ha z) s =
      (ENNReal.ofReal a)⁻¹ ^ ((k : ℝ) + p) * fitPow μ p L z (a * s) := by
  have h0 : (ENNReal.ofReal a)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have ht : (ENNReal.ofReal a)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr ha).ne'
  unfold fitPow
  rw [rescaledSource, Measure.restrict_smul, lintegral_smul_measure,
    setLIntegral_map measurableSet_ball (measurable_infEDist.pow_const p)
      (similarity q a ha).measurable,
    preimage_similarity_ball]
  simp only [claws_infEDist_modelSimilarity, ENNReal.mul_rpow_of_nonneg _ _ hp, smul_eq_mul]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp ht), ← mul_assoc,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ h0 ht]

/-- The dilation law of `B_p` at every positive radius, for every family. -/
theorem claws_betaPow_rescaledSource {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    {p : ℝ} (hp : 0 < p) (q : Space n) (a : ℝ) (ha : 0 < a) (z : Space n) {s : ℝ}
    (hs : 0 < s) :
    betaPow (rescaledSource μ k q a ha) k T p (similarity q a ha z) s =
      betaPow μ k T p z (a * s) := by
  have h0 : (ENNReal.ofReal a)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have ht : (ENNReal.ofReal a)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr ha).ne'
  have hkp : 0 ≤ (k : ℝ) + p := by positivity
  rw [claws_betaPow_of_pos _ _ _ _ _ hs, claws_betaPow_of_pos _ _ _ _ _ (mul_pos ha hs)]
  rw [← (modelSimilarity T q a ha).iInf_comp]
  simp only [claws_fitPow_rescaledSource μ hp.le]
  rw [← ENNReal.mul_iInf_of_ne (ENNReal.rpow_pos (pos_iff_ne_zero.mpr h0) ht).ne'
      (ENNReal.rpow_ne_top_of_nonneg hkp ht),
    ENNReal.ofReal_mul ha.le,
    ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr ha).ne') (Or.inl ENNReal.ofReal_ne_top),
    ENNReal.mul_rpow_of_nonneg _ _ hkp]
  ring

/-- Dilation law. -/
theorem claws_rescaling_proof : BetaPowRescalingStatement := by
  intro n _ k _ _ T μ p hp q R hR z
  refine ⟨fun s hs => claws_betaPow_rescaledSource μ k T hp q R hR z hs, fun a _ => ⟨?_, ?_⟩⟩
  · unfold energyS
    have h1 : ∫⁻ r in Ioo 0 a,
          betaPow (rescaledSource μ k q R hR) k T p (similarity q R hR z) r ^ (2 / p)
            ∂scaleMeasure =
        ∫⁻ r in Ioo 0 a, betaPow μ k T p z (R * r) ^ (2 / p) ∂scaleMeasure :=
      setLIntegral_congr_fun measurableSet_Ioo fun r hr => by
        rw [claws_betaPow_rescaledSource μ k T hp q R hR z hr.1]
    rw [h1]
    have h2 := setLIntegral_Ioo_scaleMeasure_comp_const_mul hR
      (fun t => betaPow μ k T p z t ^ (2 / p)) (a * R)
    rwa [mul_div_cancel_right₀ a hR.ne'] at h2
  · unfold energyT
    have h1 : ∫⁻ r in Ioo 0 a,
          betaPow (rescaledSource μ k q R hR) k T p (similarity q R hR z) r ∂scaleMeasure =
        ∫⁻ r in Ioo 0 a, betaPow μ k T p z (R * r) ∂scaleMeasure :=
      setLIntegral_congr_fun measurableSet_Ioo fun r hr => by
        rw [claws_betaPow_rescaledSource μ k T hp q R hR z hr.1]
    rw [h1]
    have h2 := setLIntegral_Ioo_scaleMeasure_comp_const_mul hR
      (fun t => betaPow μ k T p z t) (a * R)
    rwa [mul_div_cancel_right₀ a hR.ne'] at h2

end ParabolicRectifiability.BetaP
