import ParabolicRectifiability.QuantitativeCharacterization.Statements.ReverseBound
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Kernel.Composition.MapComap

/-! # Transfer to one reference from its parts

Proof of `d2_model_transfer_of_parts`. The four sibling statements `CouplingStatement`,
`ComparisonStatement`, `ErrorIntegralStatement` and `MainTermStatement` enter as hypotheses
(implication form).

Proof idea. Constants: `C_disp, Bal` from the coupling at `A_ref`; `Be` from the
error statement at `(L, C_disp)`; `Bm = max Bal Be`. For `A ≥ 1`: `D₀` (coupling), `Ce` (error),
`Λ = 1 + 2 C_disp (1 + L)`, `Cm` from the main term at `(C_disp, D₀, Λ, C_ref)`, and
`C₁ = 2 D₀ Λ^{k+2} Cm + 2 Ce`. For a pair `(z,r)` of the model with `r > 0`, `κ_z` is a
probability, so `β_μ(z,r)² = ∫ β_μ(z,r)² dκ_z`, and the comparison holds for `κ_z`-a.e. `v`
(the displacement bound of the kernel). No measurable selection of a transported centre is used.
For `r ≤ 0` the beta vanishes by its convention. Integrating over the model pairs, the
reference term is enlarged to `P(c,ρ) × (0,ρ)` and bounded by the main term (the second `D₀`),
the error term by the error statement.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization.ReverseTree

open ParabolicRectifiability.Foundations

/-- The model pairs `{(z,r) : z ∈ P(c,ρ), L⁻¹ d(z) ≤ r < ρ}` form a Borel set. -/
theorem d2mt_measurableSet_modelPairs {n : ℕ} (L : ℝ) (Γ : Set (Space n)) (c : Space n)
    (ρ : ℝ) : MeasurableSet (d2_modelPairs L Γ c ρ) :=
  (measurableSet_ball.preimage measurable_fst).inter
    ((measurableSet_le (measurable_const.mul
        ((Metric.continuous_infDist_pt Γ).measurable.comp measurable_fst)) measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const))

/-- The kernel average `(z,r) ↦ ∫ β_{σ,T}(v,Λr)² dκ_z(v)` is measurable. -/
theorem d2mt_measurable_kernelBeta {n : ℕ} (σ : Measure (Space n)) [IsFiniteMeasureOnCompacts σ]
    (k : ℕ) (T : FamilyKind) (Λ : ℝ) (κ : ProbabilityTheory.Kernel (Space n) (Space n))
    [ProbabilityTheory.IsSFiniteKernel κ] :
    Measurable (fun p : Space n × ℝ => ∫⁻ v, betaSq σ k T v (Λ * p.2) ∂(κ p.1)) := by
  have hf : Measurable (fun q : (Space n × ℝ) × Space n => betaSq σ k T q.2 (Λ * q.1.2)) :=
    (measurable_betaSq σ k T).comp
      (measurable_snd.prodMk (measurable_const.mul (measurable_snd.comp measurable_fst)))
  have h := hf.lintegral_kernel_prod_right'
    (κ := ProbabilityTheory.Kernel.comap κ Prod.fst measurable_fst)
  simpa only [ProbabilityTheory.Kernel.comap_apply] using h

/-- The pointwise averaged comparison on the model pairs: for `(z,r)` in the model pairs,
`β_μ(z,r)² ≤ 2 D₀ Λ^{k+2} 1_{P(c,ρ)×(0,ρ)}(z,r) ∫ β_σ(v,Λr)² dκ_z(v) + 2 e(z,r)`. -/
theorem d2mt_pointwise (hcmp : ComparisonStatement) {n k : ℕ} (T : FamilyKind) {L Cdisp D₀ : ℝ}
    (hL : 1 ≤ L) (hCdisp : 1 ≤ Cdisp) (hD₀ : 0 < D₀) (μ σ : Measure (Space n))
    (Γ : Set (Space n)) (κ : ProbabilityTheory.Kernel (Space n) (Space n))
    (hκ : ProbabilityTheory.IsMarkovKernel κ)
    (hdisp : ∀ y, ∀ᵐ v ∂(κ y), dist y v ≤ Cdisp * Metric.infDist y Γ) (c : Space n) (ρ : ℝ)
    (hbind : (μ.restrict (Metric.ball c (2 * ρ))).bind κ ≤ ENNReal.ofReal D₀ • σ) :
    ∀ p ∈ d2_modelPairs L Γ c ρ, betaSq μ k T p.1 p.2 ≤
      ENNReal.ofReal (2 * D₀ * (1 + 2 * Cdisp * (1 + L)) ^ (k + 2)) *
          (Metric.ball c ρ ×ˢ Ioo 0 ρ).indicator
            (fun q : Space n × ℝ =>
              ∫⁻ v, betaSq σ k T v ((1 + 2 * Cdisp * (1 + L)) * q.2) ∂(κ q.1)) p +
        2 * d2_transportError k Cdisp Γ μ p.1 p.2 := by
  have := hκ
  intro p hp
  obtain ⟨hz, hLr, hrρ⟩ := hp
  rcases le_or_gt p.2 0 with hr | hr
  · rw [betaSq_of_nonpos μ k T p.1 hr]
    exact (zero_le : (0 : ℝ≥0∞) ≤ _)
  · have hmem : p ∈ Metric.ball c ρ ×ˢ Ioo 0 ρ := ⟨hz, hr, hrρ⟩
    rw [Set.indicator_of_mem hmem]
    calc betaSq μ k T p.1 p.2 = ∫⁻ _v, betaSq μ k T p.1 p.2 ∂(κ p.1) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ v, (ENNReal.ofReal (2 * D₀ * (1 + 2 * Cdisp * (1 + L)) ^ (k + 2)) *
              betaSq σ k T v ((1 + 2 * Cdisp * (1 + L)) * p.2) +
            2 * d2_transportError k Cdisp Γ μ p.1 p.2) ∂(κ p.1) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hdisp p.1] with v hv
          exact hcmp n k T L Cdisp D₀ hL hCdisp hD₀ μ σ Γ κ hκ hdisp c ρ hbind p.1 p.2 hz hr hrρ
            hLr v hv
      _ = ENNReal.ofReal (2 * D₀ * (1 + 2 * Cdisp * (1 + L)) ^ (k + 2)) *
              ∫⁻ v, betaSq σ k T v ((1 + 2 * Cdisp * (1 + L)) * p.2) ∂(κ p.1) +
            2 * d2_transportError k Cdisp Γ μ p.1 p.2 := by
          rw [lintegral_add_right _ measurable_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const, measure_univ, mul_one]

/-- **Transfer to one reference**  from its parts: the implication of the statement
`d2_model_transfer_of_parts`. -/
theorem d2_model_transfer_of_parts_proof :
    CouplingStatement → ComparisonStatement → ErrorIntegralStatement → MainTermStatement →
      ModelTransferStatement := by
  intro hcpl hcmp herr hmain n hn k hk1 hkn L hL Aref hAref Cref hCref
  obtain ⟨Cdisp, hCdisp, Bal, hBal, hcplA⟩ := hcpl n hn k hk1 hkn Aref hAref
  obtain ⟨Be, hBe, herrA⟩ := herr n hn k hk1 hkn L Cdisp hL hCdisp
  refine ⟨max Bal Be, le_max_of_le_left hBal, ?_⟩
  intro A hA
  obtain ⟨D₀, hD₀, hcplμ⟩ := hcplA A hA
  obtain ⟨Ce, hCe, herrμ⟩ := herrA A hA
  have hθ : 0 ≤ 2 * Cdisp * (1 + L) :=
    mul_nonneg (mul_nonneg zero_le_two (by linarith)) (by linarith)
  have hΛ : 1 ≤ 1 + 2 * Cdisp * (1 + L) := by linarith
  have hΛpos : 0 < 1 + 2 * Cdisp * (1 + L) := by linarith
  obtain ⟨Cm, hCm, hmainμ⟩ :=
    hmain n hn k hk1 hkn Cdisp D₀ (1 + 2 * Cdisp * (1 + L)) Cref hCdisp hD₀ hΛ hCref
  have ha : 0 < 2 * D₀ * (1 + 2 * Cdisp * (1 + L)) ^ (k + 2) :=
    mul_pos (mul_pos two_pos hD₀) (pow_pos hΛpos _)
  refine ⟨2 * D₀ * (1 + 2 * Cdisp * (1 + L)) ^ (k + 2) * Cm + 2 * Ce,
    add_pos (mul_pos ha hCm) (mul_pos two_pos hCe), ?_⟩
  intro μ hμ1 hμ2 T Γ σ hσ1 hσsupp hADR hcarl c hc ρ hρ hmeet hgrowth
  have hBalρ : Bal * ρ ≤ max Bal Be * ρ := mul_le_mul_of_nonneg_right (le_max_left _ _) hρ.le
  have hBeρ : Be * ρ ≤ max Bal Be * ρ := mul_le_mul_of_nonneg_right (le_max_right _ _) hρ.le
  have hgBal : ∀ b ∈ μ.support ∩ Metric.ball c (Bal * ρ), ∀ s : ℝ, 0 < s → s ≤ Bal * ρ →
      μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k) := fun b hb s hs hsle =>
    hgrowth b ⟨hb.1, Metric.ball_subset_ball hBalρ hb.2⟩ s hs (hsle.trans hBalρ)
  have hgBe : ∀ b ∈ μ.support ∩ Metric.ball c (Be * ρ), ∀ s : ℝ, 0 < s → s ≤ Be * ρ →
      μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k) := fun b hb s hs hsle =>
    hgrowth b ⟨hb.1, Metric.ball_subset_ball hBeρ hb.2⟩ s hs (hsle.trans hBeρ)
  obtain ⟨κ, hκ, hdisp, hbind⟩ := hcplμ μ hμ1 hμ2 Γ σ hσ1 hσsupp hADR c ρ hρ hmeet hgBal
  have hE := herrμ μ hμ1 hμ2 Γ c hc ρ hρ hgBe
  have hM := hmainμ μ hμ1 hμ2 T Γ σ hσ1 hcarl κ hκ hdisp c ρ hρ hmeet hbind
  have := hκ
  have := hσ1
  have hS := d2mt_measurableSet_modelPairs L Γ c ρ
  have hB : MeasurableSet (Metric.ball c ρ ×ˢ Ioo 0 ρ) := measurableSet_ball.prod measurableSet_Ioo
  have hGm : Measurable ((Metric.ball c ρ ×ˢ Ioo 0 ρ).indicator
      (fun q : Space n × ℝ =>
        ∫⁻ v, betaSq σ k T v ((1 + 2 * Cdisp * (1 + L)) * q.2) ∂(κ q.1))) :=
    (d2mt_measurable_kernelBeta σ k T (1 + 2 * Cdisp * (1 + L)) κ).indicator hB
  have hpt := d2mt_pointwise hcmp (k := k) T hL hCdisp hD₀ μ σ Γ κ hκ hdisp c ρ hbind
  have hCm0 : 0 ≤ Cm * ρ ^ k := mul_nonneg hCm.le (pow_nonneg hρ.le _)
  have hCe0 : 0 ≤ Ce * ρ ^ k := mul_nonneg hCe.le (pow_nonneg hρ.le _)
  calc ∫⁻ p in d2_modelPairs L Γ c ρ, betaSq μ k T p.1 p.2 ∂(pointScaleMeasure μ)
      ≤ ∫⁻ p in d2_modelPairs L Γ c ρ,
          (ENNReal.ofReal (2 * D₀ * (1 + 2 * Cdisp * (1 + L)) ^ (k + 2)) *
              (Metric.ball c ρ ×ˢ Ioo 0 ρ).indicator
                (fun q : Space n × ℝ =>
                  ∫⁻ v, betaSq σ k T v ((1 + 2 * Cdisp * (1 + L)) * q.2) ∂(κ q.1)) p +
            2 * d2_transportError k Cdisp Γ μ p.1 p.2) ∂(pointScaleMeasure μ) :=
        setLIntegral_mono' hS hpt
    _ = ENNReal.ofReal (2 * D₀ * (1 + 2 * Cdisp * (1 + L)) ^ (k + 2)) *
            ∫⁻ p in d2_modelPairs L Γ c ρ,
              (Metric.ball c ρ ×ˢ Ioo 0 ρ).indicator
                (fun q : Space n × ℝ =>
                  ∫⁻ v, betaSq σ k T v ((1 + 2 * Cdisp * (1 + L)) * q.2) ∂(κ q.1)) p
              ∂(pointScaleMeasure μ) +
          2 * ∫⁻ p in d2_modelPairs L Γ c ρ, d2_transportError k Cdisp Γ μ p.1 p.2
              ∂(pointScaleMeasure μ) := by
        rw [lintegral_add_left (hGm.const_mul _), lintegral_const_mul _ hGm,
          lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    _ ≤ ENNReal.ofReal (2 * D₀ * (1 + 2 * Cdisp * (1 + L)) ^ (k + 2)) *
            ENNReal.ofReal (Cm * ρ ^ k) + 2 * ENNReal.ofReal (Ce * ρ ^ k) := by
        gcongr
        exact (setLIntegral_le_lintegral _ _).trans ((lintegral_indicator hB _).le.trans hM)
    _ = ENNReal.ofReal ((2 * D₀ * (1 + 2 * Cdisp * (1 + L)) ^ (k + 2) * Cm + 2 * Ce) * ρ ^ k) := by
        rw [show (2 * D₀ * (1 + 2 * Cdisp * (1 + L)) ^ (k + 2) * Cm + 2 * Ce) * ρ ^ k =
            2 * D₀ * (1 + 2 * Cdisp * (1 + L)) ^ (k + 2) * (Cm * ρ ^ k) + 2 * (Ce * ρ ^ k) by ring,
          ENNReal.ofReal_add (mul_nonneg ha.le hCm0) (mul_nonneg zero_le_two hCe0),
          ENNReal.ofReal_mul ha.le, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]

end ParabolicRectifiability.QuantitativeCharacterization.ReverseTree
