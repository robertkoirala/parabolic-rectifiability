import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.TransferStatements
import ParabolicRectifiability.Metric.ProperSpace

/-! # The normalized moving-ball probability kernel

Proves `b3_offCarrierKernel : OffCarrierKernelStatement` as `b3_offCarrierKernel_proof`.

Route (selection-free). With `d(y) = dist(y, Γ)` and the moving ball `B_y = P(y, 2 d(y))`,
`K_y = δ_y` for `y ∈ Γ` and `K_y = σ⌊B_y / σ(B_y)` for `y ∉ Γ`.
* Off `Γ`, `0 < d(y)` (`Γ` closed and nonempty). A point `γ ∈ Γ` with `d(y,γ) < 3 d(y)/2`,
  chosen non-measurably and used only for the bounds, gives
  `P(γ, d(y)/2) ⊆ B_y ⊆ P(γ, 4 d(y))`, hence `0 < c (d/2)^k ≤ σ(B_y) ≤ C (4d)^k < ∞`
  (`b3ker_denominator`).
* Borel kernel: `y ↦ σ(S ∩ B_y)` is a parameter integral of the open set
  `{(y,w) : dist w y < 2 d(y)}` against the sigma-finite `σ` (`measurable_measure_prodMk_left`),
  and the definition is piecewise on the closed set `Γ` (`b3ker_measurable_measure`).
* `K_y(Γᶜ) = 0` from `σ(Γᶜ) = σ((supp σ)ᶜ) = 0`; displacement `d(y,v) < 2 d(y) ≤ 3 d(y)` off
  `Γ`, and `v = y` on `Γ`.
-/

noncomputable section

open MeasureTheory Set Function ProbabilityTheory
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.SourceTransferTree

open ParabolicRectifiability.Foundations

/-- The moving ball `B_y = P(y, 2 dist(y, Γ))`. -/
def b3ker_ball {n : ℕ} (Γ : Set (Space n)) (y : Space n) : Set (Space n) :=
  Metric.ball y (2 * Metric.infDist y Γ)

/-- The joint moving-ball set `{(y, w) : dist w y < 2 dist(y, Γ)}`. -/
def b3ker_graph {n : ℕ} (Γ : Set (Space n)) : Set (Space n × Space n) :=
  {p | dist p.2 p.1 < 2 * Metric.infDist p.1 Γ}

open Classical in
/-- The kernel's measures: `δ_y` on `Γ`, the normalized `σ⌊B_y` off `Γ`. -/
def b3ker_measure {n : ℕ} (Γ : Set (Space n)) (σ : Measure (Space n)) (y : Space n) :
    Measure (Space n) :=
  if y ∈ Γ then Measure.dirac y else (σ (b3ker_ball Γ y))⁻¹ • σ.restrict (b3ker_ball Γ y)

theorem b3ker_measurableSet_graph {n : ℕ} (Γ : Set (Space n)) :
    MeasurableSet (b3ker_graph Γ) :=
  (isOpen_lt (continuous_snd.dist continuous_fst)
    (continuous_const.mul ((Metric.continuous_infDist_pt Γ).comp continuous_fst))).measurableSet

/-- Parameter integration: `y ↦ σ(S ∩ B_y)` is measurable for a Borel `S`. -/
theorem b3ker_measurable_section {n : ℕ} (Γ : Set (Space n)) (σ : Measure (Space n))
    [SFinite σ] {s : Set (Space n)} (hs : MeasurableSet s) :
    Measurable fun y => σ (s ∩ b3ker_ball Γ y) := by
  have hT : MeasurableSet (Prod.snd ⁻¹' s ∩ b3ker_graph Γ) :=
    (measurable_snd hs).inter (b3ker_measurableSet_graph Γ)
  have heq : (fun y => σ (s ∩ b3ker_ball Γ y)) =
      fun y => σ (Prod.mk y ⁻¹' (Prod.snd ⁻¹' s ∩ b3ker_graph Γ)) := by
    funext y
    rfl
  rw [heq]
  exact measurable_measure_prodMk_left hT

/-- The kernel is Borel. -/
theorem b3ker_measurable_measure {n : ℕ} (Γ : Set (Space n)) (hΓ : IsClosed Γ)
    (σ : Measure (Space n)) [SFinite σ] : Measurable (b3ker_measure Γ σ) := by
  classical
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have h1 : Measurable fun y : Space n => s.indicator (1 : Space n → ℝ≥0∞) y :=
    measurable_one.indicator hs
  have h0 := b3ker_measurable_section Γ σ MeasurableSet.univ
  simp only [univ_inter] at h0
  have h2 : Measurable fun y => (σ (b3ker_ball Γ y))⁻¹ * σ (s ∩ b3ker_ball Γ y) :=
    h0.inv.mul (b3ker_measurable_section Γ σ hs)
  have heq : (fun y => b3ker_measure Γ σ y s) =
      Γ.piecewise (fun y => s.indicator (1 : Space n → ℝ≥0∞) y)
        (fun y => (σ (b3ker_ball Γ y))⁻¹ * σ (s ∩ b3ker_ball Γ y)) := by
    funext y
    by_cases hy : y ∈ Γ
    · rw [Set.piecewise_eq_of_mem _ _ _ hy, b3ker_measure]
      simp only [hy, ↓reduceIte]
      rw [Measure.dirac_apply]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hy, b3ker_measure]
      simp only [hy, ↓reduceIte]
      rw [Measure.smul_apply,
        Measure.restrict_apply hs, smul_eq_mul]
  rw [heq]
  exact Measurable.piecewise hΓ.measurableSet h1 h2

/-- Off `Γ` the denominator `σ(B_y)` is positive and finite: with a nearby carrier point `γ`
(chosen only for the bounds), `P(γ, d/2) ⊆ B_y ⊆ P(γ, 4d)`, so
`c (d/2)^k ≤ σ(B_y) ≤ C (4d)^k`. -/
theorem b3ker_denominator {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hσ : IsADRCarrier k c C Γ σ) {y : Space n} (hy : y ∉ Γ) :
    σ (b3ker_ball Γ y) ≠ 0 ∧ σ (b3ker_ball Γ y) ≠ ⊤ := by
  set d := Metric.infDist y Γ with hd
  have hdpos : 0 < d := (hσ.isClosed.notMem_iff_infDist_pos hσ.nonempty).1 hy
  obtain ⟨γ, hγ, hyγ⟩ : ∃ γ ∈ Γ, dist y γ < 3 * d / 2 :=
    (Metric.infDist_lt_iff hσ.nonempty).1 (by linarith)
  have hsub1 : Metric.ball γ (d / 2) ⊆ b3ker_ball Γ y := by
    intro w hw
    have hw' : dist w γ < d / 2 := hw
    show dist w y < 2 * d
    have := dist_triangle w γ y
    have := dist_comm y γ
    linarith
  have hsub2 : b3ker_ball Γ y ⊆ Metric.ball γ (4 * d) := by
    intro w hw
    have hw' : dist w y < 2 * d := hw
    show dist w γ < 4 * d
    have := dist_triangle w y γ
    linarith
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (c * (d / 2) ^ k) :=
    ENNReal.ofReal_pos.2 (mul_pos hσ.lower_pos (pow_pos (by linarith) k))
  refine ⟨?_, ?_⟩
  · exact (lt_of_lt_of_le hpos
      ((hσ.lower γ hγ (d / 2) (by linarith)).trans (measure_mono hsub1))).ne'
  · exact ((measure_mono hsub2).trans (hσ.upper γ hγ (4 * d) (by linarith))).trans_lt
      ENNReal.ofReal_lt_top |>.ne

/-- Every `K_y` is a probability measure. -/
theorem b3ker_isProbabilityMeasure {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)}
    {σ : Measure (Space n)} (hσ : IsADRCarrier k c C Γ σ) (y : Space n) :
    IsProbabilityMeasure (b3ker_measure Γ σ y) := by
  by_cases hy : y ∈ Γ
  · rw [b3ker_measure]
    simp only [hy, ↓reduceIte]
    infer_instance
  · constructor
    rw [b3ker_measure]
    simp only [hy, ↓reduceIte]
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, smul_eq_mul]
    obtain ⟨h0, htop⟩ := b3ker_denominator hσ hy
    exact ENNReal.inv_mul_cancel h0 htop

/-- `K_y` is carried by `Γ`. -/
theorem b3ker_compl {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hσ : IsADRCarrier k c C Γ σ) (y : Space n) : b3ker_measure Γ σ y Γᶜ = 0 := by
  by_cases hy : y ∈ Γ
  · rw [b3ker_measure]
    simp only [hy, ↓reduceIte]
    rw [Measure.dirac_apply]
    exact Set.indicator_of_notMem (fun h : y ∈ Γᶜ => h hy) _
  · have hσc : σ Γᶜ = 0 := by
      rw [← hσ.support_eq]
      exact Measure.measure_compl_support
    rw [b3ker_measure]
    simp only [hy, ↓reduceIte]
    rw [Measure.smul_apply,
      Measure.restrict_apply hσ.isClosed.measurableSet.compl, smul_eq_mul,
      measure_mono_null inter_subset_left hσc, mul_zero]

/-- Displacement: `K_y`-a.e. `d(y, v) ≤ 3 dist(y, Γ)`. -/
theorem b3ker_ae_displacement {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)}
    {σ : Measure (Space n)} (hσ : IsADRCarrier k c C Γ σ) (y : Space n) :
    ∀ᵐ v ∂(b3ker_measure Γ σ y), edist y v ≤ 3 * Metric.infEDist y Γ := by
  by_cases hy : y ∈ Γ
  · rw [b3ker_measure]
    simp only [hy, ↓reduceIte]
    rw [ae_dirac_eq]
    exact Filter.eventually_pure.2 (by simp)
  · set d := Metric.infDist y Γ with hd
    have hE : Metric.infEDist y Γ = ENNReal.ofReal d := by
      rw [hd, Metric.infDist, ENNReal.ofReal_toReal (Metric.infEDist_ne_top hσ.nonempty)]
    have hsub : {v | ¬ edist y v ≤ 3 * Metric.infEDist y Γ} ⊆ (b3ker_ball Γ y)ᶜ := by
      intro v hv hvB
      apply hv
      have hv' : dist v y < 2 * d := hvB
      have hd0 : 0 ≤ d := Metric.infDist_nonneg
      calc edist y v = ENNReal.ofReal (dist y v) := edist_dist y v
        _ ≤ ENNReal.ofReal (3 * d) :=
            ENNReal.ofReal_le_ofReal (by rw [dist_comm]; linarith)
        _ = 3 * Metric.infEDist y Γ := by
            rw [ENNReal.ofReal_mul (by norm_num), hE, ENNReal.ofReal_ofNat]
    have hB : MeasurableSet (b3ker_ball Γ y) := Metric.isOpen_ball.measurableSet
    rw [ae_iff]
    refine measure_mono_null hsub ?_
    rw [b3ker_measure]
    simp only [hy, ↓reduceIte]
    rw [Measure.smul_apply, Measure.restrict_apply hB.compl,
      smul_eq_mul, compl_inter_self, measure_empty, mul_zero]

/-- The normalized moving-ball probability kernel: `OffCarrierKernelStatement`. -/
theorem b3_offCarrierKernel_proof : OffCarrierKernelStatement := by
  intro n k c C Γ σ hσ
  have := hσ.finiteOnCompacts
  refine ⟨⟨b3ker_measure Γ σ, b3ker_measurable_measure Γ hσ.isClosed σ⟩,
    ⟨fun y => b3ker_isProbabilityMeasure hσ y⟩, fun y => b3ker_compl hσ y,
    fun y => b3ker_ae_displacement hσ y⟩

end ParabolicRectifiability.Characterization.SourceTransferTree
