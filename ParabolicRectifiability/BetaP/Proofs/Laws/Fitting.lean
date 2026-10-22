import ParabolicRectifiability.Foundations.BetaPow
import ParabolicRectifiability.Measure.FittingMinimum

/-! # The `p`-fitting API: countable fitting, joint measurability and attainment

Shared `p`-fitting API for the measurability law `BetaPowMeasurabilityStatement` and the
zero-error bridge `squareEnergy_eq_zero_of_energyS_eq_zero`.

These are the `p`-versions of the quadratic statements `continuous_fit`,
`iInf_fit_modelSequence`, `measurable_fit`, `measurable_iInf_fit`, `measurable_betaSq` and
`exists_globalFittingError_minimizer`, reusing their generic lemmas
(`continuous_parameter_ballIntegral`, `modelSequence`, `boundedModels`, `clampModel`):

* `d_P(w,L)^p = (d_P(w,L)^2)^{p/2} = modelCost L w ^ (p/2)` (`cfit_infEDist_rpow_eq`), so the
  `p`-integrand is `ofReal (q_L(w)^{p/2})` with the real squared cost `q_L = modelRealCost L`;
* `L ↦ fitPow μ p L z r` is continuous for a finite-on-compacts source and `p ≥ 0`
  (`cfit_continuous_fitPow`), hence the infimum over the dense `modelSequence` is the full
  infimum (`cfit_iInf_fitPow_modelSequence`);
* `(z,r) ↦ fitPow μ p L z r` is jointly Borel (`cfit_measurable_fitPow`), so is the countable
  infimum and `B_p` (`cfit_measurable_betaPow`);
* on every bounded testing ball the `p`-fit is attained (`cfit_exists_fitPow_minimizer`):
  clamping a model to the box containing `P(z,r)` decreases the cost pointwise on the ball, and
  the continuous fit has a minimum on the compact bounded family;
* a vanishing `p`-fit of one model forces the vanishing of its quadratic fit
  (`cfit_fit_eq_zero_of_fitPow_eq_zero`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

variable {n k : ℕ} {T : FamilyKind}

/-- `d_P(w,L)^p = (d_P(w,L)^2)^{p/2}`, with `d_P(w,L)^2 = modelCost L w`, for every real `p`. -/
theorem cfit_infEDist_rpow_eq (p : ℝ) (L : Models n k T) (w : Space n) :
    Metric.infEDist w (modelSet L) ^ p = modelCost L w ^ (p / 2) := by
  calc Metric.infEDist w (modelSet L) ^ p
      = Metric.infEDist w (modelSet L) ^ ((2 : ℝ) * (p / 2)) := by congr 1; ring
    _ = (Metric.infEDist w (modelSet L) ^ (2 : ℝ)) ^ (p / 2) := ENNReal.rpow_mul _ _ _
    _ = modelCost L w ^ (p / 2) := by rw [ENNReal.rpow_two]; rfl

/-- The `p`-fitting integral through the squared cost. -/
theorem cfit_fitPow_eq_lintegral_modelCost (μ : Measure (Space n)) (p : ℝ) (L : Models n k T)
    (z : Space n) (r : ℝ) :
    fitPow μ p L z r = ∫⁻ w in Metric.ball z r, modelCost L w ^ (p / 2) ∂μ := by
  simp only [fitPow, cfit_infEDist_rpow_eq]

/-- Real form of the `p`-fitting integral for a finite-on-compacts source, `p ≥ 0`. -/
theorem cfit_fitPow_eq_ofReal_integral (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    {p : ℝ} (hp : 0 ≤ p) (L : Models n k T) (z : Space n) (r : ℝ) :
    fitPow μ p L z r =
      ENNReal.ofReal (∫ w in Metric.ball z r, modelRealCost L w ^ (p / 2) ∂μ) := by
  have hp2 : 0 ≤ p / 2 := by linarith
  have hc : Continuous (fun w : Space n => modelRealCost L w ^ (p / 2)) :=
    (continuous_modelRealCost.comp (continuous_const.prodMk continuous_id)).rpow_const
      (fun _ => Or.inr hp2)
  have hint : IntegrableOn (fun w : Space n => modelRealCost L w ^ (p / 2))
      (Metric.ball z r) μ :=
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall z r)).mono_set
      Metric.ball_subset_closedBall
  rw [cfit_fitPow_eq_lintegral_modelCost]
  have hpt : ∀ w, modelCost L w ^ (p / 2) = ENNReal.ofReal (modelRealCost L w ^ (p / 2)) :=
    fun w => by
      rw [modelCost_eq_ofReal, ENNReal.ofReal_rpow_of_nonneg (modelRealCost_nonneg L w) hp2]
  simp only [hpt]
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (modelRealCost_nonneg L w) _)).symm

/-- **Continuity in the model** of the `p`-fitting integral on a bounded ball (`p ≥ 0`), through
the ambient parameter spaces as in `continuous_fit`. -/
theorem cfit_continuous_fitPow (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    {p : ℝ} (hp : 0 ≤ p) (z : Space n) (r : ℝ) :
    Continuous (fun L : Models n k T => fitPow μ p L z r) := by
  have hp2 : 0 ≤ p / 2 := by linarith
  have hHc : Continuous (Function.uncurry
      (fun (q : HorizontalParameters n) (w : Space n) => horizontalParameterCost q w ^ (p / 2))) :=
    (continuous_horizontalParameterCost n).rpow_const (fun _ => Or.inr hp2)
  have hVc : Continuous (Function.uncurry
      (fun (q : SpatialParameters n) (w : Space n) => spatialParameterCost q w ^ (p / 2))) :=
    (continuous_spatialParameterCost n).rpow_const (fun _ => Or.inr hp2)
  have hH := continuous_parameter_ballIntegral μ hHc z r
  have hV := continuous_parameter_ballIntegral μ hVc z r
  have hHm := hH.comp (HorizontalModel.continuous_parameters (n := n) (k := k))
  have hVm := hV.comp (VerticalModel.continuous_parameters (n := n) (k := k))
  have hi : Continuous (fun L : Models n k T =>
      ∫ w in Metric.ball z r, modelRealCost L w ^ (p / 2) ∂μ) := by
    cases T with
    | horizontal => exact hHm
    | vertical => exact hVm
    | mixed =>
      apply (hHm.sumElim hVm).congr
      intro L
      cases L <;> rfl
  simp only [cfit_fitPow_eq_ofReal_integral μ hp]
  exact ENNReal.continuous_ofReal.comp hi

/-- **Countable fitting**: the infimum over the dense `modelSequence` is the full infimum, for
every finite-on-compacts source, `p ≥ 0`, centre and radius. -/
theorem cfit_iInf_fitPow_modelSequence [Nonempty (Models n k T)] (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] {p : ℝ} (hp : 0 ≤ p) (z : Space n) (r : ℝ) :
    (⨅ Q : Models n k T, fitPow μ p Q z r) =
      ⨅ j : ℕ, fitPow μ p (modelSequence n k T j) z r := by
  have h := (denseRange_modelSequence n k T).ciInf' (cfit_continuous_fitPow μ hp z r)
  simpa only [iInf_subtype, iInf_range] using h.symm

/-- Joint Borel measurability of one model's `p`-fitting integral in the centre and radius. -/
theorem cfit_measurable_fitPow (μ : Measure (Space n)) [SFinite μ] (p : ℝ) (L : Models n k T) :
    Measurable (fun x : Space n × ℝ => fitPow μ p L x.1 x.2) := by
  classical
  have hm : Measurable (fun w : Space n => Metric.infEDist w (modelSet L) ^ p) :=
    Metric.continuous_infEDist.measurable.pow_const p
  have hint : Measurable (Function.uncurry (fun (x : Space n × ℝ) (w : Space n) =>
      (Metric.ball x.1 x.2).indicator (fun w => Metric.infEDist w (modelSet L) ^ p) w)) := by
    change Measurable (fun q : (Space n × ℝ) × Space n =>
      if dist q.2 q.1.1 < q.1.2 then Metric.infEDist q.2 (modelSet L) ^ p else 0)
    exact Measurable.ite
      (measurableSet_lt (measurable_snd.dist measurable_fst.fst) measurable_fst.snd)
      (hm.comp measurable_snd) measurable_const
  have h := hint.lintegral_prod_right (ν := μ)
  simpa only [fitPow, lintegral_indicator measurableSet_ball] using h

/-- Joint Borel measurability of the fitting infimum (countability through `modelSequence`; an
unavailable family gives the constant `⊤`). -/
theorem cfit_measurable_iInf_fitPow (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    {p : ℝ} (hp : 0 ≤ p) :
    Measurable (fun x : Space n × ℝ => ⨅ L : Models n k T, fitPow μ p L x.1 x.2) := by
  have : SigmaFinite μ := source_sigmaFinite μ
  cases isEmpty_or_nonempty (Models n k T) with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    simp only [cfit_iInf_fitPow_modelSequence μ hp]
    exact Measurable.iInf fun j => cfit_measurable_fitPow μ p (modelSequence n k T j)

/-- Joint Borel measurability of `(z,r) ↦ B_p(z,r)` for a finite-on-compacts source, `p ≥ 0`
(every family). -/
theorem cfit_measurable_betaPow (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (k : ℕ) (T : FamilyKind) {p : ℝ} (hp : 0 ≤ p) :
    Measurable (fun x : Space n × ℝ => betaPow μ k T p x.1 x.2) := by
  unfold betaPow
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    ((measurable_snd.ennreal_ofReal.inv.pow_const ((k : ℝ) + p)).mul
      (cfit_measurable_iInf_fitPow (k := k) (T := T) μ hp))
    measurable_const

/-- **Attainment on a bounded testing ball**: for an available family, a finite-on-compacts
source and `p ≥ 0`, some model minimizes `L ↦ fitPow μ p L z r` (no nonzero-mass hypothesis). -/
theorem cfit_exists_fitPow_minimizer (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (hT : Nonempty (Models n k T)) {p : ℝ} (hp : 0 ≤ p) (z : Space n) (r : ℝ) :
    ∃ L : Models n k T, fitPow μ p L z r = ⨅ Q : Models n k T, fitPow μ p Q z r := by
  obtain ⟨R, hR, -, hbounds⟩ := compact_carrier_bounds (isCompact_closedBall z r)
  obtain ⟨L, -, hmin⟩ := (isCompact_boundedModels n k T R (R ^ 2)).exists_isMinOn
    (boundedModels_nonempty hT R (R ^ 2) hR.le (sq_nonneg R))
    (cfit_continuous_fitPow μ hp z r).continuousOn
  refine ⟨L, le_antisymm (le_iInf fun Q => ?_) (iInf_le _ L)⟩
  have hQ' := clampModel_mem_bounded Q R (R ^ 2) hR.le (sq_nonneg R)
  calc fitPow μ p L z r ≤ fitPow μ p (clampModel Q R (R ^ 2) (sq_nonneg R)) z r :=
        isMinOn_iff.mp hmin _ hQ'
    _ ≤ fitPow μ p Q z r := by
      rw [cfit_fitPow_eq_lintegral_modelCost, cfit_fitPow_eq_lintegral_modelCost]
      refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
      have hb := hbounds w (Metric.ball_subset_closedBall hw)
      exact ENNReal.rpow_le_rpow
        (modelCost_clampModel_le Q R (R ^ 2) hR.le (sq_nonneg R) w hb.1 hb.2) (by linarith)

/-- A vanishing `p`-fit (`p > 0`) of one model on a ball forces its quadratic fit to vanish:
`d_P(·,L) = 0` holds `μ`-a.e. on the ball. -/
theorem cfit_fit_eq_zero_of_fitPow_eq_zero {μ : Measure (Space n)} {p : ℝ} (hp : 0 < p)
    {L : Models n k T} {z : Space n} {r : ℝ} (h : fitPow μ p L z r = 0) :
    fit μ L z r = 0 := by
  rw [cfit_fitPow_eq_lintegral_modelCost] at h
  have hm : Measurable (fun w : Space n => modelCost L w ^ (p / 2)) :=
    (measurable_modelCost L).pow_const _
  have hae := (lintegral_eq_zero_iff hm).mp h
  unfold fit
  refine (lintegral_eq_zero_iff (measurable_modelCost L)).mpr ?_
  filter_upwards [hae] with w hw
  have hw' : modelCost L w ^ (p / 2) = 0 := hw
  rcases ENNReal.rpow_eq_zero_iff.mp hw' with h0 | h0
  · exact h0.1
  · exact absurd h0.2 (not_lt.mpr (by linarith))

end ParabolicRectifiability.BetaP
