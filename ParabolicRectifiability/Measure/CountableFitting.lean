import ParabolicRectifiability.Geometry.ModelSpace
import ParabolicRectifiability.Metric.ProperSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.IsLUB

/-! # A measure-independent countable fitting family

Defines the unnormalized fitting integral `fit μ L z r = ∫_{ball z r} dist(w, L)² dμ(w)`,
proves that it is continuous in the model parameter, and fixes one dense sequence of models
`modelSequence` such that the infimum over all models equals the infimum along the
sequence, for every source
finite on compact sets and every positive-radius ball (`exists_countable_fitting_family`). -/
noncomputable section
open MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal
namespace ParabolicRectifiability

/-- Unnormalized integral of the already squared geometric distance. -/
def fit {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n)) (L : Models n k T)
    (z : Space n) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in Metric.ball z r, modelCost L w ∂μ

theorem measure_closedBall_lt_top {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] (z : Space n) (r : ℝ) :
    μ (Metric.closedBall z r) < ⊤ := (isCompact_closedBall z r).measure_lt_top

theorem measure_ball_lt_top {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] (z : Space n) (r : ℝ) :
    μ (Metric.ball z r) < ⊤ :=
  (measure_mono Metric.ball_subset_closedBall).trans_lt (measure_closedBall_lt_top μ z r)

theorem integrableOn_modelRealCost {n k : ℕ} {T : FamilyKind}
    (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ] (L : Models n k T)
    (z : Space n) (r : ℝ) : IntegrableOn (modelRealCost L) (Metric.ball z r) μ := by
  have hc : Continuous (modelRealCost L) :=
    continuous_modelRealCost.comp (continuous_const.prodMk continuous_id)
  exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall z r)).mono_set
    Metric.ball_subset_closedBall

theorem fit_eq_ofReal_integral {n k : ℕ} {T : FamilyKind}
    (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ] (L : Models n k T)
    (z : Space n) (r : ℝ) :
    fit μ L z r = ENNReal.ofReal (∫ w in Metric.ball z r, modelRealCost L w ∂μ) := by
  simp only [fit, modelCost_eq_ofReal]
  exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_modelRealCost μ L z r)
    (Filter.Eventually.of_forall (modelRealCost_nonneg L))).symm

theorem fit_ne_top {n k : ℕ} {T : FamilyKind}
    (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ] (L : Models n k T)
    (z : Space n) (r : ℝ) : fit μ L z r ≠ ⊤ := by
  rw [fit_eq_ofReal_integral]
  exact ENNReal.ofReal_ne_top

/-- Ambient parameters have locally dominated integrals on each bounded ball.
The domination is local in parameter space, allowing arbitrarily distant anchors. -/
theorem continuous_parameter_ballIntegral {n : ℕ} {X : Type*}
    [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    {f : X → Space n → ℝ} (hf : Continuous (Function.uncurry f))
    (z : Space n) (r : ℝ) :
    Continuous (fun p => ∫ w in Metric.ball z r, f p w ∂μ) := by
  let ν := μ.restrict (Metric.ball z r)
  have : IsFiniteMeasure ν := ⟨by
    simpa [ν] using measure_ball_lt_top μ z r⟩
  have h := continuous_parametric_integral_of_continuous (μ := ν) hf
    (isCompact_closedBall z r)
  have he : ν.restrict (Metric.closedBall z r) = ν := by
    dsimp [ν]
    rw [Measure.restrict_restrict measurableSet_closedBall,
      inter_eq_right.mpr Metric.ball_subset_closedBall]
  simpa only [he] using h

theorem continuous_fit {n k : ℕ} {T : FamilyKind}
    (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (z : Space n) (r : ℝ) : Continuous (fun L : Models n k T => fit μ L z r) := by
  have hH := continuous_parameter_ballIntegral μ (continuous_horizontalParameterCost n) z r
  have hV := continuous_parameter_ballIntegral μ (continuous_spatialParameterCost n) z r
  have hHm := hH.comp (HorizontalModel.continuous_parameters (n := n) (k := k))
  have hVm := hV.comp (VerticalModel.continuous_parameters (n := n) (k := k))
  have hi : Continuous (fun L : Models n k T =>
      ∫ w in Metric.ball z r, modelRealCost L w ∂μ) := by
    cases T with
    | horizontal => exact hHm
    | vertical => exact hVm
    | mixed =>
      apply (hHm.sumElim hVm).congr
      intro L
      cases L <;> rfl
  simp only [fit_eq_ofReal_integral]
  exact ENNReal.continuous_ofReal.comp hi

/-- A genuine dense sequence of models, chosen without a measure or ball. -/
def modelSequence (n k : ℕ) (T : FamilyKind) [Nonempty (Models n k T)] : ℕ → Models n k T :=
  denseSeq (Models n k T)

theorem denseRange_modelSequence (n k : ℕ) (T : FamilyKind) [Nonempty (Models n k T)] :
    DenseRange (modelSequence n k T) := denseRange_denseSeq _

theorem iInf_fit_modelSequence {n k : ℕ} {T : FamilyKind} [Nonempty (Models n k T)]
    (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ] (z : Space n) (r : ℝ) :
    (⨅ Q : Models n k T, fit μ Q z r) = ⨅ j : ℕ, fit μ (modelSequence n k T j) z r := by
  have h := (denseRange_modelSequence n k T).ciInf' (continuous_fit μ z r)
  simpa only [iInf_subtype, iInf_range] using h.symm

/-- One sequence serves every finite-on-compacts source and every positive-radius ball. -/
theorem exists_countable_fitting_family (n k : ℕ) (T : FamilyKind)
    (h : Nonempty (Models n k T)) :
    ∃ L : ℕ → Models n k T,
      ∀ (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ],
      ∀ (z : Space n) (r : ℝ), 0 < r →
      (⨅ Q : Models n k T, fit μ Q z r) = ⨅ j : ℕ, fit μ (L j) z r := by
  let := h
  exact ⟨modelSequence n k T, fun μ _ z r _ => iInf_fit_modelSequence μ z r⟩

@[simp] theorem fit_zero {n k : ℕ} {T : FamilyKind} (L : Models n k T)
    (z : Space n) (r : ℝ) : fit (0 : Measure (Space n)) L z r = 0 := by simp [fit]

theorem iInf_fit_of_isEmpty {n k : ℕ} {T : FamilyKind} [IsEmpty (Models n k T)]
    (μ : Measure (Space n)) (z : Space n) (r : ℝ) :
    (⨅ Q : Models n k T, fit μ Q z r) = ⊤ := by simp

@[simp] theorem iInf_fit_zero_of_nonempty {n k : ℕ} {T : FamilyKind}
    [Nonempty (Models n k T)] (z : Space n) (r : ℝ) :
    (⨅ Q : Models n k T, fit (0 : Measure (Space n)) Q z r) = 0 := by simp

end ParabolicRectifiability
