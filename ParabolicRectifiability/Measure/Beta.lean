import ParabolicRectifiability.Measure.CountableFitting
import Mathlib.MeasureTheory.Measure.Prod

/-! # Natural squared beta: joint measurability and the finite-radius bound

The fitting infimum is reduced to a countable infimum using the measure-independent
dense sequence of models `modelSequence`.
All functions take extended nonnegative values, with no normalization by mass.
-/
noncomputable section
open MeasureTheory Set Topology
open scoped ENNReal
namespace ParabolicRectifiability

/-- A compact exhaustion supplies finite spanning sets for a source finite on compact sets. -/
def sourceFiniteSpanningSets {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ] :
    μ.FiniteSpanningSetsIn {s | IsCompact s} where
  set := compactExhaustion n
  set_mem j := (compactExhaustion n).isCompact j
  finite j := ((compactExhaustion n).isCompact j).measure_lt_top
  spanning := (compactExhaustion n).iUnion_eq

theorem source_sigmaFinite {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ] :
    SigmaFinite μ := (sourceFiniteSpanningSets μ).sigmaFinite

theorem measurable_modelCost {n k : ℕ} {T : FamilyKind} (L : Models n k T) :
    Measurable (modelCost L) := by
  have hc : Continuous (modelRealCost L) :=
    continuous_modelRealCost.comp (continuous_const.prodMk continuous_id)
  change Measurable (fun z => modelCost L z)
  simp only [modelCost_eq_ofReal]
  exact hc.measurable.ennreal_ofReal

/-- The jointly measurable integrand for fitting on a moving ball. -/
def fittingIntegrand {n k : ℕ} {T : FamilyKind} (L : Models n k T)
    (p : Space n × ℝ) (w : Space n) : ℝ≥0∞ :=
  (Metric.ball p.1 p.2).indicator (modelCost L) w

theorem measurable_fittingIntegrand {n k : ℕ} {T : FamilyKind} (L : Models n k T) :
    Measurable (Function.uncurry (fittingIntegrand L)) := by
  classical
  change Measurable (fun p : (Space n × ℝ) × Space n =>
    if dist p.2 p.1.1 < p.1.2 then modelCost L p.2 else 0)
  exact Measurable.ite
    (measurableSet_lt (measurable_snd.dist measurable_fst.fst) measurable_fst.snd)
    ((measurable_modelCost L).comp measurable_snd) measurable_const

theorem measurable_fit {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n)) [SFinite μ]
    (L : Models n k T) : Measurable (fun p : Space n × ℝ => fit μ L p.1 p.2) := by
  have h := (measurable_fittingIntegrand L).lintegral_prod_right (ν := μ)
  simpa only [fit, fittingIntegrand, lintegral_indicator measurableSet_ball] using h

/-- Countability enters through the genuine sequence, not an uncountable measurable infimum. -/
theorem measurable_iInf_fit {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] :
    Measurable (fun p : Space n × ℝ => ⨅ L : Models n k T, fit μ L p.1 p.2) := by
  have : SigmaFinite μ := source_sigmaFinite μ
  cases isEmpty_or_nonempty (Models n k T) with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    simp only [iInf_fit_modelSequence]
    exact Measurable.iInf fun j => measurable_fit μ (modelSequence n k T j)

/-- Natural squared beta number: for `r > 0`, this is
`r^(-k-2) * inf_L ∫_{ball z r} dist(w,L)^2 dμ(w)`, valued in `ℝ≥0∞`.
There is no division by ball mass and the measure is the supplied source.
For `r ≤ 0` the value is zero. An unavailable family has value infinity at
every positive radius, including for the zero source; the zero-source law
therefore explicitly requires an available family. -/
def betaSq {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (z : Space n) (r : ℝ) : ℝ≥0∞ :=
  if 0 < r then (ENNReal.ofReal r)⁻¹ ^ (k + 2) * ⨅ L : Models n k T, fit μ L z r else 0

theorem betaSq_of_pos {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (z : Space n) {r : ℝ} (hr : 0 < r) :
    betaSq μ k T z r = (ENNReal.ofReal r)⁻¹ ^ (k + 2) * ⨅ L : Models n k T, fit μ L z r := by
  simp [betaSq, hr]

@[simp] theorem betaSq_of_nonpos {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (z : Space n) {r : ℝ} (hr : r ≤ 0) : betaSq μ k T z r = 0 := by
  simp [betaSq, not_lt.mpr hr]

/-- Joint measurability in center and radius for a source finite on compact
sets. The proof uses the countable fitting family and also covers unavailable
families through their empty infimum. -/
theorem measurable_betaSq {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (k : ℕ) (T : FamilyKind) : Measurable (fun p : Space n × ℝ => betaSq μ k T p.1 p.2) := by
  unfold betaSq
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    ((measurable_snd.ennreal_ofReal.inv.pow_const (k + 2)).mul (measurable_iInf_fit μ)) measurable_const

/-- A point on the actual represented model bounds the squared geometric distance. -/
theorem modelCost_le_edist_sq {n k : ℕ} {T : FamilyKind} (L : Models n k T)
    {z : Space n} (hz : z ∈ modelSet L) (w : Space n) : modelCost L w ≤ edist w z ^ 2 := by
  exact pow_le_pow_left' (Metric.infEDist_le_edist_of_mem hz) 2

theorem fit_le_radius_sq_mul_measure {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n))
    (L : Models n k T) {z : Space n} (hz : z ∈ modelSet L) (r : ℝ) :
    fit μ L z r ≤ ENNReal.ofReal r ^ 2 * μ (Metric.ball z r) := by
  calc
    fit μ L z r ≤ ∫⁻ _w in Metric.ball z r, ENNReal.ofReal r ^ 2 ∂μ :=
      setLIntegral_mono' measurableSet_ball fun w hw =>
        (modelCost_le_edist_sq L hz w).trans (pow_le_pow_left' (by
          rw [edist_dist]
          exact ENNReal.ofReal_le_ofReal (Metric.mem_ball.mp hw).le) 2)
    _ = _ := by simp

/-- Exact cancellation at a positive, finite radius. -/
theorem inv_radius_pow_mul_sq {r : ℝ} (hr : 0 < r) (k : ℕ) (a : ℝ≥0∞) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (ENNReal.ofReal r ^ 2 * a) =
      (ENNReal.ofReal r)⁻¹ ^ k * a := by
  have h0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  rw [pow_add]
  calc
    _ = (ENNReal.ofReal r)⁻¹ ^ k * (((ENNReal.ofReal r)⁻¹ * ENNReal.ofReal r) ^ 2 * a) := by
      rw [mul_pow]
      simp only [mul_assoc, mul_left_comm, mul_comm]
    _ = _ := by rw [ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top]; simp

theorem betaSq_le_radius_inv_pow_mul_measure {n : ℕ} (μ : Measure (Space n))
    (k : ℕ) (T : FamilyKind) [Nonempty (Models n k T)] (z : Space n)
    {r : ℝ} (hr : 0 < r) :
    betaSq μ k T z r ≤ (ENNReal.ofReal r)⁻¹ ^ k * μ (Metric.ball z r) := by
  obtain ⟨L, hz⟩ := exists_model_mem (inferInstance : Nonempty (Models n k T)) z
  rw [betaSq_of_pos μ k T z hr]
  calc
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ (k + 2) * fit μ L z r := by gcongr; exact iInf_le _ L
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (ENNReal.ofReal r ^ 2 * μ (Metric.ball z r)) :=
      by gcongr; exact fit_le_radius_sq_mul_measure μ L hz r
    _ = _ := inv_radius_pow_mul_sq hr k _

/-- Pointwise finiteness at every finite radius when the source is finite
on compact sets and the model family is available. This does not assert
finiteness of the scale integral defining `squareEnergy`. -/
theorem betaSq_lt_top {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (k : ℕ) (T : FamilyKind) [Nonempty (Models n k T)] (z : Space n) (r : ℝ) :
    betaSq μ k T z r < ⊤ := by
  by_cases hr : 0 < r
  · apply (betaSq_le_radius_inv_pow_mul_measure μ k T z hr).trans_lt
    apply lt_top_iff_ne_top.mpr
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr).ne'))
      (measure_ball_lt_top μ z r).ne
  · simp [betaSq, hr]

@[simp] theorem betaSq_zero {n : ℕ} (k : ℕ) (T : FamilyKind)
    [Nonempty (Models n k T)] (z : Space n) (r : ℝ) :
    betaSq (0 : Measure (Space n)) k T z r = 0 := by simp [betaSq]

theorem betaSq_of_isEmpty {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    [IsEmpty (Models n k T)] (z : Space n) {r : ℝ} (hr : 0 < r) :
    betaSq μ k T z r = ⊤ := by
  rw [betaSq_of_pos μ k T z hr, iInf_fit_of_isEmpty]
  exact ENNReal.mul_top (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top))

end ParabolicRectifiability
