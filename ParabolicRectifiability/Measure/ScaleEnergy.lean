import ParabolicRectifiability.Measure.Beta
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # The measure `dr/r`, measurable square energy, and the original-source threshold

Finite positive annuli, together with the null nonpositive half-line, give an
explicit sigma-finite exhaustion. Square energy remains ENNReal-valued.
-/
noncomputable section
open MeasureTheory Set Topology
open scoped ENNReal
namespace ParabolicRectifiability

/-- Lebesgue measure on positive radii with exactly the density `1/r`. -/
def scaleMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun r => ENNReal.ofReal (1 / r))

theorem measurable_scaleDensity : Measurable (fun r : ℝ => ENNReal.ofReal (1 / r)) :=
  (measurable_const.div measurable_id).ennreal_ofReal

theorem scaleMeasure_apply (s : Set ℝ) (hs : MeasurableSet s) :
    scaleMeasure s = ∫⁻ r in s ∩ Ioi 0, ENNReal.ofReal (1 / r) ∂volume := by
  rw [scaleMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs]

/-- An explicit finite bound on every annulus bounded away from zero. -/
theorem scaleMeasure_Icc_le {a b : ℝ} (ha : 0 < a) :
    scaleMeasure (Icc a b) ≤ ENNReal.ofReal (1 / a) * ENNReal.ofReal (b - a) := by
  rw [scaleMeasure_apply _ measurableSet_Icc,
    inter_eq_left.mpr (show Icc a b ⊆ Ioi 0 from fun _ hx => ha.trans_le hx.1)]
  calc
    _ ≤ ∫⁻ _r in Icc a b, ENNReal.ofReal (1 / a) ∂volume :=
      setLIntegral_mono' measurableSet_Icc fun r hr =>
        ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le ha hr.1)
    _ = _ := by simp [Real.volume_Icc]

theorem scaleMeasure_Icc_lt_top {a b : ℝ} (ha : 0 < a) :
    scaleMeasure (Icc a b) < ⊤ :=
  (scaleMeasure_Icc_le ha).trans_lt
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))

@[simp] theorem scaleMeasure_nonpositive : scaleMeasure (Iic 0) = 0 := by
  have he : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext r
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false]
    exact fun h => (not_lt_of_ge h.1) h.2
  rw [scaleMeasure_apply _ measurableSet_Iic, he]
  simp

@[simp] theorem scaleMeasure_compl_positive : scaleMeasure (Ioi 0)ᶜ = 0 := by
  simpa only [compl_Ioi] using scaleMeasure_nonpositive

instance instNullSingletonClassScaleMeasure : NullSingletonClass scaleMeasure := by
  unfold scaleMeasure
  infer_instance

@[simp] theorem scaleMeasure_singleton (r : ℝ) : scaleMeasure {r} = 0 := measure_singleton r

/-- A concrete collection of finite positive annuli. -/
def scaleAnnulus (j : ℕ) : Set ℝ := Icc (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1)

theorem measurableSet_scaleAnnulus (j : ℕ) : MeasurableSet (scaleAnnulus j) := measurableSet_Icc

theorem scaleAnnulus_measure_lt_top (j : ℕ) : scaleMeasure (scaleAnnulus j) < ⊤ :=
  scaleMeasure_Icc_lt_top (one_div_pos.mpr (by positivity))

theorem exists_mem_scaleAnnulus {r : ℝ} (hr : 0 < r) : ∃ j : ℕ, r ∈ scaleAnnulus j := by
  obtain ⟨j, hj⟩ := exists_nat_gt (max r (1 / r))
  have hu : r ≤ (j : ℝ) + 1 := by have := le_max_left r (1 / r); linarith
  have hv : 1 / r ≤ (j : ℝ) + 1 := by have := le_max_right r (1 / r); linarith
  refine ⟨j, ?_, hu⟩
  rw [div_le_iff₀ (show 0 < (j : ℝ) + 1 by positivity)]
  simpa only [mul_comm] using (div_le_iff₀ hr).mp hv

/-- The null nonpositive half-line and these annuli cover the entire real axis. -/
def scaleFiniteSpanningSets : scaleMeasure.FiniteSpanningSetsIn {s | MeasurableSet s} where
  set j := Iic 0 ∪ scaleAnnulus j
  set_mem j := measurableSet_Iic.union (measurableSet_scaleAnnulus j)
  finite j := (measure_union_le _ _).trans_lt (by
    rw [scaleMeasure_nonpositive, zero_add]
    exact scaleAnnulus_measure_lt_top j)
  spanning := by
    apply eq_univ_of_forall
    intro r
    by_cases hr : 0 < r
    · obtain ⟨j, hj⟩ := exists_mem_scaleAnnulus hr
      exact mem_iUnion.mpr ⟨j, Or.inr hj⟩
    · exact mem_iUnion.mpr ⟨0, Or.inl (le_of_not_gt hr)⟩

instance instSigmaFiniteScaleMeasure : SigmaFinite scaleMeasure := scaleFiniteSpanningSets.sigmaFinite

/-- The normalization is precisely integration against `dr/r` on positive radii. -/
theorem lintegral_scaleMeasure (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ r, g r ∂scaleMeasure =
      ∫⁻ r in Ioi 0, ENNReal.ofReal (1 / r) * g r ∂volume :=
  lintegral_withDensity_eq_lintegral_mul _ measurable_scaleDensity hg

/-- The extended nonnegative scale integral of `betaSq` against `dr/r`
on `0 < r < R`. The integrand is already squared; no second square or
mass normalization is applied. The result can be infinite, and is zero
when `R ≤ 0`. Its source is exactly the supplied `μ`. -/
def squareEnergy {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (R : ℝ) (z : Space n) : ℝ≥0∞ :=
  ∫⁻ r in Ioo 0 R, betaSq μ k T z r ∂scaleMeasure

@[simp] theorem squareEnergy_of_nonpos {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) {R : ℝ} (hR : R ≤ 0) (z : Space n) : squareEnergy μ k T R z = 0 := by
  simp [squareEnergy, Ioo_eq_empty_of_le hR]

theorem measurable_squareEnergy {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (k : ℕ) (T : FamilyKind) (R : ℝ) : Measurable (squareEnergy μ k T R) :=
  (measurable_betaSq μ k T).lintegral_prod_right (ν := scaleMeasure.restrict (Ioo 0 R))

/-- Points in the open unit parabolic ball where the mixed-family energy
of the original source, integrated over `0 < r < 2`, exceeds `ofReal M`.
The main theorem uses `M ≥ 0` and bounds this set in the original measure. -/
def exceptionalSet {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (M : ℝ) : Set (Space n) :=
  Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < squareEnergy μ k .mixed 2 z}

theorem measurableSet_exceptionalSet {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] (k : ℕ) (M : ℝ) : MeasurableSet (exceptionalSet μ k M) :=
  measurableSet_ball.inter (measurableSet_lt measurable_const (measurable_squareEnergy μ k .mixed 2))

theorem exceptionalSet_measure_lt_top {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] (k : ℕ) (M : ℝ) : μ (exceptionalSet μ k M) < ⊤ :=
  (measure_mono inter_subset_left).trans_lt (measure_ball_lt_top μ (point 0 0) 1)

/-- The original measure restricted to `exceptionalSet μ k M`. The set
is defined using energy of `μ`, before restriction; this definition does
not recompute beta or energy using the exceptional measure. -/
def exceptionalSource {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (M : ℝ) : Measure (Space n) :=
  μ.restrict (exceptionalSet μ k M)

instance instIsFiniteMeasureExceptionalSource {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] (k : ℕ) (M : ℝ) : IsFiniteMeasure (exceptionalSource μ k M) :=
  isFiniteMeasure_restrict.mpr (exceptionalSet_measure_lt_top μ k M).ne

theorem exceptionalSource_apply {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (M : ℝ)
    (s : Set (Space n)) (hs : MeasurableSet s) :
    exceptionalSource μ k M s = μ (s ∩ exceptionalSet μ k M) := Measure.restrict_apply hs

end ParabolicRectifiability
