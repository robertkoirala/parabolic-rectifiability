import ParabolicRectifiability.Geometry.ModelSimilarity
import ParabolicRectifiability.Measure.ScaleEnergy
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! # Restriction, similarity and mass laws for natural squared beta

The order and finite-scalar identities work for arbitrary Borel source measures.
Local finiteness is needed only to retain that property after rescaling.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability

theorem fit_mono_measure {n k : ℕ} {T : FamilyKind} {ν μ : Measure (Space n)} (h : ν ≤ μ)
    (L : Models n k T) (z : Space n) (r : ℝ) : fit ν L z r ≤ fit μ L z r :=
  lintegral_mono' (Measure.restrict_mono_measure h _) le_rfl

theorem fit_mono_ball {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n)) (L : Models n k T)
    {z y : Space n} {r s : ℝ} (h : Metric.ball z r ⊆ Metric.ball y s) :
    fit μ L z r ≤ fit μ L y s := lintegral_mono_set h

theorem betaSq_mono_measure {n : ℕ} {ν μ : Measure (Space n)} (h : ν ≤ μ)
    (k : ℕ) (T : FamilyKind) (z : Space n) (r : ℝ) : betaSq ν k T z r ≤ betaSq μ k T z r := by
  by_cases hr : 0 < r
  · simp only [betaSq_of_pos _ _ _ _ hr]
    gcongr
    exact fit_mono_measure h _ z r
  · simp [betaSq, hr]

/-- Radius normalization cancels only finite nonzero radius factors, never the fit. -/
theorem radius_ratio_normalization {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (p : ℕ) (I : ℝ≥0∞) :
    ENNReal.ofReal (s / r) ^ p * ((ENNReal.ofReal s)⁻¹ ^ p * I) =
      (ENNReal.ofReal r)⁻¹ ^ p * I := by
  rw [ENNReal.ofReal_div_of_pos hr, div_eq_mul_inv, mul_pow]
  calc
    _ = (ENNReal.ofReal r)⁻¹ ^ p *
      ((ENNReal.ofReal s * (ENNReal.ofReal s)⁻¹) ^ p * I) := by
        rw [mul_pow]
        simp only [mul_assoc, mul_left_comm, mul_comm]
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top]
      simp

theorem betaSq_le_of_ball_subset {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    {z y : Space n} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h : Metric.ball z r ⊆ Metric.ball y s) :
    betaSq μ k T z r ≤ ENNReal.ofReal (s / r) ^ (k + 2) * betaSq μ k T y s := by
  rw [betaSq_of_pos _ _ _ _ hr, betaSq_of_pos _ _ _ _ hs, radius_ratio_normalization hr hs]
  gcongr
  exact fit_mono_ball μ _ h

theorem squareEnergy_mono_measure {n : ℕ} {ν μ : Measure (Space n)} (h : ν ≤ μ)
    (k : ℕ) (T : FamilyKind) (R : ℝ) (z : Space n) :
    squareEnergy ν k T R z ≤ squareEnergy μ k T R z :=
  lintegral_mono fun r => betaSq_mono_measure h k T z r

theorem betaSq_restrict_le {n : ℕ} (μ : Measure (Space n)) (E : Set (Space n))
    (k : ℕ) (T : FamilyKind) (z : Space n) (r : ℝ) :
    betaSq (μ.restrict E) k T z r ≤ betaSq μ k T z r :=
  betaSq_mono_measure Measure.restrict_le_self k T z r

theorem squareEnergy_restrict_le {n : ℕ} (μ : Measure (Space n)) (E : Set (Space n))
    (k : ℕ) (T : FamilyKind) (R : ℝ) (z : Space n) :
    squareEnergy (μ.restrict E) k T R z ≤ squareEnergy μ k T R z :=
  squareEnergy_mono_measure Measure.restrict_le_self k T R z

theorem lintegral_squareEnergy_restrict_le {n : ℕ} (μ : Measure (Space n))
    (E : Set (Space n)) (k : ℕ) (T : FamilyKind) (R : ℝ) :
    (∫⁻ z, squareEnergy (μ.restrict E) k T R z ∂(μ.restrict E)) ≤
      ∫⁻ z, squareEnergy μ k T R z ∂μ :=
  lintegral_mono' Measure.restrict_le_self (squareEnergy_restrict_le μ E k T R)

theorem fit_smul {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n)) (c : ℝ≥0∞)
    (L : Models n k T) (z : Space n) (r : ℝ) :
    fit (c • μ) L z r = c * fit μ L z r := setLIntegral_smul_measure c _ _

/-- Availability is essential when the finite scalar is zero. -/
theorem betaSq_smul {n : ℕ} (μ : Measure (Space n)) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (k : ℕ) (T : FamilyKind) [Nonempty (Models n k T)] (z : Space n) (r : ℝ) :
    betaSq (c • μ) k T z r = c * betaSq μ k T z r := by
  by_cases hr : 0 < r
  · simp only [betaSq_of_pos _ _ _ _ hr, fit_smul]
    rw [← ENNReal.mul_iInf (fun h => (hc h).elim)]
    ac_rfl
  · simp [betaSq, hr]

theorem squareEnergy_smul {n : ℕ} (μ : Measure (Space n)) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (k : ℕ) (T : FamilyKind) [Nonempty (Models n k T)] (R : ℝ) (z : Space n) :
    squareEnergy (c • μ) k T R z = c * squareEnergy μ k T R z := by
  simp only [squareEnergy, betaSq_smul μ c hc]
  exact lintegral_const_mul' c _ hc

theorem lintegral_squareEnergy_smul {n : ℕ} (μ : Measure (Space n)) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (k : ℕ) (T : FamilyKind) [Nonempty (Models n k T)] (R : ℝ) :
    (∫⁻ z, squareEnergy (c • μ) k T R z ∂(c • μ)) =
      c ^ 2 * ∫⁻ z, squareEnergy μ k T R z ∂μ := by
  simp only [squareEnergy_smul μ c hc, lintegral_smul_measure,
    lintegral_const_mul' c _ hc, smul_eq_mul, pow_two, mul_assoc]

/-- The original source rescaled by its model dimension k, not ambient dimension. -/
def rescaledSource {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (q : Space n) (a : ℝ) (ha : 0 < a) : Measure (Space n) :=
  (ENNReal.ofReal a)⁻¹ ^ k • μ.map (similarity q a ha)

instance instIsFiniteMeasureOnCompactsRescaledSource {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] (k : ℕ) (q : Space n) (a : ℝ) (ha : 0 < a) :
    IsFiniteMeasureOnCompacts (rescaledSource μ k q a ha) := by
  let : IsFiniteMeasureOnCompacts (μ.map (similarity q a ha)) :=
    Measure.IsFiniteMeasureOnCompacts.map μ (similarity q a ha)
  exact IsFiniteMeasureOnCompacts.smul _
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr ha).ne'))

/-- The fixed-model pushforward identity precedes the model infimum. -/
theorem fit_rescaledSource {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n))
    (q : Space n) (a : ℝ) (ha : 0 < a) (L : Models n k T) (z : Space n) (s : ℝ) :
    fit (rescaledSource μ k q a ha) (modelSimilarity T q a ha L) (similarity q a ha z) s =
      (ENNReal.ofReal a)⁻¹ ^ (k + 2) * fit μ L z (a * s) := by
  rw [rescaledSource, fit_smul]
  unfold fit
  rw [setLIntegral_map measurableSet_ball (measurable_modelCost _) (similarity q a ha).measurable,
    preimage_similarity_ball]
  simp only [modelCost_modelSimilarity]
  rw [lintegral_const_mul' _ _
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr ha).ne'))]
  rw [pow_add, mul_assoc]

theorem betaSq_rescaledSource {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (q : Space n) (a : ℝ) (ha : 0 < a) (z : Space n) {s : ℝ} (hs : 0 < s) :
    betaSq (rescaledSource μ k q a ha) k T (similarity q a ha z) s =
      betaSq μ k T z (a * s) := by
  rw [betaSq_of_pos _ _ _ _ hs, betaSq_of_pos _ _ _ _ (mul_pos ha hs)]
  rw [← (modelSimilarity T q a ha).iInf_comp]
  simp only [fit_rescaledSource]
  rw [← ENNReal.mul_iInf_of_ne
    (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top))
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr ha).ne'))]
  rw [ENNReal.ofReal_mul ha.le,
    ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr ha).ne') (Or.inl ENNReal.ofReal_ne_top), mul_pow]
  ac_rfl

end ParabolicRectifiability
