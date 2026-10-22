import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Statements
import ParabolicRectifiability.Measure.ScaleIntegrals

/-! The atomic square-energy estimate uses a fixed model through the centre.
The explicit measurable majorant permits arbitrary nonnegative atomic weights. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Examples

private def atomScaleBound (k : ℕ) (d w r : ℝ) : ℝ≥0∞ :=
  (Ioi d).indicator (fun r => ENNReal.ofReal (w * d ^ 2) *
    (ENNReal.ofReal r)⁻¹ ^ (k + 2)) r

private theorem measurable_atomScaleBound (k : ℕ) (d w : ℝ) :
    Measurable (atomScaleBound k d w) :=
  (measurable_const.mul (measurable_inv_pow_ofReal (k + 2))).indicator measurableSet_Ioi

private theorem integral_atomScaleBound (k : ℕ) {d w : ℝ} (hd : 0 ≤ d) (hw : 0 ≤ w) :
    (∫⁻ r in Ioo 0 2, atomScaleBound k d w r ∂scaleMeasure) ≤
      ENNReal.ofReal (1 / ((k : ℝ) + 2)) * ENNReal.ofReal (w * (d ^ k)⁻¹) := by
  by_cases hd0 : d = 0
  · simp [atomScaleBound, hd0]
  have hdp : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  have hset : Ioi d ∩ Ioo 0 (2 : ℝ) = Ioo d 2 := by
    ext r
    simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hdp.trans h.1, h.2⟩⟩
  simp only [atomScaleBound]
  rw [lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, hset,
    lintegral_const_mul _ (measurable_inv_pow_ofReal (k + 2))]
  by_cases hd2 : d ≤ 2
  · rw [lintegral_inv_pow_Ioo_scaleMeasure (k + 2) (by omega) hdp hd2]
    have hden : 0 < (k : ℝ) + 2 := by positivity
    calc
      _ ≤ ENNReal.ofReal (w * d ^ 2) *
          ENNReal.ofReal ((d ^ (k + 2))⁻¹ / ((k + 2 : ℕ) : ℝ)) := by
        apply mul_le_mul_right
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact sub_le_self _ (by positivity)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hw (sq_nonneg _)),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        rw [pow_add]
        field_simp
  · rw [Ioo_eq_empty_of_le (le_of_not_ge hd2)]
    simp

/-- A model through the centre controls each atom by its squared distance. -/
private theorem betaSq_atomic_le {n k : ℕ} (z : ℕ → Space n) (w : ℕ → ℝ)
    (hw : ∀ j, 0 ≤ w j) (x : Space n) (L : Models n k .mixed)
    (hx : x ∈ modelSet L) {r : ℝ} (hr : 0 < r) :
    betaSq (Measure.sum fun j => ENNReal.ofReal (w j) • Measure.dirac (z j)) k .mixed x r ≤
      ∑' j, atomScaleBound k (dist x (z j)) (w j) r := by
  classical
  rw [betaSq_of_pos _ _ _ _ hr]
  calc
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
        fit (Measure.sum fun j => ENNReal.ofReal (w j) • Measure.dirac (z j)) L x r := by
      gcongr
      exact iInf_le _ L
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
        ∫⁻ y in Metric.ball x r, edist y x ^ 2
          ∂(Measure.sum fun j => ENNReal.ofReal (w j) • Measure.dirac (z j)) := by
      gcongr
      exact lintegral_mono (fun y => modelCost_le_edist_sq L hx y)
    _ = _ := by
      rw [← lintegral_indicator measurableSet_ball, lintegral_sum_measure,
        ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro j
      rw [lintegral_smul_measure, lintegral_dirac]
      by_cases hj : dist x (z j) < r
      · simp only [atomScaleBound, mem_Ioi, hj, indicator_of_mem,
          Metric.mem_ball, dist_comm (z j) x,
          edist_dist, smul_eq_mul]
        rw [← ENNReal.ofReal_pow dist_nonneg,
          ← ENNReal.ofReal_mul (hw j)]
        ac_rfl
      · have hj' : z j ∉ Metric.ball x r := by simpa [Metric.mem_ball, dist_comm] using hj
        simp [atomScaleBound, hj, hj']

/-- The atomic square bound at every centre, without a local finiteness assumption. -/
theorem e2_atomic_squareBound_proof : E2AtomicSquareBoundStatement := by
  intro n k hn hk hkn z w hw x
  obtain ⟨L, hx⟩ := exists_model_mem (T := .mixed)
    (AdmissibleModel.nonempty_of_range hn hk hkn.le) x
  calc
    _ ≤ ∫⁻ r in Ioo 0 2, ∑' j, atomScaleBound k (dist x (z j)) (w j) r ∂scaleMeasure := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro r hr
      exact betaSq_atomic_le z w hw x L hx hr.1
    _ = ∑' j, ∫⁻ r in Ioo 0 2, atomScaleBound k (dist x (z j)) (w j) r ∂scaleMeasure :=
      lintegral_tsum (fun j => (measurable_atomScaleBound k _ _).aemeasurable)
    _ ≤ ∑' j, ENNReal.ofReal (1 / ((k : ℝ) + 2)) *
        ENNReal.ofReal (w j * (dist x (z j) ^ k)⁻¹) :=
      ENNReal.tsum_le_tsum (fun j => integral_atomScaleBound k dist_nonneg (hw j))
    _ = _ := ENNReal.tsum_mul_left

end ParabolicRectifiability.Examples
