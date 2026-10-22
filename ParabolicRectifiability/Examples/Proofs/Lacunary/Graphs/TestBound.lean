import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements

/-! # Single-scale upper bound for the lacunary graph

A vertical line through the centre is an admissible model at dimension two. The
ball pullback and modulus bound control its fitting integral by the length of a
time interval times a constant. This uses extended integrals, so the parameter
set need not be measurable and the positive exponent need not be at least one.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- Cancellation of the radius in the single-scale fitting estimate. -/
private theorem e2_testBound_normalization {ε r S q : ℝ}
    (hε : 0 ≤ ε) (hr : 0 < r) (hS : 0 ≤ S) (hq : 0 ≤ q) :
    (ENNReal.ofReal r)⁻¹ ^ ((2 : ℝ) + q) *
        ((ENNReal.ofReal (2 * ε * r * S)) ^ q * ENNReal.ofReal (2 * r ^ 2)) =
      ENNReal.ofReal (2 ^ (q + 1) * ε ^ q * S ^ q) := by
  have hc : 0 ≤ 2 * ε * r * S := by positivity
  rw [← ENNReal.ofReal_inv_of_pos hr,
    ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hr.le) (by positivity),
    ENNReal.ofReal_rpow_of_nonneg hc hq,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc q),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hr.le) _)]
  congr 1
  rw [Real.inv_rpow hr.le, Real.rpow_add hr, Real.rpow_two,
    Real.mul_rpow (by positivity : 0 ≤ 2 * ε * r) hS,
    Real.mul_rpow (by positivity : 0 ≤ 2 * ε) hr.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε,
    Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
  have hrq : r ^ q ≠ 0 := (Real.rpow_pos_of_pos hr q).ne'
  field_simp

/-- Test the genuine beta infimum with the vertical line through the centre. -/
theorem e2_lacunary_testBound_proof :
    E2BallPullbackStatement → E2KernelBoundStatement → E2TestBoundStatement := by
  intro hball hkernel ε a N hε hε' hd E t r q hr hq
  let S := e2_lacunaryKernelSum a N r
  have hS : 0 ≤ S := by
    apply tsum_nonneg
    intro j
    apply mul_nonneg (hd.amplitude_pos j).le
    exact le_min (div_nonneg hr.le (inv_nonneg.mpr (Real.sqrt_nonneg _)))
      (div_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hr.le)
  let L : Models 1 2 .mixed := Sum.inr
    ⟨0, by decide, rfl,
      AffineSpatialPlane.singleton (EuclideanSpace.single 0 (lacunaryFunction ε a N t))⟩
  have hmem (s : ℝ) :
      point (EuclideanSpace.single 0 (lacunaryFunction ε a N t)) s ∈ modelSet L := by
    simp [L, modelSet, AdmissibleModel.toSet, VerticalModel.toSet, point]
  have hdist (s : ℝ) :
      Metric.infEDist (lacunaryGraphMap ε a N s) (modelSet L) ≤
        ENNReal.ofReal |lacunaryFunction ε a N s - lacunaryFunction ε a N t| := by
    calc
      _ ≤ edist (lacunaryGraphMap ε a N s)
          (point (EuclideanSpace.single 0 (lacunaryFunction ε a N t)) s) :=
        Metric.infEDist_le_edist_of_mem (hmem s)
      _ = _ := by
        rw [edist_dist, lacunaryGraphMap, dist_point]
        simp [← PiLp.single_sub, PiLp.norm_single, Real.norm_eq_abs]
  have hg : Measurable (fun w : Space 1 => Metric.infEDist w (modelSet L) ^ q) :=
    Metric.continuous_infEDist.measurable.pow_const q
  have hfit : fitPow (lacunarySource ε a N E) q L (lacunaryGraphMap ε a N t) r ≤
      (ENNReal.ofReal (2 * ε * r * S)) ^ q * ENNReal.ofReal (2 * r ^ 2) := by
    unfold fitPow
    rw [hball ε a N hε hε' hd E t r hr _ hg]
    calc
      _ ≤ ∫⁻ _s in E ∩ Ioo (t - r ^ 2) (t + r ^ 2),
          (ENNReal.ofReal (2 * ε * r * S)) ^ q := by
        apply setLIntegral_mono measurable_const
        intro s hs
        have hst : |s - t| ≤ r ^ 2 := by
          rw [abs_le]
          exact ⟨by linarith [hs.2.1], by linarith [hs.2.2]⟩
        apply ENNReal.rpow_le_rpow _ hq.le
        exact (hdist s).trans (ENNReal.ofReal_le_ofReal
          (hkernel ε a N hε.le hd s t r hr hst).2)
      _ = (ENNReal.ofReal (2 * ε * r * S)) ^ q *
          volume (E ∩ Ioo (t - r ^ 2) (t + r ^ 2)) := by simp
      _ ≤ (ENNReal.ofReal (2 * ε * r * S)) ^ q * ENNReal.ofReal (2 * r ^ 2) := by
        apply mul_le_mul_right
        calc
          _ ≤ volume (Ioo (t - r ^ 2) (t + r ^ 2)) := measure_mono inter_subset_right
          _ = _ := by rw [Real.volume_Ioo]; congr 1; ring
  unfold betaPow
  rw [ite_eq_left hr]
  calc
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ ((2 : ℝ) + q) *
        fitPow (lacunarySource ε a N E) q L (lacunaryGraphMap ε a N t) r :=
      mul_le_mul_right (iInf_le _ L) _
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ ((2 : ℝ) + q) *
        ((ENNReal.ofReal (2 * ε * r * S)) ^ q * ENNReal.ofReal (2 * r ^ 2)) :=
      mul_le_mul_right hfit _
    _ = _ := e2_testBound_normalization hε.le hr hS hq.le

end ParabolicRectifiability.Examples
