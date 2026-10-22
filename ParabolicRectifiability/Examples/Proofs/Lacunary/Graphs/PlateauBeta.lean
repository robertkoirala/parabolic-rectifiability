import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import ParabolicRectifiability.Geometry.ModelDistance

/-! # The mixed beta lower bound at a lacunary plateau radius

At spatial dimension one and parabolic dimension two, the admissible family
consists of vertical lines. Their actual spatial anchors supply the constants
in the plateau estimate. The normalization cancels the frequency exactly.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples
open ParabolicRectifiability.Foundations

private theorem e2_vertical_one_two_distance (L : VerticalModel 1 2)
    (x t : ℝ) :
    Metric.infEDist (point (EuclideanSpace.single 0 x) t) L.toSet =
      ENNReal.ofReal |x - L.spatial.anchor 0| := by
  have hr : L.spatialRank = 0 := by have := L.rank_eq; omega
  have hd : L.spatial.direction = ⊥ :=
    Submodule.finrank_eq_zero.mp (L.spatial.rank_eq.trans hr)
  have ha : L.spatial.anchor = EuclideanSpace.single 0 (L.spatial.anchor 0) := by
    ext i
    fin_cases i
    simp
  rw [L.infEDist_eq_projection, edist_dist]
  congr 1
  change dist (point (EuclideanSpace.single 0 x) t)
    (point (L.spatial.projection (EuclideanSpace.single 0 x)) t) = _
  rw [dist_point]
  simp only [sub_self, abs_zero, Real.sqrt_zero, max_eq_left (norm_nonneg _)]
  simp only [AffineSpatialPlane.projection, AffineSpatialPlane.linearProjection,
    hd, Submodule.starProjection_bot, zero_apply, add_zero]
  rw [ha, ← PiLp.single_sub, PiLp.norm_single, Real.norm_eq_abs]
  simp

private theorem e2_plateau_normalization (ε A M q : ℝ)
    (hε : 0 < ε) (hA : 0 < A) (hM : 0 < M) :
    (ENNReal.ofReal (Real.sqrt (Real.pi / M)))⁻¹ ^ (2 + q) *
        ENNReal.ofReal (Real.pi / (2 * M) * (12 / 25 * (ε * (A / Real.sqrt M))) ^ q) =
      ENNReal.ofReal (1 / 2 * Real.pi ^ (-(q / 2)) * (12 / 25) ^ q * ε ^ q * A ^ q) := by
  let r := Real.sqrt (Real.pi / M)
  have hr : 0 < r := Real.sqrt_pos.2 (div_pos Real.pi_pos hM)
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hr2 : r ^ 2 = Real.pi / M := Real.sq_sqrt (by positivity)
  have hrs : r * Real.sqrt M = Real.sqrt Real.pi := by
    dsimp [r]
    rw [Real.sqrt_div Real.pi_pos.le, div_mul_cancel₀ _ hs.ne']
  have hc : r⁻¹ ^ 2 * (Real.pi / (2 * M)) = 1 / 2 := by
    have he : Real.pi = r ^ 2 * M := (eq_div_iff hM.ne').mp hr2 |>.symm
    rw [he]
    field_simp
  have ham : r⁻¹ * (12 / 25 * (ε * (A / Real.sqrt M))) =
      (12 / 25 * ε * A) / Real.sqrt Real.pi := by
    rw [← hrs]
    field_simp
  change (ENNReal.ofReal r)⁻¹ ^ (2 + q) * _ = _
  rw [← ENNReal.ofReal_inv_of_pos hr, ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hr),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hr.le) _)]
  congr 1
  rw [Real.rpow_add (inv_pos.mpr hr), Real.rpow_two]
  calc
    r⁻¹ ^ 2 * r⁻¹ ^ q * (Real.pi / (2 * M) * (12 / 25 * (ε * (A / Real.sqrt M))) ^ q) =
        (r⁻¹ ^ 2 * (Real.pi / (2 * M))) *
          (r⁻¹ ^ q * (12 / 25 * (ε * (A / Real.sqrt M))) ^ q) := by ring
    _ = 1 / 2 * (r⁻¹ * (12 / 25 * (ε * (A / Real.sqrt M)))) ^ q := by
      rw [hc, Real.mul_rpow (inv_nonneg.mpr hr.le) (by positivity)]
    _ = 1 / 2 * Real.pi ^ (-(q / 2)) * (12 / 25) ^ q * ε ^ q * A ^ q := by
      rw [ham, Real.div_rpow (by positivity) hp.le,
        Real.mul_rpow (by positivity) hA.le,
        Real.mul_rpow (by norm_num) hε.le,
        Real.sqrt_eq_rpow, ← Real.rpow_mul Real.pi_pos.le,
        Real.rpow_neg Real.pi_pos.le]
      ring_nf

/-- Plateau occupancy forces a uniform lower bound for every genuine mixed
model, hence for their fitting infimum with the exact beta normalization. -/
theorem e2_plateau_beta_proof :
    E2BallPullbackStatement → E2PlateauLowerStatement → E2PlateauBetaStatement := by
  intro hball hlower ε a N hε hε' hd E hE j t hocc q hq
  have hN : 0 < (N j : ℝ) := by exact_mod_cast hd.frequency_pos j
  have hr : 0 < e2_plateauRadius N j := Real.sqrt_pos.2 (div_pos Real.pi_pos hN)
  have hr2 : e2_plateauRadius N j ^ 2 = Real.pi / N j :=
    Real.sq_sqrt (by positivity)
  have hfit :
      ENNReal.ofReal (Real.pi / (2 * N j) *
        (12 / 25 * (ε * (a j / Real.sqrt (N j)))) ^ q) ≤
        ⨅ L : Models 1 2 .mixed,
          fitPow (lacunarySource ε a N E) q L (lacunaryGraphMap ε a N t)
            (e2_plateauRadius N j) := by
    apply le_iInf
    intro L
    change HorizontalModel 1 2 ⊕ VerticalModel 1 2 at L
    cases L with
    | inl L =>
      let : IsEmpty (HorizontalModel 1 2) :=
        HorizontalModel.isEmpty_of_not_available (by omega)
      exact isEmptyElim L
    | inr L =>
      have hm : Measurable (fun w : Space 1 => Metric.infEDist w L.toSet ^ q) :=
        Metric.continuous_infEDist.measurable.pow_const q
      change _ ≤ ∫⁻ w in Metric.ball _ _, Metric.infEDist w L.toSet ^ q ∂_
      rw [hball ε a N hε hε' hd E t _ hr _ hm, hr2]
      have hint : (fun s => Metric.infEDist (lacunaryGraphMap ε a N s) L.toSet ^ q) =
          (fun s => ENNReal.ofReal (|lacunaryFunction ε a N s - L.spatial.anchor 0| ^ q)) := by
        funext s
        rw [lacunaryGraphMap, e2_vertical_one_two_distance,
          ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq.le]
      rw [hint]
      exact hlower ε a N hε.le hd E hE j t hocc q hq (L.spatial.anchor 0)
  rw [betaPow, ite_eq_left hr]
  calc
    _ = (ENNReal.ofReal (e2_plateauRadius N j))⁻¹ ^ ((2 : ℝ) + q) *
        ENNReal.ofReal (Real.pi / (2 * N j) *
          (12 / 25 * (ε * (a j / Real.sqrt (N j)))) ^ q) :=
      (e2_plateau_normalization ε (a j) (N j) q hε (hd.amplitude_pos j) hN).symm
    _ ≤ _ := mul_le_mul_right hfit _

end ParabolicRectifiability.Examples
