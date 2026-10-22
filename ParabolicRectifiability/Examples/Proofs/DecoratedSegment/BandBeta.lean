import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # The beta lower bound on a band of radii

The two disjoint segments give a lower bound for every affine line. Their union is
contained in the ball and in the original source set, so monotonicity of restricted
measures transfers that bound to the full source, even when the source set is not
measurable. Taking the infimum over all lines preserves this uniform lower bound.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.BetaP (Plane horizontalSegment)

private lemma horizontalSegment_measurable (u v b : ℝ) :
    MeasurableSet (horizontalSegment u v b) := by
  have h0 : Continuous (fun w : Plane => w 0) := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  have h1 : Continuous (fun w : Plane => w 1) := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  exact ((isClosed_le continuous_const h0).inter
    ((isClosed_le h0 continuous_const).inter
      (isClosed_eq h1 continuous_const))).measurableSet

private lemma band_normalization (p h δ r : ℝ) (hp : 2 < p) (hh : 0 < h)
    (hδ : 0 < δ) (hr : 0 < r) (hr4 : r ≤ 4 * h) :
    ENNReal.ofReal (e2_sapFitConst p * (4 : ℝ) ^ (-p - 1) * δ) ≤
      (ENNReal.ofReal r)⁻¹ ^ (1 + p) *
        ENNReal.ofReal (e2_sapFitConst p * δ * h ^ (p + 1)) := by
  have hc : 0 ≤ e2_sapFitConst p := by
    unfold e2_sapFitConst
    positivity
  have hcost : 0 ≤ e2_sapFitConst p * δ * h ^ (p + 1) := by positivity
  have hpow : (4 * h) ^ (-(1 + p)) ≤ r ^ (-(1 + p)) :=
    Real.rpow_le_rpow_of_nonpos hr hr4 (by linarith)
  have hcancel : h ^ (-(1 + p)) * h ^ (p + 1) = 1 := by
    rw [← Real.rpow_add hh]
    ring_nf
    exact Real.rpow_zero h
  have hidentity : (4 * h) ^ (-(1 + p)) *
      (e2_sapFitConst p * δ * h ^ (p + 1)) =
        e2_sapFitConst p * (4 : ℝ) ^ (-p - 1) * δ := by
    rw [Real.mul_rpow (by norm_num) hh.le]
    have hexp : -(1 + p) = -p - 1 := by ring
    calc
      _ = e2_sapFitConst p * (4 : ℝ) ^ (-(1 + p)) * δ *
          (h ^ (-(1 + p)) * h ^ (p + 1)) := by ring
      _ = _ := by rw [hcancel, mul_one, hexp]
  rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg, ENNReal.ofReal_rpow_of_pos hr,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
  apply ENNReal.ofReal_le_ofReal
  rw [← hidentity]
  exact mul_le_mul_of_nonneg_right hpow hcost

/-- The exact band implication: pair cost and ball containment imply the beta bound
for the complete restricted Hausdorff source and the infimum over every affine line. -/
theorem e2_sap_bandBeta_proof (hP : E2sapPairCost) (hB : E2sapBallContain) :
    E2sapBandBeta := by
  intro E p hp x y h δ ξ hh hδ hδ4 hξ hIE hJE r hr2 hr4
  have hr : 0 < r := by linarith
  obtain ⟨hIB, hJB⟩ := hB x y h δ ξ r hh hδ.le hδ4 hξ hr2
  have hdisj : Disjoint (horizontalSegment (x - h) (x + h) y)
      (horizontalSegment (x + ξ - δ * h / 2) (x + ξ + δ * h / 2) (y + h)) := by
    apply Set.disjoint_left.mpr
    intro w hwI hwJ
    have hI := hwI.2.2
    have hJ := hwJ.2.2
    linarith
  have hcost : ENNReal.ofReal (e2_sapFitConst p * δ * h ^ (p + 1)) ≤
      ⨅ U : AffineSpatialPlane 2 1,
        ∫⁻ w in Metric.ball (e2_sapPt x y) r,
          Metric.infEDist w U.toSet ^ p ∂(μH[1].restrict E) := by
    refine le_iInf fun U => (hP p hp x y h δ ξ hh hδ hδ4 hξ U).trans ?_
    rw [← lintegral_union (horizontalSegment_measurable _ _ _) hdisj]
    apply lintegral_mono' ?_ le_rfl
    rw [Measure.restrict_restrict measurableSet_ball]
    apply Measure.restrict_mono_set
    intro w hw
    rcases hw with hw | hw
    · exact ⟨hIB hw, hIE hw⟩
    · exact ⟨hJB hw, hJE hw⟩
  rw [euclideanBetaPow, ite_eq_left hr]
  norm_num only [Nat.cast_one]
  exact (band_normalization p h δ r hp hh hδ hr hr4).trans
    (mul_le_mul_right hcost _)

end ParabolicRectifiability.Examples
