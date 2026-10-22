import ParabolicRectifiability.Analysis.RegularExtension.AffineCutoff.CutoffComparison
import ParabolicRectifiability.Analysis.HalfTimeDerivative.TailOscillation

/-! # The explicit smooth cutoff and the source bounds

The cutoff of `affineEnergy_cutoff_le_proof` is constructed explicitly: it is the
parabolic bump `ψ_R(u,t) = a(|u|^2/R^2) b(t/R^2)` of
`SmoothCutoff.parabolicBump`, centred at the origin. It equals one on `P(0,2R)`,
vanishes outside the closed set `{|u|^2 ≤ 8R^2, |t| ≤ 8R^2} ⊆ P(0,3R)`, and has the parabolic
`C^{2,1}` bounds `B/R`, `B/R^2`, `B/R^2` with `B = bumpBound m` (the same construction as
`TraceExtension.exists_parabolic_cutoff`, at the ratio required by `TailCutoff`).

The elementary `TailCutoff` fields are derived from it; the energy estimate itself uses the
derivative bounds (`HasParabolicDerivBounds`), not only these fields.

Source bounds: a parabolic `L`-Lipschitz `F` on Fourier coordinates gives an `L`-Lipschitz
function on `Space m`, and its genuine mean `c` over `P(0,R)` satisfies `|F(0) - c| ≤ L R`
(`abs_tailMean_sub_origin_le` assumes compact support only for integrability;
continuity and boundedness on the finite-volume cylinder suffice here), so `|F - c| ≤ 7 L R`
on `P̄(0,6R)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-- The explicit smooth cutoff on parabolic space: the parabolic bump
`a(|u|^2/R^2) b(t/R^2)` centred at the origin. -/
def rx4_cutoffSpace (m : ℕ) (R : ℝ) (y : Space m) : ℝ :=
  SmoothCutoff.parabolicBump R (point (0 : Spatial m) 0) (y.1, y.2.val)

/-- The same cutoff in ordinary Fourier coordinates. -/
def rx4_cutoff (m : ℕ) (R : ℝ) (q : FourierSpace m) : ℝ :=
  SmoothCutoff.parabolicBump R (point (0 : Spatial m) 0) (WithLp.ofLp q)

section Cutoff

variable {m : ℕ} {R : ℝ}

theorem rx4_cutoff_eq (q : FourierSpace m) :
    rx4_cutoff m R q = rx4_cutoffSpace m R (fourierToParabolic m q) := rfl

theorem rx4_cutoffSpace_hasParabolicDerivBounds (hR : 0 < R) :
    HasParabolicDerivBounds (rx4_cutoffSpace m R) (SmoothCutoff.bumpBound m) R :=
  { contDiff := (SmoothCutoff.contDiff_parabolicBump R (point (0 : Spatial m) 0)).of_le
      ENat.LEInfty.out
    spatial_le := fun u t =>
      SmoothCutoff.norm_fderiv_parabolicBump_spatial_le hR (point (0 : Spatial m) 0) t u
    spatial₂_le := fun u t =>
      SmoothCutoff.norm_fderiv_fderiv_parabolicBump_spatial_le hR (point (0 : Spatial m) 0) t u
    time_le := fun u t =>
      SmoothCutoff.abs_deriv_parabolicBump_time_le hR (point (0 : Spatial m) 0) u t }

theorem rx4_cutoffSpace_mem_Icc (y : Space m) :
    0 ≤ rx4_cutoffSpace m R y ∧ rx4_cutoffSpace m R y ≤ 1 :=
  ⟨SmoothCutoff.parabolicBump_nonneg _ _ _, SmoothCutoff.parabolicBump_le_one _ _ _⟩

/-- The cutoff is nonzero only in the open ball `P(0,3R) ⊆ P(0,4R)`. -/
theorem rx4_cutoffSpace_support (hR : 0 < R) (y : Space m)
    (hy : rx4_cutoffSpace m R y ≠ 0) : y ∈ Metric.ball (point (0 : Spatial m) 0) (4 * R) := by
  have hmem : (y.1, y.2.val) ∈ SmoothCutoff.bumpSupportSet R (point (0 : Spatial m) 0) := by
    by_contra h
    exact hy (SmoothCutoff.parabolicBump_eq_zero hR h)
  have h3 := SmoothCutoff.point_mem_ball_of_mem_bumpSupportSet hR hmem
  exact Metric.ball_subset_ball (by linarith) h3

theorem rx4_continuous_cutoffSpace : Continuous (rx4_cutoffSpace m R) :=
  (SmoothCutoff.contDiff_parabolicBump R (point (0 : Spatial m) 0)).continuous.comp
    (continuous_fst.prodMk continuous_time)

/-- The explicit cutoff has the elementary `TailCutoff` properties with `Cχ = bumpBound m`. -/
theorem rx4_tailCutoff (hR : 0 < R) :
    HalfTimeDerivative.TailCutoff (rx4_cutoff m R) R (SmoothCutoff.bumpBound m) := by
  have hχ := rx4_cutoffSpace_hasParabolicDerivBounds (m := m) hR
  refine
    { measurable := (rx4_continuous_cutoffSpace.comp (fourierToParabolic m).continuous).measurable
      nonneg := fun x => SmoothCutoff.parabolicBump_nonneg _ _ _
      le_one := fun x => SmoothCutoff.parabolicBump_le_one _ _ _
      inner := ?_
      outer := ?_
      spatial := ?_ }
  · intro x hx
    rw [analyticCylinder_eq_preimage_ball _ _ (by positivity), mem_preimage,
      fourierToParabolicMeasurableEquiv_apply] at hx
    exact SmoothCutoff.parabolicBump_eq_one hR hx
  · intro x hx
    by_contra h
    apply hx
    rw [analyticCylinder_eq_preimage_ball _ _ (by positivity), mem_preimage,
      fourierToParabolicMeasurableEquiv_apply]
    exact rx4_cutoffSpace_support hR (point (WithLp.ofLp x).1 (WithLp.ofLp x).2) h
  · intro u v s
    have hd : Differentiable ℝ (fun w : Spatial m => rx4_cutoffSpace m R (point w s)) :=
      (hχ.contDiff.comp (contDiff_id.prodMk contDiff_const)).differentiable two_ne_zero
    have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hd w) (fun w _ => hχ.spatial_le w s) (mem_univ v) (mem_univ u)
    rw [Real.norm_eq_abs] at h
    exact h

end Cutoff

/-! ## Source bounds -/

section Source

variable {m : ℕ} {F : FourierSpace m → ℝ} {L R : ℝ}

/-- A parabolic `L`-Lipschitz function on Fourier coordinates is `L`-Lipschitz on `Space m`. -/
theorem rx4_norm_sub_le_of_parabolicLipschitz (hF : HalfTimeDerivative.ParabolicLipschitz F L)
    (p q : Space m) :
    ‖F ((fourierToParabolic m).symm p) - F ((fourierToParabolic m).symm q)‖ ≤ L * dist p q := by
  rcases p with ⟨u, ⟨t⟩⟩
  rcases q with ⟨v, ⟨s⟩⟩
  change |F (WithLp.toLp 2 (u, t)) - F (WithLp.toLp 2 (v, s))| ≤ L * dist (point u t) (point v s)
  rw [dist_point]
  exact hF u v t s

/-- The genuine mean over `P(0,R)` is within `L R` of the central value. This is
`HalfTimeDerivative.abs_tailMean_sub_origin_le` without its compact-support hypothesis, which
was used there only for integrability: here `F` is continuous and bounded on the cylinder. -/
theorem rx4_abs_tailMean_sub_origin_le (hF : HalfTimeDerivative.ParabolicLipschitz F L)
    (hL : 0 ≤ L) (hR : 0 < R) :
    |HalfTimeDerivative.tailMean F R - F (WithLp.toLp 2 ((0 : Spatial m), 0))| ≤ L * R := by
  let E := analyticCylinder (point (0 : Spatial m) 0) R
  let a := (volume E).toReal
  have hp : 0 < a := ENNReal.toReal_pos (HalfTimeDerivative.tailBase_volume hR).1.ne'
    (HalfTimeDerivative.tailBase_volume hR).2.ne
  let _inst : IsFiniteMeasure (volume.restrict E) :=
    ⟨by simpa [E] using (HalfTimeDerivative.tailBase_volume hR).2⟩
  have hi : IntegrableOn F E volume := by
    refine Measure.integrableOn_of_bounded
      (M := |F (WithLp.toLp 2 ((0 : Spatial m), 0))| + L * R)
      (HalfTimeDerivative.tailBase_volume hR).2.ne
      (hF.continuous hL).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (measurableSet_analyticCylinder _ _)] with x hx
    have h1 := HalfTimeDerivative.parabolicLip_base_bound hF hL hR hx
    have h2 := abs_sub_abs_le_abs_sub (F x) (F (WithLp.toLp 2 ((0 : Spatial m), 0)))
    rw [Real.norm_eq_abs]
    linarith
  let f0 := F (WithLp.toLp 2 ((0 : Spatial m), 0))
  have he : HalfTimeDerivative.tailMean F R - f0 = a⁻¹ * ∫ x in E, (F x - f0) := by
    rw [integral_sub hi (integrable_const f0), integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    change a⁻¹ * (∫ x in E, F x) - f0 = a⁻¹ * ((∫ x in E, F x) - a * f0)
    field_simp [hp.ne']
  have hb : |∫ x in E, (F x - f0)| ≤ (L * R) * a := by
    have hn : ‖∫ x in E, (F x - f0)‖ ≤ (L * R) * (volume.restrict E).real univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [ae_restrict_mem (measurableSet_analyticCylinder _ _)] with x hx
      simpa only [Real.norm_eq_abs] using HalfTimeDerivative.parabolicLip_base_bound hF hL hR hx
    simpa [a, Measure.real] using hn
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ a⁻¹ * ((L * R) * a) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hp.le)
    _ = L * R := by field_simp

/-- On `P̄(0,6R)` the localized source deviates from the mean by at most `7 L R`. -/
theorem rx4_norm_sub_tailMean_le (hF : HalfTimeDerivative.ParabolicLipschitz F L)
    (hL : 0 ≤ L) (hR : 0 < R) (q : Space m)
    (hq : dist q (point (0 : Spatial m) 0) ≤ 6 * R) :
    ‖F ((fourierToParabolic m).symm q) - HalfTimeDerivative.tailMean F R‖ ≤ 7 * L * R := by
  have h1 := rx4_norm_sub_le_of_parabolicLipschitz hF q (point (0 : Spatial m) 0)
  have h0 : F ((fourierToParabolic m).symm (point (0 : Spatial m) 0)) =
      F (WithLp.toLp 2 ((0 : Spatial m), 0)) := rfl
  rw [h0] at h1
  have h2 := rx4_abs_tailMean_sub_origin_le hF hL hR
  rw [abs_sub_comm, ← Real.norm_eq_abs] at h2
  calc ‖F ((fourierToParabolic m).symm q) - HalfTimeDerivative.tailMean F R‖
      ≤ ‖F ((fourierToParabolic m).symm q) - F (WithLp.toLp 2 ((0 : Spatial m), 0))‖ +
        ‖F (WithLp.toLp 2 ((0 : Spatial m), 0)) - HalfTimeDerivative.tailMean F R‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ L * (6 * R) + L * R := add_le_add (h1.trans (mul_le_mul_of_nonneg_left hq hL)) h2
    _ = 7 * L * R := by ring

end Source

end ParabolicRectifiability
