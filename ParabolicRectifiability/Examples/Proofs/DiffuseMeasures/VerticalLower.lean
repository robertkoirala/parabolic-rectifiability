import ParabolicRectifiability.Metric.BaseVolume
import ParabolicRectifiability.Examples.Proofs.DensityTests.DiffuseEstimateStatements
import ParabolicRectifiability.Geometry.ModelDistance

/-! # Vertical lower fit for the diffuse base

Proof of `E2DiffuseVerticalLowerStatement` (the lower bound against vertical models),
`e2_diffuse_verticalLower_proof`.

Route. A vertical model `(a₀ + W) × ℝ` has spatial rank
`q = k - 2 < n`, so `Wᗮ` contains a unit vector `e`. For `z = (x,t) ∈ D` and `r ∈ I`, put
`c = ⟨x - a₀, e⟩` and `σ = 1` if `c ≥ 0`, `σ = -1` if `c < 0` (the sign of `c`, not its
opposite), so that `|c + σ·3r/4| = |c| + 3r/4`. On the spatial subball
`B(x + σ(3r/4)e, r/4) ⊆ B(x,r)` one has `|⟨y - a₀, e⟩| ≥ 3r/4 - r/4 = r/2`, and
`d_P(w,L) = ‖y - π_W y - a₀‖ ≥ |⟨y - a₀, e⟩|` (`VerticalModel.infEDist_eq_projection`,
`VerticalModel.dist_projection_sq`). The rectangle `B(x + σ(3r/4)e, r/4) × (t - r², t + r²)`
lies in `P(z,r) ⊆ P(0,1/4)`, where `ω = λ`, and has volume `ω_n (r/4)^n · 2r²`. Hence the bound
with `a = 2 ω_n 4^{-n} 2^{-p}`. No spherical-cap volume is used.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The sign choice `σ = 1` if `c ≥ 0` and `σ = -1` if `c < 0`.
Then `|c + σ·3r/4| = |c| + 3r/4`, and every perturbation of size `< r/4` stays at absolute
value at least `r/2`. -/
theorem e2d4_sign (c r : ℝ) (hr : 0 ≤ r) :
    ∃ σ : ℝ, σ = (if 0 ≤ c then 1 else -1) ∧ |σ| = 1 ∧
      |c + σ * (3 * r / 4)| = |c| + 3 * r / 4 ∧
      ∀ δ : ℝ, |δ| < r / 4 → r / 2 ≤ |c + σ * (3 * r / 4) + δ| := by
  by_cases hc : 0 ≤ c
  · refine ⟨1, by simp [hc], abs_one, ?_, fun δ hδ => ?_⟩
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c + 1 * (3 * r / 4)), abs_of_nonneg hc]
      ring
    · have h := abs_lt.mp hδ
      exact le_abs.mpr (Or.inl (by linarith [h.1]))
  · have hc' : ¬0 ≤ c := hc
    replace hc : c < 0 := not_le.mp hc
    refine ⟨-1, by simp [hc'], by simp, ?_, fun δ hδ => ?_⟩
    · rw [abs_of_neg (by linarith : c + -1 * (3 * r / 4) < 0), abs_of_neg hc]
      ring
    · have h := abs_lt.mp hδ
      exact le_abs.mpr (Or.inr (by linarith [h.2]))

/-- A spatial plane of rank `m < n` has a unit normal vector. -/
theorem e2d4_unitNormal {n m : ℕ} (P : AffineSpatialPlane n m) (hm : m < n) :
    ∃ e : Spatial n, e ∈ P.directionᗮ ∧ ‖e‖ = 1 := by
  have hdim := P.direction.finrank_add_finrank_orthogonal
  rw [P.rank_eq, finrank_euclideanSpace_fin] at hdim
  have hpos : 0 < Module.finrank ℝ P.directionᗮ := by omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hv' : (v : Spatial n) ≠ 0 := fun h => hv (Subtype.ext h)
  exact ⟨(‖(v : Spatial n)‖⁻¹ : ℝ) • (v : Spatial n), P.directionᗮ.smul_mem _ v.2,
    norm_smul_inv_norm hv'⟩

/-- Ordinary Euclidean ball volume, delegated to the shared spatial-volume formula. -/
theorem e2d4_volume_ball {n : ℕ} (x : Spatial n) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Spatial n)) (Metric.ball x r) = omega n * ENNReal.ofReal r ^ n := by
  exact ParabolicRectifiability.volume_spatial_ball x hr

/-- The distance from a point to a vertical model is at least the absolute normal component
`|⟨y - a₀, e⟩|` of its spatial part, for a unit normal `e ⊥ W`. -/
theorem e2d4_le_infEDist {n k : ℕ} (L : VerticalModel n k) {e : Spatial n}
    (he : e ∈ L.spatial.directionᗮ) (he1 : ‖e‖ = 1) (w : Space n) {d : ℝ}
    (hw : d ≤ |inner ℝ (w.1 - L.spatial.anchor) e|) :
    ENNReal.ofReal d ≤ Metric.infEDist w L.toSet := by
  rw [L.infEDist_eq_projection, edist_dist]
  apply ENNReal.ofReal_le_ofReal
  have hsq := L.dist_projection_sq w.1 w.2.val
  have hw' : point w.1 w.2.val = w := rfl
  rw [hw'] at hsq
  have hdn : dist w (L.projection w) =
      ‖w.1 - L.spatial.direction.starProjection w.1 - L.spatial.anchor‖ :=
    (pow_left_inj₀ dist_nonneg (norm_nonneg _) two_ne_zero).mp hsq
  have h0 : inner ℝ (L.spatial.direction.starProjection w.1) e = 0 :=
    Submodule.inner_right_of_mem_orthogonal (L.spatial.direction.starProjection_apply_mem w.1) he
  have hin : inner ℝ (w.1 - L.spatial.direction.starProjection w.1 - L.spatial.anchor) e =
      inner ℝ (w.1 - L.spatial.anchor) e := by
    rw [sub_right_comm, inner_sub_left, h0, sub_zero]
  rw [hdn]
  calc d ≤ |inner ℝ (w.1 - L.spatial.anchor) e| := hw
    _ = |inner ℝ (w.1 - L.spatial.direction.starProjection w.1 - L.spatial.anchor) e| := by
        rw [hin]
    _ ≤ ‖w.1 - L.spatial.direction.starProjection w.1 - L.spatial.anchor‖ * ‖e‖ :=
        abs_real_inner_le_norm _ _
    _ = ‖w.1 - L.spatial.direction.starProjection w.1 - L.spatial.anchor‖ := by
        rw [he1, mul_one]

/-- The real identity `2 ω 4^{-n} 2^{-p} r^{n+2+p} = (r/2)^p · (ω (r/4)^n · 2r²)`. -/
theorem e2d4_real_identity (ω0 r p : ℝ) (n : ℕ) (hr : 0 < r) :
    2 * ω0 * ((4 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ (-p) * r ^ ((n : ℝ) + 2 + p) =
      (r / 2) ^ p * (ω0 * (r / 4) ^ n * (2 * r ^ 2)) := by
  rw [Real.div_rpow hr.le two_pos.le, Real.rpow_neg two_pos.le, Real.rpow_add hr,
    Real.rpow_add hr, Real.rpow_natCast, Real.rpow_two, div_pow]
  ring

/-- The same identity after `ENNReal.ofReal`. -/
theorem e2d4_ennreal_identity (ω0 r p : ℝ) (n : ℕ) (hω : 0 ≤ ω0) (hr : 0 < r)
    (hp : 0 ≤ p) :
    ENNReal.ofReal (2 * ω0 * ((4 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ (-p)) *
        ENNReal.ofReal r ^ ((n : ℝ) + 2 + p) =
      ENNReal.ofReal (r / 2) ^ p *
        (ENNReal.ofReal ω0 * ENNReal.ofReal (r / 4) ^ n * ENNReal.ofReal (2 * r ^ 2)) := by
  have ha : 0 ≤ 2 * ω0 * ((4 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ (-p) :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hω) (inv_nonneg.mpr (pow_nonneg
      (by norm_num) n))) (Real.rpow_nonneg zero_le_two _)
  have h4 : 0 ≤ r / 4 := by linarith
  have h2 : 0 ≤ r / 2 := by linarith
  rw [ENNReal.ofReal_rpow_of_pos hr, ENNReal.ofReal_rpow_of_nonneg h2 hp,
    ← ENNReal.ofReal_pow h4, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hω,
    ← ENNReal.ofReal_mul (mul_nonneg hω (pow_nonneg h4 _)),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg h2 _), e2d4_real_identity ω0 r p n hr]

/-- Vertical lower fit for the diffuse base (`E2DiffuseVerticalLowerStatement`). -/
theorem e2_diffuse_verticalLower_proof : E2DiffuseVerticalLowerStatement := by
  intro n k p hk hp
  obtain ⟨ω0, hω0, hωe⟩ : ∃ ω0 : ℝ, 0 < ω0 ∧ omega n = ENNReal.ofReal ω0 :=
    ⟨(omega n).toReal, ENNReal.toReal_pos (omega_pos n).ne' (omega_lt_top n).ne,
      (ENNReal.ofReal_toReal (omega_lt_top n).ne).symm⟩
  refine ⟨2 * ω0 * ((4 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ (-p),
    mul_pos (mul_pos (mul_pos two_pos hω0) (inv_pos.mpr (pow_pos (by norm_num) n)))
      (Real.rpow_pos_of_pos two_pos _), ?_⟩
  intro L z hz r hr
  have hr0 : 0 < r := by linarith [hr.1]
  -- the unit normal `e ⊥ W` (rank `k - 2 < n`) and the sign `σ` of `c = ⟨x - a₀, e⟩`
  have hq : L.spatialRank < n := by have := L.rank_eq; omega
  obtain ⟨e, he, he1⟩ := e2d4_unitNormal L.spatial hq
  obtain ⟨σ, -, hσ, -, hσδ⟩ := e2d4_sign (inner ℝ (z.1 - L.spatial.anchor) e) r hr0.le
  -- the spatial subball `B(x + σ(3r/4)e, r/4)` and its rectangle
  obtain ⟨x', hx'⟩ : ∃ x' : Spatial n, x' = z.1 + (σ * (3 * r / 4)) • e := ⟨_, rfl⟩
  have hsub : Metric.ball x' (r / 4) ⊆ Metric.ball z.1 r := by
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    have hxx : dist x' z.1 = 3 * r / 4 := by
      rw [hx', dist_eq_norm, add_sub_cancel_left, norm_smul, he1, mul_one, Real.norm_eq_abs,
        abs_mul, hσ, one_mul, abs_of_pos (by linarith)]
    calc dist y z.1 ≤ dist y x' + dist x' z.1 := dist_triangle _ _ _
      _ < r := by linarith
  have hSm : MeasurableSet ((coordinatesMeasurableEquiv n) ⁻¹'
      (Metric.ball x' (r / 4) ×ˢ Ioo (z.2.val - r ^ 2) (z.2.val + r ^ 2))) :=
    (coordinatesMeasurableEquiv n).measurable (measurableSet_ball.prod measurableSet_Ioo)
  have hSball : (coordinatesMeasurableEquiv n) ⁻¹'
      (Metric.ball x' (r / 4) ×ˢ Ioo (z.2.val - r ^ 2) (z.2.val + r ^ 2)) ⊆
        Metric.ball z r := by
    rw [← coordinates_preimage_ball_rectangle z r hr0]
    exact preimage_mono (prod_mono hsub subset_rfl)
  have hball : Metric.ball z r ⊆ Metric.ball (point 0 0) (1 / 4) := by
    intro w hw
    rw [Metric.mem_ball] at hw ⊢
    have hz' : dist z (point 0 0) < 1 / 16 := Metric.mem_ball.mp hz
    have hr1 : r ≤ 1 / 16 := hr.2
    calc dist w (point 0 0) ≤ dist w z + dist z (point 0 0) := dist_triangle _ _ _
      _ < 1 / 4 := by linarith
  have hvolS : e2_diffuseBase n ((coordinatesMeasurableEquiv n) ⁻¹'
      (Metric.ball x' (r / 4) ×ˢ Ioo (z.2.val - r ^ 2) (z.2.val + r ^ 2))) =
      ENNReal.ofReal ω0 * ENNReal.ofReal (r / 4) ^ n * ENNReal.ofReal (2 * r ^ 2) := by
    rw [Measure.restrict_apply hSm, inter_eq_left.mpr (hSball.trans hball), parabolicVolume_apply,
      MeasurableEquiv.symm_preimage_preimage, coordinateVolume, Measure.prod_prod,
      Real.volume_Ioo, e2d4_volume_ball x' (by linarith : (0 : ℝ) < r / 4), hωe,
      show z.2.val + r ^ 2 - (z.2.val - r ^ 2) = 2 * r ^ 2 by ring]
  -- on the rectangle, the distance to the model is at least `r/2`
  have hc : ∀ w ∈ (coordinatesMeasurableEquiv n) ⁻¹'
      (Metric.ball x' (r / 4) ×ˢ Ioo (z.2.val - r ^ 2) (z.2.val + r ^ 2)),
      ENNReal.ofReal (r / 2) ^ p ≤ Metric.infEDist w L.toSet ^ p := by
    intro w hw
    simp only [mem_preimage, coordinatesMeasurableEquiv_apply, mem_prod] at hw
    refine ENNReal.rpow_le_rpow (e2d4_le_infEDist L he he1 w ?_) hp.le
    have h1 : inner ℝ (w.1 - L.spatial.anchor) e =
        inner ℝ (z.1 - L.spatial.anchor) e + σ * (3 * r / 4) + inner ℝ (w.1 - x') e := by
      have hdec : w.1 - L.spatial.anchor =
          (z.1 - L.spatial.anchor) + (σ * (3 * r / 4)) • e + (w.1 - x') := by
        rw [hx']; abel
      rw [hdec, inner_add_left, inner_add_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, he1]
      ring
    have h2 : |inner ℝ (w.1 - x') e| < r / 4 := by
      calc |inner ℝ (w.1 - x') e| ≤ ‖w.1 - x'‖ * ‖e‖ := abs_real_inner_le_norm _ _
        _ = dist w.1 x' := by rw [he1, mul_one, dist_eq_norm]
        _ < r / 4 := Metric.mem_ball.mp hw.1
    rw [h1]
    exact hσδ _ h2
  calc ENNReal.ofReal (2 * ω0 * ((4 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ (-p)) *
        ENNReal.ofReal r ^ ((n : ℝ) + 2 + p)
      = ENNReal.ofReal (r / 2) ^ p *
          e2_diffuseBase n ((coordinatesMeasurableEquiv n) ⁻¹'
            (Metric.ball x' (r / 4) ×ˢ Ioo (z.2.val - r ^ 2) (z.2.val + r ^ 2))) := by
        rw [hvolS]
        exact e2d4_ennreal_identity ω0 r p n hω0.le hr0 hp.le
    _ = ∫⁻ _ in (coordinatesMeasurableEquiv n) ⁻¹'
          (Metric.ball x' (r / 4) ×ˢ Ioo (z.2.val - r ^ 2) (z.2.val + r ^ 2)),
          ENNReal.ofReal (r / 2) ^ p ∂(e2_diffuseBase n) :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ w in (coordinatesMeasurableEquiv n) ⁻¹'
          (Metric.ball x' (r / 4) ×ˢ Ioo (z.2.val - r ^ 2) (z.2.val + r ^ 2)),
          Metric.infEDist w L.toSet ^ p ∂(e2_diffuseBase n) :=
        setLIntegral_mono' hSm hc
    _ ≤ ∫⁻ w in Metric.ball z r, Metric.infEDist w L.toSet ^ p ∂(e2_diffuseBase n) :=
        lintegral_mono_set hSball

end ParabolicRectifiability.Examples
