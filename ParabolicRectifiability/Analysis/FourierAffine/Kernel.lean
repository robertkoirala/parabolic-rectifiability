import ParabolicRectifiability.Analysis.Coordinates
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # A parabolic smoothing kernel and its scale derivative

One fixed kernel per spatial rank `m`, used in the Fourier-affine bound
`fourierAffine_bound`. The bump `φ` is `c · exp(-1/(1/4 - ‖z‖²))` on the Euclidean ball of
radius `1/2`, which lies strictly inside the unit parabolic coordinate ball.
It is radial, hence even in every spatial coordinate. With `k = m + 2`,
`φ_r(u,t) = r^(-k) φ(u/r, t/r²)` and `ψ_r = r ∂_r φ_r` is written in closed form
through the derivative of the one-variable profile. All statements include `m = 0`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology ContDiff

namespace ParabolicRectifiability.FourierAffine

variable {m : ℕ}

/-! ### Coordinates, balls and dilations -/

/-- The open parabolic coordinate ball `{q : ‖u_q - u_p‖ < r, |t_q - t_p| < r²}`. -/
def coordBall (p : FourierSpace m) (r : ℝ) : Set (FourierSpace m) :=
  {q | ‖(WithLp.ofLp q).1 - (WithLp.ofLp p).1‖ < r ∧
    |(WithLp.ofLp q).2 - (WithLp.ofLp p).2| < r ^ 2}

/-- Parabolic dilation `(u,t) ↦ (r u, r² t)` of the ordinary Euclidean coordinates. -/
def dilate (r : ℝ) (z : FourierSpace m) : FourierSpace m :=
  WithLp.toLp 2 (r • (WithLp.ofLp z).1, r ^ 2 * (WithLp.ofLp z).2)

theorem norm_sq_eq (z : FourierSpace m) :
    ‖z‖ ^ 2 = ‖(WithLp.ofLp z).1‖ ^ 2 + (WithLp.ofLp z).2 ^ 2 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 z
  rw [Real.norm_eq_abs, sq_abs] at h
  exact h

theorem norm_fst_le (z : FourierSpace m) : ‖(WithLp.ofLp z).1‖ ≤ ‖z‖ := by
  have h := norm_sq_eq z
  nlinarith [norm_nonneg z, norm_nonneg (WithLp.ofLp z).1, sq_nonneg (WithLp.ofLp z).2]

theorem abs_snd_le (z : FourierSpace m) : |(WithLp.ofLp z).2| ≤ ‖z‖ := by
  have h := norm_sq_eq z
  rw [← sq_abs (WithLp.ofLp z).2] at h
  nlinarith [norm_nonneg z, norm_nonneg (WithLp.ofLp z).1, abs_nonneg (WithLp.ofLp z).2]

theorem norm_le_of_coords (z : FourierSpace m) {a b : ℝ} (ha : ‖(WithLp.ofLp z).1‖ ≤ a)
    (hb : |(WithLp.ofLp z).2| ≤ b) : ‖z‖ ≤ a + b := by
  have h0 : 0 ≤ ‖(WithLp.ofLp z).1‖ := norm_nonneg _
  have h1 : 0 ≤ |(WithLp.ofLp z).2| := abs_nonneg _
  have hs : ‖z‖ ^ 2 ≤ (a + b) ^ 2 := by
    rw [norm_sq_eq, ← sq_abs (WithLp.ofLp z).2]
    nlinarith
  nlinarith [norm_nonneg z]

@[simp] theorem ofLp_dilate (r : ℝ) (z : FourierSpace m) :
    WithLp.ofLp (dilate r z) = (r • (WithLp.ofLp z).1, r ^ 2 * (WithLp.ofLp z).2) := rfl

theorem dilate_dilate (a b : ℝ) (z : FourierSpace m) :
    dilate a (dilate b z) = dilate (a * b) z := by
  simp only [dilate, WithLp.ofLp_toLp, smul_smul, mul_pow, mul_assoc]

@[simp] theorem dilate_one (z : FourierSpace m) : dilate 1 z = z := by
  apply WithLp.ofLp_injective
  simp only [ofLp_dilate, one_smul, one_pow, one_mul]

theorem dilate_neg (r : ℝ) (z : FourierSpace m) : dilate r (-z) = -dilate r z := by
  apply WithLp.ofLp_injective
  simp only [ofLp_dilate, WithLp.ofLp_neg, Prod.fst_neg, Prod.snd_neg, smul_neg, mul_neg,
    Prod.neg_mk]

theorem norm_sq_dilate (r : ℝ) (z : FourierSpace m) :
    ‖dilate r z‖ ^ 2 = ‖(WithLp.ofLp z).1‖ ^ 2 * r ^ 2 + (WithLp.ofLp z).2 ^ 2 * r ^ 4 := by
  rw [norm_sq_eq, ofLp_dilate, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem coords_dilate_le (r : ℝ) (w : FourierSpace m) :
    ‖(WithLp.ofLp (dilate r w)).1‖ ≤ |r| * ‖w‖ ∧ |(WithLp.ofLp (dilate r w)).2| ≤ r ^ 2 * ‖w‖ := by
  rw [ofLp_dilate, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg r)]
  exact ⟨mul_le_mul_of_nonneg_left (norm_fst_le w) (abs_nonneg r),
    mul_le_mul_of_nonneg_left (abs_snd_le w) (sq_nonneg r)⟩

/-- Coordinates of a point whose inverse dilation is small. -/
theorem coords_le_of_norm_dilate_inv_le {r : ℝ} (hr : r ≠ 0) {z : FourierSpace m} {ρ : ℝ}
    (h : ‖dilate r⁻¹ z‖ ≤ ρ) :
    ‖(WithLp.ofLp z).1‖ ≤ |r| * ρ ∧ |(WithLp.ofLp z).2| ≤ r ^ 2 * ρ := by
  have hz : z = dilate r (dilate r⁻¹ z) := by rw [dilate_dilate, mul_inv_cancel₀ hr, dilate_one]
  obtain ⟨h1, h2⟩ := coords_dilate_le r (dilate r⁻¹ z)
  rw [← hz] at h1 h2
  exact ⟨h1.trans (mul_le_mul_of_nonneg_left h (abs_nonneg r)),
    h2.trans (mul_le_mul_of_nonneg_left h (sq_nonneg r))⟩

/-- Dilation as a real-linear map. -/
def dilateₗ (r : ℝ) : FourierSpace m →ₗ[ℝ] FourierSpace m :=
  ((WithLp.linearEquiv 2 ℝ (Spatial m × ℝ)).symm : (Spatial m × ℝ) →ₗ[ℝ] FourierSpace m) ∘ₗ
    ((r • LinearMap.id).prodMap ((r ^ 2) • LinearMap.id)) ∘ₗ
    ((WithLp.linearEquiv 2 ℝ (Spatial m × ℝ)).symm.symm : FourierSpace m →ₗ[ℝ] (Spatial m × ℝ))

theorem dilateₗ_apply (r : ℝ) (z : FourierSpace m) : dilateₗ r z = dilate r z := rfl

theorem det_dilateₗ (r : ℝ) : LinearMap.det (dilateₗ (m := m) r) = r ^ (m + 2) := by
  rw [dilateₗ, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_smul,
    LinearMap.det_id, LinearMap.det_id, Module.finrank_self,
    show Module.finrank ℝ (Spatial m) = m from finrank_euclideanSpace_fin]
  ring

theorem continuous_dilate₂ : Continuous fun x : ℝ × FourierSpace m => dilate x.1 x.2 :=
  (fourierCoordinatesHomeomorph m).symm.continuous.comp
    ((continuous_fst.smul (continuous_fst.comp
      ((fourierCoordinatesHomeomorph m).continuous.comp continuous_snd))).prodMk
      ((continuous_fst.pow 2).mul (continuous_snd.comp
        ((fourierCoordinatesHomeomorph m).continuous.comp continuous_snd))))

theorem continuous_dilate (r : ℝ) : Continuous (dilate (m := m) r) :=
  continuous_dilate₂.comp (continuous_const.prodMk continuous_id)

/-- Dilation as a continuous linear map. -/
def dilateL (r : ℝ) : FourierSpace m →L[ℝ] FourierSpace m :=
  ⟨dilateₗ r, continuous_dilate r⟩

theorem dilateL_apply (r : ℝ) (z : FourierSpace m) : dilateL r z = dilate r z := rfl

/-- Dilation by a nonzero factor as a continuous linear equivalence. -/
def dilateEquiv (r : ℝ) (hr : r ≠ 0) : FourierSpace m ≃L[ℝ] FourierSpace m :=
  ContinuousLinearEquiv.equivOfInverse (dilateL r) (dilateL r⁻¹)
    (fun z => by
      simp only [dilateL_apply, dilate_dilate, inv_mul_cancel₀ hr, dilate_one])
    (fun z => by
      simp only [dilateL_apply, dilate_dilate, mul_inv_cancel₀ hr, dilate_one])

theorem det_dilateEquiv (r : ℝ) (hr : r ≠ 0) :
    LinearMap.det (dilateEquiv (m := m) r hr : FourierSpace m →ₗ[ℝ] FourierSpace m) =
      r ^ (m + 2) :=
  det_dilateₗ r

/-- Reflection of the spatial coordinates, `(u,t) ↦ (-u,t)`. -/
def reflectₗ : FourierSpace m →ₗ[ℝ] FourierSpace m :=
  ((WithLp.linearEquiv 2 ℝ (Spatial m × ℝ)).symm : (Spatial m × ℝ) →ₗ[ℝ] FourierSpace m) ∘ₗ
    (((-1 : ℝ) • LinearMap.id).prodMap LinearMap.id) ∘ₗ
    ((WithLp.linearEquiv 2 ℝ (Spatial m × ℝ)).symm.symm : FourierSpace m →ₗ[ℝ] (Spatial m × ℝ))

theorem ofLp_reflectₗ (z : FourierSpace m) :
    WithLp.ofLp (reflectₗ z) = (-(WithLp.ofLp z).1, (WithLp.ofLp z).2) := by
  change ((-1 : ℝ) • (WithLp.ofLp z).1, (WithLp.ofLp z).2) = _
  rw [neg_one_smul]

theorem reflectₗ_reflectₗ (z : FourierSpace m) : reflectₗ (reflectₗ z) = z := by
  apply WithLp.ofLp_injective
  rw [ofLp_reflectₗ, ofLp_reflectₗ, neg_neg]

theorem det_reflectₗ : LinearMap.det (reflectₗ (m := m)) = (-1) ^ m := by
  rw [reflectₗ, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul,
    LinearMap.det_id, LinearMap.det_id,
    show Module.finrank ℝ (Spatial m) = m from finrank_euclideanSpace_fin]
  ring

theorem continuous_reflectₗ : Continuous (reflectₗ (m := m)) := by
  show Continuous fun z : FourierSpace m =>
    (WithLp.toLp 2 ((-1 : ℝ) • (WithLp.ofLp z).1, (WithLp.ofLp z).2) : FourierSpace m)
  exact (fourierCoordinatesHomeomorph m).symm.continuous.comp
    (((continuous_fst.comp (fourierCoordinatesHomeomorph m).continuous).const_smul (-1 : ℝ)).prodMk
      (continuous_snd.comp (fourierCoordinatesHomeomorph m).continuous))

/-- The spatial reflection as a continuous linear map. -/
def reflectL : FourierSpace m →L[ℝ] FourierSpace m := ⟨reflectₗ, continuous_reflectₗ⟩

/-- The spatial reflection as a continuous linear equivalence. -/
def reflectEquiv : FourierSpace m ≃L[ℝ] FourierSpace m :=
  ContinuousLinearEquiv.equivOfInverse reflectL reflectL reflectₗ_reflectₗ reflectₗ_reflectₗ

theorem norm_reflectₗ (z : FourierSpace m) : ‖reflectₗ z‖ = ‖z‖ := by
  have h : ‖reflectₗ z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [norm_sq_eq, norm_sq_eq, ofLp_reflectₗ, norm_neg]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

theorem dilate_reflectₗ (r : ℝ) (z : FourierSpace m) :
    dilate r (reflectₗ z) = reflectₗ (dilate r z) := by
  apply WithLp.ofLp_injective
  rw [ofLp_reflectₗ, ofLp_dilate, ofLp_dilate, ofLp_reflectₗ, smul_neg]

/-! ### Linear change of variables -/

theorem det_ne_zero_of_equiv (L : FourierSpace m ≃L[ℝ] FourierSpace m) :
    LinearMap.det (L : FourierSpace m →ₗ[ℝ] FourierSpace m) ≠ 0 :=
  (LinearEquiv.isUnit_det' (L : FourierSpace m ≃ₗ[ℝ] FourierSpace m)).ne_zero

theorem integral_comp_continuousLinearEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : FourierSpace m ≃L[ℝ] FourierSpace m) (g : FourierSpace m → E) :
    ∫ z, g (L z) = |LinearMap.det (L : FourierSpace m →ₗ[ℝ] FourierSpace m)|⁻¹ • ∫ z, g z := by
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (FourierSpace m))
    (det_ne_zero_of_equiv L)
  have hemb : MeasurableEmbedding ⇑(L : FourierSpace m →ₗ[ℝ] FourierSpace m) :=
    L.toHomeomorph.measurableEmbedding
  calc ∫ z, g (L z) = ∫ z, g ((L : FourierSpace m →ₗ[ℝ] FourierSpace m) z) := rfl
    _ = ∫ y, g y ∂(Measure.map ⇑(L : FourierSpace m →ₗ[ℝ] FourierSpace m) volume) :=
        (hemb.integral_map g).symm
    _ = _ := by
        rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]

theorem lintegral_comp_continuousLinearEquiv (L : FourierSpace m ≃L[ℝ] FourierSpace m)
    (g : FourierSpace m → ℝ≥0∞) :
    ∫⁻ z, g (L z) =
      ENNReal.ofReal |LinearMap.det (L : FourierSpace m →ₗ[ℝ] FourierSpace m)|⁻¹ * ∫⁻ z, g z := by
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (FourierSpace m))
    (det_ne_zero_of_equiv L)
  have hemb : MeasurableEmbedding ⇑(L : FourierSpace m →ₗ[ℝ] FourierSpace m) :=
    L.toHomeomorph.measurableEmbedding
  calc ∫⁻ z, g (L z) = ∫⁻ z, g ((L : FourierSpace m →ₗ[ℝ] FourierSpace m) z) := rfl
    _ = ∫⁻ y, g y ∂(Measure.map ⇑(L : FourierSpace m →ₗ[ℝ] FourierSpace m) volume) :=
        (hemb.lintegral_map g).symm
    _ = _ := by rw [hmap, lintegral_smul_measure, abs_inv, smul_eq_mul]

theorem integral_comp_dilate_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (g : FourierSpace m → E) :
    ∫ z, g (dilate r⁻¹ z) = r ^ (m + 2) • ∫ w, g w := by
  have h := integral_comp_continuousLinearEquiv (dilateEquiv (m := m) r⁻¹ (inv_ne_zero hr.ne')) g
  rw [det_dilateEquiv, abs_of_pos (show (0 : ℝ) < r⁻¹ ^ (m + 2) by positivity), inv_pow,
    inv_inv] at h
  exact h

theorem lintegral_comp_dilate_inv {r : ℝ} (hr : 0 < r) (g : FourierSpace m → ℝ≥0∞) :
    ∫⁻ z, g (dilate r⁻¹ z) = ENNReal.ofReal (r ^ (m + 2)) * ∫⁻ w, g w := by
  have h := lintegral_comp_continuousLinearEquiv (dilateEquiv (m := m) r⁻¹ (inv_ne_zero hr.ne')) g
  rw [det_dilateEquiv, abs_of_pos (show (0 : ℝ) < r⁻¹ ^ (m + 2) by positivity), inv_pow,
    inv_inv] at h
  exact h

theorem integral_comp_reflect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : FourierSpace m → E) : ∫ z, g (reflectₗ z) = ∫ z, g z := by
  have h := integral_comp_continuousLinearEquiv (reflectEquiv (m := m)) g
  have hd : LinearMap.det (reflectEquiv (m := m) : FourierSpace m →ₗ[ℝ] FourierSpace m) =
      (-1) ^ m := det_reflectₗ
  rw [hd, abs_pow, abs_neg, abs_one, one_pow, inv_one, one_smul] at h
  exact h

/-! ### The bump `φ` -/

/-- The unnormalized radial bump. -/
def rawBump (z : FourierSpace m) : ℝ := expNegInvGlue (1 / 4 - ‖z‖ ^ 2)

/-- Its total mass. -/
def bumpMass (m : ℕ) : ℝ := ∫ z : FourierSpace m, rawBump z

/-- The normalized one-variable profile `ρ`, so that `φ z = ρ (‖z‖²)`. -/
def profile (m : ℕ) (s : ℝ) : ℝ := (bumpMass m)⁻¹ * expNegInvGlue (1 / 4 - s)

/-- The fixed kernel `φ = φ_m`. -/
def bump (z : FourierSpace m) : ℝ := profile m (‖z‖ ^ 2)

/-- `φ_r(u,t) = r^(-k) φ(u/r, t/r²)`. -/
def kernel (r : ℝ) (z : FourierSpace m) : ℝ := (r ^ (m + 2))⁻¹ * bump (dilate r⁻¹ z)

/-- Closed form of `ψ_1`: `-k ρ(‖w‖²) - ρ'(‖w‖²) (2‖u‖² + 4t²)`. -/
def scaleKernelOne (w : FourierSpace m) : ℝ :=
  -((m : ℝ) + 2) * profile m (‖w‖ ^ 2) -
    deriv (profile m) (‖w‖ ^ 2) * (2 * ‖(WithLp.ofLp w).1‖ ^ 2 + 4 * (WithLp.ofLp w).2 ^ 2)

/-- `ψ_r(z) = r^(-k) ψ_1(u/r, t/r²)`; `hasDerivAt_kernel` identifies it with `r ∂_r φ_r`. -/
def scaleKernel (r : ℝ) (z : FourierSpace m) : ℝ :=
  (r ^ (m + 2))⁻¹ * scaleKernelOne (dilate r⁻¹ z)

theorem continuous_rawBump : Continuous (rawBump (m := m)) :=
  (expNegInvGlue.contDiff (n := 0)).continuous.comp (continuous_const.sub (continuous_norm.pow 2))

theorem rawBump_eq_zero {z : FourierSpace m} (hz : 1 / 2 ≤ ‖z‖) : rawBump z = 0 :=
  expNegInvGlue.zero_of_nonpos (by nlinarith)

theorem hasCompactSupport_rawBump : HasCompactSupport (rawBump (m := m)) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (1 / 2)) fun z hz =>
    rawBump_eq_zero (by rw [mem_closedBall_zero_iff, not_le] at hz; exact hz.le)

theorem bumpMass_pos : 0 < bumpMass m := by
  rw [bumpMass, integral_pos_iff_support_of_nonneg (f := rawBump (m := m))
    (fun z => expNegInvGlue.nonneg _)
    (continuous_rawBump.integrable_of_hasCompactSupport hasCompactSupport_rawBump)]
  refine (Metric.measure_ball_pos volume (0 : FourierSpace m)
    (by norm_num : (0 : ℝ) < 1 / 2)).trans_le (measure_mono fun z hz => ?_)
  rw [mem_ball_zero_iff] at hz
  exact (expNegInvGlue.pos_of_pos (by nlinarith [norm_nonneg z])).ne'

theorem contDiff_profile : ContDiff ℝ ∞ (profile m) := by
  unfold profile
  exact contDiff_const.mul (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

theorem profile_eq_zero {s : ℝ} (hs : 1 / 4 ≤ s) : profile m s = 0 := by
  rw [profile, expNegInvGlue.zero_of_nonpos (by linarith), mul_zero]

theorem deriv_profile_eq_zero {s : ℝ} (hs : 1 / 4 < s) : deriv (profile m) s = 0 := by
  have h : profile m =ᶠ[𝓝 s] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hs] with x hx using profile_eq_zero (le_of_lt hx)
  rw [h.deriv_eq, deriv_const]

theorem bump_eq (z : FourierSpace m) : bump z = (bumpMass m)⁻¹ * rawBump z := rfl

theorem contDiff_bump : ContDiff ℝ ∞ (bump (m := m)) :=
  contDiff_profile.comp (contDiff_norm_sq ℝ)

theorem bump_nonneg (z : FourierSpace m) : 0 ≤ bump z :=
  mul_nonneg (inv_nonneg.mpr bumpMass_pos.le) (expNegInvGlue.nonneg _)

theorem bump_eq_zero {z : FourierSpace m} (hz : 1 / 2 ≤ ‖z‖) : bump z = 0 := by
  rw [bump_eq, rawBump_eq_zero hz, mul_zero]

theorem integral_bump : ∫ z : FourierSpace m, bump z = 1 := by
  simp_rw [bump_eq]
  rw [integral_const_mul]
  exact inv_mul_cancel₀ bumpMass_pos.ne'

theorem hasCompactSupport_bump : HasCompactSupport (bump (m := m)) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (1 / 2)) fun z hz =>
    bump_eq_zero (by rw [mem_closedBall_zero_iff, not_le] at hz; exact hz.le)

/-- The support lies strictly inside the unit parabolic ball. -/
theorem tsupport_bump_subset : tsupport (bump (m := m)) ⊆ coordBall 0 1 := by
  have hsub : Function.support (bump (m := m)) ⊆ closedBall 0 (1 / 2) := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    by_contra h
    exact hz (bump_eq_zero (not_le.mp h).le)
  refine (closure_minimal hsub isClosed_closedBall).trans fun z hz => ?_
  rw [mem_closedBall_zero_iff] at hz
  simp only [coordBall, mem_ofPred_eq, WithLp.ofLp_zero, Prod.fst_zero, Prod.snd_zero, sub_zero,
    one_pow]
  exact ⟨by linarith [norm_fst_le z], by linarith [abs_snd_le z]⟩

/-- Invariance under every spatial linear isometry; in particular `φ` is even in each
spatial coordinate. -/
theorem bump_spatial_isometry (L : Spatial m ≃ₗᵢ[ℝ] Spatial m) (u : Spatial m) (t : ℝ) :
    bump (WithLp.toLp 2 (L u, t) : FourierSpace m) = bump (WithLp.toLp 2 (u, t)) := by
  simp only [bump]
  rw [norm_sq_eq, norm_sq_eq]
  simp only [LinearIsometryEquiv.norm_map]

theorem continuous_kernel (r : ℝ) : Continuous (kernel (m := m) r) :=
  continuous_const.mul (contDiff_bump.continuous.comp (continuous_dilate _))

theorem kernel_eq_zero {r : ℝ} {z : FourierSpace m} (hz : |r| + r ^ 2 < ‖z‖) :
    kernel r z = 0 := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [kernel]
  by_contra hne
  have hb : ‖dilate r⁻¹ z‖ ≤ 1 / 2 := by
    by_contra h
    exact hne (by rw [kernel, bump_eq_zero (not_le.mp h).le, mul_zero])
  obtain ⟨h1, h2⟩ := coords_le_of_norm_dilate_inv_le hr hb
  have := norm_le_of_coords z h1 h2
  nlinarith [abs_nonneg r, sq_nonneg r]

theorem hasCompactSupport_kernel (r : ℝ) : HasCompactSupport (kernel (m := m) r) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (|r| + r ^ 2)) fun z hz =>
    kernel_eq_zero (by rw [mem_closedBall_zero_iff, not_le] at hz; exact hz)

theorem integrable_kernel (r : ℝ) : Integrable (kernel (m := m) r) :=
  (continuous_kernel r).integrable_of_hasCompactSupport (hasCompactSupport_kernel r)

theorem integral_kernel {r : ℝ} (hr : 0 < r) : ∫ z : FourierSpace m, kernel r z = 1 := by
  simp only [kernel]
  rw [integral_const_mul, integral_comp_dilate_inv hr (bump (m := m)), integral_bump,
    smul_eq_mul, mul_one, inv_mul_cancel₀ (pow_ne_zero _ hr.ne')]

/-! ### Properties of `ψ_r` -/

theorem scaleKernelOne_eq_zero {w : FourierSpace m} (hw : 1 / 2 < ‖w‖) : scaleKernelOne w = 0 := by
  have hs : 1 / 4 < ‖w‖ ^ 2 := by nlinarith
  rw [scaleKernelOne, profile_eq_zero hs.le, deriv_profile_eq_zero hs]
  ring

theorem contDiff_scaleKernelOne : ContDiff ℝ ∞ (scaleKernelOne (m := m)) := by
  have h1 : ContDiff ℝ ∞ (fun w : FourierSpace m => profile m (‖w‖ ^ 2)) :=
    contDiff_profile.comp (contDiff_norm_sq ℝ)
  have hd : ContDiff ℝ ∞ (deriv (profile m)) := (contDiff_infty_iff_deriv.mp contDiff_profile).2
  have h2 : ContDiff ℝ ∞ (fun w : FourierSpace m => deriv (profile m) (‖w‖ ^ 2)) :=
    hd.comp (contDiff_norm_sq ℝ)
  have h3 : ContDiff ℝ ∞ (fun w : FourierSpace m => ‖(WithLp.ofLp w).1‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (WithLp.fstL 2 ℝ (Spatial m) ℝ).contDiff
  have h4 : ContDiff ℝ ∞ (fun w : FourierSpace m => (WithLp.ofLp w).2) :=
    (WithLp.sndL 2 ℝ (Spatial m) ℝ).contDiff
  exact (contDiff_const.mul h1).sub (h2.mul ((contDiff_const.mul h3).add
    (contDiff_const.mul (h4.pow 2))))

theorem hasCompactSupport_scaleKernelOne : HasCompactSupport (scaleKernelOne (m := m)) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (1 / 2)) fun w hw =>
    scaleKernelOne_eq_zero (by rw [mem_closedBall_zero_iff, not_le] at hw; exact hw)

theorem scaleKernel_one : scaleKernel 1 = scaleKernelOne (m := m) := by
  funext z
  simp [scaleKernel]

/-- Points in the support of `ψ_r`. -/
theorem coords_of_scaleKernel_ne_zero {r : ℝ} {z : FourierSpace m} (hne : scaleKernel r z ≠ 0) :
    r ≠ 0 ∧ ‖(WithLp.ofLp z).1‖ ≤ |r| * (1 / 2) ∧ |(WithLp.ofLp z).2| ≤ r ^ 2 * (1 / 2) := by
  have hr : r ≠ 0 := by
    rintro rfl
    exact hne (by simp [scaleKernel])
  have hb : ‖dilate r⁻¹ z‖ ≤ 1 / 2 := by
    by_contra h
    exact hne (by rw [scaleKernel, scaleKernelOne_eq_zero (not_le.mp h), mul_zero])
  exact ⟨hr, coords_le_of_norm_dilate_inv_le hr hb⟩

theorem scaleKernel_eq_zero {r : ℝ} {z : FourierSpace m} (hz : |r| + r ^ 2 < ‖z‖) :
    scaleKernel r z = 0 := by
  by_contra hne
  obtain ⟨-, h1, h2⟩ := coords_of_scaleKernel_ne_zero hne
  have := norm_le_of_coords z h1 h2
  nlinarith [abs_nonneg r, sq_nonneg r]

/-- `ψ_r = r ∂_r φ_r` pointwise. -/
theorem hasDerivAt_kernel {r : ℝ} (hr : 0 < r) (z : FourierSpace m) :
    HasDerivAt (fun s => kernel s z) (scaleKernel r z / r) r := by
  have hr0 : r ≠ 0 := hr.ne'
  have hfun : (fun s => kernel s z) = fun s => (s ^ (m + 2))⁻¹ *
      profile m (‖(WithLp.ofLp z).1‖ ^ 2 * s⁻¹ ^ 2 + (WithLp.ofLp z).2 ^ 2 * s⁻¹ ^ 4) := by
    funext s
    rw [kernel, bump, norm_sq_dilate]
  have hQ := (((hasDerivAt_inv hr0).pow 2).const_mul (‖(WithLp.ofLp z).1‖ ^ 2)).add
    (((hasDerivAt_inv hr0).pow 4).const_mul ((WithLp.ofLp z).2 ^ 2))
  have h := ((hasDerivAt_pow (m + 2) r).inv (pow_ne_zero _ hr0)).mul
    (((contDiff_infty_iff_deriv.mp (contDiff_profile (m := m))).1 _).hasDerivAt.comp r hQ)
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, Pi.inv_apply, Pi.add_apply, Pi.pow_apply,
    show m + 2 - 1 = m + 1 by omega, show (2 : ℕ) - 1 = 1 from rfl, show (4 : ℕ) - 1 = 3 from rfl,
    pow_one, scaleKernel, scaleKernelOne, norm_sq_dilate, ofLp_dilate, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  generalize profile m (‖(WithLp.ofLp z).1‖ ^ 2 * r⁻¹ ^ 2 + (WithLp.ofLp z).2 ^ 2 * r⁻¹ ^ 4) = P
  generalize deriv (profile m)
    (‖(WithLp.ofLp z).1‖ ^ 2 * r⁻¹ ^ 2 + (WithLp.ofLp z).2 ^ 2 * r⁻¹ ^ 4) = P'
  push_cast
  field_simp
  ring

theorem contDiff_scaleKernel (r : ℝ) : ContDiff ℝ ∞ (scaleKernel (m := m) r) :=
  contDiff_const.mul (contDiff_scaleKernelOne.comp (dilateL (m := m) r⁻¹).contDiff)

theorem continuous_scaleKernel (r : ℝ) : Continuous (scaleKernel (m := m) r) :=
  (contDiff_scaleKernel r).continuous

theorem hasCompactSupport_scaleKernel (r : ℝ) : HasCompactSupport (scaleKernel (m := m) r) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (|r| + r ^ 2)) fun z hz =>
    scaleKernel_eq_zero (by rw [mem_closedBall_zero_iff, not_le] at hz; exact hz)

theorem integrable_scaleKernel (r : ℝ) : Integrable (scaleKernel (m := m) r) :=
  (continuous_scaleKernel r).integrable_of_hasCompactSupport (hasCompactSupport_scaleKernel r)

theorem tsupport_scaleKernel_subset {r : ℝ} (hr : 0 < r) :
    tsupport (scaleKernel (m := m) r) ⊆ coordBall 0 r := by
  have hclosed : IsClosed {z : FourierSpace m | ‖(WithLp.ofLp z).1‖ ≤ r * (1 / 2) ∧
      |(WithLp.ofLp z).2| ≤ r ^ 2 * (1 / 2)} :=
    (isClosed_le (WithLp.fstL 2 ℝ (Spatial m) ℝ).continuous.norm continuous_const).inter
      (isClosed_le (WithLp.sndL 2 ℝ (Spatial m) ℝ).continuous.abs continuous_const)
  have hsub : Function.support (scaleKernel (m := m) r) ⊆ {z : FourierSpace m |
      ‖(WithLp.ofLp z).1‖ ≤ r * (1 / 2) ∧ |(WithLp.ofLp z).2| ≤ r ^ 2 * (1 / 2)} := by
    intro z hz
    obtain ⟨-, h1, h2⟩ := coords_of_scaleKernel_ne_zero hz
    rw [abs_of_pos hr] at h1
    exact ⟨h1, h2⟩
  refine (closure_minimal hsub hclosed).trans fun z hz => ?_
  obtain ⟨h1, h2⟩ := hz
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  simp only [coordBall, mem_ofPred_eq, WithLp.ofLp_zero, Prod.fst_zero, Prod.snd_zero, sub_zero]
  exact ⟨by linarith, by linarith⟩

theorem scaleKernelOne_neg (w : FourierSpace m) : scaleKernelOne (-w) = scaleKernelOne w := by
  simp only [scaleKernelOne, norm_neg, WithLp.ofLp_neg, Prod.fst_neg, Prod.snd_neg, neg_sq]

theorem scaleKernel_neg (r : ℝ) (z : FourierSpace m) : scaleKernel r (-z) = scaleKernel r z := by
  rw [scaleKernel, scaleKernel, dilate_neg, scaleKernelOne_neg]

theorem scaleKernelOne_reflect (w : FourierSpace m) :
    scaleKernelOne (reflectₗ w) = scaleKernelOne w := by
  simp only [scaleKernelOne, norm_reflectₗ, ofLp_reflectₗ, norm_neg]

theorem scaleKernel_reflect (r : ℝ) (z : FourierSpace m) :
    scaleKernel r (reflectₗ z) = scaleKernel r z := by
  rw [scaleKernel, scaleKernel, dilate_reflectₗ, scaleKernelOne_reflect]

/-- Every first spatial moment vanishes. -/
theorem integral_linear_mul_scaleKernel (r : ℝ) (B : Spatial m →L[ℝ] ℝ) :
    ∫ z : FourierSpace m, B (WithLp.ofLp z).1 * scaleKernel r z = 0 := by
  have h := integral_comp_reflect (m := m) (fun z => B (WithLp.ofLp z).1 * scaleKernel r z)
  simp only [ofLp_reflectₗ, map_neg, scaleKernel_reflect, neg_mul, integral_neg] at h
  linarith

theorem integral_coord_mul_scaleKernel (r : ℝ) (i : Fin m) :
    ∫ z : FourierSpace m, (WithLp.ofLp z).1 i * scaleKernel r z = 0 :=
  integral_linear_mul_scaleKernel r (EuclideanSpace.proj i)

/-- `‖ψ_r‖₂² = r^(-k) ‖ψ_1‖₂²`. -/
theorem integral_sq_scaleKernel {r : ℝ} (hr : 0 < r) :
    ∫ z : FourierSpace m, scaleKernel r z ^ 2 =
      (r ^ (m + 2))⁻¹ * ∫ w : FourierSpace m, scaleKernelOne w ^ 2 := by
  simp only [scaleKernel, mul_pow]
  rw [integral_const_mul, show (∫ z : FourierSpace m, scaleKernelOne (dilate r⁻¹ z) ^ 2) =
      r ^ (m + 2) • ∫ w : FourierSpace m, scaleKernelOne w ^ 2 from
    integral_comp_dilate_inv hr (fun w => scaleKernelOne w ^ 2), smul_eq_mul]
  have hk : (r ^ (m + 2)) ≠ 0 := pow_ne_zero _ hr.ne'
  field_simp

/-- Differentiation in the scale under a bounded continuous weight, e.g. a Fourier character. -/
theorem hasDerivAt_integral_kernel {r : ℝ} (hr : 0 < r) {e : FourierSpace m → ℂ}
    (he : Continuous e) (hb : ∀ z, ‖e z‖ ≤ 1) :
    HasDerivAt (fun s => ∫ z, e z * (kernel s z : ℂ))
      ((∫ z, e z * (scaleKernel r z : ℂ)) / r) r := by
  obtain ⟨M1, hM1⟩ := contDiff_scaleKernelOne.continuous.bounded_above_of_compact_support
    (hasCompactSupport_scaleKernelOne (m := m))
  have hM1n : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hball : ball r (r / 2) ∈ 𝓝 r := ball_mem_nhds r (by linarith)
  have hpos : ∀ x ∈ ball r (r / 2), r / 2 < x ∧ x < 3 * r / 2 := by
    intro x hx
    rw [Real.ball_eq_Ioo] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s z => e z * (kernel s z : ℂ))
    (F' := fun s z => e z * ((scaleKernel s z / s : ℝ) : ℂ))
    (bound := (closedBall (0 : FourierSpace m) (3 * r / 2 + (3 * r / 2) ^ 2)).indicator
      fun _ => ((r / 2) ^ (m + 2))⁻¹ * M1 * (2 / r)) hball
    (Eventually.of_forall fun s =>
      (he.mul (Complex.continuous_ofReal.comp (continuous_kernel s))).aestronglyMeasurable)
    ((integrable_kernel r).norm.mono'
      (he.mul (Complex.continuous_ofReal.comp (continuous_kernel r))).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [norm_mul, Complex.norm_real]
        exact mul_le_of_le_one_left (norm_nonneg _) (hb z)))
    ((he.mul (Complex.continuous_ofReal.comp
      ((continuous_scaleKernel r).div_const r))).aestronglyMeasurable)
    (Eventually.of_forall fun z x hx => by
      obtain ⟨hx1, hx2⟩ := hpos x hx
      have hx0 : 0 < x := by linarith
      rw [norm_mul, Complex.norm_real]
      refine (mul_le_of_le_one_left (norm_nonneg _) (hb z)).trans ?_
      by_cases hz : z ∈ closedBall (0 : FourierSpace m) (3 * r / 2 + (3 * r / 2) ^ 2)
      · rw [indicator_of_mem hz, Real.norm_eq_abs, abs_div, abs_of_pos hx0, scaleKernel,
          abs_mul, abs_inv, abs_of_pos (by positivity : 0 < x ^ (m + 2))]
        have h1 : |scaleKernelOne (dilate x⁻¹ z)| ≤ M1 := by
          simpa [Real.norm_eq_abs] using hM1 (dilate x⁻¹ z)
        have h2 : (x ^ (m + 2))⁻¹ ≤ ((r / 2) ^ (m + 2))⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hx1.le _)
        have h3 : 1 / x ≤ 2 / r := by
          rw [div_le_div_iff₀ hx0 hr]; linarith
        calc (x ^ (m + 2))⁻¹ * |scaleKernelOne (dilate x⁻¹ z)| / x
            = (x ^ (m + 2))⁻¹ * |scaleKernelOne (dilate x⁻¹ z)| * (1 / x) := by ring
          _ ≤ ((r / 2) ^ (m + 2))⁻¹ * M1 * (2 / r) := by gcongr
      · rw [indicator_of_notMem hz]
        rw [mem_closedBall_zero_iff, not_le] at hz
        have hz' : |x| + x ^ 2 < ‖z‖ := by
          rw [abs_of_pos hx0]
          nlinarith
        rw [scaleKernel_eq_zero hz', zero_div, norm_zero])
    ((integrableOn_const (measure_closedBall_lt_top (x := (0 : FourierSpace m))).ne).integrable_indicator
      measurableSet_closedBall)
    (Eventually.of_forall fun z x hx =>
      ((hasDerivAt_kernel (by linarith [(hpos x hx).1]) z).ofReal_comp).const_mul (e z))
  have he' : (fun z => e z * ((scaleKernel r z / r : ℝ) : ℂ)) =
      fun z => e z * (scaleKernel r z : ℂ) / (r : ℂ) := by
    funext z
    push_cast
    ring
  have h2 := key.2
  rw [he', integral_div] at h2
  exact h2

theorem integral_scaleKernel {r : ℝ} (hr : 0 < r) : ∫ z : FourierSpace m, scaleKernel r z = 0 := by
  have hd := hasDerivAt_integral_kernel (m := m) hr (e := fun _ => (1 : ℂ)) continuous_const
    (fun _ => by simp)
  have hconst : (fun s => ∫ z : FourierSpace m, (1 : ℂ) * (kernel s z : ℂ)) =ᶠ[𝓝 r]
      fun _ => (1 : ℂ) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    simp only [one_mul]
    rw [integral_complex_ofReal, integral_kernel hs, Complex.ofReal_one]
  have h0 := (hasDerivAt_const r (1 : ℂ)).congr_of_eventuallyEq hconst
  have hu := hd.unique h0
  simp only [one_mul, integral_complex_ofReal, div_eq_zero_iff, Complex.ofReal_eq_zero] at hu
  rcases hu with h | h
  · exact h
  · exact absurd h hr.ne'

end ParabolicRectifiability.FourierAffine
