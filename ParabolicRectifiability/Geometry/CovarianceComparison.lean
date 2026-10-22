import ParabolicRectifiability.Geometry.Covariance

/-!
# Affine comparison on one noncollapsed source

The covariance, mass, barycenter and both errors belong to the same bounded
source. Competing planes are arbitrary. Larger fitting measures enter only
through domination and finite bounds on nonnegative extended integrals.
-/
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace ParabolicRectifiability
open MeasureTheory Set
open scoped ENNReal

variable {n l : ℕ}

/-- Operator difference plus the affine anchor difference at the testing scale. -/
def affineComparison (L L' : AffineSpatialPlane n l) (x : Spatial n) (r : ℝ) : ℝ :=
  ‖L.linearProjection - L'.linearProjection‖ + r⁻¹ * ‖L.projection x - L'.projection x‖

theorem affineComparison_nonneg (L L' : AffineSpatialPlane n l) (x : Spatial n)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ affineComparison L L' x r :=
  add_nonneg (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr hr) (norm_nonneg _))

/-- Anchor and radius change, with an explicit coefficient. -/
theorem affineComparison_change_anchor_radius (L L' : AffineSpatialPlane n l)
    (x y : Spatial n) (r s A : ℝ) (hr : 0 < r) (hs : 0 < s) (_hA : 0 ≤ A)
    (hxy : ‖y - x‖ ≤ A * r) :
    affineComparison L L' y s ≤ (1 + (A + 1) * r / s) * affineComparison L L' x r := by
  let d := affineComparison L L' x r
  have hd : ‖L.linearProjection - L'.linearProjection‖ ≤ d :=
    le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg _))
  have hx : ‖L.projection x - L'.projection x‖ ≤ r * d := by
    dsimp [d, affineComparison]
    simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    exact le_add_of_nonneg_left (mul_nonneg hr.le (norm_nonneg _))
  have hy : ‖L.projection y - L'.projection y‖ ≤ (A + 1) * r * d := by
    calc
      _ ≤ ‖L.projection x - L'.projection x‖ +
          ‖L.linearProjection - L'.linearProjection‖ * ‖y - x‖ :=
        L.affine_anchor_inequality L' x y
      _ ≤ r * d + d * (A * r) := add_le_add hx
        (mul_le_mul hd hxy (norm_nonneg _) (affineComparison_nonneg L L' x hr.le))
      _ = _ := by ring
  calc
    _ ≤ d + s⁻¹ * ((A + 1) * r * d) := add_le_add hd
      (mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hs.le))
    _ = _ := by dsimp [d]; ring

/-- The numerical step retains 36 and does not require positive error. -/
theorem two_mul_add_sqrt_le_six_mul_sqrt {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hDE : D ^ 2 ≤ 4 * E) : 2 * D + Real.sqrt (2 * E) ≤ 6 * Real.sqrt E := by
  have hs := Real.sq_sqrt hE
  have ht := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE)
  have h1 : D ≤ 2 * Real.sqrt E := by nlinarith [Real.sqrt_nonneg E]
  have h2 : Real.sqrt (2 * E) ≤ 2 * Real.sqrt E := by
    nlinarith [Real.sqrt_nonneg E, Real.sqrt_nonneg (2 * E)]
  linarith

namespace SpatialSource
variable (S : SpatialSource n)

theorem eigenvalue_le_trace (i : Fin n) : S.eigenvalue i ≤ spatialTrace S.covariance := by
  rw [S.trace_covariance_eq_sum]
  exact Finset.single_le_sum (fun j _ => S.eigenvalue_nonneg j) (Finset.mem_univ i)

theorem eigenvalue_lower_le_mass_radius_sq (hl0 : 1 ≤ l) (hln : l ≤ n)
    (lambda : ℝ) (hle : lambda ≤ S.eigenvalue ⟨l - 1, by omega⟩) :
    lambda ≤ S.mass * S.radius ^ 2 :=
  hle.trans ((S.eigenvalue_le_trace _).trans S.trace_covariance_le)

theorem mass_pos_of_eigenvalue_lower (hl0 : 1 ≤ l) (hln : l ≤ n)
    (lambda : ℝ) (hp : 0 < lambda) (hle : lambda ≤ S.eigenvalue ⟨l - 1, by omega⟩) :
    0 < S.mass := by
  have h := S.eigenvalue_lower_le_mass_radius_sq hl0 hln lambda hle
  exact pos_of_mul_pos_left (hp.trans_le h) (sq_nonneg _)

theorem mass_lower_of_eigenvalue_lower (hl0 : 1 ≤ l) (hln : l ≤ n)
    (k : ℕ) (_hk : 1 ≤ k) (a : ℝ) (_ha : 0 < a)
    (hle : a * S.radius ^ (k + 2) ≤ S.eigenvalue ⟨l - 1, by omega⟩) :
    a * S.radius ^ k ≤ S.mass := by
  have h := S.eigenvalue_lower_le_mass_radius_sq hl0 hln _ hle
  rw [pow_add, ← mul_assoc] at h
  exact (mul_le_mul_iff_right₀ (pow_pos S.radius_pos 2)).mp (by
    simpa only [mul_comm] using h)

theorem trace_complement_covariance_le_fittingError (L : AffineSpatialPlane n l) :
    spatialTrace ((1 - L.linearProjection) * S.covariance) ≤ S.fittingError L := by
  rw [S.fittingError_variance]
  exact le_add_of_nonneg_right (mul_nonneg S.mass_nonneg (sq_nonneg _))

theorem mass_mul_barycenter_residual_sq_le (L : AffineSpatialPlane n l) :
    S.mass * ‖S.barycenter - L.projection S.barycenter‖ ^ 2 ≤ S.fittingError L := by
  rw [S.fittingError_variance]
  exact le_add_of_nonneg_left (spatialTrace_complement_mul_nonneg _ _
    L.linearProjection_isStarProjection S.covariance_isPositive)

theorem barycenter_residual_sq_le (L : AffineSpatialPlane n l) (hM : 0 < S.mass) :
    ‖S.barycenter - L.projection S.barycenter‖ ^ 2 ≤ S.fittingError L / S.mass := by
  apply (le_div_iff₀ hM).mpr
  simpa only [mul_comm] using S.mass_mul_barycenter_residual_sq_le L

/-- Arbitrary competitors are compared through the actual top-l source plane. -/
theorem linearProjection_sub_sq_le (hl0 : 1 ≤ l) (hln : l ≤ n)
    (lambda : ℝ) (hp : 0 < lambda) (hle : lambda ≤ S.eigenvalue ⟨l - 1, by omega⟩)
    (L L' : AffineSpatialPlane n l) :
    ‖L.linearProjection - L'.linearProjection‖ ^ 2 ≤
      4 * (S.fittingError L + S.fittingError L') / lambda := by
  let W := S.topPlane l hln
  have hLower := S.covariance_sub_topProjection_isPositive l hl0 hln lambda hp hle
  have hfit (K : AffineSpatialPlane n l) :
      ‖K.linearProjection - W.linearProjection‖ ^ 2 ≤ (2 / lambda) * S.fittingError K :=
    (K.projection_comparison_of_positive W S.covariance S.covariance_isSelfAdjoint
      lambda hp hLower).trans (mul_le_mul_of_nonneg_left
        (S.trace_complement_covariance_le_fittingError K) (by positivity))
  have ht : ‖L.linearProjection - L'.linearProjection‖ ≤
      ‖L.linearProjection - W.linearProjection‖ + ‖L'.linearProjection - W.linearProjection‖ := by
    calc
      _ = ‖(L.linearProjection - W.linearProjection) -
          (L'.linearProjection - W.linearProjection)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have ht2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
  have h1 := hfit L
  have h2 := hfit L'
  have he : 4 * (S.fittingError L + S.fittingError L') / lambda =
      2 * ((2 / lambda) * S.fittingError L) + 2 * ((2 / lambda) * S.fittingError L') := by ring
  rw [he]
  nlinarith [sq_nonneg (‖L.linearProjection - W.linearProjection‖ -
    ‖L'.linearProjection - W.linearProjection‖)]

theorem scaled_barycenter_residual_le_sqrt (L : AffineSpatialPlane n l)
    (lambda : ℝ) (hp : 0 < lambda) (hsize : lambda ≤ S.mass * S.radius ^ 2) :
    S.radius⁻¹ * ‖S.barycenter - L.projection S.barycenter‖ ≤
      Real.sqrt (S.fittingError L / lambda) := by
  have hmul := S.mass_mul_barycenter_residual_sq_le L
  have hnum : lambda * ‖S.barycenter - L.projection S.barycenter‖ ^ 2 ≤
      S.fittingError L * S.radius ^ 2 := by
    calc
      _ ≤ (S.mass * S.radius ^ 2) * ‖S.barycenter - L.projection S.barycenter‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsize (sq_nonneg _)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hmul (sq_nonneg S.radius)]
  have hsq : (S.radius⁻¹ * ‖S.barycenter - L.projection S.barycenter‖) ^ 2 ≤
      S.fittingError L / lambda := by
    apply (le_div_iff₀ hp).mpr
    calc
      _ = (lambda * ‖S.barycenter - L.projection S.barycenter‖ ^ 2) / S.radius ^ 2 := by
        simp only [mul_pow, inv_pow, div_eq_mul_inv]; ring
      _ ≤ _ := (div_le_iff₀ (pow_pos S.radius_pos 2)).mpr hnum
  nlinarith [Real.sq_sqrt (div_nonneg (S.fittingError_nonneg L) hp.le),
    Real.sqrt_nonneg (S.fittingError L / lambda)]

theorem scaled_center_anchor_le (hl0 : 1 ≤ l) (hln : l ≤ n)
    (lambda : ℝ) (hp : 0 < lambda) (hle : lambda ≤ S.eigenvalue ⟨l - 1, by omega⟩)
    (L L' : AffineSpatialPlane n l) :
    S.radius⁻¹ * ‖L.projection S.center.1 - L'.projection S.center.1‖ ≤
      ‖L.linearProjection - L'.linearProjection‖ + Real.sqrt (S.fittingError L / lambda) +
        Real.sqrt (S.fittingError L' / lambda) := by
  have hM := S.mass_pos_of_eigenvalue_lower hl0 hln lambda hp hle
  have hsize := S.eigenvalue_lower_le_mass_radius_sq hl0 hln lambda hle
  have hbar : ‖L.projection S.barycenter - L'.projection S.barycenter‖ ≤
      ‖S.barycenter - L.projection S.barycenter‖ +
        ‖S.barycenter - L'.projection S.barycenter‖ := by
    simpa only [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub
      (L.projection S.barycenter) S.barycenter (L'.projection S.barycenter)
  have hcenter : ‖S.center.1 - S.barycenter‖ ≤ S.radius := by
    simpa only [norm_sub_rev] using S.barycenter_mem_ball hM
  have ha := (L.affine_anchor_inequality L' S.barycenter S.center.1).trans
    (add_le_add hbar (mul_le_mul_of_nonneg_left hcenter (norm_nonneg _)))
  have h := mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr S.radius_pos.le)
  have hcancel : S.radius⁻¹ * (‖S.barycenter - L.projection S.barycenter‖ +
        ‖S.barycenter - L'.projection S.barycenter‖ +
        ‖L.linearProjection - L'.linearProjection‖ * S.radius) =
      S.radius⁻¹ * ‖S.barycenter - L.projection S.barycenter‖ +
      S.radius⁻¹ * ‖S.barycenter - L'.projection S.barycenter‖ +
      ‖L.linearProjection - L'.linearProjection‖ := by field_simp [S.radius_pos.ne']
  rw [hcancel] at h
  linarith [S.scaled_barycenter_residual_le_sqrt L lambda hp hsize,
    S.scaled_barycenter_residual_le_sqrt L' lambda hp hsize]

/-- Exact constant 36, including zero fitting error. -/
theorem affineComparison_sq_le (hl0 : 1 ≤ l) (hln : l ≤ n)
    (lambda : ℝ) (hp : 0 < lambda) (hle : lambda ≤ S.eigenvalue ⟨l - 1, by omega⟩)
    (L L' : AffineSpatialPlane n l) :
    affineComparison L L' S.center.1 S.radius ^ 2 ≤
      36 * (S.fittingError L + S.fittingError L') / lambda := by
  let E := (S.fittingError L + S.fittingError L') / lambda
  have hE : 0 ≤ E := div_nonneg (add_nonneg (S.fittingError_nonneg L)
    (S.fittingError_nonneg L')) hp.le
  have hD : ‖L.linearProjection - L'.linearProjection‖ ^ 2 ≤ 4 * E := by
    simpa only [E, mul_div_assoc] using S.linearProjection_sub_sq_le hl0 hln lambda hp hle L L'
  have hs : Real.sqrt (S.fittingError L / lambda) + Real.sqrt (S.fittingError L' / lambda) ≤
      Real.sqrt (2 * E) := by
    have h1 := Real.sq_sqrt (div_nonneg (S.fittingError_nonneg L) hp.le)
    have h2 := Real.sq_sqrt (div_nonneg (S.fittingError_nonneg L') hp.le)
    have h3 := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE)
    have he : S.fittingError L / lambda + S.fittingError L' / lambda = E := by dsimp [E]; ring
    nlinarith [sq_nonneg (Real.sqrt (S.fittingError L / lambda) -
      Real.sqrt (S.fittingError L' / lambda)), Real.sqrt_nonneg (2 * E),
      Real.sqrt_nonneg (S.fittingError L / lambda), Real.sqrt_nonneg (S.fittingError L' / lambda)]
  have htotal : affineComparison L L' S.center.1 S.radius ≤ 6 * Real.sqrt E := by
    have ha := S.scaled_center_anchor_le hl0 hln lambda hp hle L L'
    have hn := two_mul_add_sqrt_le_six_mul_sqrt (norm_nonneg _) hE hD
    dsimp [affineComparison]
    linarith
  have hsq := pow_le_pow_left₀ (affineComparison_nonneg L L' S.center.1 S.radius_pos.le) htotal 2
  have he := Real.sq_sqrt hE
  rw [mul_div_assoc]
  change _ ≤ 36 * E
  nlinarith

/-- The noncollapse hypothesis and both competing errors use this one source. -/
theorem same_source_comparison (hl0 : 1 ≤ l) (hln : l ≤ n) (k : ℕ) (hk : 1 ≤ k)
    (a : ℝ) (ha : 0 < a)
    (hle : a * S.radius ^ (k + 2) ≤ S.eigenvalue ⟨l - 1, by omega⟩)
    (L L' : AffineSpatialPlane n l) :
    a * S.radius ^ k ≤ S.mass ∧
    affineComparison L L' S.center.1 S.radius ^ 2 ≤
      36 * (S.fittingError L + S.fittingError L') / (a * S.radius ^ (k + 2)) :=
  ⟨S.mass_lower_of_eigenvalue_lower hl0 hln k hk a ha hle,
    S.affineComparison_sq_le hl0 hln _ (mul_pos ha (pow_pos S.radius_pos _)) hle L L'⟩

end SpatialSource

/-- Nonnegative fitting integral on an arbitrary measure, possibly of infinite mass. -/
def spatialFittingIntegral (mu : Measure (Space n)) (L : AffineSpatialPlane n l) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (‖z.1 - L.projection z.1‖ ^ 2) ∂mu

theorem spatialFittingIntegral_eq_infDist (mu : Measure (Space n))
    (L : AffineSpatialPlane n l) :
    spatialFittingIntegral mu L = ∫⁻ z, ENNReal.ofReal ((Metric.infDist z.1 L.toSet) ^ 2) ∂mu := by
  simp_rw [L.spatial_infDist_eq]
  rfl

theorem spatialFittingIntegral_mono_measure (L : AffineSpatialPlane n l)
    {mu nu : Measure (Space n)} (h : mu ≤ nu) :
    spatialFittingIntegral mu L ≤ spatialFittingIntegral nu L := lintegral_mono' h le_rfl

theorem spatialFittingIntegral_ne_top_of_le (mu : Measure (Space n))
    (L : AffineSpatialPlane n l) (B : ℝ) (h : spatialFittingIntegral mu L ≤ ENNReal.ofReal B) :
    spatialFittingIntegral mu L ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

namespace SpatialSource
variable (S : SpatialSource n)

theorem ofReal_fittingError (L : AffineSpatialPlane n l) :
    ENNReal.ofReal (S.fittingError L) = spatialFittingIntegral S.measure L :=
  ofReal_integral_eq_lintegral_ofReal (S.integrable_fittingError L)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)

/-- Domination uses extended integrals on the larger source; only the common
bounded source's already integrable error is converted to a real value. -/
theorem fittingError_le_of_measure_le (L : AffineSpatialPlane n l)
    (mu : Measure (Space n)) (hmu : S.measure ≤ mu) (B : ℝ) (hB : 0 ≤ B)
    (hfit : spatialFittingIntegral mu L ≤ ENNReal.ofReal B) : S.fittingError L ≤ B := by
  have h := (spatialFittingIntegral_mono_measure L hmu).trans hfit
  rw [← S.ofReal_fittingError L] at h
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp h

/-- Different fitting scales, with covariance still taken from the single
common source dominated by both fitting measures. -/
theorem affineComparison_sq_le_of_dominated (hl0 : 1 ≤ l) (hln : l ≤ n)
    (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 0 < a)
    (hle : a * S.radius ^ (k + 2) ≤ S.eigenvalue ⟨l - 1, by omega⟩)
    (Lc Lp : AffineSpatialPlane n l) (mu_c mu_p : Measure (Space n))
    (hc : S.measure ≤ mu_c) (hp : S.measure ≤ mu_p)
    (R b_c b_p : ℝ) (hR : 0 < R) (hbc : 0 ≤ b_c) (hbp : 0 ≤ b_p)
    (hfc : spatialFittingIntegral mu_c Lc ≤ ENNReal.ofReal (S.radius ^ (k + 2) * b_c))
    (hfp : spatialFittingIntegral mu_p Lp ≤ ENNReal.ofReal (R ^ (k + 2) * b_p)) :
    affineComparison Lc Lp S.center.1 S.radius ^ 2 ≤
      36 / a * (b_c + (R / S.radius) ^ (k + 2) * b_p) := by
  have hec := S.fittingError_le_of_measure_le Lc mu_c hc _
    (mul_nonneg (pow_nonneg S.radius_pos.le _) hbc) hfc
  have hep := S.fittingError_le_of_measure_le Lp mu_p hp _
    (mul_nonneg (pow_nonneg hR.le _) hbp) hfp
  calc
    _ ≤ 36 * (S.fittingError Lc + S.fittingError Lp) / (a * S.radius ^ (k + 2)) :=
      (S.same_source_comparison hl0 hln k hk a ha hle Lc Lp).2
    _ ≤ 36 * (S.radius ^ (k + 2) * b_c + R ^ (k + 2) * b_p) /
        (a * S.radius ^ (k + 2)) := by
          gcongr
          exact mul_nonneg ha.le (pow_nonneg S.radius_pos.le _)
    _ = _ := by rw [div_pow]; field_simp [S.radius_pos.ne', ha.ne']

end SpatialSource
end ParabolicRectifiability
