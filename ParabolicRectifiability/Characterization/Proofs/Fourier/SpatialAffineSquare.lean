import ParabolicRectifiability.Characterization.Proofs.Fourier.SpatialAffineGlobal
import ParabolicRectifiability.Characterization.Proofs.Fourier.SpatialAffineEnergy

/-! # The spatial affine square of a Lipschitz map

This file proves `ba1_spatial_affine_square_proof : SpatialAffineSquareStatement`: the square
function of best affine approximation errors of an `L`-Lipschitz map `F : ℝ^k → ℝ^d` over
`B(b,R) × (0,R)` is at most `C L² R^k`.

**Route.** Cut off `F - F(b)` by the Lipschitz cutoff
`χ(v) = max(0, min(1, 3 - |v - b|/R))`, equal to `1` on `B(b,2R)` and `0` off `B(b,3R)`:
`G = χ (F - F(b))` (`b1sas_field`). Then
* `G = F - F(b)` on every testing ball `B(u,s)`, `u ∈ B(b,R)`, `s < R`, so the affine errors of
  `F` are at most those of `G` (`b1sas_errorSq_le_field`; constants are affine);
* `|G(x) - G(y)| ≤ 4L|x - y|` and `G = 0` off `B(b,3R)`, so every coordinate satisfies
  `∫ |G_i(x + t e_j) - G_i(x)|² dx ≤ 32 L² (3R)^k |B(0,1)| t²` (`b1sas_field_translate_le`),
  hence `∫ |ξ|² |Ĝ_i|² ≤ 2k 3^k |B(0,1)| L² R^k` (`b1sas_fourierEnergy_le`);
* the global estimate `b1sas_spatial_global` concludes.
No dilation or translation of the statement is needed: the global estimate is scale free.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology FourierTransform

namespace ParabolicRectifiability.Characterization

variable {k d : ℕ}

/-! ### The cutoff -/

/-- The Lipschitz cutoff `χ(v) = max(0, min(1, 3 - |v - b|/R))`. -/
def b1sas_cut (b : Spatial k) (R : ℝ) (v : Spatial k) : ℝ :=
  max 0 (min 1 (3 - ‖v - b‖ / R))

theorem b1sas_cut_nonneg (b : Spatial k) (R : ℝ) (v : Spatial k) : 0 ≤ b1sas_cut b R v :=
  le_max_left _ _

theorem b1sas_cut_le_one (b : Spatial k) (R : ℝ) (v : Spatial k) : b1sas_cut b R v ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem b1sas_cut_eq_one {b v : Spatial k} {R : ℝ} (hR : 0 < R) (hv : ‖v - b‖ ≤ 2 * R) :
    b1sas_cut b R v = 1 := by
  have h : ‖v - b‖ / R ≤ 2 := (div_le_iff₀ hR).2 (by linarith)
  unfold b1sas_cut
  rw [min_eq_left (by linarith : (1 : ℝ) ≤ 3 - ‖v - b‖ / R), max_eq_right zero_le_one]

theorem b1sas_cut_eq_zero {b v : Spatial k} {R : ℝ} (hR : 0 < R) (hv : 3 * R ≤ ‖v - b‖) :
    b1sas_cut b R v = 0 := by
  have h : 3 ≤ ‖v - b‖ / R := (le_div_iff₀ hR).2 (by linarith)
  unfold b1sas_cut
  rw [min_eq_right (by linarith : 3 - ‖v - b‖ / R ≤ 1), max_eq_left (by linarith : 3 - ‖v - b‖ / R ≤ 0)]

theorem b1sas_cut_lip {b : Spatial k} {R : ℝ} (hR : 0 < R) (x y : Spatial k) :
    |b1sas_cut b R x - b1sas_cut b R y| ≤ ‖x - y‖ / R := by
  unfold b1sas_cut
  have h1 := abs_max_sub_max_le_max (0 : ℝ) (min 1 (3 - ‖x - b‖ / R)) 0
    (min 1 (3 - ‖y - b‖ / R))
  have h2 := abs_min_sub_min_le_max (1 : ℝ) (3 - ‖x - b‖ / R) 1 (3 - ‖y - b‖ / R)
  simp only [sub_self, abs_zero] at h1 h2
  have h1' := h1.trans (max_le (abs_nonneg _) le_rfl)
  have h2' := h2.trans (max_le (abs_nonneg _) le_rfl)
  have h4 := abs_norm_sub_norm_le (y - b) (x - b)
  rw [sub_sub_sub_cancel_right, norm_sub_rev y x] at h4
  have h3 : |(3 - ‖x - b‖ / R) - (3 - ‖y - b‖ / R)| ≤ ‖x - y‖ / R := by
    rw [show (3 - ‖x - b‖ / R) - (3 - ‖y - b‖ / R) = (‖y - b‖ - ‖x - b‖) / R by ring,
      abs_div, abs_of_pos hR]
    exact div_le_div_of_nonneg_right h4 hR.le
  linarith

theorem b1sas_continuous_cut (b : Spatial k) (R : ℝ) : Continuous (b1sas_cut b R) :=
  continuous_const.max (continuous_const.min (continuous_const.sub
    ((continuous_id.sub continuous_const).norm.div_const R)))

/-! ### The cut-off field -/

/-- `G(v) = χ(v) (F(v) - F(b))`. -/
def b1sas_field (F : Spatial k → Spatial d) (b : Spatial k) (R : ℝ) (v : Spatial k) :
    Spatial d :=
  b1sas_cut b R v • (F v - F b)

theorem b1sas_field_eq {F : Spatial k → Spatial d} {b v : Spatial k} {R : ℝ} (hR : 0 < R)
    (hv : ‖v - b‖ ≤ 2 * R) : b1sas_field F b R v = F v - F b := by
  rw [b1sas_field, b1sas_cut_eq_one hR hv, one_smul]

theorem b1sas_field_zero {F : Spatial k → Spatial d} {b v : Spatial k} {R : ℝ} (hR : 0 < R)
    (hv : 3 * R ≤ ‖v - b‖) : b1sas_field F b R v = 0 := by
  rw [b1sas_field, b1sas_cut_eq_zero hR hv, zero_smul]

theorem b1sas_field_sub_le_aux {F : Spatial k → Spatial d} {L : ℝ≥0} (hF : LipschitzWith L F)
    {b : Spatial k} {R : ℝ} (hR : 0 < R) (x y : Spatial k) (hy : ‖y - b‖ ≤ 3 * R) :
    ‖b1sas_field F b R x - b1sas_field F b R y‖ ≤ 4 * L * ‖x - y‖ := by
  have hdecomp : b1sas_field F b R x - b1sas_field F b R y =
      b1sas_cut b R x • (F x - F y) + (b1sas_cut b R x - b1sas_cut b R y) • (F y - F b) := by
    simp only [b1sas_field, sub_smul, smul_sub]
    abel
  have hFy : ‖F y - F b‖ ≤ L * (3 * R) :=
    (hF.norm_sub_le y b).trans (mul_le_mul_of_nonneg_left hy L.coe_nonneg)
  have hFxy : ‖F x - F y‖ ≤ L * ‖x - y‖ := hF.norm_sub_le x y
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (b1sas_cut_nonneg b R x)]
  have hc := b1sas_cut_lip (b := b) hR x y
  have t1 : b1sas_cut b R x * ‖F x - F y‖ ≤ 1 * (L * ‖x - y‖) :=
    mul_le_mul (b1sas_cut_le_one b R x) hFxy (norm_nonneg _) zero_le_one
  have t2 : |b1sas_cut b R x - b1sas_cut b R y| * ‖F y - F b‖ ≤
      (‖x - y‖ / R) * (L * (3 * R)) :=
    mul_le_mul hc hFy (norm_nonneg _) (div_nonneg (norm_nonneg _) hR.le)
  have t3 : (‖x - y‖ / R) * (L * (3 * R)) = 3 * L * ‖x - y‖ := by
    rw [div_mul_eq_mul_div, div_eq_iff hR.ne']
    ring
  linarith

/-- `|G(x) - G(y)| ≤ 4L|x - y|`. -/
theorem b1sas_field_sub_le {F : Spatial k → Spatial d} {L : ℝ≥0} (hF : LipschitzWith L F)
    {b : Spatial k} {R : ℝ} (hR : 0 < R) (x y : Spatial k) :
    ‖b1sas_field F b R x - b1sas_field F b R y‖ ≤ 4 * L * ‖x - y‖ := by
  by_cases hy : ‖y - b‖ ≤ 3 * R
  · exact b1sas_field_sub_le_aux hF hR x y hy
  by_cases hx : ‖x - b‖ ≤ 3 * R
  · rw [norm_sub_rev (b1sas_field F b R x), norm_sub_rev x y]
    exact b1sas_field_sub_le_aux hF hR y x hx
  · push Not at hx hy
    rw [b1sas_field_zero hR hx.le, b1sas_field_zero hR hy.le, sub_self, norm_zero]
    positivity

theorem b1sas_continuous_field {F : Spatial k → Spatial d} (hF : Continuous F) (b : Spatial k)
    (R : ℝ) : Continuous (b1sas_field F b R) :=
  (b1sas_continuous_cut b R).smul (hF.sub continuous_const)

theorem b1sas_continuous_field_coord {F : Spatial k → Spatial d} (hF : Continuous F)
    (b : Spatial k) (R : ℝ) (i : Fin d) : Continuous fun v => b1sas_field F b R v i :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp (b1sas_continuous_field hF b R)

theorem b1sas_memLp_field_coord {F : Spatial k → Spatial d} (hF : Continuous F) (b : Spatial k)
    {R : ℝ} (hR : 0 < R) (i : Fin d) :
    MemLp (fun v => b1sas_field F b R v i) 2 volume := by
  refine (b1sas_continuous_field_coord hF b R i).memLp_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall b (3 * R)) fun v hv => ?_
  rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hv
  show b1sas_field F b R v i = 0
  simp [b1sas_field_zero hR hv.le]

/-! ### The translate bound -/

theorem b1sas_norm_unit (j : Fin k) : ‖b1sas_unit j‖ = 1 :=
  (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin k)).1 j

/-- The set where a coordinate difference of `G` at step `t e_j` can be nonzero. -/
def b1sas_trSet (b : Spatial k) (R t : ℝ) (j : Fin k) : Set (Spatial k) :=
  Metric.closedBall b (3 * R) ∪ (fun x => x + t • b1sas_unit j) ⁻¹' Metric.closedBall b (3 * R)

theorem b1sas_measurableSet_trSet (b : Spatial k) (R t : ℝ) (j : Fin k) :
    MeasurableSet (b1sas_trSet b R t j) :=
  measurableSet_closedBall.union (measurableSet_closedBall.preimage (measurable_add_const _))

theorem b1sas_volume_trSet_le (b : Spatial k) {R : ℝ} (hR : 0 < R) (t : ℝ) (j : Fin k) :
    volume (b1sas_trSet b R t j) ≤
      2 * (ENNReal.ofReal ((3 * R) ^ k) * volume (Metric.ball (0 : Spatial k) 1)) := by
  have hcb : volume (Metric.closedBall b (3 * R)) =
      ENNReal.ofReal ((3 * R) ^ k) * volume (Metric.ball (0 : Spatial k) 1) := by
    rw [Measure.addHaar_closedBall volume b (by linarith : (0 : ℝ) ≤ 3 * R),
      finrank_euclideanSpace_fin]
  refine (measure_union_le _ _).trans (le_of_eq ?_)
  rw [measure_preimage_add_right, hcb, two_mul]

theorem b1sas_field_coord_translate {F : Spatial k → Spatial d} {L : ℝ≥0}
    (hF : LipschitzWith L F) {b : Spatial k} {R : ℝ} (hR : 0 < R) (i : Fin d) (j : Fin k)
    (t : ℝ) (x : Spatial k) :
    ‖b1sas_field F b R (x + t • b1sas_unit j) i - b1sas_field F b R x i‖ₑ ^ 2 ≤
      (b1sas_trSet b R t j).indicator (fun _ => ENNReal.ofReal (16 * (L : ℝ) ^ 2 * t ^ 2)) x := by
  by_cases hx : x ∈ b1sas_trSet b R t j
  · rw [indicator_of_mem hx]
    have h1 : ‖b1sas_field F b R (x + t • b1sas_unit j) i - b1sas_field F b R x i‖ ≤
        4 * L * |t| := by
      calc ‖b1sas_field F b R (x + t • b1sas_unit j) i - b1sas_field F b R x i‖
          = ‖(b1sas_field F b R (x + t • b1sas_unit j) - b1sas_field F b R x) i‖ := by
            rw [PiLp.sub_apply]
        _ ≤ ‖b1sas_field F b R (x + t • b1sas_unit j) - b1sas_field F b R x‖ :=
            PiLp.norm_apply_le _ _
        _ ≤ 4 * L * ‖(x + t • b1sas_unit j) - x‖ := b1sas_field_sub_le hF hR _ _
        _ = 4 * L * |t| := by
            rw [add_sub_cancel_left, norm_smul, b1sas_norm_unit, mul_one, Real.norm_eq_abs]
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (4 * (L : ℝ) * |t|) ^ 2 = 16 * (L : ℝ) ^ 2 * t ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
      ring
    linarith
  · rw [indicator_of_notMem hx]
    simp only [b1sas_trSet, mem_union, mem_preimage, Metric.mem_closedBall, dist_eq_norm,
      not_or, not_le] at hx
    rw [b1sas_field_zero hR hx.2.le, b1sas_field_zero hR hx.1.le, sub_self]
    simp

/-- The translate bound for one coordinate of `G`:
`∫ |G_i(x + t e_j) - G_i(x)|² dx ≤ 32 L² (3R)^k |B(0,1)| t²`. -/
theorem b1sas_field_translate_le {F : Spatial k → Spatial d} {L : ℝ≥0}
    (hF : LipschitzWith L F) {b : Spatial k} {R : ℝ} (hR : 0 < R) (i : Fin d) (j : Fin k)
    (t : ℝ) :
    ∫⁻ x, ‖b1sas_field F b R (x + t • b1sas_unit j) i - b1sas_field F b R x i‖ₑ ^ 2 ≤
      ENNReal.ofReal (32 * (L : ℝ) ^ 2 * (3 * R) ^ k *
        (volume (Metric.ball (0 : Spatial k) 1)).toReal * t ^ 2) := by
  have hV : volume (Metric.ball (0 : Spatial k) 1) ≠ ⊤ := b1sas_volume_ball_one_lt_top.ne
  calc ∫⁻ x, ‖b1sas_field F b R (x + t • b1sas_unit j) i - b1sas_field F b R x i‖ₑ ^ 2
      ≤ ∫⁻ x, (b1sas_trSet b R t j).indicator
          (fun _ => ENNReal.ofReal (16 * (L : ℝ) ^ 2 * t ^ 2)) x :=
        lintegral_mono fun x => b1sas_field_coord_translate hF hR i j t x
    _ = ENNReal.ofReal (16 * (L : ℝ) ^ 2 * t ^ 2) * volume (b1sas_trSet b R t j) :=
        lintegral_indicator_const (b1sas_measurableSet_trSet b R t j) _
    _ ≤ ENNReal.ofReal (16 * (L : ℝ) ^ 2 * t ^ 2) *
          (2 * (ENNReal.ofReal ((3 * R) ^ k) * volume (Metric.ball (0 : Spatial k) 1))) :=
        mul_le_mul_right (b1sas_volume_trSet_le b hR t j) _
    _ = ENNReal.ofReal (32 * (L : ℝ) ^ 2 * (3 * R) ^ k *
          (volume (Metric.ball (0 : Spatial k) 1)).toReal * t ^ 2) := by
        have hp : 0 ≤ (3 * R) ^ k := pow_nonneg (by linarith) k
        have ha : 0 ≤ 16 * (L : ℝ) ^ 2 * t ^ 2 := by positivity
        have hr : 32 * (L : ℝ) ^ 2 * (3 * R) ^ k *
            (volume (Metric.ball (0 : Spatial k) 1)).toReal * t ^ 2 =
            (16 * (L : ℝ) ^ 2 * t ^ 2) *
              (2 * ((3 * R) ^ k * (volume (Metric.ball (0 : Spatial k) 1)).toReal)) := by
          ring
        have e2 : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := ENNReal.ofReal_ofNat 2
        rw [hr, ENNReal.ofReal_mul ha, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul hp, ENNReal.ofReal_toReal hV, e2]

/-! ### Agreement on the testing balls -/

/-- For `u ∈ B(b,R)` and `0 < s < R`, the affine error of `F` at `(u,s)` is at most that of
`G` (in fact equal: `G = F - F(b)` on `B(u,s) ⊆ B(b,2R)` and constants are affine). -/
theorem b1sas_errorSq_le_field {F : Spatial k → Spatial d} {b u : Spatial k} {R s : ℝ}
    (hR : 0 < R) (hu : u ∈ Metric.ball b R) (hs : s ∈ Ioo 0 R) :
    spatialAffineErrorSq F u s ≤ spatialAffineErrorSq (b1sas_field F b R) u s := by
  rw [b1sas_errorSq_of_pos F u hs.1, b1sas_errorSq_of_pos (b1sas_field F b R) u hs.1]
  refine mul_le_mul_right (le_iInf₂ fun a B => ?_) _
  have h1 : (⨅ (a' : Spatial d) (B' : Spatial k →L[ℝ] Spatial d),
        ∫⁻ v in Metric.ball u s, ‖F v - (a' + B' v)‖ₑ ^ 2) ≤
      ∫⁻ v in Metric.ball u s, ‖F v - (a + F b + B v)‖ₑ ^ 2 :=
    (iInf_le (fun a' : Spatial d => ⨅ B' : Spatial k →L[ℝ] Spatial d,
        ∫⁻ v in Metric.ball u s, ‖F v - (a' + B' v)‖ₑ ^ 2) (a + F b)).trans
      (iInf_le (fun B' : Spatial k →L[ℝ] Spatial d =>
        ∫⁻ v in Metric.ball u s, ‖F v - (a + F b + B' v)‖ₑ ^ 2) B)
  refine h1.trans (le_of_eq ?_)
  refine setLIntegral_congr_fun measurableSet_ball fun v hv => ?_
  show ‖F v - (a + F b + B v)‖ₑ ^ 2 = ‖b1sas_field F b R v - (a + B v)‖ₑ ^ 2
  have hvu : ‖v - u‖ < s := mem_ball_iff_norm.1 hv
  have hub : ‖u - b‖ < R := mem_ball_iff_norm.1 hu
  have hvb : ‖v - b‖ ≤ 2 * R := by
    have := norm_sub_le_norm_sub_add_norm_sub v u b
    linarith [hs.2]
  rw [b1sas_field_eq hR hvb, show F v - (a + F b + B v) = F v - F b - (a + B v) by abel]

/-! ### The main estimate -/

/-- **The spatial affine-square estimate for Lipschitz maps** (`SpatialAffineSquareStatement`),
in quantitative form. For all `k, d` there is
`C > 0` such that every `L`-Lipschitz `F : ℝ^k → ℝ^d` satisfies
`∫_{B(b,R)} ∫_0^R spatialAffineErrorSq F u s ds/s du ≤ C L² R^k`; here
`C = |B(0,1)| (24π² + 2k + 2)² · d · 2k · 3^k |B(0,1)| + 1`. -/
theorem ba1_spatial_affine_square_proof : SpatialAffineSquareStatement := by
  intro k d
  have hV0 : 0 ≤ (volume (Metric.ball (0 : Spatial k) 1)).toReal := ENNReal.toReal_nonneg
  have hK0 : 0 ≤ b1sas_C k * (d * (k * (32 * 3 ^ k *
      (volume (Metric.ball (0 : Spatial k) 1)).toReal / 16))) :=
    mul_nonneg (b1sas_C_nonneg k) (mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg (Nat.cast_nonneg k) (div_nonneg (mul_nonneg (by positivity) hV0)
        (by norm_num))))
  refine ⟨b1sas_C k * (d * (k * (32 * 3 ^ k *
    (volume (Metric.ball (0 : Spatial k) 1)).toReal / 16))) + 1,
    add_pos_of_nonneg_of_pos hK0 one_pos, ?_⟩
  intro F L hF b R hR
  have hA0 : 0 ≤ 32 * (L : ℝ) ^ 2 * (3 * R) ^ k *
      (volume (Metric.ball (0 : Spatial k) 1)).toReal :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (pow_nonneg (by linarith) k)) hV0
  have hGm : Measurable (b1sas_field F b R) :=
    (b1sas_continuous_field hF.continuous b R).measurable
  have hL2 : ∀ i : Fin d, MemLp (fun v => b1sas_field F b R v i) 2 volume := fun i =>
    b1sas_memLp_field_coord hF.continuous b hR i
  have hE : ∀ i : Fin d, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) *
      ‖(𝓕 (b1sas_realLp (hL2 i)) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 ≤
        ENNReal.ofReal (k * (32 * (L : ℝ) ^ 2 * (3 * R) ^ k *
          (volume (Metric.ball (0 : Spatial k) 1)).toReal / 16)) := fun i =>
    b1sas_fourierEnergy_le (hL2 i) hA0 fun j n => b1sas_field_translate_le hF hR i j _
  have harith : b1sas_C k * (d * (k * (32 * (L : ℝ) ^ 2 * (3 * R) ^ k *
        (volume (Metric.ball (0 : Spatial k) 1)).toReal / 16))) ≤
      (b1sas_C k * (d * (k * (32 * 3 ^ k *
        (volume (Metric.ball (0 : Spatial k) 1)).toReal / 16))) + 1) * (L : ℝ) ^ 2 * R ^ k := by
    have hLR : 0 ≤ (L : ℝ) ^ 2 * R ^ k := mul_nonneg (sq_nonneg _) (pow_nonneg hR.le k)
    have he : b1sas_C k * (d * (k * (32 * (L : ℝ) ^ 2 * (3 * R) ^ k *
          (volume (Metric.ball (0 : Spatial k) 1)).toReal / 16))) =
        b1sas_C k * (d * (k * (32 * 3 ^ k *
          (volume (Metric.ball (0 : Spatial k) 1)).toReal / 16))) * ((L : ℝ) ^ 2 * R ^ k) := by
      rw [mul_pow]
      ring
    rw [he]
    nlinarith
  calc ∫⁻ u in Metric.ball b R, ∫⁻ s in Ioo 0 R, spatialAffineErrorSq F u s ∂scaleMeasure
      ≤ ∫⁻ u in Metric.ball b R, ∫⁻ s in Ioo 0 R,
          spatialAffineErrorSq (b1sas_field F b R) u s ∂scaleMeasure :=
        setLIntegral_mono' measurableSet_ball fun u hu =>
          setLIntegral_mono' measurableSet_Ioo fun s hs => b1sas_errorSq_le_field hR hu hs
    _ ≤ ∫⁻ u, ∫⁻ s, spatialAffineErrorSq (b1sas_field F b R) u s ∂scaleMeasure :=
        (setLIntegral_le_lintegral _ _).trans
          (lintegral_mono fun u => setLIntegral_le_lintegral _ _)
    _ ≤ ENNReal.ofReal (b1sas_C k) * ∑ i : Fin d, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) *
          ‖(𝓕 (b1sas_realLp (hL2 i)) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 :=
        b1sas_spatial_global hGm hL2
    _ ≤ ENNReal.ofReal (b1sas_C k) * ∑ _i : Fin d, ENNReal.ofReal (k * (32 * (L : ℝ) ^ 2 *
          (3 * R) ^ k * (volume (Metric.ball (0 : Spatial k) 1)).toReal / 16)) :=
        mul_le_mul_right (Finset.sum_le_sum fun i _ => hE i) _
    _ = ENNReal.ofReal (b1sas_C k * (d * (k * (32 * (L : ℝ) ^ 2 * (3 * R) ^ k *
          (volume (Metric.ball (0 : Spatial k) 1)).toReal / 16)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg d),
          ← ENNReal.ofReal_mul (b1sas_C_nonneg k)]
    _ ≤ ENNReal.ofReal ((b1sas_C k * (d * (k * (32 * 3 ^ k *
          (volume (Metric.ball (0 : Spatial k) 1)).toReal / 16))) + 1) *
          (L : ℝ) ^ 2 * R ^ k) :=
        ENNReal.ofReal_le_ofReal harith

end ParabolicRectifiability.Characterization
