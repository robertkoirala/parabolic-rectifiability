import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ProjectionEnergy

/-! # The discrete affine estimate

Proof of `d1e_AffinePoincareStatement → d1e2_DiscreteAffineStatement`, as
`d1e2_discrete_affine_proof` (implication form: the second-order affine Poincaré statement is a
hypothesis).

Write `r = r_j = F.scale j`, `F_j` for the actual stage, `F⁰` for the projection limit and
`F₀ = x_* + U_* u` for the initial stage, `b_j = d1e_curvature`, `T_j = d1e2_tailSum` and
`W_j = b_j² + T_j = d1e2_levelMajorant`.

1. **Poincaré for the smooth stage** (`d1e2disc_stage_poincare`). `F_j` is `C^∞`
   (`CoherentChart.contDiff_stage`), so the premise with `d = n` gives
   `a_{F_j}(y,r)² ≤ C r^{-m} ∫ (‖D_u²F_j‖² + |∂_tF_j|²)`, and pointwise
   `‖D_u²F_j‖² + |∂_tF_j|² ≤ (‖D_u²F_j‖ + |∂_tF_j|)² = r^{-2} b_j²` (the same `fderiv`/`deriv`
   terms as in `d1e_curvature`). Hence `a_{F_j}(y,r)² ≤ C r^{-(m+2)} ∫ b_j²`.
2. **Competitor shift** (`d1e2disc_competitor_shift`). For every `(a, B)` the competitor
   `(a - x_*, B - U_*)` of `F⁰ - F₀` has residual `(F_j - a - Bu) + (F⁰ - F_j)`, so its fitting
   integral is at most `2 ∫ |F_j - a - Bu|² + 2 C_T r² ∫ T_j` (the first summand is continuous,
   hence measurable; the second is bounded by the tail hypothesis and a finite constant is
   pulled out without measurability). Taking the infima and the normalization `r^{-(m+4)}`:
   `a_{F⁰-F₀}(y,r)² ≤ 2 a_{F_j}(y,r)² + 2 C_T r^{-(m+2)} ∫ T_j`.
3. **Assembly.** `b_j² ≤ W_j` and `T_j ≤ W_j` pointwise give
   `a_{F⁰-F₀}(y,r)² ≤ 2 (C + C_T) r^{-(m+2)} ∫ W_j`, with `C = C_P(m)` the Poincaré constant.

No measurability of an affine error, of the path errors or of the tail sum is used. Spatial
rank zero is included (the Poincaré premise covers `m = 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-! ## Elementary inequalities -/

/-- The base normalization exponent: `baseDimension (Spatial m) + 2 = m + 4`. -/
theorem d1e2disc_baseDimension_add_two (m : ℕ) : baseDimension (Spatial m) + 2 = m + 4 := by
  rw [baseDimension, finrank_euclideanSpace_fin]

/-- `‖x + y‖ₑ² ≤ 2 ‖x‖ₑ² + 2 ‖y‖ₑ²`. -/
theorem d1e2disc_enorm_add_sq_le {Y : Type*} [SeminormedAddCommGroup Y] (x y : Y) :
    ‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  have h := norm_add_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have hxy := norm_nonneg (x + y)
  calc ‖x + y‖ₑ ^ 2 = ENNReal.ofReal (‖x + y‖ ^ 2) := by
        rw [← ofReal_norm, ENNReal.ofReal_pow hxy]
    _ ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [mul_nonneg (sub_nonneg.2 h) (add_nonneg (add_nonneg hx hy) hxy),
          sq_nonneg (‖x‖ - ‖y‖)]
    _ = 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_pow hx, ENNReal.ofReal_pow hy, ofReal_norm, ofReal_norm,
          ENNReal.ofReal_ofNat 2]

/-- The Poincaré integrand against the normalized derivative size:
`A² + B² ≤ (A + B)² = r^{-2} (r (A + B))²` for `A, B ≥ 0` and `r > 0`. -/
theorem d1e2disc_sq_add_sq_le {A B r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 < r) :
    ENNReal.ofReal (A ^ 2 + B ^ 2) ≤
      (ENNReal.ofReal r)⁻¹ ^ 2 * ENNReal.ofReal ((r * (A + B)) ^ 2) := by
  rw [← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_pow (inv_nonneg.2 hr.le),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h : r⁻¹ ^ 2 * (r * (A + B)) ^ 2 = (A + B) ^ 2 := by
    rw [mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, one_mul]
  rw [h]
  nlinarith [mul_nonneg hA hB]

/-- Normalization bookkeeping: with `ρ s = 1`, a fitting bound
`I ≤ 2 J + 2 c s² T` becomes `ρ^{m+4} I ≤ 2 ρ^{m+4} J + 2 c ρ^{m+2} T`. -/
theorem d1e2disc_scale_combine {ρ s c I J T : ℝ≥0∞} (m : ℕ) (hρs : ρ * s = 1)
    (h : I ≤ 2 * J + 2 * (c * s ^ 2 * T)) :
    ρ ^ (m + 4) * I ≤ 2 * (ρ ^ (m + 4) * J) + 2 * c * ρ ^ (m + 2) * T := by
  calc ρ ^ (m + 4) * I ≤ ρ ^ (m + 4) * (2 * J + 2 * (c * s ^ 2 * T)) := by gcongr
    _ = 2 * (ρ ^ (m + 4) * J) + 2 * c * ρ ^ (m + 2) * T * (ρ * s) ^ 2 := by ring
    _ = 2 * (ρ ^ (m + 4) * J) + 2 * c * ρ ^ (m + 2) * T := by rw [hρs, one_pow, mul_one]

/-- The final constant: `A ≤ 2 X + 2 c' ρ I_T`, `X ≤ c ρ I_b` and `I_b, I_T ≤ I_W` give
`A ≤ 2 (c + c') ρ I_W`. -/
theorem d1e2disc_final_combine {A X c c' ρ Ib IT IW : ℝ≥0∞}
    (h2 : A ≤ 2 * X + 2 * c' * ρ * IT) (h1 : X ≤ c * ρ * Ib) (hb : Ib ≤ IW) (hT : IT ≤ IW) :
    A ≤ 2 * (c + c') * ρ * IW := by
  calc A ≤ 2 * X + 2 * c' * ρ * IT := h2
    _ ≤ 2 * (c * ρ * Ib) + 2 * c' * ρ * IT := by gcongr
    _ ≤ 2 * (c * ρ * IW) + 2 * c' * ρ * IW := by gcongr
    _ = 2 * (c + c') * ρ * IW := by ring

/-! ## Step 1: Poincaré for the smooth stage -/

/-- **Poincaré for the actual stage**: from the rank-`m` Poincaré
property with constant `C` (the body of `d1e_AffinePoincareStatement m`), applied to
`H = F_j` with `d = n`, `a_{F_j}(y, r_j)² ≤ C r_j^{-(m+2)} ∫_{P_b(y,r_j)} b_j²`. -/
theorem d1e2disc_stage_poincare {m : ℕ} {C : ℝ}
    (hP : ∀ (d : ℕ) (H : Spatial m → ℝ → Spatial d),
      ContDiff ℝ 2 (fun x : Spatial m × ℝ => H x.1 x.2) →
      ∀ (p : Space m) (r : ℝ), 0 < r →
        affineErrorSq (parabolicVolume m) (fun z : Space m => H z.1 z.2.val) p r ≤
          ENNReal.ofReal C * (ENNReal.ofReal r)⁻¹ ^ m *
            ∫⁻ z in Metric.ball p r,
              ENNReal.ofReal (‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w z.2.val) v) z.1‖ ^ 2 +
                ‖deriv (fun s => H z.1 s) z.2.val‖ ^ 2) ∂parabolicVolume m)
    {n : ℕ} {ι : Type} (F : CoherentFamily n m ι) (P : CoherentChart.InitialChart F)
    (y : Space m) (j : ℕ) :
    affineErrorSq (parabolicVolume m)
        (fun z : Space m => CoherentChart.stage F P j z.1 z.2.val) y (F.scale j) ≤
      ENNReal.ofReal C * (ENNReal.ofReal (F.scale j))⁻¹ ^ (m + 2) *
        ∫⁻ q in Metric.ball y (F.scale j),
          ENNReal.ofReal (d1e_curvature F P j q.1 q.2.val ^ 2) ∂parabolicVolume m := by
  have hr : 0 < F.scale j := CoherentChart.scale_pos F j
  have hC2 : ContDiff ℝ 2 (fun x : Spatial m × ℝ => CoherentChart.stage F P j x.1 x.2) :=
    (CoherentChart.contDiff_stage F P j).of_le ENat.LEInfty.out
  have h1 : affineErrorSq (parabolicVolume m)
        (fun z : Space m => CoherentChart.stage F P j z.1 z.2.val) y (F.scale j) ≤
      ENNReal.ofReal C * (ENNReal.ofReal (F.scale j))⁻¹ ^ m *
        ∫⁻ z in Metric.ball y (F.scale j),
          ENNReal.ofReal (‖fderiv ℝ (fun v => fderiv ℝ
              (fun w => CoherentChart.stage F P j w z.2.val) v) z.1‖ ^ 2 +
            ‖deriv (fun s => CoherentChart.stage F P j z.1 s) z.2.val‖ ^ 2) ∂parabolicVolume m :=
    hP n (fun u t => CoherentChart.stage F P j u t) hC2 y (F.scale j) hr
  have hρ : (ENNReal.ofReal (F.scale j))⁻¹ ^ 2 ≠ ∞ :=
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hr).ne')
  have h2 : ∫⁻ z in Metric.ball y (F.scale j),
        ENNReal.ofReal (‖fderiv ℝ (fun v => fderiv ℝ
            (fun w => CoherentChart.stage F P j w z.2.val) v) z.1‖ ^ 2 +
          ‖deriv (fun s => CoherentChart.stage F P j z.1 s) z.2.val‖ ^ 2) ∂parabolicVolume m ≤
      (ENNReal.ofReal (F.scale j))⁻¹ ^ 2 * ∫⁻ q in Metric.ball y (F.scale j),
          ENNReal.ofReal (d1e_curvature F P j q.1 q.2.val ^ 2) ∂parabolicVolume m :=
    calc _ ≤ ∫⁻ q in Metric.ball y (F.scale j), (ENNReal.ofReal (F.scale j))⁻¹ ^ 2 *
            ENNReal.ofReal (d1e_curvature F P j q.1 q.2.val ^ 2) ∂parabolicVolume m :=
          lintegral_mono fun z => d1e2disc_sq_add_sq_le (by positivity) (by positivity) hr
      _ = _ := lintegral_const_mul' _ _ hρ
  calc _ ≤ _ := h1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (F.scale j))⁻¹ ^ m *
        ((ENNReal.ofReal (F.scale j))⁻¹ ^ 2 * ∫⁻ q in Metric.ball y (F.scale j),
          ENNReal.ofReal (d1e_curvature F P j q.1 q.2.val ^ 2) ∂parabolicVolume m) := by
        gcongr
    _ = _ := by ring

/-! ## Step 2: the competitor shift -/

/-- **Competitor shift** (from the tail estimate). Under the pointwise tail hypothesis with
constant `C_T ≥ 0`, `a_{F⁰-F₀}(y, r_j)² ≤ 2 a_{F_j}(y, r_j)² + 2 C_T r_j^{-(m+2)} ∫ T_j`:
the competitor `(a - x_*, B - U_*)` of `F⁰ - F₀` has residual `(F_j - a - Bu) + (F⁰ - F_j)`. -/
theorem d1e2disc_competitor_shift {m n : ℕ} {ι : Type} (F : CoherentFamily n m ι)
    (P : CoherentChart.InitialChart F) {CT : ℝ} (hCT : 0 ≤ CT)
    (htail : ∀ (p : Space m) (j : ℕ),
      ‖d1e_projectionLimit F P p.1 p.2.val - CoherentChart.stage F P j p.1 p.2.val‖ₑ ^ 2 ≤
        ENNReal.ofReal (CT * F.scale j ^ 2) * d1e2_tailSum F P j p)
    (y : Space m) (j : ℕ) :
    affineErrorSq (parabolicVolume m)
        (fun p : Space m => d1e_projectionLimit F P p.1 p.2.val - (P.origin + P.isometry p.1))
        y (F.scale j) ≤
      2 * affineErrorSq (parabolicVolume m)
          (fun z : Space m => CoherentChart.stage F P j z.1 z.2.val) y (F.scale j) +
        2 * ENNReal.ofReal CT * (ENNReal.ofReal (F.scale j))⁻¹ ^ (m + 2) *
          ∫⁻ q in Metric.ball y (F.scale j), d1e2_tailSum F P j q ∂parabolicVolume m := by
  have hr : 0 < F.scale j := CoherentChart.scale_pos F j
  have hstage : Continuous fun q : Space m => CoherentChart.stage F P j q.1 q.2.val :=
    (CoherentChart.contDiff_stage F P j).continuous.comp
      (continuous_fst.prodMk (Metric.Snowflaking.continuous_ofSnowflaking.comp continuous_snd))
  have hfit : ∀ (a : Spatial n) (B : Spatial m →L[ℝ] Spatial n),
      affineFitIntegral (parabolicVolume m)
          (fun p : Space m => d1e_projectionLimit F P p.1 p.2.val - (P.origin + P.isometry p.1))
          (a - P.origin) (B - P.isometry.toContinuousLinearMap) y (F.scale j) ≤
        2 * affineFitIntegral (parabolicVolume m)
            (fun z : Space m => CoherentChart.stage F P j z.1 z.2.val) a B y (F.scale j) +
          2 * (ENNReal.ofReal (CT * F.scale j ^ 2) *
            ∫⁻ q in Metric.ball y (F.scale j), d1e2_tailSum F P j q ∂parabolicVolume m) := by
    intro a B
    have hcont : Continuous fun q : Space m =>
        CoherentChart.stage F P j q.1 q.2.val - (a + B q.1) :=
      hstage.sub (continuous_const.add (B.continuous.comp continuous_fst))
    have hmeas : Measurable fun q : Space m =>
        2 * ‖CoherentChart.stage F P j q.1 q.2.val - (a + B q.1)‖ₑ ^ 2 :=
      (hcont.measurable.enorm.pow_const 2).const_mul 2
    have h2top : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
    unfold affineFitIntegral
    calc ∫⁻ q in Metric.ball y (F.scale j),
          ‖(d1e_projectionLimit F P q.1 q.2.val - (P.origin + P.isometry q.1)) -
            ((a - P.origin) + (B - P.isometry.toContinuousLinearMap) q.1)‖ₑ ^ 2
            ∂parabolicVolume m
        ≤ ∫⁻ q in Metric.ball y (F.scale j),
          (2 * ‖CoherentChart.stage F P j q.1 q.2.val - (a + B q.1)‖ₑ ^ 2 +
            2 * (ENNReal.ofReal (CT * F.scale j ^ 2) * d1e2_tailSum F P j q))
            ∂parabolicVolume m := by
          refine lintegral_mono fun q => ?_
          have hid : (d1e_projectionLimit F P q.1 q.2.val - (P.origin + P.isometry q.1)) -
              ((a - P.origin) + (B - P.isometry.toContinuousLinearMap) q.1) =
              (CoherentChart.stage F P j q.1 q.2.val - (a + B q.1)) +
                (d1e_projectionLimit F P q.1 q.2.val -
                  CoherentChart.stage F P j q.1 q.2.val) := by
            rw [_root_.sub_apply, LinearIsometry.coe_toContinuousLinearMap]
            abel
          rw [hid]
          refine (d1e2disc_enorm_add_sq_le _ _).trans ?_
          gcongr
          exact htail q j
      _ = 2 * ∫⁻ q in Metric.ball y (F.scale j),
            ‖CoherentChart.stage F P j q.1 q.2.val - (a + B q.1)‖ₑ ^ 2 ∂parabolicVolume m +
          2 * (ENNReal.ofReal (CT * F.scale j ^ 2) *
            ∫⁻ q in Metric.ball y (F.scale j), d1e2_tailSum F P j q ∂parabolicVolume m) := by
          rw [lintegral_add_left hmeas, lintegral_const_mul' _ _ h2top,
            lintegral_const_mul' _ _ h2top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hinf : (⨅ (a : Spatial n) (B : Spatial m →L[ℝ] Spatial n),
        affineFitIntegral (parabolicVolume m)
          (fun p : Space m => d1e_projectionLimit F P p.1 p.2.val - (P.origin + P.isometry p.1))
          a B y (F.scale j)) ≤
      2 * (⨅ (a : Spatial n) (B : Spatial m →L[ℝ] Spatial n),
        affineFitIntegral (parabolicVolume m)
          (fun z : Space m => CoherentChart.stage F P j z.1 z.2.val) a B y (F.scale j)) +
        2 * (ENNReal.ofReal (CT * F.scale j ^ 2) *
          ∫⁻ q in Metric.ball y (F.scale j), d1e2_tailSum F P j q ∂parabolicVolume m) := by
    rw [ENNReal.mul_iInf_of_ne two_ne_zero ENNReal.ofNat_ne_top, ENNReal.iInf_add]
    refine le_iInf fun a => ?_
    rw [ENNReal.mul_iInf_of_ne two_ne_zero ENNReal.ofNat_ne_top, ENNReal.iInf_add]
    refine le_iInf fun B => ?_
    exact iInf₂_le_of_le (a - P.origin) (B - P.isometry.toContinuousLinearMap) (hfit a B)
  rw [ENNReal.ofReal_mul hCT, ENNReal.ofReal_pow hr.le] at hinf
  have hρs : (ENNReal.ofReal (F.scale j))⁻¹ * ENNReal.ofReal (F.scale j) = 1 :=
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top
  rw [affineErrorSq_of_pos _ _ _ hr, affineErrorSq_of_pos _ _ _ hr,
    d1e2disc_baseDimension_add_two]
  exact d1e2disc_scale_combine m hρs hinf

/-! ## Step 3: the discrete affine estimate -/

/-- **The discrete affine estimate** at the radii `r_j`. The constant is the Poincaré constant
`C = C_P(m)`; the bound is `2 (C + C_T) r_j^{-(m+2)} ∫_{P_b(y,r_j)} W_j`. -/
theorem d1e2_discrete_affine_proof :
    d1e_AffinePoincareStatement → d1e2_DiscreteAffineStatement := by
  intro hPoinc m
  obtain ⟨C, hC, hPm⟩ := hPoinc m
  refine ⟨C, hC, ?_⟩
  intro n ι F P CT hCT htail y j
  have h1 := d1e2disc_stage_poincare hPm F P y j
  have h2 := d1e2disc_competitor_shift F P hCT htail y j
  have hb : ∫⁻ q in Metric.ball y (F.scale j),
        ENNReal.ofReal (d1e_curvature F P j q.1 q.2.val ^ 2) ∂parabolicVolume m ≤
      ∫⁻ q in Metric.ball y (F.scale j), d1e2_levelMajorant F P j q ∂parabolicVolume m :=
    lintegral_mono fun q => by
      unfold d1e2_levelMajorant
      exact le_self_add
  have hT : ∫⁻ q in Metric.ball y (F.scale j), d1e2_tailSum F P j q ∂parabolicVolume m ≤
      ∫⁻ q in Metric.ball y (F.scale j), d1e2_levelMajorant F P j q ∂parabolicVolume m :=
    lintegral_mono fun q => by
      unfold d1e2_levelMajorant
      exact le_add_self
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_add hC hCT,
    ENNReal.ofReal_ofNat 2]
  exact d1e2disc_final_combine h2 h1 hb hT

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
