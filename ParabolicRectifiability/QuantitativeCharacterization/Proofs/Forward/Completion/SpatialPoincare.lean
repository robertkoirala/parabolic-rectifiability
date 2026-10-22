import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion

/-! # First-order spatial Poincaré on a Euclidean ball, Banach-valued

Proof of `d1e_spatial_poincare_proof : d1e_SpatialPoincareStatement`, with constant
`C₁ = 2^{m+2}`.

Route (classical, no Bochner average). Put `B = B(u₀, r)` and `h = 1_B ‖Df‖²`.
* `d1espacep_segment`: FTC along the segment and Cauchy-Schwarz on `(0, 1]`,
  `‖f y - f x‖² ≤ ‖y - x‖² ∫₀¹ ‖Df(x + τ(y - x))‖² dτ`; for `x, y ∈ B` the segment stays in
  `B` (convexity) and `‖y - x‖ < 2r`.
* `d1espacep_lintegral_affine(_le)`: Haar substitution `y ↦ b + a • y` with Jacobian
  `|a|^{-m} ≤ 2^m` for `a ≥ 1/2`.
* `d1espacep_double_le`: for every `τ`, `∫_B ∫_B h(y + τ(x - y)) ≤ 2^m |B| ∫ h` (substitute in
  `x` when `τ ≥ 1/2`, swap and substitute in `y` when `τ < 1/2`).
* `d1espacep_double_integral`: Tonelli, `∫_B ∫_B ‖f x - f y‖² ≤ 2^{m+2} r² |B| ∫_B ‖Df‖²`.
* `d1espacep_main`: a good point `y ∈ B` below the average (`exists_le_setLAverage`) gives
  `c = f y`.

Rank zero is covered by the same argument (the ball is the single point, of volume one).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Module
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-- Haar substitution `y ↦ b + a • y` on `ℝ^m` for the lower Lebesgue integral. -/
theorem d1espacep_lintegral_affine {m : ℕ} {g : EuclideanSpace ℝ (Fin m) → ℝ≥0∞}
    (hg : Measurable g) (b : EuclideanSpace ℝ (Fin m)) {a : ℝ} (ha : a ≠ 0) :
    ∫⁻ y, g (b + a • y) = ENNReal.ofReal |(a ^ m)⁻¹| * ∫⁻ z, g z := by
  have hgb : Measurable fun z : EuclideanSpace ℝ (Fin m) => g (b + z) :=
    hg.comp (measurable_const_add b)
  calc ∫⁻ y, g (b + a • y) = ∫⁻ z, g (b + z) ∂(Measure.map (a • ·) volume) :=
        (lintegral_map hgb (measurable_const_smul a)).symm
    _ = ENNReal.ofReal |(a ^ m)⁻¹| * ∫⁻ z, g (b + z) := by
        rw [Measure.map_addHaar_smul volume ha, lintegral_smul_measure,
          finrank_euclideanSpace_fin, smul_eq_mul]
    _ = ENNReal.ofReal |(a ^ m)⁻¹| * ∫⁻ z, g z := by
        rw [lintegral_add_left_eq_self g b]

/-- The Jacobian bound: for `a ≥ 1/2` the substitution `y ↦ b + a • y` costs at most `2^m`. -/
theorem d1espacep_lintegral_affine_le {m : ℕ} {g : EuclideanSpace ℝ (Fin m) → ℝ≥0∞}
    (hg : Measurable g) (b : EuclideanSpace ℝ (Fin m)) {a : ℝ} (ha : 1 / 2 ≤ a) :
    ∫⁻ y, g (b + a • y) ≤ 2 ^ m * ∫⁻ z, g z := by
  have hpos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  rw [d1espacep_lintegral_affine hg b hpos.ne']
  have hinv : a⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hpos (by norm_num)]
    calc (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
      _ ≤ a := ha
  have hJ : ENNReal.ofReal |(a ^ m)⁻¹| ≤ 2 ^ m := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos hpos m)), ← inv_pow]
    calc ENNReal.ofReal (a⁻¹ ^ m) ≤ ENNReal.ofReal (2 ^ m) :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) hinv m)
      _ = 2 ^ m := by rw [ENNReal.ofReal_pow (by norm_num)]; simp
  exact mul_le_mul' hJ le_rfl

/-- Cauchy-Schwarz on the unit interval `(0, 1]` (a probability measure). -/
theorem d1espacep_sq_lintegral_le {k : ℝ → ℝ≥0∞}
    (hk : AEMeasurable k (volume.restrict (Ioc (0 : ℝ) 1))) :
    (∫⁻ τ in Ioc (0 : ℝ) 1, k τ) ^ 2 ≤ ∫⁻ τ in Ioc (0 : ℝ) 1, k τ ^ 2 := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc (0 : ℝ) 1))
    Real.HolderConjugate.two_two hk (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have hone : ∫⁻ _τ in Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) = 1 := by simp
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, hone] at hH
  calc (∫⁻ τ in Ioc (0 : ℝ) 1, k τ) ^ 2
      ≤ ((∫⁻ τ in Ioc (0 : ℝ) 1, k τ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = ∫⁻ τ in Ioc (0 : ℝ) 1, k τ ^ (2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    _ = ∫⁻ τ in Ioc (0 : ℝ) 1, k τ ^ 2 := by simp_rw [ENNReal.rpow_two]

/-- **Segment formula** for a `C¹` map into a Banach space:
`‖f y - f x‖² ≤ ‖y - x‖² ∫₀¹ ‖Df(x + τ(y - x))‖² dτ`. -/
theorem d1espacep_segment {m : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] {f : EuclideanSpace ℝ (Fin m) → Y} (hf : ContDiff ℝ 1 f)
    (x y : EuclideanSpace ℝ (Fin m)) :
    ‖f y - f x‖ₑ ^ 2 ≤
      ‖y - x‖ₑ ^ 2 * ∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x + τ • (y - x))‖ₑ ^ 2 := by
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hcont : Continuous fun z => fderiv ℝ f z := hf.continuous_fderiv one_ne_zero
  have hγ : Continuous fun τ : ℝ => x + τ • (y - x) := by fun_prop
  have hderiv : ∀ τ : ℝ, HasDerivAt (fun s : ℝ => f (x + s • (y - x)))
      (fderiv ℝ f (x + τ • (y - x)) (y - x)) τ := by
    intro τ
    have h1 : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) τ := by
      simpa using ((hasDerivAt_id' τ).smul_const (y - x)).const_add x
    exact (hdiff (x + τ • (y - x))).hasFDerivAt.comp_hasDerivAt τ h1
  have hint : IntervalIntegrable (fun τ : ℝ => fderiv ℝ f (x + τ • (y - x)) (y - x))
      volume 0 1 :=
    ((hcont.comp hγ).clm_apply continuous_const).intervalIntegrable 0 1
  have hFTC : ∫ τ in (0 : ℝ)..1, fderiv ℝ f (x + τ • (y - x)) (y - x) = f y - f x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hderiv τ) hint]
    simp
  have hk : Measurable fun τ : ℝ => ‖fderiv ℝ f (x + τ • (y - x))‖ₑ :=
    (hcont.comp hγ).measurable.enorm
  have h1 : ‖f y - f x‖ₑ ≤
      (∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x + τ • (y - x))‖ₑ) * ‖y - x‖ₑ := by
    rw [← hFTC, intervalIntegral.integral_of_le zero_le_one,
      ← lintegral_mul_const' _ _ enorm_ne_top]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    exact lintegral_mono fun τ => ContinuousLinearMap.le_opENorm _ _
  calc ‖f y - f x‖ₑ ^ 2
      ≤ ((∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x + τ • (y - x))‖ₑ) * ‖y - x‖ₑ) ^ 2 := by
        gcongr
    _ = ‖y - x‖ₑ ^ 2 * (∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x + τ • (y - x))‖ₑ) ^ 2 := by
        ring
    _ ≤ ‖y - x‖ₑ ^ 2 * ∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x + τ • (y - x))‖ₑ ^ 2 :=
        mul_le_mul' le_rfl (d1espacep_sq_lintegral_le hk.aemeasurable)

/-- For every `τ` and every set `B`: `∫_B ∫_B h(y + τ(x - y)) ≤ 2^m |B| ∫ h`. Substitute in the
inner variable `x` when `τ ≥ 1/2`; swap the order and substitute in `y` when `τ < 1/2`. -/
theorem d1espacep_double_le {m : ℕ} {h : EuclideanSpace ℝ (Fin m) → ℝ≥0∞} (hh : Measurable h)
    (B : Set (EuclideanSpace ℝ (Fin m))) (τ : ℝ) :
    ∫⁻ y in B, ∫⁻ x in B, h (y + τ • (x - y)) ≤ 2 ^ m * volume B * ∫⁻ z, h z := by
  rcases le_or_gt (1 / 2 : ℝ) τ with hτ | hτ
  · calc ∫⁻ y in B, ∫⁻ x in B, h (y + τ • (x - y))
        ≤ ∫⁻ _y in B, 2 ^ m * ∫⁻ z, h z := by
          refine lintegral_mono fun y => ?_
          calc ∫⁻ x in B, h (y + τ • (x - y)) ≤ ∫⁻ x, h (y + τ • (x - y)) :=
                setLIntegral_le_lintegral _ _
            _ = ∫⁻ x, h ((y - τ • y) + τ • x) := by
                refine lintegral_congr fun x => ?_
                rw [smul_sub]
                congr 1
                abel
            _ ≤ 2 ^ m * ∫⁻ z, h z := d1espacep_lintegral_affine_le hh _ hτ
      _ = 2 ^ m * volume B * ∫⁻ z, h z := by rw [setLIntegral_const]; ring
  · have hmeas : Measurable (Function.uncurry fun y x : EuclideanSpace ℝ (Fin m) =>
        h (y + τ • (x - y))) :=
      hh.comp (by fun_prop : Continuous fun p : EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin m) => p.1 + τ • (p.2 - p.1)).measurable
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    calc ∫⁻ x in B, ∫⁻ y in B, h (y + τ • (x - y))
        ≤ ∫⁻ _x in B, 2 ^ m * ∫⁻ z, h z := by
          refine lintegral_mono fun x => ?_
          calc ∫⁻ y in B, h (y + τ • (x - y)) ≤ ∫⁻ y, h (y + τ • (x - y)) :=
                setLIntegral_le_lintegral _ _
            _ = ∫⁻ y, h (τ • x + (1 - τ) • y) := by
                refine lintegral_congr fun y => ?_
                rw [smul_sub, sub_smul, one_smul]
                congr 1
                abel
            _ ≤ 2 ^ m * ∫⁻ z, h z := d1espacep_lintegral_affine_le hh _ (by linarith)
      _ = 2 ^ m * volume B * ∫⁻ z, h z := by rw [setLIntegral_const]; ring

/-- **Double-integral Poincaré** on a ball:
`∫_B ∫_B ‖f x - f y‖² ≤ 2^{m+2} r² |B| ∫_B ‖Df‖²`. -/
theorem d1espacep_double_integral {m : ℕ} {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [CompleteSpace Y] {f : EuclideanSpace ℝ (Fin m) → Y}
    (hf : ContDiff ℝ 1 f) (u₀ : EuclideanSpace ℝ (Fin m)) {r : ℝ} (hr : 0 < r) :
    ∫⁻ y in Metric.ball u₀ r, ∫⁻ x in Metric.ball u₀ r, ‖f x - f y‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 ^ (m + 2) * r ^ 2) * volume (Metric.ball u₀ r) *
        ∫⁻ z in Metric.ball u₀ r, ‖fderiv ℝ f z‖ₑ ^ 2 := by
  have hBm : MeasurableSet (Metric.ball u₀ r) := measurableSet_ball
  have hcont : Continuous fun z => fderiv ℝ f z := hf.continuous_fderiv one_ne_zero
  set h : EuclideanSpace ℝ (Fin m) → ℝ≥0∞ :=
    (Metric.ball u₀ r).indicator fun z => ‖fderiv ℝ f z‖ₑ ^ 2 with hh_def
  have hh : Measurable h := (hcont.measurable.enorm.pow_const 2).indicator hBm
  have hpt : ∀ y ∈ Metric.ball u₀ r, ∀ x ∈ Metric.ball u₀ r,
      ‖f x - f y‖ₑ ^ 2 ≤
        ENNReal.ofReal (2 * r) ^ 2 * ∫⁻ τ in Ioc (0 : ℝ) 1, h (y + τ • (x - y)) := by
    intro y hy x hx
    have hxy : ‖x - y‖ₑ ≤ ENNReal.ofReal (2 * r) := by
      rw [← ofReal_norm, ← dist_eq_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := dist_triangle_right x y u₀
      rw [Metric.mem_ball] at hx hy
      linarith
    have heq : ∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (y + τ • (x - y))‖ₑ ^ 2 =
        ∫⁻ τ in Ioc (0 : ℝ) 1, h (y + τ • (x - y)) := by
      refine setLIntegral_congr_fun measurableSet_Ioc fun τ hτ => ?_
      have hmem : y + τ • (x - y) ∈ Metric.ball u₀ r :=
        (convex_ball u₀ r).add_smul_sub_mem hy hx ⟨hτ.1.le, hτ.2⟩
      simp only [hh_def, Set.indicator_of_mem hmem]
    calc ‖f x - f y‖ₑ ^ 2
        ≤ ‖x - y‖ₑ ^ 2 * ∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (y + τ • (x - y))‖ₑ ^ 2 :=
          d1espacep_segment hf y x
      _ ≤ ENNReal.ofReal (2 * r) ^ 2 * ∫⁻ τ in Ioc (0 : ℝ) 1, h (y + τ • (x - y)) := by
          rw [heq]
          gcongr
  have hin : ∀ y : EuclideanSpace ℝ (Fin m), Measurable (Function.uncurry
      fun (x : EuclideanSpace ℝ (Fin m)) (τ : ℝ) => h (y + τ • (x - y))) := fun y =>
    hh.comp (by fun_prop : Continuous fun p : EuclideanSpace ℝ (Fin m) × ℝ =>
      y + p.2 • (p.1 - y)).measurable
  have hout : Measurable (Function.uncurry fun (y : EuclideanSpace ℝ (Fin m)) (τ : ℝ) =>
      ∫⁻ x in Metric.ball u₀ r, h (y + τ • (x - y))) := by
    have hF : Measurable fun q : (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin m) =>
        h (q.1.1 + q.1.2 • (q.2 - q.1.1)) :=
      hh.comp (by fun_prop : Continuous fun q : (EuclideanSpace ℝ (Fin m) × ℝ) ×
        EuclideanSpace ℝ (Fin m) => q.1.1 + q.1.2 • (q.2 - q.1.1)).measurable
    exact hF.lintegral_prod_right'
  have hconst : ENNReal.ofReal (2 ^ (m + 2) * r ^ 2) = ENNReal.ofReal (2 * r) ^ 2 * 2 ^ m := by
    have e : (2 : ℝ) ^ (m + 2) * r ^ 2 = (2 * r) ^ 2 * 2 ^ m := by ring
    rw [e, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * r) ^ 2),
      ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 2 * r),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  have hI : volume (Ioc (0 : ℝ) 1) = 1 := by simp
  have hint : ∫⁻ z, h z = ∫⁻ z in Metric.ball u₀ r, ‖fderiv ℝ f z‖ₑ ^ 2 := by
    rw [hh_def, lintegral_indicator hBm]
  have hfin : ENNReal.ofReal (2 * r) ^ 2 ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  calc ∫⁻ y in Metric.ball u₀ r, ∫⁻ x in Metric.ball u₀ r, ‖f x - f y‖ₑ ^ 2
      ≤ ∫⁻ y in Metric.ball u₀ r, ∫⁻ x in Metric.ball u₀ r,
          ENNReal.ofReal (2 * r) ^ 2 * ∫⁻ τ in Ioc (0 : ℝ) 1, h (y + τ • (x - y)) :=
        setLIntegral_mono' hBm fun y hy => setLIntegral_mono' hBm fun x hx => hpt y hy x hx
    _ = ENNReal.ofReal (2 * r) ^ 2 * ∫⁻ y in Metric.ball u₀ r, ∫⁻ x in Metric.ball u₀ r,
          ∫⁻ τ in Ioc (0 : ℝ) 1, h (y + τ • (x - y)) := by
        rw [← lintegral_const_mul' _ _ hfin]
        exact lintegral_congr fun y => lintegral_const_mul' _ _ hfin
    _ = ENNReal.ofReal (2 * r) ^ 2 * ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ y in Metric.ball u₀ r,
          ∫⁻ x in Metric.ball u₀ r, h (y + τ • (x - y)) := by
        congr 1
        calc ∫⁻ y in Metric.ball u₀ r, ∫⁻ x in Metric.ball u₀ r,
              ∫⁻ τ in Ioc (0 : ℝ) 1, h (y + τ • (x - y))
            = ∫⁻ y in Metric.ball u₀ r, ∫⁻ τ in Ioc (0 : ℝ) 1,
                ∫⁻ x in Metric.ball u₀ r, h (y + τ • (x - y)) :=
              lintegral_congr fun y => lintegral_lintegral_swap (hin y).aemeasurable
          _ = _ := lintegral_lintegral_swap hout.aemeasurable
    _ ≤ ENNReal.ofReal (2 * r) ^ 2 * ∫⁻ _τ in Ioc (0 : ℝ) 1,
          2 ^ m * volume (Metric.ball u₀ r) * ∫⁻ z, h z :=
        mul_le_mul' le_rfl (lintegral_mono fun τ => d1espacep_double_le hh _ τ)
    _ = ENNReal.ofReal (2 ^ (m + 2) * r ^ 2) * volume (Metric.ball u₀ r) *
          ∫⁻ z in Metric.ball u₀ r, ‖fderiv ℝ f z‖ₑ ^ 2 := by
        rw [setLIntegral_const, hI, hconst, hint]
        ring

/-- **Spatial Poincaré on a ball** with constant `2^{m+2}`: a good base point `y ∈ B` (first
moment method) gives `c = f y`. -/
theorem d1espacep_main {m : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] (f : EuclideanSpace ℝ (Fin m) → Y) (hf : ContDiff ℝ 1 f)
    (u₀ : EuclideanSpace ℝ (Fin m)) (r : ℝ) (hr : 0 < r) :
    ∃ c : Y, ∫⁻ u in Metric.ball u₀ r, ‖f u - c‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 ^ (m + 2) * r ^ 2) * ∫⁻ u in Metric.ball u₀ r, ‖fderiv ℝ f u‖ₑ ^ 2 := by
  have hfc : Continuous f := hf.continuous
  have hΦ : Measurable fun y => ∫⁻ x in Metric.ball u₀ r, ‖f x - f y‖ₑ ^ 2 := by
    refine Measurable.lintegral_prod_right ?_
    exact (((hfc.comp continuous_snd).sub (hfc.comp continuous_fst)).enorm.measurable).pow_const
      2
  have hpos : volume (Metric.ball u₀ r) ≠ 0 := (Metric.measure_ball_pos volume u₀ hr).ne'
  have hfin : volume (Metric.ball u₀ r) ≠ ∞ := MeasureTheory.measure_ball_lt_top.ne
  obtain ⟨y₀, -, hy₀⟩ := exists_le_setLAverage hpos hfin hΦ.aemeasurable
  refine ⟨f y₀, hy₀.trans ?_⟩
  rw [setLAverage_eq]
  refine ENNReal.div_le_of_le_mul ?_
  calc ∫⁻ y in Metric.ball u₀ r, ∫⁻ x in Metric.ball u₀ r, ‖f x - f y‖ₑ ^ 2
      ≤ ENNReal.ofReal (2 ^ (m + 2) * r ^ 2) * volume (Metric.ball u₀ r) *
          ∫⁻ z in Metric.ball u₀ r, ‖fderiv ℝ f z‖ₑ ^ 2 := d1espacep_double_integral hf u₀ hr
    _ = ENNReal.ofReal (2 ^ (m + 2) * r ^ 2) *
          (∫⁻ u in Metric.ball u₀ r, ‖fderiv ℝ f u‖ₑ ^ 2) * volume (Metric.ball u₀ r) := by
        ring

/-- **First-order spatial Poincaré** (`d1e_SpatialPoincareStatement`):
for every rank `m` the constant `C = 2^{m+2}` (chosen before the Banach target) works on every
ball. -/
theorem d1e_spatial_poincare_proof : d1e_SpatialPoincareStatement := by
  intro m
  refine ⟨2 ^ (m + 2), by positivity, ?_⟩
  intro Y _ _ _ f hf u₀ r hr
  exact d1espacep_main f hf u₀ r hr

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
