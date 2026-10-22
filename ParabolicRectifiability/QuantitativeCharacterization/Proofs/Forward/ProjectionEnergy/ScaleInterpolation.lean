import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ProjectionEnergy

/-! # Interpolation between the discrete radii

Proof of `d1e2_scale_interpolation_proof : d1e2_ScaleInterpolationStatement`.

Route: every `s ∈ (0,R) ∩ (0,r₀]` lies in some
`(r_{j+1}, r_j]` with `r_{j+1} < R` (`r_j = 10^{-j} r₀ → 0`); countable subadditivity
(`lintegral_iUnion_le`, no measurability of the affine error); on `(r_{j+1}, r_j]` the ball
inclusion `P_b(y,s) ⊆ P_b(y,r_j)` and `r_j ≤ 10 s` give `a_f(y,s)² ≤ 10^{k+2} a_f(y,r_j)²`
(`k = baseDimension (Spatial m) = m + 2`); the `dr/r` mass of `(r_{j+1}, r_j]` is at most `9`.
Constant `C = 9 · 10^{k+2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

theorem d1e2interp_ratio_eq : CoherentChart.ratio = 1 / 10 := rfl

/-- Positivity of the geometric radii. -/
theorem d1e2interp_pos {r : ℕ → ℝ} (h0 : 0 < r 0)
    (hr : ∀ j, r (j + 1) = CoherentChart.ratio * r j) (j : ℕ) : 0 < r j := by
  induction j with
  | zero => exact h0
  | succ k ih =>
    rw [hr k, d1e2interp_ratio_eq]
    positivity

/-- Closed form `r_j = h^j r_0`. -/
theorem d1e2interp_eq_pow {r : ℕ → ℝ}
    (hr : ∀ j, r (j + 1) = CoherentChart.ratio * r j) (j : ℕ) :
    r j = CoherentChart.ratio ^ j * r 0 := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [hr k, ih, pow_succ]
    ring

/-- Every `s ∈ (0, r_0]` lies in a geometric annulus `(r_{j+1}, r_j]`. -/
theorem d1e2interp_cover {r : ℕ → ℝ} (h0 : 0 < r 0)
    (hr : ∀ j, r (j + 1) = CoherentChart.ratio * r j) {s : ℝ} (hs : 0 < s)
    (hs0 : s ≤ r 0) : ∃ j, r (j + 1) < s ∧ s ≤ r j := by
  classical
  have hex : ∃ n, r n < s := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hs h0)
      (show CoherentChart.ratio < 1 by rw [d1e2interp_ratio_eq]; norm_num)
    refine ⟨n, ?_⟩
    rw [d1e2interp_eq_pow hr n]
    exact (lt_div_iff₀ h0).1 hn
  have hne : Nat.find hex ≠ 0 := by
    intro h
    have h' := Nat.find_spec hex
    rw [h] at h'
    exact absurd hs0 (not_le.2 h')
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
  refine ⟨j, ?_, ?_⟩
  · have h' := Nat.find_spec hex
    rw [hj] at h'
    exact h'
  · have hmin := Nat.find_min hex (show j < Nat.find hex by omega)
    exact not_lt.1 hmin

/-- On `s ≤ t ≤ 10 s` the affine error at `s` is at most `10^{k+2}` times the one at `t`
(ball inclusion and the normalization). Generic in the measure and the map. -/
theorem d1e2interp_affineErrorSq_le {E Y : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (μ : Measure (E × Time)) (f : E × Time → Y) (y : E × Time) {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) (ht : t ≤ 10 * s) :
    affineErrorSq μ f y s ≤ 10 ^ (baseDimension E + 2) * affineErrorSq μ f y t := by
  have ht0 : 0 < t := hs.trans_le hst
  rw [affineErrorSq_of_pos μ f y hs, affineErrorSq_of_pos μ f y ht0]
  have hinf : (⨅ (a : Y) (B : E →L[ℝ] Y), affineFitIntegral μ f a B y s) ≤
      ⨅ (a : Y) (B : E →L[ℝ] Y), affineFitIntegral μ f a B y t :=
    iInf_mono fun a => iInf_mono fun B => lintegral_mono_set (Metric.ball_subset_ball hst)
  have hreal : s⁻¹ ≤ 10 * t⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hs ht0]
    linarith
  have hpre : (ENNReal.ofReal s)⁻¹ ≤ 10 * (ENNReal.ofReal t)⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos hs, ← ENNReal.ofReal_inv_of_pos ht0,
      ← ENNReal.ofReal_ofNat 10, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hreal
  calc (ENNReal.ofReal s)⁻¹ ^ (baseDimension E + 2) *
        ⨅ (a : Y) (B : E →L[ℝ] Y), affineFitIntegral μ f a B y s
      ≤ (10 * (ENNReal.ofReal t)⁻¹) ^ (baseDimension E + 2) *
        ⨅ (a : Y) (B : E →L[ℝ] Y), affineFitIntegral μ f a B y t :=
        mul_le_mul' (pow_le_pow_left' hpre _) hinf
    _ = 10 ^ (baseDimension E + 2) * ((ENNReal.ofReal t)⁻¹ ^ (baseDimension E + 2) *
        ⨅ (a : Y) (B : E →L[ℝ] Y), affineFitIntegral μ f a B y t) := by
      rw [mul_pow, mul_assoc]

/-- The `dr/r` mass of a geometric annulus `(h r, r]` is at most `9`. -/
theorem d1e2interp_scaleMeasure_annulus_le {a : ℝ} (ha : 0 < a) (S : Set ℝ)
    (hS : S ⊆ Icc (CoherentChart.ratio * a) a) : scaleMeasure S ≤ 9 := by
  have hpos : 0 < CoherentChart.ratio * a := by rw [d1e2interp_ratio_eq]; positivity
  calc scaleMeasure S ≤ scaleMeasure (Icc (CoherentChart.ratio * a) a) := measure_mono hS
    _ ≤ ENNReal.ofReal (1 / (CoherentChart.ratio * a)) *
        ENNReal.ofReal (a - CoherentChart.ratio * a) := scaleMeasure_Icc_le hpos
    _ = 9 := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have : 1 / (CoherentChart.ratio * a) * (a - CoherentChart.ratio * a) = 9 := by
        rw [d1e2interp_ratio_eq]
        field_simp
        ring
      rw [this]
      norm_num

/-- **Interpolation between the discrete radii**: the type `d1e2_ScaleInterpolationStatement`. -/
theorem d1e2_scale_interpolation_proof : d1e2_ScaleInterpolationStatement := by
  intro m
  refine ⟨9 * 10 ^ (baseDimension (Spatial m) + 2), by positivity, ?_⟩
  intro d f r h0 hr y R
  have hC : ENNReal.ofReal (9 * 10 ^ (baseDimension (Spatial m) + 2)) =
      9 * 10 ^ (baseDimension (Spatial m) + 2) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num)]
    norm_num
  have hcover : Ioo 0 R ∩ Iic (r 0) ⊆ ⋃ j, Ioc (r (j + 1)) (r j) ∩ Ioo 0 R := by
    rintro s ⟨⟨hs0, hsR⟩, hsr⟩
    obtain ⟨j, h1, h2⟩ := d1e2interp_cover h0 hr hs0 hsr
    exact mem_iUnion.2 ⟨j, ⟨h1, h2⟩, hs0, hsR⟩
  have hterm : ∀ j : ℕ,
      ∫⁻ s in Ioc (r (j + 1)) (r j) ∩ Ioo 0 R,
          affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure ≤
        ENNReal.ofReal (9 * 10 ^ (baseDimension (Spatial m) + 2)) *
          (if r (j + 1) < R then affineErrorSq (parabolicVolume m) f y (r j) else 0) := by
    intro j
    have hmeas : MeasurableSet (Ioc (r (j + 1)) (r j) ∩ Ioo 0 R) :=
      measurableSet_Ioc.inter measurableSet_Ioo
    split_ifs with hj
    · have hpt : ∀ s ∈ Ioc (r (j + 1)) (r j) ∩ Ioo 0 R,
          affineErrorSq (parabolicVolume m) f y s ≤
            10 ^ (baseDimension (Spatial m) + 2) *
              affineErrorSq (parabolicVolume m) f y (r j) := by
        rintro s ⟨⟨h1, h2⟩, hs0, -⟩
        refine d1e2interp_affineErrorSq_le (parabolicVolume m) f y hs0 h2 ?_
        have := hr j
        rw [d1e2interp_ratio_eq] at this
        linarith
      have hmass : scaleMeasure (Ioc (r (j + 1)) (r j) ∩ Ioo 0 R) ≤ 9 := by
        refine d1e2interp_scaleMeasure_annulus_le (d1e2interp_pos h0 hr j) _ ?_
        rintro s ⟨⟨h1, h2⟩, -⟩
        exact ⟨(hr j) ▸ h1.le, h2⟩
      calc ∫⁻ s in Ioc (r (j + 1)) (r j) ∩ Ioo 0 R,
            affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure
          ≤ ∫⁻ _s in Ioc (r (j + 1)) (r j) ∩ Ioo 0 R,
            10 ^ (baseDimension (Spatial m) + 2) *
              affineErrorSq (parabolicVolume m) f y (r j) ∂scaleMeasure :=
            setLIntegral_mono' hmeas hpt
        _ = 10 ^ (baseDimension (Spatial m) + 2) *
              affineErrorSq (parabolicVolume m) f y (r j) *
              scaleMeasure (Ioc (r (j + 1)) (r j) ∩ Ioo 0 R) := setLIntegral_const _ _
        _ ≤ 10 ^ (baseDimension (Spatial m) + 2) *
              affineErrorSq (parabolicVolume m) f y (r j) * 9 := mul_le_mul' le_rfl hmass
        _ = ENNReal.ofReal (9 * 10 ^ (baseDimension (Spatial m) + 2)) *
              affineErrorSq (parabolicVolume m) f y (r j) := by
            rw [hC]
            ring
    · have hempty : Ioc (r (j + 1)) (r j) ∩ Ioo 0 R = ∅ := by
        refine eq_empty_of_forall_notMem ?_
        rintro s ⟨⟨h1, -⟩, -, hsR⟩
        exact hj (h1.trans hsR)
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
      exact zero_le
  calc ∫⁻ s in Ioo 0 R ∩ Iic (r 0), affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure
      ≤ ∫⁻ s in ⋃ j, Ioc (r (j + 1)) (r j) ∩ Ioo 0 R,
          affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure := lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ s in Ioc (r (j + 1)) (r j) ∩ Ioo 0 R,
          affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure := lintegral_iUnion_le _ _
    _ ≤ ∑' j, ENNReal.ofReal (9 * 10 ^ (baseDimension (Spatial m) + 2)) *
          (if r (j + 1) < R then affineErrorSq (parabolicVolume m) f y (r j) else 0) :=
        ENNReal.tsum_le_tsum hterm
    _ = _ := ENNReal.tsum_mul_left

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
