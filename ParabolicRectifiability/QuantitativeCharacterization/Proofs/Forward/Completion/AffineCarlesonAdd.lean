import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion
import ParabolicRectifiability.Analysis.TraceExtension.TracePieces.Measurability

/-! # Subadditivity of the affine Carleson bound

`d1e_affineCarleson_add_proof` has the type `d1e_AffineCarlesonAddStatement`: if continuous
`f, g` satisfy affine Carleson bounds `B₁, B₂`, then `f + g` satisfies one with `2 (B₁ + B₂)`.

Route.
* **Pointwise.** For competitors `(a₁, B₁)` of `f` and `(a₂, B₂)` of `g`, the sum
  `(a₁ + a₂, B₁ + B₂)` is a competitor of `f + g`, and
  `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²` gives
  `affineErrorSq (f + g) ≤ 2 affineErrorSq f + 2 affineErrorSq g` (infima in `ℝ≥0∞`).
* **Measurability.** For continuous `f` the error `(y, s) ↦ affineErrorSq f y s`
  against the unrestricted volume is jointly measurable: for each fixed competitor the ball
  integral is jointly measurable in centre and radius (`measurable_setLIntegral_ball`); on each
  fixed ball the restricted volume is finite and `‖q.1‖` is bounded, so the fit integral is
  continuous in the competitor (`continuous_lintegral_enorm_sub_affine_sq`) and the infimum is
  the infimum over a dense sequence (`iInf_eq_iInf_denseRange`). This is the unrestricted
  adapter of `measurable_traceErrorSq_of_isCompact_proof`.
* **Integration.** Tonelli's additivity (`lintegral_add_left`) in the scale and then the centre
  variable, and the two Carleson bounds.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

section CarlesonAdd

variable {m d : ℕ}

/-- `‖x + y‖ₑ² ≤ 2‖x‖ₑ² + 2‖y‖ₑ²`. -/
theorem d1ecarladd_enorm_add_sq_le {Y : Type*} [NormedAddCommGroup Y] (x y : Y) :
    ‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  have h : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    have h1 := norm_add_le x y
    have h2 : 0 ≤ ‖x + y‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  calc ‖x + y‖ₑ ^ 2 = ENNReal.ofReal (‖x + y‖ ^ 2) := by
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) := ENNReal.ofReal_le_ofReal h
    _ = 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
          ofReal_norm, ofReal_norm, ENNReal.ofReal_ofNat]

/-- The fit integral of the summed competitor is at most twice the sum of the fit integrals. -/
theorem d1ecarladd_fitIntegral_add_le (μ : Measure (Space m)) (f g : Space m → Spatial d)
    (hf : Measurable f) (a₁ a₂ : Spatial d) (B₁ B₂ : Spatial m →L[ℝ] Spatial d)
    (y : Space m) (s : ℝ) :
    affineFitIntegral μ (f + g) (a₁ + a₂) (B₁ + B₂) y s ≤
      2 * affineFitIntegral μ f a₁ B₁ y s + 2 * affineFitIntegral μ g a₂ B₂ y s := by
  unfold affineFitIntegral
  have hm : Measurable fun q : Space m => 2 * ‖f q - (a₁ + B₁ q.1)‖ₑ ^ 2 :=
    ((hf.sub (measurable_const.add (B₁.continuous.measurable.comp measurable_fst))).enorm.pow_const
      2).const_mul 2
  calc ∫⁻ q in Metric.ball y s, ‖(f + g) q - (a₁ + a₂ + (B₁ + B₂) q.1)‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ q in Metric.ball y s,
          (2 * ‖f q - (a₁ + B₁ q.1)‖ₑ ^ 2 + 2 * ‖g q - (a₂ + B₂ q.1)‖ₑ ^ 2) ∂μ := by
        refine lintegral_mono fun q => ?_
        have hq : (f + g) q - (a₁ + a₂ + (B₁ + B₂) q.1) =
            (f q - (a₁ + B₁ q.1)) + (g q - (a₂ + B₂ q.1)) := by
          simp only [Pi.add_apply, add_apply]
          abel
        rw [hq]
        exact d1ecarladd_enorm_add_sq_le _ _
    _ = 2 * ∫⁻ q in Metric.ball y s, ‖f q - (a₁ + B₁ q.1)‖ₑ ^ 2 ∂μ +
          2 * ∫⁻ q in Metric.ball y s, ‖g q - (a₂ + B₂ q.1)‖ₑ ^ 2 ∂μ := by
        rw [lintegral_add_left hm, lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]

/-- **Pointwise subadditivity**: `κ_{f+g}² ≤ 2 κ_f² + 2 κ_g²` at every centre and radius. -/
theorem d1ecarladd_affineErrorSq_add_le (μ : Measure (Space m)) (f g : Space m → Spatial d)
    (hf : Measurable f) (y : Space m) (s : ℝ) :
    affineErrorSq μ (f + g) y s ≤ 2 * affineErrorSq μ f y s + 2 * affineErrorSq μ g y s := by
  rcases le_or_gt s 0 with hs | hs
  · simp only [affineErrorSq_of_nonpos _ _ _ hs, mul_zero, add_zero, le_refl]
  rw [affineErrorSq_of_pos _ _ _ hs, affineErrorSq_of_pos _ _ _ hs,
    affineErrorSq_of_pos _ _ _ hs]
  set c := (ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) with hc
  have key : (⨅ (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d),
        affineFitIntegral μ (f + g) a B y s) ≤
      2 * (⨅ (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d), affineFitIntegral μ f a B y s) +
        2 * ⨅ (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d), affineFitIntegral μ g a B y s := by
    simp_rw [ENNReal.mul_iInf_of_ne (two_ne_zero) ENNReal.ofNat_ne_top]
    refine ENNReal.le_iInf_add_iInf fun a₁ a₂ => ENNReal.le_iInf_add_iInf fun B₁ B₂ => ?_
    exact (iInf_le_of_le (a₁ + a₂) (iInf_le _ (B₁ + B₂))).trans
      (d1ecarladd_fitIntegral_add_le μ f g hf a₁ a₂ B₁ B₂ y s)
  calc c * ⨅ (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d), affineFitIntegral μ (f + g) a B y s
      ≤ c * (2 * (⨅ (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d),
          affineFitIntegral μ f a B y s) +
        2 * ⨅ (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d), affineFitIntegral μ g a B y s) :=
        mul_le_mul_right key c
    _ = 2 * (c * ⨅ (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d),
          affineFitIntegral μ f a B y s) +
        2 * (c * ⨅ (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d),
          affineFitIntegral μ g a B y s) := by ring

/-- **Joint measurability** of the unrestricted affine error of a continuous function against
the base volume. -/
theorem d1ecarladd_measurable_affineErrorSq (f : Space m → Spatial d) (hf : Continuous f) :
    Measurable (fun z : Space m × ℝ => affineErrorSq (parabolicVolume m) f z.1 z.2) := by
  classical
  have hfm : Measurable f := hf.measurable
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Spatial d × (Spatial m →L[ℝ] Spatial d) → Space m × ℝ → ℝ≥0∞,
      Φ = fun x z =>
        ∫⁻ q in Metric.ball z.1 z.2, ‖f q - (x.1 + x.2 q.1)‖ₑ ^ 2 ∂parabolicVolume m :=
    ⟨_, rfl⟩
  have hΦm : ∀ x, Measurable (Φ x) := fun x => by
    rw [hΦ]
    exact measurable_setLIntegral_ball _ ((hfm.sub (measurable_const.add
      (x.2.continuous.measurable.comp measurable_fst))).enorm.pow_const 2)
  have hΦc : ∀ z : Space m × ℝ, Continuous fun x => Φ x z := fun z => by
    have _ : IsFiniteMeasure ((parabolicVolume m).restrict (Metric.ball z.1 z.2)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact MeasureTheory.measure_ball_lt_top⟩
    have hD : ∀ᵐ q ∂(parabolicVolume m).restrict (Metric.ball z.1 z.2),
        ‖q.1‖ ≤ ‖z.1.1‖ + |z.2| := by
      refine ae_restrict_of_forall_mem measurableSet_ball fun q hq => ?_
      have h1 : dist q.1 z.1.1 ≤ dist q z.1 := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      have h2 : dist q z.1 < z.2 := hq
      have h3 : ‖q.1‖ - ‖z.1.1‖ ≤ ‖q.1 - z.1.1‖ := norm_sub_norm_le _ _
      rw [← dist_eq_norm] at h3
      have h4 : z.2 ≤ |z.2| := le_abs_self _
      linarith
    rw [hΦ]
    exact continuous_lintegral_enorm_sub_affine_sq
      ((parabolicVolume m).restrict (Metric.ball z.1 z.2)) hfm.aestronglyMeasurable
      measurable_fst.aestronglyMeasurable (by positivity) hD
  have hd := TopologicalSpace.denseRange_denseSeq (Spatial d × (Spatial m →L[ℝ] Spatial d))
  have hinf : ∀ z, (⨅ (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d), Φ (a, B) z) =
      ⨅ i, Φ (TopologicalSpace.denseSeq (Spatial d × (Spatial m →L[ℝ] Spatial d)) i) z := by
    intro z
    exact (iInf_prod (f := fun x => Φ x z)).symm.trans (iInf_eq_iInf_denseRange hd (hΦc z))
  have heq : (fun z : Space m × ℝ => affineErrorSq (parabolicVolume m) f z.1 z.2) =
      fun z => if 0 < z.2 then (ENNReal.ofReal z.2)⁻¹ ^ (baseDimension (Spatial m) + 2) *
        ⨅ i, Φ (TopologicalSpace.denseSeq (Spatial d × (Spatial m →L[ℝ] Spatial d)) i) z
        else 0 := by
    funext z
    rw [← hinf z, hΦ]
    rfl
  rw [heq]
  refine Measurable.ite (measurableSet_lt measurable_const measurable_snd) ?_ measurable_const
  exact ((ENNReal.measurable_ofReal.comp measurable_snd).inv.pow_const _).mul
    (Measurable.iInf fun i => hΦm _)

end CarlesonAdd

/-- **Subadditivity of the affine Carleson bound** (`d1e_AffineCarlesonAddStatement`): for
continuous `f, g : Space m → ℝ^d`, affine Carleson bounds `B₁, B₂` give `2 (B₁ + B₂)` for
`f + g`. -/
theorem d1e_affineCarleson_add_proof : d1e_AffineCarlesonAddStatement := by
  intro m d f g B₁ B₂ hf hg hF hG
  refine ⟨by linarith [hF.1, hG.1], fun z R hR => ?_⟩
  have hmf := d1ecarladd_measurable_affineErrorSq f hf
  have hmg := d1ecarladd_measurable_affineErrorSq g hg
  have hsf : ∀ y : Space m, Measurable fun s => affineErrorSq (parabolicVolume m) f y s :=
    fun y => hmf.comp measurable_prodMk_left
  have hsg : ∀ y : Space m, Measurable fun s => affineErrorSq (parabolicVolume m) g y s :=
    fun y => hmg.comp measurable_prodMk_left
  have hIf : Measurable fun y : Space m =>
      ∫⁻ s in Ioo 0 R, affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure :=
    hmf.lintegral_prod_right'
  have hIg : Measurable fun y : Space m =>
      ∫⁻ s in Ioo 0 R, affineErrorSq (parabolicVolume m) g y s ∂scaleMeasure :=
    hmg.lintegral_prod_right'
  have hk0 : (0 : ℝ) ≤ R ^ baseDimension (Spatial m) := by positivity
  unfold affineCarlesonIntegral
  calc ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R,
        affineErrorSq (parabolicVolume m) (f + g) y s ∂scaleMeasure ∂parabolicVolume m
      ≤ ∫⁻ y in Metric.ball z R,
          (2 * ∫⁻ s in Ioo 0 R, affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure +
            2 * ∫⁻ s in Ioo 0 R, affineErrorSq (parabolicVolume m) g y s ∂scaleMeasure)
          ∂parabolicVolume m := by
        refine lintegral_mono fun y => ?_
        calc ∫⁻ s in Ioo 0 R, affineErrorSq (parabolicVolume m) (f + g) y s ∂scaleMeasure
            ≤ ∫⁻ s in Ioo 0 R, (2 * affineErrorSq (parabolicVolume m) f y s +
                2 * affineErrorSq (parabolicVolume m) g y s) ∂scaleMeasure :=
              lintegral_mono fun s => d1ecarladd_affineErrorSq_add_le _ f g hf.measurable y s
          _ = _ := by
              rw [lintegral_add_left ((hsf y).const_mul 2),
                lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
                lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    _ = 2 * affineCarlesonIntegral (parabolicVolume m) f z R +
          2 * affineCarlesonIntegral (parabolicVolume m) g z R := by
        rw [lintegral_add_left (hIf.const_mul 2), lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
        rfl
    _ ≤ 2 * ENNReal.ofReal (B₁ * R ^ baseDimension (Spatial m)) +
          2 * ENNReal.ofReal (B₂ * R ^ baseDimension (Spatial m)) :=
        add_le_add (mul_le_mul_right (hF.2 z R hR) 2) (mul_le_mul_right (hG.2 z R hR) 2)
    _ = ENNReal.ofReal (2 * (B₁ + B₂) * R ^ baseDimension (Spatial m)) := by
        have h1 : 0 ≤ B₁ * R ^ baseDimension (Spatial m) := mul_nonneg hF.1 hk0
        have h2 : 0 ≤ B₂ * R ^ baseDimension (Spatial m) := mul_nonneg hG.1 hk0
        rw [show 2 * (B₁ + B₂) * R ^ baseDimension (Spatial m) =
            2 * (B₁ * R ^ baseDimension (Spatial m)) + 2 * (B₂ * R ^ baseDimension (Spatial m)) by
              ring,
          ENNReal.ofReal_add (mul_nonneg zero_le_two h1) (mul_nonneg zero_le_two h2),
          ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
