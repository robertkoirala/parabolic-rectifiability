import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ProjectionEnergy
import ParabolicRectifiability.Measure.ScaleIntegrals

/-! # Radii above `r₀` and the all-radius assembly

Proof of `d1e2_AllRadiusStatement`, the projection-energy estimate at all radii given the one at
radii at most `r₀`. No hypotheses.

Proof sketch. Put `v = (2 ω_m).toReal`; the constant is
`C = v² / 2 = 2 ω_m²`. For `s > r₀`, the zero competitor `(a, B) = (0, 0)` and `|f|² ≤ M r₀²`
give `a_f(y,s)² ≤ s^{-(m+4)} M r₀² |P_b(y,s)| = v M r₀² s^{-2}` (`affineErrorSq_le_fitIntegral`,
`parabolicVolume_ball`). Since `∫_{(r₀,∞)} s^{-2} ds/s = r₀^{-2}/2`
(`lintegral_inv_pow_Ioi_scaleMeasure`), the scale integral over `(0,R) ∩ (r₀,∞)` is at most the
constant `v M / 2` at every centre. Split `Ioo 0 R = (Ioo 0 R ∩ Iic r₀) ∪ (Ioo 0 R ∩ Ioi r₀)`
(`lintegral_union_le`), integrate in `y` over `P_b(z,R)` with `lintegral_add_right` for the
(measurable) constant and `setLIntegral_const`, and use `|P_b(z,R)| = v R^{m+2}`. The support of
`f` and the number of root components play no role.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

theorem d1e2allr_baseDimension (m : ℕ) : baseDimension (Spatial m) = m + 2 := by
  simp [baseDimension]

/-- The ball volume `2 ω_m s^{m+2}` as an `ofReal`. -/
theorem d1e2allr_volume_ball (m : ℕ) (y : Space m) {s : ℝ} (hs : 0 < s) :
    parabolicVolume m (Metric.ball y s) =
      ENNReal.ofReal ((2 * omega m).toReal * s ^ (m + 2)) := by
  have h2 : 2 * omega m ≠ ⊤ := ENNReal.mul_ne_top (by simp) (omega_lt_top m).ne
  rw [parabolicVolume_ball y s hs, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal h2, ENNReal.ofReal_pow hs.le]

/-- Zero fit at a large radius: `a_f(y,s)² ≤ v (M r₀²) s^{-2}` from `|f|² ≤ M r₀²`. -/
theorem d1e2allr_large {m d : ℕ} (f : Space m → Spatial d) (r₀ M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ p : Space m, ‖f p‖ₑ ^ 2 ≤ ENNReal.ofReal (M * r₀ ^ 2)) (y : Space m) {s : ℝ}
    (hs : 0 < s) :
    affineErrorSq (parabolicVolume m) f y s ≤
      ENNReal.ofReal ((2 * omega m).toReal * (M * r₀ ^ 2)) * (ENNReal.ofReal s)⁻¹ ^ 2 := by
  have hv : 0 ≤ (2 * omega m).toReal := ENNReal.toReal_nonneg
  have hfit : affineFitIntegral (parabolicVolume m) f 0 0 y s ≤
      ENNReal.ofReal (M * r₀ ^ 2) *
        ENNReal.ofReal ((2 * omega m).toReal * s ^ (m + 2)) := by
    calc affineFitIntegral (parabolicVolume m) f 0 0 y s
        = ∫⁻ q in Metric.ball y s,
            ‖f q - (0 + (0 : Spatial m →L[ℝ] Spatial d) q.1)‖ₑ ^ 2 ∂parabolicVolume m := rfl
      _ ≤ ∫⁻ q in Metric.ball y s, ENNReal.ofReal (M * r₀ ^ 2) ∂parabolicVolume m :=
          lintegral_mono fun q => by
            rw [zero_apply, add_zero, sub_zero]
            exact hf q
      _ = _ := by rw [setLIntegral_const, d1e2allr_volume_ball m y hs]
  refine (affineErrorSq_le_fitIntegral _ _ _ hs 0 0).trans ?_
  refine (mul_le_mul' le_rfl hfit).trans (le_of_eq ?_)
  have hMr : 0 ≤ M * r₀ ^ 2 := by positivity
  have hsp : 0 ≤ (2 * omega m).toReal * s ^ (m + 2) := by positivity
  have hsi : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
  have e1 : (ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) =
      ENNReal.ofReal (s⁻¹ ^ (m + 2 + 2)) := by
    rw [d1e2allr_baseDimension, ENNReal.ofReal_pow hsi, ENNReal.ofReal_inv_of_pos hs]
  have e2 : (ENNReal.ofReal s)⁻¹ ^ 2 = ENNReal.ofReal (s⁻¹ ^ 2) := by
    rw [ENNReal.ofReal_pow hsi, ENNReal.ofReal_inv_of_pos hs]
  rw [e1, e2, ← ENNReal.ofReal_mul hMr, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * omega m).toReal * (M * r₀ ^ 2))]
  congr 1
  have key : s⁻¹ ^ (m + 2) * s ^ (m + 2) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hs.ne', one_pow]
  calc s⁻¹ ^ (m + 2 + 2) * (M * r₀ ^ 2 * ((2 * omega m).toReal * s ^ (m + 2)))
      = (s⁻¹ ^ (m + 2) * s ^ (m + 2)) * ((2 * omega m).toReal * (M * r₀ ^ 2)) * s⁻¹ ^ 2 := by
        ring
    _ = _ := by rw [key]; ring

/-- Scale integral over `(0,R) ∩ (r₀,∞)` of the large-radius majorant: at most `v M / 2`. -/
theorem d1e2allr_scale_tail {m d : ℕ} (f : Space m → Spatial d) (r₀ M : ℝ) (hr₀ : 0 < r₀)
    (hM : 0 ≤ M) (hf : ∀ p : Space m, ‖f p‖ₑ ^ 2 ≤ ENNReal.ofReal (M * r₀ ^ 2))
    (y : Space m) (R : ℝ) :
    ∫⁻ s in Ioo 0 R ∩ Ioi r₀, affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure ≤
      ENNReal.ofReal ((2 * omega m).toReal * M / 2) := by
  have hv : 0 ≤ (2 * omega m).toReal := ENNReal.toReal_nonneg
  calc ∫⁻ s in Ioo 0 R ∩ Ioi r₀, affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure
      ≤ ∫⁻ s in Ioo 0 R ∩ Ioi r₀,
          ENNReal.ofReal ((2 * omega m).toReal * (M * r₀ ^ 2)) * (ENNReal.ofReal s)⁻¹ ^ 2
            ∂scaleMeasure :=
        setLIntegral_mono' (measurableSet_Ioo.inter measurableSet_Ioi) fun s hs =>
          d1e2allr_large f r₀ M hM hf y (hr₀.trans hs.2)
    _ ≤ ∫⁻ s in Ioi r₀,
          ENNReal.ofReal ((2 * omega m).toReal * (M * r₀ ^ 2)) * (ENNReal.ofReal s)⁻¹ ^ 2
            ∂scaleMeasure :=
        lintegral_mono_set inter_subset_right
    _ = ENNReal.ofReal ((2 * omega m).toReal * (M * r₀ ^ 2)) *
          ∫⁻ s in Ioi r₀, (ENNReal.ofReal s)⁻¹ ^ 2 ∂scaleMeasure :=
        lintegral_const_mul _ (measurable_inv_pow_ofReal 2)
    _ = ENNReal.ofReal ((2 * omega m).toReal * (M * r₀ ^ 2)) *
          ENNReal.ofReal (((r₀ ^ 2)⁻¹) / ((2 : ℕ) : ℝ)) := by
        rw [lintegral_inv_pow_Ioi_scaleMeasure 2 two_pos hr₀]
    _ = ENNReal.ofReal ((2 * omega m).toReal * M / 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        field_simp

theorem d1e2allr_proof_aux (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {d : ℕ} (f : Space m → Spatial d) (r₀ A M : ℝ), 0 < r₀ → 0 ≤ A → 0 ≤ M →
      (∀ p : Space m, ‖f p‖ₑ ^ 2 ≤ ENNReal.ofReal (M * r₀ ^ 2)) →
      (∀ (z : Space m) (R : ℝ), 0 < R →
        ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ Iic r₀,
            affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure ∂parabolicVolume m ≤
          ENNReal.ofReal (A * R ^ (m + 2))) →
      HasAffineCarlesonBound (parabolicVolume m) f (A + C * M) := by
  have hv : 0 ≤ (2 * omega m).toReal := ENNReal.toReal_nonneg
  refine ⟨(2 * omega m).toReal ^ 2 / 2, by positivity, ?_⟩
  intro d f r₀ A M hr₀ hA hM hf hsmall
  refine ⟨by positivity, fun z R hR => ?_⟩
  have hsplit : Ioo (0 : ℝ) R = (Ioo 0 R ∩ Iic r₀) ∪ (Ioo 0 R ∩ Ioi r₀) := by
    rw [← inter_union_distrib_left, Iic_union_Ioi, inter_univ]
  have hpt : ∀ y : Space m, ∫⁻ s in Ioo 0 R, affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure ≤
      ∫⁻ s in Ioo 0 R ∩ Iic r₀, affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure +
        ENNReal.ofReal ((2 * omega m).toReal * M / 2) := fun y => by
    calc ∫⁻ s in Ioo 0 R, affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure
        = ∫⁻ s in (Ioo 0 R ∩ Iic r₀) ∪ (Ioo 0 R ∩ Ioi r₀),
            affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure := by rw [← hsplit]
      _ ≤ _ := (lintegral_union_le _ _ _).trans
          (add_le_add le_rfl (d1e2allr_scale_tail f r₀ M hr₀ hM hf y R))
  calc affineCarlesonIntegral (parabolicVolume m) f z R
      = ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R,
          affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure ∂parabolicVolume m := rfl
    _ ≤ ∫⁻ y in Metric.ball z R,
          (∫⁻ s in Ioo 0 R ∩ Iic r₀, affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure +
            ENNReal.ofReal ((2 * omega m).toReal * M / 2)) ∂parabolicVolume m :=
        lintegral_mono hpt
    _ = ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ Iic r₀,
          affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure ∂parabolicVolume m +
        ENNReal.ofReal ((2 * omega m).toReal * M / 2) *
          parabolicVolume m (Metric.ball z R) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ ENNReal.ofReal (A * R ^ (m + 2)) +
        ENNReal.ofReal ((2 * omega m).toReal * M / 2) *
          ENNReal.ofReal ((2 * omega m).toReal * R ^ (m + 2)) := by
        refine add_le_add (hsmall z R hR) (mul_le_mul' le_rfl ?_)
        rw [d1e2allr_volume_ball m z hR]
    _ = ENNReal.ofReal ((A + (2 * omega m).toReal ^ 2 / 2 * M) *
          R ^ baseDimension (Spatial m)) := by
        rw [d1e2allr_baseDimension, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **Radii above `r₀` and the all-radius assembly.** The constant is `C = 2 ω_m²`. -/
theorem d1e2_all_radius_proof : d1e2_AllRadiusStatement := fun m => d1e2allr_proof_aux m

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
