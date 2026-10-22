import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ProjectionEnergy
import ParabolicRectifiability.Analysis.TraceExtension.TracePieces.Measurability

/-! # The integrated energy at radii at most `r₀`

Proof of `d1e2_small_radii_proof`, in its implication form

`d1e2_ScaleInterpolationStatement → d1e2_KernelIntegrationStatement → d1e2_SmallRadiiStatement`.

Both statements enter as hypotheses.

Route. Fix `m`, the interpolation constant `C₁` and
the kernel constant `C₂`. For each centre `y`, the interpolation premise and the discrete
hypothesis give, pointwise,
`∫_{(0,R) ∩ (0,r₀]} a_f(y,s)² ds/s ≤ C₁ ∑_j [r_{j+1} < R] A r_j^{-(m+2)} ∫_{P_b(y,r_j)} W_j`.
Each summand is measurable in `y` (base `measurable_setLIntegral_ball` along `y ↦ (y, r_j)`;
only the measurable `W_j` is integrated, never the affine error), so the `y`-integral over
`P_b(z,R)` commutes with the sum (`lintegral_tsum`). For a selected level `r_{j+1} < R` gives
`r_j = 10 r_{j+1} < 10 R`, and the kernel premise bounds the level by
`A C₂ ∫_{P_b(z,11R)} W_j`. Finally `∑_j ∫ W_j = ∫ ∑_j W_j ≤ M |P_b(z,11R)|` and
`|P_b(z,11R)| = 2ω_m 11^{m+2} R^{m+2}` (base `parabolicVolume_ball`). The constant is
`C = C₁ C₂ (2ω_m).toReal 11^{m+2}`. A negative `A` or `M` never occurs (the statement assumes
`0 ≤ A`, `0 ≤ M`); the right side is `ENNReal.ofReal` of a nonnegative real.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-- The geometric radii `r_{j+1} = h r_j` with `r_0 > 0` are positive. -/
theorem d1e2small_radius_pos {r : ℕ → ℝ} (hr0 : 0 < r 0)
    (hrec : ∀ j, r (j + 1) = CoherentChart.ratio * r j) (j : ℕ) : 0 < r j := by
  induction j with
  | zero => exact hr0
  | succ j ih =>
    rw [hrec j]
    exact mul_pos CoherentChart.ratio_pos ih

/-- The buffer of the selected levels: `r_{j+1} < R` gives `r_j ≤ 10 R`. -/
theorem d1e2small_radius_le {r : ℕ → ℝ} (hrec : ∀ j, r (j + 1) = CoherentChart.ratio * r j)
    {R : ℝ} {j : ℕ} (h : r (j + 1) < R) : r j ≤ 10 * R := by
  have h1 : r (j + 1) = 1 / 10 * r j := by rw [hrec j, CoherentChart.ratio]
  linarith

/-- Ball integrals of a fixed measurable integrand at a fixed radius are measurable in the
centre (base `measurable_setLIntegral_ball` composed with `y ↦ (y, ρ)`). -/
theorem d1e2small_measurable_ballIntegral {m : ℕ} {W : Space m → ℝ≥0∞} (hW : Measurable W)
    (ρ : ℝ) : Measurable fun y : Space m => ∫⁻ q in Metric.ball y ρ, W q ∂parabolicVolume m := by
  have h := (measurable_setLIntegral_ball (parabolicVolume m) hW).comp
    (measurable_id.prodMk measurable_const : Measurable fun y : Space m => (y, ρ))
  exact h

/-- The volume of the buffered ball, as `ENNReal.ofReal` of a real. -/
theorem d1e2small_volume_ball {m : ℕ} (z : Space m) {ρ : ℝ} (hρ : 0 < ρ) :
    parabolicVolume m (Metric.ball z ρ) =
      ENNReal.ofReal ((2 * omega m).toReal * ρ ^ (m + 2)) := by
  rw [parabolicVolume_ball z ρ hρ, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (ENNReal.mul_ne_top (by simp) (omega_lt_top m).ne),
    ENNReal.ofReal_pow hρ.le]

/-- **The integrated energy at radii at most `r₀`** (`d1e2_small_radii_proof`, implication form):
from the interpolation and kernel statements, the integrated energy at radii at most
`r₀` is at most `C A M R^{m+2}` with `C = C₁ C₂ (2ω_m).toReal 11^{m+2}`. -/
theorem d1e2_small_radii_proof :
    d1e2_ScaleInterpolationStatement → d1e2_KernelIntegrationStatement →
      d1e2_SmallRadiiStatement := by
  intro hI hK m
  obtain ⟨C₁, hC₁, hI⟩ := hI m
  obtain ⟨C₂, hC₂, hK⟩ := hK m
  refine ⟨C₁ * C₂ * (2 * omega m).toReal * 11 ^ (m + 2),
    mul_nonneg (mul_nonneg (mul_nonneg hC₁ hC₂) ENNReal.toReal_nonneg) (by positivity), ?_⟩
  intro d f r W A M hr0 hrec hA hM hWm hWsum hdisc z R hR
  have hpos : ∀ j, 0 < r j := d1e2small_radius_pos hr0 hrec
  -- Step 1: pointwise in `y`, interpolation followed by the discrete estimate.
  have hpt : ∀ y : Space m,
      ∫⁻ s in Ioo 0 R ∩ Iic (r 0), affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure ≤
        ENNReal.ofReal C₁ * ∑' j, (if r (j + 1) < R then ENNReal.ofReal A *
          ((ENNReal.ofReal (r j))⁻¹ ^ (m + 2) *
            ∫⁻ q in Metric.ball y (r j), W j q ∂parabolicVolume m) else 0) := by
    intro y
    refine (hI f r hr0 hrec y R).trans ?_
    gcongr ENNReal.ofReal C₁ * ?_
    refine ENNReal.tsum_le_tsum fun j => ?_
    by_cases h : r (j + 1) < R
    · simp only [ite_eq_left h]
      exact (hdisc y j).trans_eq (mul_assoc _ _ _)
    · simp only [ite_eq_right h, le_refl]
  -- Step 2: each summand is measurable in `y` (only the measurable `W j` is integrated).
  have hmeas : ∀ j, Measurable fun y : Space m =>
      (if r (j + 1) < R then ENNReal.ofReal A *
        ((ENNReal.ofReal (r j))⁻¹ ^ (m + 2) *
          ∫⁻ q in Metric.ball y (r j), W j q ∂parabolicVolume m) else 0) := by
    intro j
    by_cases h : r (j + 1) < R
    · simp only [ite_eq_left h]
      exact ((d1e2small_measurable_ballIntegral (hWm j) (r j)).const_mul _).const_mul _
    · simp only [ite_eq_right h]
      exact measurable_const
  -- Step 3: the averaging kernel at each selected level, with the `11 R` buffer.
  have hterm : ∀ j, ∫⁻ y in Metric.ball z R,
      (if r (j + 1) < R then ENNReal.ofReal A *
        ((ENNReal.ofReal (r j))⁻¹ ^ (m + 2) *
          ∫⁻ q in Metric.ball y (r j), W j q ∂parabolicVolume m) else 0) ∂parabolicVolume m ≤
      ENNReal.ofReal A * ENNReal.ofReal C₂ *
        ∫⁻ q in Metric.ball z (11 * R), W j q ∂parabolicVolume m := by
    intro j
    by_cases h : r (j + 1) < R
    · simp only [ite_eq_left h]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc (ENNReal.ofReal A)]
      gcongr ENNReal.ofReal A * ?_
      exact hK (W j) (hWm j) z R (r j) (hpos j) (d1e2small_radius_le hrec h)
    · simp only [ite_eq_right h, lintegral_zero, zero_le]
  -- Step 4: sum, exchange `∑` and `∫` for the measurable `W j`, and the volume of `P_b(z,11R)`.
  have h11 : (0 : ℝ) < 11 * R := mul_pos (by norm_num) hR
  calc ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ Iic (r 0),
          affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure ∂parabolicVolume m
      ≤ ∫⁻ y in Metric.ball z R, ENNReal.ofReal C₁ * ∑' j, (if r (j + 1) < R then
          ENNReal.ofReal A * ((ENNReal.ofReal (r j))⁻¹ ^ (m + 2) *
            ∫⁻ q in Metric.ball y (r j), W j q ∂parabolicVolume m) else 0)
          ∂parabolicVolume m :=
        lintegral_mono hpt
    _ = ENNReal.ofReal C₁ * ∑' j, ∫⁻ y in Metric.ball z R, (if r (j + 1) < R then
          ENNReal.ofReal A * ((ENNReal.ofReal (r j))⁻¹ ^ (m + 2) *
            ∫⁻ q in Metric.ball y (r j), W j q ∂parabolicVolume m) else 0)
          ∂parabolicVolume m := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_tsum fun j => (hmeas j).aemeasurable]
    _ ≤ ENNReal.ofReal C₁ * ∑' j, ENNReal.ofReal A * ENNReal.ofReal C₂ *
          ∫⁻ q in Metric.ball z (11 * R), W j q ∂parabolicVolume m := by
        gcongr ENNReal.ofReal C₁ * ?_
        exact ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal C₁ * (ENNReal.ofReal A * ENNReal.ofReal C₂ *
          ∫⁻ q in Metric.ball z (11 * R), ∑' j, W j q ∂parabolicVolume m) := by
        rw [ENNReal.tsum_mul_left, lintegral_tsum fun j => (hWm j).aemeasurable]
    _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal A * ENNReal.ofReal C₂ *
          ∫⁻ _ in Metric.ball z (11 * R), ENNReal.ofReal M ∂parabolicVolume m) := by
        gcongr ENNReal.ofReal C₁ * (ENNReal.ofReal A * ENNReal.ofReal C₂ * ?_)
        exact lintegral_mono fun q => hWsum q
    _ = ENNReal.ofReal (C₁ * C₂ * (2 * omega m).toReal * 11 ^ (m + 2) * A * M * R ^ (m + 2)) := by
        rw [setLIntegral_const, d1e2small_volume_ball z h11, ← ENNReal.ofReal_mul hM,
          ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (mul_nonneg hA hC₂),
          ← ENNReal.ofReal_mul hC₁, mul_pow]
        congr 1
        ring

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
