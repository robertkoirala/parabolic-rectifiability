import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # Coefficient-to-annulus comparison

For `Λ ≥ 1`, `ℓ > 0` and `d_P(x, z) < 2ℓ`:
`β_μ(z, Λℓ)² ≤ 2·6^{k+2} ∫_{(Λ+2)ℓ}^{2(Λ+2)ℓ} β_μ(x, r)² dr/r`, any source and any family.

Route: for `r` in the window `W = ((Λ+2)ℓ, 2(Λ+2)ℓ)`, `P(z, Λℓ) ⊆ P(x, r)` and
`r/(Λℓ) < 2 + 4/Λ ≤ 6`, so the base `betaSq_le_of_ball_subset` gives
`β(z, Λℓ)² ≤ 6^{k+2} β(x, r)²`; integrating the constant over `W`, whose `dr/r` mass is
`log 2 ≥ 1/2` (here bounded below directly by `1/(2c) · c` with `c = (Λ+2)ℓ`), gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

open ParabolicRectifiability.Foundations

/-- The `dr/r` mass of the window `(c, 2c)` is at least `1/2` (it is `log 2`). -/
theorem d1aann_half_le_scaleMeasure {c : ℝ} (hc : 0 < c) :
    ENNReal.ofReal (1 / 2) ≤ scaleMeasure (Ioo c (2 * c)) := by
  have hpos : Ioo c (2 * c) ⊆ Ioi 0 := fun r hr => hc.trans hr.1
  rw [scaleMeasure_apply _ measurableSet_Ioo, inter_eq_left.mpr hpos]
  have hc0 : c ≠ 0 := hc.ne'
  have hreal : (1 : ℝ) / 2 = 1 / (2 * c) * (2 * c - c) := by
    rw [show 2 * c - c = c by ring]
    field_simp
  calc ENNReal.ofReal (1 / 2)
      = ENNReal.ofReal (1 / (2 * c)) * volume (Ioo c (2 * c)) := by
        rw [Real.volume_Ioo, ← ENNReal.ofReal_mul (div_nonneg zero_le_one (by linarith)), ← hreal]
    _ = ∫⁻ _r in Ioo c (2 * c), ENNReal.ofReal (1 / (2 * c)) ∂volume :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in Ioo c (2 * c), ENNReal.ofReal (1 / r) ∂volume := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro r hr
        exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (hc.trans hr.1) hr.2.le)

/-- On the window, the coefficient ball lies in the test ball with radius ratio at most `6`. -/
theorem d1aann_betaSq_le_window {n k : ℕ} (μ : Measure (Space n)) (T : FamilyKind)
    {Λ ℓ : ℝ} {z x : Space n} (hΛ : 1 ≤ Λ) (hℓ : 0 < ℓ) (hxz : dist x z < 2 * ℓ)
    {r : ℝ} (hr : r ∈ Ioo ((Λ + 2) * ℓ) (2 * ((Λ + 2) * ℓ))) :
    betaSq μ k T z (Λ * ℓ) ≤ ENNReal.ofReal 6 ^ (k + 2) * betaSq μ k T x r := by
  have hΛℓ : 0 < Λ * ℓ := mul_pos (by linarith) hℓ
  have hc : 0 < (Λ + 2) * ℓ := mul_pos (by linarith) hℓ
  have hr0 : 0 < r := hc.trans hr.1
  have hsub : Metric.ball z (Λ * ℓ) ⊆ Metric.ball x r := by
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    have hzx : dist z x < 2 * ℓ := by rw [dist_comm]; exact hxz
    have h1 : dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
    have h2 : (Λ + 2) * ℓ < r := hr.1
    linarith
  have hℓΛ : ℓ ≤ Λ * ℓ := le_mul_of_one_le_left hℓ.le hΛ
  have hratio : r / (Λ * ℓ) ≤ 6 := by
    rw [div_le_iff₀ hΛℓ]
    have h2 : r < 2 * ((Λ + 2) * ℓ) := hr.2
    linarith
  calc betaSq μ k T z (Λ * ℓ)
      ≤ ENNReal.ofReal (r / (Λ * ℓ)) ^ (k + 2) * betaSq μ k T x r :=
        betaSq_le_of_ball_subset μ k T hΛℓ hr0 hsub
    _ ≤ ENNReal.ofReal 6 ^ (k + 2) * betaSq μ k T x r :=
        mul_le_mul' (pow_le_pow_left' (ENNReal.ofReal_le_ofReal hratio) _) le_rfl

/-- **Coefficient-to-annulus comparison** (`CoeffAnnulusStatement`). -/
theorem d1a_coeffAnnulus_proof : CoeffAnnulusStatement := by
  intro n k μ T Λ ℓ z x hΛ hℓ hxz
  have hc : 0 < (Λ + 2) * ℓ := mul_pos (by linarith) hℓ
  have hW := d1aann_half_le_scaleMeasure hc
  have h6 : ENNReal.ofReal 6 ^ (k + 2) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hint : betaSq μ k T z (Λ * ℓ) * scaleMeasure (Ioo ((Λ + 2) * ℓ) (2 * ((Λ + 2) * ℓ))) ≤
      ENNReal.ofReal 6 ^ (k + 2) *
        ∫⁻ r in Ioo ((Λ + 2) * ℓ) (2 * ((Λ + 2) * ℓ)), betaSq μ k T x r ∂scaleMeasure := by
    rw [← setLIntegral_const, ← lintegral_const_mul' _ _ h6]
    exact setLIntegral_mono' measurableSet_Ioo fun r hr =>
      d1aann_betaSq_le_window μ T hΛ hℓ hxz hr
  have hconst : ENNReal.ofReal (2 * 6 ^ (k + 2)) =
      ENNReal.ofReal 2 * ENNReal.ofReal 6 ^ (k + 2) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num)]
  have htwo : ENNReal.ofReal 2 * ENNReal.ofReal (1 / 2) = 1 := by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  calc betaSq μ k T z (Λ * ℓ)
      = ENNReal.ofReal 2 * (ENNReal.ofReal (1 / 2) * betaSq μ k T z (Λ * ℓ)) := by
        rw [← mul_assoc, htwo, one_mul]
    _ ≤ ENNReal.ofReal 2 * (scaleMeasure (Ioo ((Λ + 2) * ℓ) (2 * ((Λ + 2) * ℓ))) *
          betaSq μ k T z (Λ * ℓ)) :=
        mul_le_mul' le_rfl (mul_le_mul' hW le_rfl)
    _ = ENNReal.ofReal 2 * (betaSq μ k T z (Λ * ℓ) *
          scaleMeasure (Ioo ((Λ + 2) * ℓ) (2 * ((Λ + 2) * ℓ)))) := by
        rw [mul_comm (scaleMeasure _)]
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal 6 ^ (k + 2) *
          ∫⁻ r in Ioo ((Λ + 2) * ℓ) (2 * ((Λ + 2) * ℓ)), betaSq μ k T x r ∂scaleMeasure) :=
        mul_le_mul' le_rfl hint
    _ = ENNReal.ofReal (2 * 6 ^ (k + 2)) *
          ∫⁻ r in Ioo ((Λ + 2) * ℓ) (2 * ((Λ + 2) * ℓ)), betaSq μ k T x r ∂scaleMeasure := by
        rw [hconst, mul_assoc]

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
