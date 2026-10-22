import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.IntegralAuxiliaryStatements

/-! # The positive weight

Proof of `i2_PositiveWeightStatement`, the auxiliary statement `i2_positiveWeight`.

Route: `w z = (1 + (S z).toReal)⁻¹` on the Borel set `{S < ∞}` and
`1` elsewhere (`Measurable.ite`, `measurable_squareEnergy`); `0 < w ≤ 1`; `ofReal (w z) * S z ≤ 1`
on `{S < ∞}`, which has full measure, so `∫_A ofReal w · S dμ ≤ μ A < ∞` for bounded `A`
(`lintegral_mono_ae`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

/-- The weight `(1 + S.toReal)⁻¹` where `S < ∞`, and `1` elsewhere. -/
def i2_pw_weight (s : ℝ≥0∞) : ℝ :=
  if s < ⊤ then (1 + s.toReal)⁻¹ else 1

theorem i2_pw_weight_pos (s : ℝ≥0∞) : 0 < i2_pw_weight s := by
  unfold i2_pw_weight
  split_ifs
  · exact inv_pos.2 (by positivity)
  · exact one_pos

theorem i2_pw_weight_le_one (s : ℝ≥0∞) : i2_pw_weight s ≤ 1 := by
  unfold i2_pw_weight
  split_ifs
  · exact inv_le_one_of_one_le₀ (by simp)
  · exact le_rfl

theorem i2_pw_measurable_weight : Measurable i2_pw_weight := by
  unfold i2_pw_weight
  refine Measurable.ite (measurableSet_Iio (a := (⊤ : ℝ≥0∞))) ?_ measurable_const
  exact ((measurable_const.add ENNReal.measurable_toReal)).inv

/-- Off `{S = ∞}`, `ofReal w * S ≤ 1`. -/
theorem i2_pw_mul_le_one {s : ℝ≥0∞} (hs : s < ⊤) :
    ENNReal.ofReal (i2_pw_weight s) * s ≤ 1 := by
  have hw : i2_pw_weight s = (1 + s.toReal)⁻¹ := by simp [i2_pw_weight, hs]
  rw [hw, ← ENNReal.ofReal_toReal hs.ne, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  have h0 : 0 < 1 + s.toReal := by positivity
  rw [inv_mul_le_iff₀ h0]
  linarith

/-- **Positivity of the weight** (`i2_positiveWeight`). -/
theorem i2_positiveWeight_proof : i2_PositiveWeightStatement := by
  intro n _ k _ _ μ hμ _ T _ R _ hae
  have := hμ
  refine ⟨fun z => i2_pw_weight (squareEnergy μ k T R z), ?_, fun z => ⟨i2_pw_weight_pos _,
    i2_pw_weight_le_one _⟩, ?_⟩
  · exact i2_pw_measurable_weight.comp (measurable_squareEnergy μ k T R)
  · rintro A ⟨_, hAb⟩
    calc ∫⁻ z in A, ENNReal.ofReal (i2_pw_weight (squareEnergy μ k T R z)) * squareEnergy μ k T R z ∂μ
        ≤ ∫⁻ _ in A, (1 : ℝ≥0∞) ∂μ :=
          lintegral_mono_ae (ae_restrict_of_ae (hae.mono fun z hz => i2_pw_mul_le_one hz))
      _ = μ A := by rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
      _ < ⊤ := hAb.measure_lt_top

end ParabolicRectifiability.IntegralCanonical
