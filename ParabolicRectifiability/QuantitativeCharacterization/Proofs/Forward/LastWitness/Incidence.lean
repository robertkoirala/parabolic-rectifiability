import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.LastWitness
import ParabolicRectifiability.Measure.Neck.PlaneTime.ConstructionFacts

/-! # Incidence of occurrences (`d1d_incidence`)

Proof of `Forward.Witness.d1d_incidence_proof : IncidenceStatement`.

Under horizontal recorded-time compatibility with tolerance `γ ≤ 1`, two occurrences whose
recorded scales are at most `ρ` and whose spatial centres are within `ρ` are within `ρ` in the
parabolic distance: `|t - t'| ≤ γ M ≤ M ≤ ρ²` with `M = max(|x - x'|², r_i², r_{i'}²)`, and
`ms3_dist_le_of` concludes. Every helper carries the prefix `d1dinc_`.
-/

set_option autoImplicit false

noncomputable section

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Witness

/-- The coherent scales are positive. -/
theorem d1dinc_scale_pos {n m : ℕ} {ι : Type} (F : CoherentFamily n m ι) (i : ℕ) :
    0 < F.scale i := by
  unfold CoherentFamily.scale coherentScale
  exact div_pos F.initialRadius_pos (pow_pos (by norm_num) i)

/-- **Incidence** (`IncidenceStatement`). -/
theorem d1d_incidence_proof : IncidenceStatement := by
  intro n m ι F C d γ hγ hT i i' a a' ha ha' ρ hi hi' hx
  have hsi := d1dinc_scale_pos F i
  have hsi' := d1dinc_scale_pos F i'
  have hρ : 0 ≤ ρ := le_trans hsi.le hi
  have ht := hT (Sum.inl (i, a)) (Sum.inl (i', a')) ha ha'
  simp only [NeckRecord.position, NeckRecord.scale] at ht
  set M : ℝ := max (‖(F.center i a).1 - (F.center i' a').1‖ ^ 2)
    (max (F.scale i ^ 2) (F.scale i' ^ 2)) with hMdef
  have hM0 : 0 ≤ M := le_trans (sq_nonneg _) (le_max_left _ _)
  have hMρ : M ≤ ρ ^ 2 :=
    max_le (pow_le_pow_left₀ (norm_nonneg _) hx 2)
      (max_le (pow_le_pow_left₀ hsi.le hi 2) (pow_le_pow_left₀ hsi'.le hi' 2))
  have hγM : γ * M ≤ M := by
    have := mul_le_mul_of_nonneg_right hγ hM0
    linarith
  exact ms3_dist_le_of hρ hx (le_trans ht (le_trans hγM hMρ))

end Witness

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
