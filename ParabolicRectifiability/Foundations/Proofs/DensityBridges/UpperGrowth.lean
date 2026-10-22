import ParabolicRectifiability.Foundations.Proofs.DensityBridges.UpperGrowthLemmas

/-! # Support-centred upper growth implies absolute continuity

`fgac_absolutelyContinuous_of_upper_growth` has exactly the type of
`QuantitativeCharacterization.absolutelyContinuous_of_upper_growth`. It is assembled from
`fgac_absolutelyContinuous_hausdorffP_of_growth` and `fgac_ball_le_of_support_growth`.

Assembly: the adapter turns support-centred growth with constant `A` (all radii) into
all-centre growth with constant `2^k A` for `0 < r ≤ 1`, and the growth criterion with
`B = 2^k A`, `r₀ = 1` gives `μ ≪ H_P^k`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- Support-centred upper growth implies absolute continuity: the statement of
`QuantitativeCharacterization.absolutelyContinuous_of_upper_growth`. -/
theorem fgac_absolutelyContinuous_of_upper_growth :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular → ∀ A : ℝ,
    (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)) →
      μ ≪ hausdorffP n k := by
  intro n hn k hk hkn μ hfin hreg A hA
  exact fgac_absolutelyContinuous_hausdorffP_of_growth n hn k hk hkn μ hfin hreg
    (2 ^ k * A) 1 one_pos fun p r hr _ => fgac_ball_le_of_support_growth k μ A hA p r hr

end ParabolicRectifiability.Foundations
