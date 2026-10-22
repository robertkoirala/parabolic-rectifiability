import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # Local original-source fits exist

Proof of `d1c_localFits_proof : LocalFitsStatement`. No additional
hypotheses.

Route (source localization): for each level `j` and point `g`, apply the base
`NeckSelection.exists_fit_minimizer` to the finite measure `ν = μ⌞closedBall(g, 40 r_j)` (finite
since `μ` is finite on compacts) and the family `𝒢.type.toFamilyKind` (nonempty by
`NeckSelection.nonempty_models 𝒢.type_available`). Since `ν⌞P(g, 40 r_j) = μ⌞P(g, 40 r_j)`
(`d1cfits_restrict_ball_eq`), every fit of `ν` on the open ball `P(g, 40 r_j)` is the fit of the
original `μ` (`d1cfits_fit_restrict_closedBall`); the minimizer of `ν` therefore minimizes the
original-source objective (`iInf_le`). The models are chosen by `choose`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

/-- Source localization: `(μ⌞closedBall(g, r))⌞P(g, r) = μ⌞P(g, r)`. -/
theorem d1cfits_restrict_ball_eq {n : ℕ} (μ : Measure (Space n)) (g : Space n) (r : ℝ) :
    (μ.restrict (Metric.closedBall g r)).restrict (Metric.ball g r) =
      μ.restrict (Metric.ball g r) :=
  Measure.restrict_restrict_of_subset Metric.ball_subset_closedBall

/-- The fit on `P(g, r)` of `μ⌞closedBall(g, r)` is the fit of the original `μ`. -/
theorem d1cfits_fit_restrict_closedBall {n k : ℕ} {F : FamilyKind} (μ : Measure (Space n))
    (L : Models n k F) (g : Space n) (r : ℝ) :
    fit (μ.restrict (Metric.closedBall g r)) L g r = fit μ L g r := by
  unfold fit
  rw [d1cfits_restrict_ball_eq]

/-- The original-source fitting infimum on `P(g, r)` is attained, for `μ` finite on compacts. -/
theorem d1cfits_exists_minimizer {n k : ℕ} {F : FamilyKind} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] (hF : Nonempty (Models n k F)) (g : Space n) (r : ℝ) :
    ∃ M : Models n k F, ∀ M' : Models n k F, fit μ M g r ≤ fit μ M' g r := by
  have : IsFiniteMeasure (μ.restrict (Metric.closedBall g r)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall g r).measure_lt_top.ne
  obtain ⟨M, hM⟩ :=
    NeckSelection.exists_fit_minimizer (μ.restrict (Metric.closedBall g r)) hF g r
  refine ⟨M, fun M' => ?_⟩
  have h3 : typeFittingError (μ.restrict (Metric.closedBall g r)) k F g r ≤
      fit (μ.restrict (Metric.closedBall g r)) M' g r :=
    iInf_le (fun L => fit (μ.restrict (Metric.closedBall g r)) L g r) M'
  have h4 : fit (μ.restrict (Metric.closedBall g r)) M g r ≤
      fit (μ.restrict (Metric.closedBall g r)) M' g r := hM.trans h3
  rwa [d1cfits_fit_restrict_closedBall, d1cfits_fit_restrict_closedBall] at h4

/-- **Local fits exist** (`LocalFitsStatement`). -/
theorem d1c_localFits_proof : LocalFitsStatement := by
  intro n E ℓ₀ P μ k Λ b 𝒢 hμ
  have := hμ
  have hF : Nonempty (Models n k 𝒢.type.toFamilyKind) :=
    NeckSelection.nonempty_models 𝒢.type_available
  have key : ∀ (j : ℕ) (g : Space n), ∃ M : Models n k 𝒢.type.toFamilyKind,
      ∀ M' : Models n k 𝒢.type.toFamilyKind,
        fit μ M g (40 * stageScale 𝒢 j) ≤ fit μ M' g (40 * stageScale 𝒢 j) :=
    fun j g => d1cfits_exists_minimizer μ hF g (40 * stageScale 𝒢 j)
  choose M hM using key
  exact ⟨⟨M, hM⟩⟩

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
