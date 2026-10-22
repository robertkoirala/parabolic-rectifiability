import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ProjectionEnergy
import ParabolicRectifiability.Geometry.Chart.LevelPartitionsAndCoverage
import ParabolicRectifiability.Geometry.Chart.InductionEstimates

/-! # The path square sum `∑_j d_j(u,t)² ≤ E`

Proof of `d1e2_PathErrorSumStatement`, from the finite path estimate of the coherent chart.

Proof sketch: `δ₀ = CoherentChart.deltaThreshold n σ`. For `0 ≤ δ ≤ δ₀`, `DeltaSmall n σ δ`
is the first conjunct of `CoherentChart.smallness_of_le` (taken at `E = 0`, `κ = 0`). For every
truncation level `N`, the finite path bound `PathBoundUpTo F P E N` is the base theorem
`CoherentChart.pathBound_of_verticalSquareBound_proof` fed with the induction estimates
`CoherentChart.induction_estimates_proof`; its truncated square bound comes from the full vertical
square bound by `ENNReal.sum_le_tsum`. This proof compares all path points with one common final
point. Termwise `ofReal (e.toReal ^ 2) ≤ e ^ 2`, and `ENNReal.tsum_le_of_sum_range_le` passes to
the series. Neither an energy threshold nor `0 ≤ E` is used; for `E < 0` the right side is `0`.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-- Termwise comparison: `ofReal (x.toReal ^ 2) ≤ x ^ 2` in `ℝ≥0∞` (an equality when `x < ⊤`). -/
theorem d1e2path_ofReal_toReal_sq_le (x : ℝ≥0∞) :
    ENNReal.ofReal (x.toReal ^ 2) ≤ x ^ 2 := by
  rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg]
  exact pow_le_pow_left₀ (by positivity) ENNReal.ofReal_toReal_le 2

/-- The vertical square bound for the levels `0, …, N` follows from the full one. -/
theorem d1e2path_verticalSquareBoundUpTo {n m : ℕ} {ι : Type*} {F : CoherentFamily n m ι}
    {E : ℝ} (hE : F.VerticalSquareBound E) (N : ℕ) : F.VerticalSquareBoundUpTo E N :=
  fun w => (ENNReal.sum_le_tsum (Finset.range (N + 1))).trans (hE w)

/-- **The path square sum**: below the smallness threshold, `∑_j d_j(u,t)² ≤ E` at every base
point. -/
theorem d1e2_pathError_sum_proof : d1e2_PathErrorSumStatement := by
  intro n σ hσ
  refine ⟨CoherentChart.deltaThreshold n σ, CoherentChart.deltaThreshold_pos hσ, ?_⟩
  intro m ι F δ E hδ hδ₀ hF hE P u t
  have hsmall : CoherentChart.DeltaSmall n σ δ :=
    (CoherentChart.smallness_of_le (n := n) (E := 0) (κ := 0) hσ hδ hδ₀
      (CoherentChart.energyThreshold_pos hσ).le
      (by norm_num [CoherentChart.heightThreshold])).1
  have hpath : ∀ N : ℕ, CoherentChart.PathBoundUpTo F P E N := fun N =>
    CoherentChart.pathBound_of_verticalSquareBound_proof
      CoherentChart.induction_estimates_proof hσ hδ hsmall (hF N)
      (d1e2path_verticalSquareBoundUpTo hE N) P
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  calc ∑ j ∈ Finset.range N, ENNReal.ofReal (d1e_pathError F P j u t ^ 2)
      ≤ ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (d1e_pathError F P j u t ^ 2) :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ N))
    _ ≤ ∑ j ∈ Finset.range (N + 1),
          CoherentChart.localError F j (CoherentChart.pathPoint F P j u t) ^ 2 :=
        Finset.sum_le_sum fun j _ => d1e2path_ofReal_toReal_sq_le _
    _ ≤ ENNReal.ofReal E := hpath N u t

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
