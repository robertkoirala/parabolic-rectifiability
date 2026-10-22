import ParabolicRectifiability.Measure.Neck.Definitions
import ParabolicRectifiability.Measure.FittingMinimum

/-!
# Fitted models as plane data

The construction data of `Construction` record a fitted model of type
`T` by its spatial plane of rank `T.rank k` and (horizontal case) its time level, with
the represented set `T.lowerModelSet L τ`. This file converts an admissible model of type
`T` into such plane data with the same represented set, shows that every type available
in dimension `k` has models, and that the original-source fitting infimum on a ball is
attained (`exists_globalFittingError_minimizer` applied to the restriction of the finite
source to the ball, whose mass lies in the compact closed ball).
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal

namespace NeckSelection

/-- The spatial plane of a model of type `T`, as a plane of rank `T.rank k`. -/
def modelPlane {n k : ℕ} :
    (T : NeckType) → Models n k T.toFamilyKind → AffineSpatialPlane n (T.rank k)
  | .horizontal, M => HorizontalModel.spatial M
  | .vertical, M => AffineSpatialPlane.ofTranslate (VerticalModel.spatial M).direction
      (by
        have h1 := (VerticalModel.spatial M).rank_eq
        have h2 := VerticalModel.rank_eq M
        show _ = k - 2
        omega)
      (VerticalModel.spatial M).anchor

/-- The time level of a model of type `T` (unused, and set to `0`, in the vertical case). -/
def modelTime {n k : ℕ} : (T : NeckType) → Models n k T.toFamilyKind → ℝ
  | .horizontal, M => HorizontalModel.time M
  | .vertical, _ => 0

theorem lowerModelSet_modelPlane {n k : ℕ} (T : NeckType) (M : Models n k T.toFamilyKind) :
    T.lowerModelSet (modelPlane T M) (modelTime T M) = modelSet M := by
  cases T with
  | horizontal => rfl
  | vertical =>
    ext z
    show z.1 ∈ (modelPlane .vertical M).toSet ↔ z.1 ∈ (VerticalModel.spatial M).toSet
    simp only [modelPlane, AffineSpatialPlane.ofTranslate_toSet, Set.mem_ofPred_eq,
      AffineSpatialPlane.mem_toSet]

theorem nonempty_models {n k : ℕ} {T : NeckType} (hT : T.Available n k) :
    Nonempty (Models n k T.toFamilyKind) := by
  cases T with
  | horizontal => exact HorizontalModel.nonempty_iff.mpr hT
  | vertical => exact VerticalModel.nonempty_iff.mpr hT

/-- The original-source fitting infimum on a ball is attained. -/
theorem exists_fit_minimizer {n k : ℕ} {F : FamilyKind} (ν : Measure (Space n))
    [IsFiniteMeasure ν] (hF : Nonempty (Models n k F)) (x : Space n) (ρ : ℝ) :
    ∃ M : Models n k F, ∫⁻ w in Metric.ball x ρ, modelCost M w ∂ν ≤
      typeFittingError ν k F x ρ := by
  obtain ⟨M, hM, -⟩ := exists_globalFittingError_minimizer (ν.restrict (Metric.ball x ρ)) hF
    (isCompact_closedBall x ρ)
    (ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet fun w hw =>
      Metric.ball_subset_closedBall hw)
  exact ⟨M, le_of_eq hM⟩

end NeckSelection

end ParabolicRectifiability
