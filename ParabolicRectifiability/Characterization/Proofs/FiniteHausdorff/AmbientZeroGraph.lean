import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Measure.ScaleEnergy
import ParabolicRectifiability.Metric.Hausdorff
import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import ParabolicRectifiability.Enhancements.Statements.ScaledCore
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # The ambient zero-norm vertical graph

Proves `b4_ambient_zero_norm_graph_proof`, with exactly the type of
`b4_ambient_zero_norm_graph`; it is the second conjunct of `FiniteHausdorffCriterionStatement`.

Route: direction `W = ⊤`, offset `0`, function `0`, representative `0`. The
normal space `W^⊥ = ⊥` is zero, so the Lipschitz and BMO bounds are `0` and the half-time
representation is vacuous (`Fin 0`). The graph map is `(u,t) ↦ (u,t)`, so the image is `X`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-- The normal space of the full spatial direction has dimension zero. -/
theorem b4p6_finrank_top_orthogonal (n : ℕ) :
    Module.finrank ℝ (⊤ : Submodule ℝ (Spatial n)).orthogonal = 0 := by
  rw [Submodule.top_orthogonal_eq_bot, finrank_bot]

/-- The zero function on the full direction is a general regular vertical function of norm
at most `0`: Lipschitz constant `0`, representative `0` with BMO bound `0`, and a vacuous
representation over `Fin 0`. -/
theorem b4p6_isGeneralRegularVerticalFunction_top_zero (n : ℕ) :
    IsGeneralRegularVerticalFunction (⊤ : Submodule ℝ (Spatial n)) (fun _ => 0) 0 := by
  refine ⟨fun _ => 0, 0, 0, LipschitzWith.const 0,
    ⟨NNReal.coe_nonneg _, locallyIntegrable_zero, ?_⟩, ?_, by simp⟩
  · intro p r _
    simp [parabolicBallAverage]
  · intro i
    exact (Fin.cast (b4p6_finrank_top_orthogonal n) i).elim0

/-- The full vertical graph of the zero function on `W = ⊤`, at norm `0`. -/
def b4p6_graph (n : ℕ) : GeneralRegularVerticalGraph n (n + 2) 0 where
  vertical_dimension := by omega
  direction := ⊤
  rank_eq := by rw [finrank_top, finrank_euclideanSpace_fin]
  offset := 0
  function := fun _ => 0
  regular := b4p6_isGeneralRegularVerticalFunction_top_zero n

/-- Its image is the whole space. -/
theorem b4p6_graph_image (n : ℕ) : (b4p6_graph n).image = univ := by
  refine eq_univ_of_forall fun z => ⟨(⟨z.1, Submodule.mem_top⟩, z.2), ?_⟩
  simp [GeneralRegularVerticalGraph.map, b4p6_graph]

/-- **Ambient zero-norm vertical graph**: the statement of `b4_ambient_zero_norm_graph`. -/
theorem b4_ambient_zero_norm_graph_proof :
    ∀ n : ℕ, 1 ≤ n →
      ∃ G : GeneralRegularVerticalGraph n (n + 2) 0, ∀ E : Set (Space n), E ⊆ G.image := by
  intro n _
  exact ⟨b4p6_graph n, fun E => (b4p6_graph_image n).symm ▸ subset_univ E⟩

end ParabolicRectifiability.Characterization
