import ParabolicRectifiability.Measure.Neck.ConstructionConclusions
import ParabolicRectifiability.Measure.Neck.Selection.ModelFit
import ParabolicRectifiability.Measure.Neck.Selection.Greedy

/-!
# One stage of the source construction

Proof of `exists_stageChoice`.

For a stage `j ≥ 1` and an entering set `E ⊆ S ⊆ P(q,R)`:

* the cutoff takes only finitely many values `≥ r_j > 0` on `S`
  (`IsSourceCutoff.finite_values`), so the decreasing terminal selection attains its
  maxima; terminal centers are `r_j`-separated in the compact set `closure P(q,R)`, so
  the selection stops, and afterwards `f < r_j` (`exists_terminal_selection`);
* a maximal `κ r_j`-separated subset of the remainder is finite and its `κ r_j`-balls
  cover the remainder (`exists_maximal_net`);
* the original-source fitting infimum on `P(g, 40 r_j)` is attained at every candidate
  (`exists_fit_minimizer`), and the minimizing model is recorded by its plane and time.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal

open NeckSelection

/-- **`exists_stageChoice`**: existence of the data of one stage. -/
theorem exists_stageChoice_proof (n : ℕ) :
    ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n), T.Available n k → k < n + 2 →
      P.IsAdmissible → ∀ j : ℕ, 1 ≤ j → ∀ E : Set (Space n), E ⊆ P.S →
        ∃ D : ConstructionData n k T, D.IsStageChoice P j E := by
  intro k T P hT _ hP j _ E hE
  classical
  have := P.finite
  have : Nonempty (Space n) := ⟨P.q⟩
  have hF := nonempty_models hT
  have hr : 0 < P.scale T j := P.scale_pos T hP.R_pos j
  have hB : IsCompact (Metric.closedBall P.q P.R) := isCompact_closedBall _ _
  have hEB : E ⊆ Metric.closedBall P.q P.R :=
    hE.trans (hP.S_subset.trans Metric.ball_subset_closedBall)
  have hfin : (P.f '' E ∩ Ici (P.scale T j)).Finite :=
    (hP.cutoff.finite_values _ hr).subset (inter_subset_inter_left _ (image_mono hE))
  obtain ⟨m, t, ht, hdone⟩ := exists_terminal_selection hB hEB P.f hr hfin
  obtain ⟨c, g, hgA, hgsep, hcover⟩ := exists_maximal_net hB
    (A := E \ ⋃ (i : ℕ) (_ : i < m), Metric.ball (t i) (P.f (t i))) (Set.sdiff_subset.trans hEB)
    (mul_pos T.sourceSeparation_pos hr)
  choose M hM using fun i => exists_fit_minimizer P.ν hF (g i) (40 * P.scale T j)
  obtain ⟨M₀⟩ := hF
  have hfit : ∀ i, ∫⁻ z in Metric.ball (g i) (40 * P.scale T j),
      Metric.infEDist z (T.lowerModelSet (modelPlane T (M i)) (modelTime T (M i))) ^ 2 ∂P.ν ≤
        typeFittingError P.ν k T.toFamilyKind (g i) (40 * P.scale T j) := by
    intro i
    rw [lowerModelSet_modelPlane]
    exact hM i
  refine ⟨{ rootPlane := modelPlane T M₀
            rootTime := 0
            rootCenter := P.q
            termCount := fun _ => m
            term := fun _ => t
            candCount := fun _ => c
            cand := fun _ => g
            plane := fun _ i => modelPlane T (M i)
            time := fun _ i => modelTime T (M i) }, ?_⟩
  exact
    { term_mem := ht.mem
      term_large := ht.large
      term_max := ht.max
      term_done := hdone
      cand_mem := hgA
      cand_separated := hgsep
      cand_cover := hcover
      fit_minimal := fun i _ => hfit i }

end ParabolicRectifiability
