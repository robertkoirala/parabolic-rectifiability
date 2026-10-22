import ParabolicRectifiability.Measure.Neck.ConstructionConclusions
import ParabolicRectifiability.Measure.Neck.RegionCore.KeptSets

/-!
# Region facts of the source construction

Proofs of the two parts of `regionFacts_of_construction`:

* `separationFacts_of_construction_proof` (`separationFacts_of_construction`): centers in `closure P(q,R)`, radii in `[0, 4R]`, stopping separation `1/20`,
  core separation, and the buffers with `C_* = 8` (initial radius `r_0 ≤ 8R`, root on `L_*`
  within `R` of `q`, all occurrences in `P(q, 8R)`). No energy smallness is used.
* `compactness_of_separationFacts_proof` (`compactness_of_separationFacts`): the center set is
  closed (only finitely many centers of stages `≤ j₀` lie off `closure(S_{j₀})`) and bounded,
  hence compact; every core point is a level limit of continuing candidates; the core equals
  `⋂_j closure(S_j)` and is compact.

`ConstructionDefs` is imported only for the definition `ConstructionData.SeparationFacts`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal

/-- **`separationFacts_of_construction`**: stopping and core separation and the buffer bounds of the
constructed neck, with `C_* = 8`. -/
theorem separationFacts_of_construction_proof (n : ℕ) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n)
      (D : ConstructionData n k T), T.Available n k → k < n + 2 →
      ∀ hP : P.IsAdmissible, D.IsSourceConstruction P → D.SeparationFacts P hP.R_pos Cs := by
  refine ⟨8, by norm_num, ?_⟩
  intro k T P D _ _ hP hD
  have hR := hP.R_pos
  have hroot : dist D.rootCenter P.q ≤ P.R := hD.root_dist
  refine
    { centers_subset := ?_
      radius_nonneg := ?_
      radius_le := ?_
      stop_separation := ?_
      core_separation := ?_
      initialRadius_le := T.ms4_rootRadius_le hR
      initialPoint_mem := hD.root_mem
      initialPoint_near := ?_
      center_mem := ?_ }
  · intro z hz
    rcases hz with hz | hz
    · exact Metric.closure_ball_subset_closedBall
        (closure_mono ((D.ms4_kept_subset_S P 0).trans hP.S_subset) (mem_iInter.1 hz 0))
    · obtain ⟨j, h⟩ := D.ms4_exists_stopAt P hz
      exact Metric.ball_subset_closedBall
        (hP.S_subset (D.ms4_entering_subset_S P j (h.mem_entering hD)))
  · intro c _
    by_cases hst : D.IsTermCenter c ∨ D.IsCollCenter P c
    · obtain ⟨j, h⟩ := D.ms4_exists_stopAt P hst
      exact (h.pos hD hR).le
    · rw [D.ms4_radius_eq_zero_of_not P hst]
  · intro c _
    by_cases hst : D.IsTermCenter c ∨ D.IsCollCenter P c
    · obtain ⟨j, h⟩ := D.ms4_exists_stopAt P hst
      exact h.le_four hD hP
    · rw [D.ms4_radius_eq_zero_of_not P hst]
      linarith
  · intro c _ c' _ hc hc' hne
    obtain ⟨j, h⟩ := D.ms4_exists_stopAt P (D.ms4_stop_of_radius_pos P hc)
    obtain ⟨j', h'⟩ := D.ms4_exists_stopAt P (D.ms4_stop_of_radius_pos P hc')
    exact h.separation hD hR h' hne
  · intro c _ hc z hz hz0
    obtain ⟨j, h⟩ := D.ms4_exists_stopAt P (D.ms4_stop_of_radius_pos P hc)
    exact h.le_dist_of_mem_closure le_rfl
      (mem_iInter.1 (ConstructionData.ms4_mem_coreLimit_of_mem_centers hD hR hz hz0) j)
  · have h1 : ‖D.rootCenter.1 - P.q.1‖ ≤ dist D.rootCenter P.q := by
      rw [← dist_eq_norm, Prod.dist_eq]
      exact le_max_left _ _
    linarith
  · intro j a ha
    by_cases hj : j = 0
    · subst hj
      have hc : (D.family P hR).center 0 a = D.rootCenter := by
        show (if (0 : ℕ) = 0 then D.rootCenter else D.cand 0 a) = _
        rw [ite_eq_left rfl]
      rw [hc, Metric.mem_ball]
      linarith
    · have ha' : a ∈ D.contIndex P j := by
        have : (D.family P hR).index j = D.contIndex P j := by
          show (if j = 0 then {0} else D.contIndex P j) = _
          rw [ite_eq_right hj]
        rw [← this]
        exact ha
      have hc : (D.family P hR).center j a = D.cand j a := by
        show (if j = 0 then D.rootCenter else D.cand j a) = _
        rw [ite_eq_right hj]
      classical
      have hlt : a < D.candCount j := Finset.mem_range.1 (Finset.mem_filter.1 ha').1
      have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 hj
      have hS : D.cand j a ∈ P.S :=
        D.ms4_entering_subset_S P j (D.ms4_afterTerm_subset P _ _ (hD.cand_mem j hj1 a hlt))
      rw [hc]
      exact Metric.ball_subset_ball (by linarith) (hP.S_subset hS)

/-- **`compactness_of_separationFacts`**: compactness of the centers, level limits at the core, and
compactness of the core. Only the bound `centers ⊆ closedBall q R` of `separationFacts_of_construction_proof` is used. -/
theorem compactness_of_separationFacts_proof (n : ℕ) :
    ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T) (Cs : ℝ),
      T.Available n k → k < n + 2 → ∀ hP : P.IsAdmissible, D.IsSourceConstruction P →
      D.SeparationFacts P hP.R_pos Cs →
      IsCompact (D.centers P) ∧
        (∀ z ∈ D.centers P, D.radius P z = 0 → (D.family P hP.R_pos).IsLevelLimit z) ∧
        IsCompact (D.core P) := by
  intro k T P D Cs _ _ hP hD hsep
  have hR := hP.R_pos
  refine ⟨?_, ?_, ?_⟩
  · exact (isCompact_closedBall P.q P.R).of_isClosed_subset
      (ConstructionData.ms4_isClosed_centers hD) hsep.centers_subset
  · intro z hz hz0
    exact ConstructionData.ms4_isLevelLimit hR
      (ConstructionData.ms4_mem_coreLimit_of_mem_centers hD hR hz hz0)
  · rw [ConstructionData.ms4_core_eq_coreLimit hD hR]
    exact (isCompact_closedBall P.q P.R).of_isClosed_subset
      ConstructionData.ms4_isClosed_coreLimit fun z hz => hsep.centers_subset (mem_union_left _ hz)

end ParabolicRectifiability
