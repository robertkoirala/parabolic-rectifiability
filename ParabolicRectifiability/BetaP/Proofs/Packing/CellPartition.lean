import ParabolicRectifiability.BetaP.Proofs.Packing.VariantsStatements
import ParabolicRectifiability.Measure.Neck.DensitySelection

/-! # Cell partition (`c2_CellPartitionStatement`)

Proof: `M = 5^{n+2}`. A `1/2`-separated subset
of the centres lies in `closedBall q 1`, so it has at most `((2 + 1/2)/(1/2))^{n+2} = 5^{n+2}`
points (`card_le_of_separated_subset_closedBall`); a maximal one is a `1/2`-net
(`exists_maximal_separated_finset`). Label each centre by a net point within `1/2`, through
`F.equivFin` and `Fin.castLE`; equal labels give equal net points, hence distance `< 1`.
-/

noncomputable section

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- **Cell partition** (`c2_CellPartitionStatement`). -/
theorem c2_cellPartition_proof : c2_CellPartitionStatement := by
  intro n
  refine ⟨5 ^ (n + 2), ?_⟩
  intro q N z hz
  classical
  have hbound : ∀ F : Finset (Space n), ↑F ⊆ Set.range z →
      IsSeparatedFinset (1 / 2) F → F.card ≤ 5 ^ (n + 2) := by
    intro F hF hsep
    have hsub : (↑F : Set (Space n)) ⊆ Metric.closedBall q 1 := by
      intro x hx
      obtain ⟨i, rfl⟩ := hF hx
      exact Metric.ball_subset_closedBall (hz i)
    have h := card_le_of_separated_subset_closedBall q zero_le_one
      (by norm_num : (0 : ℝ) < 1 / 2) F hsub hsep
    have h5 : (2 * (1 : ℝ) + 1 / 2) / (1 / 2) = 5 := by norm_num
    rw [h5] at h
    exact_mod_cast h
  obtain ⟨F, hFS, hFsep, hnet⟩ :=
    exists_maximal_separated_finset (Set.range z) (by norm_num : (0 : ℝ) < 1 / 2) _ hbound
  have hcard : F.card ≤ 5 ^ (n + 2) := hbound F hFS hFsep
  have hy : ∀ i, ∃ y, y ∈ F ∧ dist (z i) y < 1 / 2 := by
    intro i
    obtain ⟨y, hyF, hyd⟩ := hnet (z i) ⟨i, rfl⟩
    exact ⟨y, hyF, hyd⟩
  choose y hyF hyd using hy
  refine ⟨fun i => Fin.castLE hcard (F.equivFin ⟨y i, hyF i⟩), ?_⟩
  intro i j hij
  have h1 : F.equivFin ⟨y i, hyF i⟩ = F.equivFin ⟨y j, hyF j⟩ :=
    Fin.castLE_injective hcard hij
  have h2 : y i = y j := congrArg Subtype.val (F.equivFin.injective h1)
  calc dist (z i) (z j) ≤ dist (z i) (y j) + dist (y j) (z j) := dist_triangle _ _ _
    _ = dist (z i) (y i) + dist (z j) (y j) := by rw [h2, dist_comm (y j)]
    _ < 1 / 2 + 1 / 2 := add_lt_add (hyd i) (hyd j)
    _ = 1 := by norm_num

end ParabolicRectifiability.BetaP
