import ParabolicRectifiability.Characterization.Proofs.Replacement.Statements

/-! # Exact Borel allocation and piece bounds

Proves the named statement `ReplacementTree.RpAllocationStatement` as
`b3_rp_allocation_proof`.

Route: `F_j = Ω_A ∩ P(z_j, 5 r_j)` for `j ∈ I` and `F_j = ∅` otherwise (`j : ℕ`), and
`E_i = disjointed F i`. Piece bound: with `g_i ∈ G_A` and `dist (z_i, g_i) < 200 r_i`,
`E_i ⊆ P(z_i, 5 r_i) ⊆ P(g_i, 205 r_i)`, and goodness at `g_i` gives
`ν(E_i) ≤ ofReal (A (205 r_i)^k) = ofReal (205^k A r_i^k)`; no sign condition on `A` is used.
-/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.Characterization.ReplacementTree

open Classical in
/-- The family to be disjointified: `Ω ∩ P(z_j, 5 r_j)` for `j ∈ I`, empty otherwise. -/
def b3rpa_family {X : Type*} [PseudoMetricSpace X] (Ω : Set X) (I : Set ℕ) (z : I → X)
    (r : I → ℝ) (j : ℕ) : Set X :=
  if h : j ∈ I then Ω ∩ Metric.ball (z ⟨j, h⟩) (5 * r ⟨j, h⟩) else ∅

theorem b3rpa_family_of_mem {X : Type*} [PseudoMetricSpace X] (Ω : Set X) (I : Set ℕ)
    (z : I → X) (r : I → ℝ) (i : I) :
    b3rpa_family Ω I z r i.1 = Ω ∩ Metric.ball (z i) (5 * r i) := by
  simp [b3rpa_family, i.2]

theorem b3rpa_family_of_not_mem {X : Type*} [PseudoMetricSpace X] (Ω : Set X) (I : Set ℕ)
    (z : I → X) (r : I → ℝ) {j : ℕ} (hj : j ∉ I) : b3rpa_family Ω I z r j = ∅ := by
  simp [b3rpa_family, hj]

theorem b3rpa_family_measurable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {Ω : Set X} (hΩ : MeasurableSet Ω) (I : Set ℕ) (z : I → X)
    (r : I → ℝ) (j : ℕ) : MeasurableSet (b3rpa_family Ω I z r j) := by
  by_cases h : j ∈ I
  · rw [b3rpa_family_of_mem Ω I z r ⟨j, h⟩]
    exact hΩ.inter measurableSet_ball
  · rw [b3rpa_family_of_not_mem Ω I z r h]
    exact MeasurableSet.empty

/-- Exact Borel allocation of a measurable set covered by the balls `P(z_i, 5 r_i)`. -/
theorem b3rpa_alloc_core {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (Ω : Set X) (hΩ : MeasurableSet Ω) (I : Set ℕ) (z : I → X)
    (r : I → ℝ) (hcov : Ω ⊆ ⋃ i, Metric.ball (z i) (5 * r i)) :
    ∃ E : I → Set X,
      (∀ i, MeasurableSet (E i)) ∧
      (∀ i, E i ⊆ Ω ∩ Metric.ball (z i) (5 * r i)) ∧
      Pairwise (Disjoint on E) ∧
      (⋃ i, E i) = Ω := by
  have hFm : ∀ j, MeasurableSet (b3rpa_family Ω I z r j) :=
    b3rpa_family_measurable hΩ I z r
  have hsub : ∀ i : I, disjointed (b3rpa_family Ω I z r) i.1 ⊆
      Ω ∩ Metric.ball (z i) (5 * r i) := by
    intro i
    rw [← b3rpa_family_of_mem Ω I z r i]
    exact disjointed_subset _ _
  refine ⟨fun i => disjointed (b3rpa_family Ω I z r) i.1, fun i => ?_, hsub, ?_, ?_⟩
  · exact MeasurableSet.disjointed hFm i.1
  · intro i j hij
    exact disjoint_disjointed (b3rpa_family Ω I z r) (fun h => hij (Subtype.ext h))
  · apply Subset.antisymm
    · exact iUnion_subset fun i => (hsub i).trans inter_subset_left
    · intro x hx
      have hxF : x ∈ ⋃ j, b3rpa_family Ω I z r j := by
        obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hx)
        refine mem_iUnion.2 ⟨i.1, ?_⟩
        rw [b3rpa_family_of_mem Ω I z r i]
        exact ⟨hx, hi⟩
      rw [← iUnion_disjointed] at hxF
      obtain ⟨j, hj⟩ := mem_iUnion.1 hxF
      have hjI : j ∈ I := by
        by_contra hjI
        have hj' := disjointed_subset (b3rpa_family Ω I z r) j hj
        rw [b3rpa_family_of_not_mem Ω I z r hjI] at hj'
        exact hj'
      exact mem_iUnion.2 ⟨⟨j, hjI⟩, hj⟩

/-- `P(z, 5 r) ⊆ P(g, 205 r)` when `dist z g < 200 r`. -/
theorem b3rpa_ball_subset {X : Type*} [PseudoMetricSpace X] {z g : X} {r : ℝ}
    (h : dist z g < 200 * r) : Metric.ball z (5 * r) ⊆ Metric.ball g (205 * r) := by
  intro x hx
  rw [Metric.mem_ball] at hx ⊢
  calc dist x g ≤ dist x z + dist z g := dist_triangle _ _ _
    _ < 5 * r + 200 * r := add_lt_add hx h
    _ = 205 * r := by ring

/-- Exact Borel allocation of `Ω_A` and the piece bounds `ν(E_i) ≤ 205^k A r_i^k`
(`RpAllocationStatement`). -/
theorem b3_rp_allocation_proof : RpAllocationStatement := by
  intro n k Γ ν A hΓ hG I z r hr hcov hprox
  obtain ⟨E, hEm, hEsub, hEdisj, hEunion⟩ :=
    b3rpa_alloc_core (Γ \ adrGoodSet Γ ν k A) (hΓ.diff hG) I z r hcov
  refine ⟨E, hEm, fun i x hx => ?_, hEdisj, hEunion, fun i => ?_⟩
  · exact ⟨(hEsub i hx).1.1, (hEsub i hx).2⟩
  · obtain ⟨g, hg, hdist⟩ := hprox i
    have hg' : g ∈ Γ ∧ ∀ s : ℝ, 0 < s → ν (Metric.ball g s) ≤ ENNReal.ofReal (A * s ^ k) :=
      hg
    have hball : E i ⊆ Metric.ball g (205 * r i) :=
      fun x hx => b3rpa_ball_subset hdist (hEsub i hx).2
    calc ν (E i) ≤ ν (Metric.ball g (205 * r i)) := measure_mono hball
      _ ≤ ENNReal.ofReal (A * (205 * r i) ^ k) := hg'.2 _ (by linarith [hr i])
      _ = ENNReal.ofReal (205 ^ k * A * r i ^ k) := by
        congr 1
        rw [mul_pow]
        ring

end ParabolicRectifiability.Characterization
