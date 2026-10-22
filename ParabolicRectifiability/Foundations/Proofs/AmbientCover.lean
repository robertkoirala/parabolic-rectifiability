import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.AmbientZeroGraph

/-! # The zero-graph cover

Proof of `AmbientZeroGraphCoverStatement`, reusing the norm-`0` zero graph `b4p6_graph` and
monotonicity in the tolerance. -/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.Characterization

/-- Monotonicity of the general regular class in the tolerance. -/
theorem bf1amb2_isGeneralRegularVerticalFunction_mono {n : ℕ}
    {W : Submodule ℝ (Spatial n)} {G : SubspaceSpace W → W.orthogonal} {ε ε' : ℝ}
    (h : IsGeneralRegularVerticalFunction W G ε) (hε : ε ≤ ε') :
    IsGeneralRegularVerticalFunction W G ε' := by
  obtain ⟨g, L, B, hL, hB, hr, hle⟩ := h
  exact ⟨g, L, B, hL, hB, hr, hle.trans hε⟩

/-- The zero graph at tolerance `ε ≥ 0`. -/
def bf1amb2_graph (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) : GeneralRegularVerticalGraph n (n + 2) ε where
  vertical_dimension := (b4p6_graph n).vertical_dimension
  direction := (b4p6_graph n).direction
  rank_eq := (b4p6_graph n).rank_eq
  offset := (b4p6_graph n).offset
  function := (b4p6_graph n).function
  regular := bf1amb2_isGeneralRegularVerticalFunction_mono (b4p6_graph n).regular hε

theorem bf1amb2_graph_image (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (bf1amb2_graph n ε hε).image = univ := by
  rw [← b4p6_graph_image n]
  rfl

theorem bf1amb2_graph_function (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (p) :
    (bf1amb2_graph n ε hε).function p = 0 := rfl

theorem bf1amb2_cover (n : ℕ) (E : Set (Space n)) (ε : ℝ) (hε : 0 < ε) :
    HasTypedGraphCover .vertical (n + 2) E ε ∧ HasTypedGraphCover .mixed (n + 2) E ε := by
  have : Nonempty (Set.univ : Set ℕ) := ⟨⟨0, trivial⟩⟩
  have hcov : (⋃ _ : (Set.univ : Set ℕ), (bf1amb2_graph n ε hε.le).image) = univ := by
    rw [iUnion_const]; exact bf1amb2_graph_image n ε hε.le
  let H : (∅ : Set ℕ) → HorizontalGraph n (n + 2) ε := fun i => (Set.notMem_empty _ i.2).elim
  refine ⟨⟨Set.univ, fun _ => bf1amb2_graph n ε hε.le, ?_⟩,
    ⟨∅, Set.univ, H, fun _ => bf1amb2_graph n ε hε.le, ?_⟩⟩
  · rw [hcov, sdiff_univ]; exact measure_empty
  · have : ((⋃ i : (∅ : Set ℕ), (H i).image) ∪
        ⋃ _ : (Set.univ : Set ℕ), (bf1amb2_graph n ε hε.le).image) = univ := by
      rw [hcov]; exact union_univ _
    rw [this, sdiff_univ]; exact measure_empty

theorem ambient_zero_graph_cover_all_proof : AmbientZeroGraphCoverStatement := by
  intro n _
  refine ⟨fun ε hε => ⟨bf1amb2_graph n ε hε.le, fun p => rfl,
    bf1amb2_graph_image n ε hε.le⟩, fun E => ⟨fun ε hε => (bf1amb2_cover n E ε hε).1,
    fun ε hε => (bf1amb2_cover n E ε hε).2⟩⟩

example : AmbientZeroGraphCoverStatement := ambient_zero_graph_cover_all_proof

end ParabolicRectifiability.Foundations
