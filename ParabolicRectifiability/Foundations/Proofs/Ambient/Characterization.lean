import ParabolicRectifiability.Foundations.Proofs.DensityBridges.FiniteUpperDensityAbsoluteContinuity
import ParabolicRectifiability.Foundations.Statements.Ambient
import ParabolicRectifiability.Foundations.Proofs.AmbientCover
import ParabolicRectifiability.Characterization.Proofs.GraphSource.DensityBounds

/-! # The ambient characterization

`f2i_ambient_rectifiable_iff_ac_iff_density` proves `AmbientCharacterizationStatement`, the
exact type of `Foundations.ambient_rectifiable_iff_ac_iff_density` and of
`Foundations.ambient_characterization`.

Route (the independent ambient case):
* rectifiable ⇒ `μ ≪ H_P^{n+2}`: the first field of `IsRegularlyRectifiableMeasure`;
* `μ ≪ H_P^{n+2}` ⇒ rectifiable of mixed and of vertical type: the one zero-function graph of
  norm `1` with image `X` (`ambient_zero_graph_cover_all_proof`) carries every measure;
* `μ ≪ H_P^{n+2}` ⇒ `0 < Θ^{n+2,*} < ∞` a.e.: B's proved graph density bounds
  `Characterization.b2_graph_density_bounds` on that graph (`Θ_* > 0`, `Θ^* < ∞` a.e. on its
  image `X`) and `Θ_* ≤ Θ^*` (`Characterization.lowerDensity_le_upperDensity`); at
  `k = n + 2` that step uses the ambient reference `(X, L^{n+1})`, not this statement;
* `0 < Θ^{n+2,*} < ∞` a.e. ⇒ `μ ≪ H_P^{n+2}`: `f2i_absolutelyContinuous_of_upperDensity_lt_top`
  at `k = n + 2`, applied to `f2i_input_upperDensityBound` (the local upper-density bound,
  supplied by `f2c_upperDensity_bound_proof`).

Neither the main characterization theorem nor the absolute-continuity bridge is used. The
absolute-continuity statement and the upper-density bound are
`f2i_absolutelyContinuous_of_upperDensity_lt_top` and `f2i_input_upperDensityBound`; the former
retains the bound as a hypothesis, and this assembly supplies it.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- Every measure absolutely continuous with respect to `H_P^{n+2}` is regularly
`(n + 2)`-rectifiable of mixed and of vertical type: the zero-function full graph of norm `1`
has image `X`, so it carries `μ`; the horizontal family of the mixed carrier is empty. -/
theorem f2i_ambient_rectifiable_of_ac {n : ℕ} (hn : 1 ≤ n) (μ : Measure (Space n))
    (hac : μ ≪ hausdorffP n (n + 2)) :
    IsRegularlyRectifiableMeasure .mixed (n + 2) μ ∧
      IsRegularlyRectifiableMeasure .vertical (n + 2) μ := by
  obtain ⟨G, -, hG⟩ := (ambient_zero_graph_cover_all_proof n hn).1 1 one_pos
  have hz : ∀ z : Space n, z ∈ G.image := fun z => by rw [hG]; exact mem_univ z
  refine ⟨⟨hac, ?_⟩, ⟨hac, ?_⟩⟩
  · refine ⟨∅, univ, fun _ => 0, fun i => (notMem_empty _ i.2).elim, fun _ => 1, fun _ => G, ?_⟩
    refine measure_mono_null (fun z hz' => ?_) measure_empty
    exact hz' (Or.inr (mem_iUnion.2 ⟨⟨0, mem_univ 0⟩, hz z⟩))
  · refine ⟨univ, fun _ => 1, fun _ => G, ?_⟩
    refine measure_mono_null (fun z hz' => ?_) measure_empty
    exact hz' (mem_iUnion.2 ⟨⟨0, mem_univ 0⟩, hz z⟩)

/-- For a locally Radon `μ ≪ H_P^{n+2}`, `0 < Θ^{n+2,*}(μ,z) < ∞` at `μ`-a.e. `z`: B's proved
graph density bounds on the zero graph with image `X`, and `Θ_* ≤ Θ^*`. -/
theorem f2i_ambient_upperDensity_of_ac {n : ℕ} (hn : 1 ≤ n) (μ : Measure (Space n))
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
    (hac : μ ≪ hausdorffP n (n + 2)) :
    ∀ᵐ z ∂μ, 0 < upperDensity μ (n + 2) z ∧ upperDensity μ (n + 2) z < ⊤ := by
  obtain ⟨G, -, hG⟩ := (ambient_zero_graph_cover_all_proof n hn).1 1 one_pos
  have h := (Characterization.b2_graph_density_bounds n hn (n + 2) (by omega) le_rfl μ hμ hreg
    hac).2 1 G
  filter_upwards [h] with z hz
  have hzG : z ∈ G.image := by rw [hG]; exact mem_univ z
  obtain ⟨hlow, hup⟩ := hz hzG
  exact ⟨lt_of_lt_of_le hlow (Characterization.lowerDensity_le_upperDensity μ (n + 2) z), hup⟩

/-- **The ambient characterization**: exactly `AmbientCharacterizationStatement`. Uses
`f2i_absolutelyContinuous_of_upperDensity_lt_top` at `k = n + 2`, and
`f2i_input_upperDensityBound` (the local upper-density bound) that it takes as hypothesis. -/
theorem f2i_ambient_rectifiable_iff_ac_iff_density : AmbientCharacterizationStatement := by
  intro n hn μ hμ hreg
  refine ⟨⟨fun h => h.1, fun hac => (f2i_ambient_rectifiable_of_ac hn μ hac).1⟩,
    ⟨fun h => h.1, fun hac => (f2i_ambient_rectifiable_of_ac hn μ hac).2⟩,
    ⟨f2i_ambient_upperDensity_of_ac hn μ hμ hreg, fun hd => ?_⟩⟩
  exact f2i_absolutelyContinuous_of_upperDensity_lt_top f2i_input_upperDensityBound n hn (n + 2)
    (by omega) le_rfl μ hμ hreg (hd.mono fun z hz => hz.2)

end ParabolicRectifiability.Foundations
