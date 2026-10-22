import ParabolicRectifiability.Foundations.Density

/-! # Local upper-density bound

Finite upper `k`-density gives a finite `A` and a radius `ρ > 0` with `Θ(z,r) ≤ A` on `(0,ρ)`.
Route: `A = Θ^{k,*} + 1`, `Filter.eventually_lt_of_limsup_lt`, `mem_nhdsGT_iff_exists_Ioo_subset`. -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- The local upper-density bound: the body of `BetaP.c2_UpperDensityBoundStatement`. -/
def f2c_UpperDensityBoundStatement : Prop :=
  ∀ {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n), upperDensity μ k z < ⊤ →
    ∃ (A : ℝ≥0∞) (ρ : ℝ), A ≠ ⊤ ∧ 0 < ρ ∧
      ∀ r : ℝ, 0 < r → r < ρ → densityRatio μ k z r ≤ A

theorem f2c_upperDensity_bound_proof : f2c_UpperDensityBoundStatement := by
  intro n μ k z h
  have hA : upperDensity μ k z < upperDensity μ k z + 1 :=
    ENNReal.lt_add_right h.ne one_ne_zero
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), densityRatio μ k z r < upperDensity μ k z + 1 :=
    Filter.eventually_lt_of_limsup_lt hA
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨upperDensity μ k z + 1, u, ?_, hu, ?_⟩
  · exact (ENNReal.add_lt_top.mpr ⟨h, ENNReal.one_lt_top⟩).ne
  · intro r hr hru
    exact (hsub ⟨hr, hru⟩).le

end ParabolicRectifiability.Foundations
