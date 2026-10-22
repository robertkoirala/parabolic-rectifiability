import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.IntegralAuxiliaryStatements

/-! # Tail vanishing at finite-energy points

Proves `i2_TailVanishingStatement`: if `S^R(z) < ∞` then `S^ρ(z) → 0` as `ρ ↓ 0`.

Route. For `ρ ≤ R`, `S^ρ(z)` is the integral of the indicator of `(0,ρ)` against
`r ↦ β²(z,r)` over `scaleMeasure`, dominated by the same integrand on `(0,R)`, whose integral
`S^R(z)` is finite. The indicator tends to `0` pointwise as `ρ ↓ 0`, so dominated convergence
along the countably generated filter `𝓝[>] 0` (the measure-continuity-from-above argument, in
integral form) gives the limit.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

theorem i2_tail_vanishing_proof : i2_TailVanishingStatement := by
  intro n _ k _ _ μ hμ _ T _ R _ z hz
  have : IsFiniteMeasureOnCompacts μ := hμ
  set f : ℝ → ℝ≥0∞ := fun r => betaSq μ k T z r with hf
  have hfm : Measurable f := (measurable_betaSq μ k T).comp measurable_prodMk_left
  have hS : ∀ ρ : ℝ, squareEnergy μ k T ρ z = ∫⁻ r, (Ioo 0 ρ).indicator f r ∂scaleMeasure := by
    intro ρ
    rw [lintegral_indicator measurableSet_Ioo]
    rfl
  simp_rw [hS]
  have hfin : ∫⁻ r, (Ioo 0 R).indicator f r ∂scaleMeasure ≠ ⊤ := by
    rw [← hS]; exact hz.ne
  have hR : ∀ᶠ ρ : ℝ in 𝓝[>] 0, ρ ≤ R := by
    have : Iio R ∈ 𝓝[>] (0 : ℝ) := mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨R, by assumption, Ioo_subset_Iio_self⟩
    exact Filter.mem_of_superset this fun _ (h : _ < R) => h.le
  have := tendsto_lintegral_filter_of_dominated_convergence (μ := scaleMeasure)
    (l := 𝓝[>] (0 : ℝ)) (F := fun ρ r => (Ioo 0 ρ).indicator f r) (f := fun _ => (0 : ℝ≥0∞))
    (fun r => (Ioo 0 R).indicator f r)
    (Filter.Eventually.of_forall fun ρ => hfm.indicator measurableSet_Ioo)
    (hR.mono fun ρ hρ => Filter.Eventually.of_forall fun r =>
      indicator_le_indicator_of_subset (Ioo_subset_Ioo_right hρ) (fun _ => zero_le) r)
    hfin
    (Filter.Eventually.of_forall fun r => by
      by_cases hr : 0 < r
      · refine tendsto_const_nhds.congr' ?_
        have : Iio r ∈ 𝓝[>] (0 : ℝ) :=
          mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨r, hr, Ioo_subset_Iio_self⟩
        filter_upwards [this] with ρ hρ
        exact (indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr (le_of_lt hρ))) _).symm
      · refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun ρ => ?_)
        exact (indicator_of_notMem (fun h => hr h.1) _).symm)
  simpa using this

end ParabolicRectifiability.IntegralCanonical
