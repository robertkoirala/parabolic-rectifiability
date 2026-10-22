import ParabolicRectifiability.Foundations.Proofs.DensityBridges.UpperDominationLemmas

/-! # Positive upper density gives Hausdorff domination: assembly

`fupdom_upper_density_domination` has exactly the type `UpperDensityDominationStatement` of
`hausdorffP_le_of_upperDensity_ge`. It is assembled from `fupdom_hausdorffP_le_of_fivefold`,
`fupdom_exists_open_measure_le` and `fupdom_input_fivefold`.

Assembly, with `C = 2·10^k` chosen after `k` and before `n`, `O`, `F`, `a`, `ρ`:
* for Borel `B`, put `E = F ∩ B ⊆ O`; for `η > 0` take (`fupdom_exists_open_measure_le`) an open
  `V` with `E ⊆ V ⊆ O` and `ρ(V) ≤ ρ(E) + η/c`, `c = ofReal (2·10^k/a)`;
  `fupdom_hausdorffP_le_of_fivefold` gives `H_P^k(E) ≤ c ρ(V) ≤ c ρ(E) + η`;
  `ENNReal.le_of_forall_pos_le_add` gives `H_P^k(E) ≤ c ρ(E)` (approximation-error limit);
* `ρ(F ∩ B) ≤ ρ(B ∩ O) = (ρ⌊O)(B)` since `F ⊆ O`;
* `H_P^k(F) ≤ c ρ(F) ≤ c ρ(closure O) < ⊤`: `O` bounded in the proper space, so its closure is
  compact and `ρ` is finite on it.
The upper-density hypothesis is used at every point of `F ∩ B`, never almost everywhere.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Foundations

/-- **Positive upper density gives Hausdorff domination**: `UpperDensityDominationStatement`. -/
theorem fupdom_upper_density_domination : UpperDensityDominationStatement := by
  intro k hk
  refine ⟨2 * 10 ^ k, by positivity, ?_⟩
  intro n hn hkn O hO hOb F hF hFO a ha ρ hfin hreg hdens
  have hc0 : ENNReal.ofReal (2 * 10 ^ k / a) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hcore : ∀ B : Set (Space n), MeasurableSet B →
      hausdorffP n k (F ∩ B) ≤ ENNReal.ofReal (2 * 10 ^ k / a) * ρ (F ∩ B) := by
    intro B _
    refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
    have hδ : (η : ℝ≥0∞) / ENNReal.ofReal (2 * 10 ^ k / a) ≠ 0 :=
      ENNReal.div_ne_zero.2 ⟨ENNReal.coe_ne_zero.2 hη.ne', ENNReal.ofReal_ne_top⟩
    obtain ⟨V, hV, hEV, _, hρV⟩ := fupdom_exists_open_measure_le ρ hfin (F ∩ B) O hO
      (inter_subset_left.trans hFO) _ hδ
    calc hausdorffP n k (F ∩ B)
        ≤ ENNReal.ofReal (2 * 10 ^ k / a) * ρ V :=
          fupdom_hausdorffP_le_of_fivefold fupdom_input_fivefold k ρ a ha (F ∩ B) V hV hEV
            fun z hz => hdens z hz.1
      _ ≤ ENNReal.ofReal (2 * 10 ^ k / a) *
            (ρ (F ∩ B) + (η : ℝ≥0∞) / ENNReal.ofReal (2 * 10 ^ k / a)) :=
          mul_le_mul' le_rfl hρV
      _ = ENNReal.ofReal (2 * 10 ^ k / a) * ρ (F ∩ B) + η := by
          rw [mul_add, ENNReal.mul_div_cancel hc0 ENNReal.ofReal_ne_top]
  refine ⟨fun B hB => ⟨hcore B hB, ?_⟩, ?_⟩
  · rw [Measure.restrict_apply hB]
    exact mul_le_mul' le_rfl (measure_mono fun x hx => ⟨hx.2, hFO hx.1⟩)
  · have h1 := hcore univ MeasurableSet.univ
    rw [inter_univ] at h1
    refine h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    have := hfin
    exact (measure_mono (hFO.trans subset_closure)).trans_lt
      hOb.isCompact_closure.measure_lt_top

end ParabolicRectifiability.Foundations
