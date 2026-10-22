import ParabolicRectifiability.Characterization.Proofs.GraphSource.ReferenceAdapters
import ParabolicRectifiability.Characterization.Proofs.GraphSource.SquareFinitenessComponents
import ParabolicRectifiability.Characterization.Proofs.GraphSource.DensityComponents
import ParabolicRectifiability.Characterization.Assembly.CoveringLemmas

/-! # Density bounds on graph images

`b2_graph_density_bounds` proves the density bounds for the full source on graph images
(the statement of `graph_density_bounds`), by the following per-carrier argument:

1. `b2_density_on_adr_carrier`: on a closed ADR carrier `(Γ, σ)`, for `μ ≪ H_P^k` locally Radon,
   `μ⌊Γ ≪ σ` (`ADRHausdorffComparisonStatement`); relative differentiation of the **full** `μ`
   against `σ` holds `σ`-a.e., hence `μ`-a.e. on `Γ`; there `0 < dμ/dσ < ∞`, and ADR gives the
   two density bounds of the full source, including its singular and off-carrier mass.
2. Vertical graphs, `k < n + 2`: the graph image is a reference carrier (vertical adapter).
   Vertical graphs, `k = n + 2`: the ambient reference `(X, L^{n+1})` with the same argument;
   neither `AmbientCharacterizationStatement` nor `AmbientAbsolutelyContinuousDensityStatement`
   is used.
3. Horizontal graphs: compact pieces covering the image modulo `H_P^k`, each inside a
   reference carrier (horizontal adapter); the `H_P^k`-null remainder is `μ`-null. The
   conclusion is restricted to the original image only at the end; no decomposition over the
   possibly non-Borel image is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.QuantitativeCharacterization

/-- Step 1: densities of the full source on a closed ADR carrier. -/
theorem b2_density_on_adr_carrier :
    ∀ n : ℕ, 1 ≤ n → ∀ (k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
      IsADRCarrier k c C Γ σ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      μ ≪ hausdorffP n k →
      ∀ᵐ z ∂μ, z ∈ Γ → 0 < lowerDensity μ k z ∧ upperDensity μ k z < ⊤ := by
  intro n hn k c C Γ σ hcar μ hfin hreg hac
  obtain ⟨a, b, -, -, hcomp⟩ := b2_adr_hausdorff_comparison k c C
  have hΓ : MeasurableSet Γ := hcar.isClosed.measurableSet
  have hacσ : μ.restrict Γ ≪ σ := by
    intro S hS
    rw [Measure.restrict_apply' hΓ]
    apply hac
    have hle := (hcomp n hn Γ σ hcar S).2
    rw [hS, mul_zero] at hle
    exact nonpos_iff_eq_zero.1 hle
  have hrel := b2_relative_differentiation n hn k c C Γ σ hcar μ hfin hreg
  have hrelμ : ∀ᵐ z ∂μ, z ∈ Γ → Tendsto (fun r : ℝ => μ (Metric.ball z r) / σ (Metric.ball z r))
      (𝓝[>] (0 : ℝ)) (𝓝 (μ.rnDeriv σ z)) :=
    (ae_restrict_iff' hΓ).1 (hacσ.ae_le hrel)
  have hpos := b2_rnDeriv_pos_on_carrier n hn k c C Γ σ hcar μ hfin hreg hacσ
  filter_upwards [hrelμ, hpos] with z hz1 hz2 hzΓ
  exact b2_density_of_ratio n hn k c C Γ σ hcar μ z hzΓ (μ.rnDeriv σ z) (hz1 hzΓ)
    (hz2 hzΓ).1 (hz2 hzΓ).2

/-- Step 3: horizontal graphs. -/
theorem b2_horizontal_graph_density :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      μ ≪ hausdorffP n k →
      ∀ (ε : ℝ) (G : HorizontalGraph n k ε), ∀ᵐ z ∂μ, z ∈ G.image →
        0 < lowerDensity μ k z ∧ upperDensity μ k z < ⊤ := by
  intro n hn k hk hkn μ hfin hreg hac ε G
  obtain ⟨L, hL, hHref⟩ := b2_horizontal_graph_reference n k hk ε
  obtain ⟨c, C, hρ⟩ := b2_reference_adr_square n hn k hk hkn L hL
  obtain ⟨J, Gc, hGc, hnull⟩ := b2_horizontal_compact_cover n k ε G
  have hpiece : ∀ j : J, ∀ᵐ z ∂μ, z ∈ (Gc j).image →
      0 < lowerDensity μ k z ∧ upperDensity μ k z < ⊤ := by
    intro j
    obtain ⟨H, hH⟩ := hHref (Gc j) (hGc j).1 (hGc j).2
    have hcar : IsADRCarrier k c C H.carrier H.measure := (hρ (Reference.horizontal H)).1
    have h := b2_density_on_adr_carrier n hn k c C H.carrier H.measure hcar μ hfin hreg hac
    filter_upwards [h] with z hz hzG using hz (hH hzG)
  have hall := ae_mem_iUnion_imp (fun j : J => (Gc j).image) hpiece
  have hrem : ∀ᵐ z ∂μ, z ∉ G.image \ ⋃ j, (Gc j).image :=
    measure_eq_zero_iff_ae_notMem.1 (hac hnull)
  filter_upwards [hall, hrem] with z hz1 hz2 hzG
  apply hz1
  by_contra hcon
  exact hz2 ⟨hzG, hcon⟩

/-- Step 2: vertical graphs, including `k = n + 2` through the ambient reference. -/
theorem b2_vertical_graph_density :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      μ ≪ hausdorffP n k →
      ∀ (ε : ℝ) (G : GeneralRegularVerticalGraph n k ε), ∀ᵐ z ∂μ, z ∈ G.image →
        0 < lowerDensity μ k z ∧ upperDensity μ k z < ⊤ := by
  intro n hn k hk hkn μ hfin hreg hac ε G
  by_cases hlt : k < n + 2
  · obtain ⟨V, hV⟩ := b2_vertical_graph_reference n k hlt ε G
    obtain ⟨g, K, B, -, -, -, hKB⟩ := G.regular
    have hK0 : (0 : ℝ) ≤ K := NNReal.coe_nonneg K
    have hB0 : (0 : ℝ) ≤ B := NNReal.coe_nonneg B
    obtain ⟨c, C, hρ⟩ := b2_reference_adr_square n hn k hk hkn (1 + ε) (by linarith)
    have hcar : IsADRCarrier k c C V.carrier V.measure := (hρ (Reference.vertical V)).1
    rw [hV] at hcar
    exact b2_density_on_adr_carrier n hn k c C G.image V.measure hcar μ hfin hreg hac
  · have hk2 : k = n + 2 := by omega
    subst hk2
    obtain ⟨c, C, hρ⟩ := b2_reference_adr_square n hn (n + 2) hk hkn 1 le_rfl
    have hcar : IsADRCarrier (n + 2) c C (Set.univ : Set (Space n)) (parabolicVolume n) :=
      (hρ (Reference.ambient rfl)).1
    have h := b2_density_on_adr_carrier n hn (n + 2) c C Set.univ (parabolicVolume n) hcar μ
      hfin hreg hac
    filter_upwards [h] with z hz _ using hz (Set.mem_univ z)

/-- Density bounds on graph images: the statement of `graph_density_bounds`. -/
theorem b2_graph_density_bounds :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      μ ≪ hausdorffP n k →
      (∀ (ε : ℝ) (G : HorizontalGraph n k ε), ∀ᵐ z ∂μ, z ∈ G.image →
        0 < lowerDensity μ k z ∧ upperDensity μ k z < ⊤) ∧
      (∀ (ε : ℝ) (G : GeneralRegularVerticalGraph n k ε), ∀ᵐ z ∂μ, z ∈ G.image →
        0 < lowerDensity μ k z ∧ upperDensity μ k z < ⊤) := by
  intro n hn k hk hkn μ hfin hreg hac
  exact ⟨b2_horizontal_graph_density n hn k hk hkn μ hfin hreg hac,
    b2_vertical_graph_density n hn k hk hkn μ hfin hreg hac⟩

end ParabolicRectifiability.Characterization
