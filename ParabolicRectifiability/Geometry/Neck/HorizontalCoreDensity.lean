import ParabolicRectifiability.Geometry.Horizontal.CoreDensity
import ParabolicRectifiability.Geometry.Neck.Conclusions
import ParabolicRectifiability.Geometry.Neck.CenterProperties

/-!
# Neck: horizontal core lower density

Positive lower density of the core's own Hausdorff measure for a horizontal neck with
Euclidean parameter space, as `horizontal_coreLowerDensity_of_parametrization_proof` (the
type of `horizontal_coreLowerDensity_of_parametrization`).

Route: from the exact horizontal parametrization `φ(u) = (G u, τ u)` on the
compact `A ⊆ ℝ^k` (Lipschitz and antilipschitz with constant `2`), restrict to the
compact preimage `A₀ = {u ∈ A | φ u ∈ 𝒞₀}`; the restricted chart has range exactly the
core `𝒞₀` (because `𝒞₀ ⊆ 𝒞 = range φ`), and
`horizontalChart_ae_lowerDensity_proof` gives the conclusion after unfolding
`HasPositiveLowerDensity`. Compactness of `A₀` is proved: `φ` is continuous on the compact
space `A` and the core is compact (`NeckRegion.isCompact_core`), hence closed.
-/

noncomputable section

namespace ParabolicRectifiability

namespace NeckHubTree

open MeasureTheory Set
open scoped ENNReal NNReal

universe u

/-- The compact restricted parameter domain: for a chart `φ : A → Space n`,
continuous on a compact `A`, the parameters mapped into a closed set `K` form a compact
set `A₀ ⊆ A`, and `φ` restricted to `A₀` has range exactly `K` whenever `K ⊆ range φ`. -/
theorem nk3_restricted_chart {n k : ℕ} {A : Set (Spatial k)} (hA : IsCompact A)
    {φ : A → Space n} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hφ' : AntilipschitzWith L φ)
    {K : Set (Space n)} (hK : IsClosed K) (hKφ : K ⊆ Set.range φ) :
    ∃ (A₀ : Set (Spatial k)) (φ₀ : A₀ → Space n), IsCompact A₀ ∧
      LipschitzWith L φ₀ ∧ AntilipschitzWith L φ₀ ∧ Set.range φ₀ = K := by
  have hsub : Subtype.val '' (φ ⁻¹' K) ⊆ A := by
    rintro _ ⟨v, -, rfl⟩
    exact v.2
  refine ⟨Subtype.val '' (φ ⁻¹' K), φ ∘ Set.inclusion hsub, ?_, ?_, ?_, ?_⟩
  · have : CompactSpace A := isCompact_iff_compactSpace.1 hA
    exact ((hK.preimage hφ.continuous).isCompact).image continuous_subtype_val
  · refine LipschitzWith.of_dist_le_mul fun u v => ?_
    have hd : dist (Set.inclusion hsub u) (Set.inclusion hsub v) = dist u v := by
      simp only [Subtype.dist_eq]
    rw [Function.comp_apply, Function.comp_apply, ← hd]
    exact hφ.dist_le_mul _ _
  · refine AntilipschitzWith.of_le_mul_dist fun u v => ?_
    have hd : dist (Set.inclusion hsub u) (Set.inclusion hsub v) = dist u v := by
      simp only [Subtype.dist_eq]
    rw [Function.comp_apply, Function.comp_apply, ← hd]
    exact hφ'.le_mul_dist _ _
  · ext z
    constructor
    · rintro ⟨w, rfl⟩
      rw [Function.comp_apply]
      obtain ⟨v, hv, hvw⟩ := w.2
      have hw : Set.inclusion hsub w = v :=
        Subtype.ext (by rw [Set.coe_inclusion]; exact hvw.symm)
      rw [hw]
      exact hv
    · intro hz
      obtain ⟨v, rfl⟩ := hKφ hz
      refine ⟨⟨v.1, Set.mem_image_of_mem Subtype.val (show v ∈ φ ⁻¹' K from hz)⟩, ?_⟩
      rw [Function.comp_apply]

/-- **Horizontal core lower density** (Euclidean parameter space): under an
exact horizontal parametrization with distortion `2`, the core's own Hausdorff measure has
positive lower `k`-density almost everywhere. The type is that of
`horizontal_coreLowerDensity_of_parametrization`. -/
theorem horizontal_coreLowerDensity_of_parametrization_proof {n k : ℕ} {ι : Type u} {q : Space n}
    {R c₀ Cd Cs σ δ E κ θ γ : ℝ} (N : NeckRegion n k .horizontal ι q R c₀ Cd Cs σ δ E κ θ γ) :
    N.HasHorizontalParametrization 2 →
      ∀ᵐ z ∂(hausdorffP n k).restrict N.core, ∃ a r₀ : ℝ, 0 < a ∧ 0 < r₀ ∧
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
          ENNReal.ofReal (a * r ^ k) ≤ (hausdorffP n k).restrict N.core (Metric.ball z r) := by
  rintro ⟨G, -, A, τ, hA, hbi, hrange⟩
  have h2 : ((2 : ℝ≥0) : ℝ) = 2 := by norm_num
  have hφL : LipschitzWith 2 (fun u : A => point (G u) (τ u)) :=
    LipschitzWith.of_dist_le_mul fun u v => by
      rw [h2]
      exact (hbi u v).2
  have hφA : AntilipschitzWith 2 (fun u : A => point (G u) (τ u)) :=
    AntilipschitzWith.of_le_mul_dist fun u v => by
      rw [h2]
      have h := (hbi u v).1
      linarith
  have hcore : N.core ⊆ Set.range (fun u : A => point (G u) (τ u)) := by
    rw [hrange]
    exact N.core_subset_centers
  obtain ⟨A₀, φ₀, hA₀, hφ₀L, hφ₀A, hrange₀⟩ :=
    nk3_restricted_chart hA hφL hφA N.isCompact_core.isClosed hcore
  have h := horizontalChart_ae_lowerDensity_proof hA₀ hφ₀L hφ₀A
  rw [hrange₀] at h
  exact h

end NeckHubTree

end ParabolicRectifiability
