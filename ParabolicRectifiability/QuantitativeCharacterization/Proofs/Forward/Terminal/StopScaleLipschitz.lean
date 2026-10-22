import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # The stopping-scale Lipschitz lemma

Proof of `d1c_stopScaleLipschitz_proof : StopScaleLipschitzStatement`.

`ρ = ⨅_{Q ∈ 𝒯} (ℓ_Q + infDist z Q)` is a conditional infimum over the nonempty index set of
members (`root_mem`) of nonnegative terms, hence bounded below by `0`: `le_ciInf` gives `ρ ≥ 0`
and, with `Metric.infDist_le_infDist_add_dist`, the `1`-Lipschitz bound; `ciInf_le` gives
`ρ(z) ≤ ℓ_Q + dist_P(z, Q)`, and `Metric.infDist_zero_of_mem` gives `ρ ≤ ℓ_Q` on the cell `Q`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section StopScaleLipschitz

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The cell sides are positive. -/
theorem d1clips_scale_pos (P : DirectPartition E ℓ₀) (j : ℕ) : 0 < P.scale j := by
  unfold DirectPartition.scale coherentScale
  exact div_pos P.scale_pos (pow_pos (by norm_num) _)

/-- Every term `ℓ_Q + dist_P(z, Q)` of the stopping scale is nonnegative. -/
theorem d1clips_term_nonneg (𝒢 : GoodRegion P μ k Λ b) (z : Space n) (Q : 𝒢.members) :
    0 ≤ P.scale Q.1.1 + Metric.infDist z (P.cellOf Q.1) :=
  add_nonneg (d1clips_scale_pos P _).le Metric.infDist_nonneg

/-- The terms of the stopping scale are bounded below (by `0`). -/
theorem d1clips_bddBelow (𝒢 : GoodRegion P μ k Λ b) (z : Space n) :
    BddBelow (Set.range fun Q : 𝒢.members => P.scale Q.1.1 + Metric.infDist z (P.cellOf Q.1)) :=
  ⟨0, by
    rintro _ ⟨Q, rfl⟩
    exact d1clips_term_nonneg 𝒢 z Q⟩

/-- `ρ(z) ≤ ℓ_Q + dist_P(z, Q)` for every member (`ciInf_le`). -/
theorem d1clips_le_term (𝒢 : GoodRegion P μ k Λ b) (z : Space n) (Q : 𝒢.members) :
    𝒢.stopScale z ≤ P.scale Q.1.1 + Metric.infDist z (P.cellOf Q.1) := by
  unfold GoodRegion.stopScale
  exact ciInf_le (d1clips_bddBelow 𝒢 z) Q

end StopScaleLipschitz

/-- **The stopping-scale Lipschitz lemma** (`StopScaleLipschitzStatement`). -/
theorem d1c_stopScaleLipschitz_proof : StopScaleLipschitzStatement := by
  intro n E ℓ₀ P μ k Λ b 𝒢
  have : Nonempty 𝒢.members := ⟨⟨𝒢.root, 𝒢.root_mem⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    unfold GoodRegion.stopScale
    exact le_ciInf fun Q => d1clips_term_nonneg 𝒢 z Q
  · intro z w
    have h : 𝒢.stopScale z - dist z w ≤ 𝒢.stopScale w := by
      change 𝒢.stopScale z - dist z w ≤
        ⨅ Q : 𝒢.members, (P.scale Q.1.1 + Metric.infDist w (P.cellOf Q.1))
      refine le_ciInf fun Q => ?_
      have h1 := d1clips_le_term 𝒢 z Q
      have h2 : Metric.infDist z (P.cellOf Q.1) ≤ Metric.infDist w (P.cellOf Q.1) + dist z w :=
        Metric.infDist_le_infDist_add_dist
      linarith
    linarith
  · intro Q hQ z
    exact d1clips_le_term 𝒢 z ⟨Q, hQ⟩
  · intro Q hQ z hz
    have h := d1clips_le_term 𝒢 z ⟨Q, hQ⟩
    rw [Metric.infDist_zero_of_mem hz, add_zero] at h
    exact h

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
