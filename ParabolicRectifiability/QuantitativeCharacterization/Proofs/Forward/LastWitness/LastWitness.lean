import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ForwardCovering
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.LastWitness
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.LastWitness.OccurrenceBound
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.LastWitness.Charging
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.LastWitness.LevelEstimate
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.LastWitness.SquareUpTo
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.LastWitness.WitnessSelection
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.LastWitness.AncestorInclusion
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.LastWitness.Incidence
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.LastWitness.PairBound

/-! # The last-witness estimate: composition in implication form

`d1dcomp_squareBound_of_upTo` and `d1dcomp_lastWitness_of` assemble the infinite square bound
from the finite truncations and the per-occurrence bound.

`d1dcomp_lastWitness_of_inputs` composes the eight proof modules of this folder into
`LastWitnessStatement`, the type of `d1_hub_lastWitness`, with three input statements as
hypotheses: `Terminal.OwnerStatement` and `Terminal.AncestorStatement` (`d1c_owner`,
`d1c_ancestor`) and `PartitionEnergy.PlaneComparisonStatement` (`d1a_planeComparison`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Witness

/-- **Monotone convergence in the truncation**: finite square bounds of the neck's
type at every truncation `N`, with one constant, give the infinite square bound. -/
theorem d1dcomp_squareBound_of_upTo {n m : ℕ} {ι : Type*} (T : NeckType) (F : CoherentFamily n m ι)
    (E : ℝ) (h : ∀ N : ℕ, TypeSquareBoundUpTo T F E N) : T.SquareBound F E := by
  cases T with
  | horizontal =>
    show ∀ w : Spatial n, ∑' j, F.comparisonEnergy (fun z : Space n => z.1) j w ^ 2 ≤
      ENNReal.ofReal E
    intro w
    refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
    rcases N with _ | N
    · simp
    · exact h N w
  | vertical =>
    show ∀ w : Space n, ∑' j, F.comparisonEnergy (fun z : Space n => z) j w ^ 2 ≤
      ENNReal.ofReal E
    intro w
    refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
    rcases N with _ | N
    · simp
    · exact h N w

/-- **Assembly.** The per-occurrence bound and the finite square sum
give `LastWitnessStatement`. -/
theorem d1dcomp_lastWitness_of (hOcc : OccurrenceBoundStatement) (hSq : SquareUpToStatement) :
    LastWitnessStatement := by
  intro n hn k hk hkn A hA
  obtain ⟨Λ₀, hΛ₀, h₁⟩ := hOcc n hn k hk hkn A hA
  refine ⟨max Λ₀ 4000, le_trans hΛ₀ (le_max_left _ _), ?_⟩
  intro Λ hΛ
  obtain ⟨B, hB, C₁, hC₁, b₀, hb₀, h₂⟩ := h₁ Λ (le_trans (le_max_left _ _) hΛ)
  refine ⟨B, hB, 44 * C₁, mul_nonneg (by norm_num) hC₁, 1, one_pos, b₀, hb₀, ?_⟩
  intro b hb hbb μ hfin hreg a ha R hR hADR P 𝒢 hroot δ κ θ γ _ _ _ hγ TN
  exact d1dcomp_squareBound_of_upTo 𝒢.type TN.family (44 * C₁ * b)
    (hSq n μ.support R P μ k Λ b 𝒢 δ κ θ γ TN C₁ (le_trans (le_max_right _ _) hΛ) hγ hC₁
      (h₂ b hb hbb μ hfin hreg a ha R hR hADR P 𝒢 hroot))
/-- **The last-witness estimate in implication form**: `LastWitnessStatement` from the three input
statements, through the eight proof modules. -/
theorem d1dcomp_lastWitness_of_inputs :
    Terminal.OwnerStatement → Terminal.AncestorStatement →
      PartitionEnergy.PlaneComparisonStatement → LastWitnessStatement :=
  fun hO hA hP =>
    d1dcomp_lastWitness_of (d1d_occurrenceBound_proof hP)
      (d1d_squareUpTo_proof d1d_witnessSelection_proof d1d_incidence_proof
        (d1d_levelEstimate_proof d1d_ancestorInclusion_proof d1d_pairBound_proof hA)
        (d1d_charging_proof hA) hO)

end Witness

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
