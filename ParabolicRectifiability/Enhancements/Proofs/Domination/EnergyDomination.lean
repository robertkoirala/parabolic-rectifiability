import ParabolicRectifiability.Enhancements.Proofs.Domination.BetaDomination

/-! # Beta and energy domination under measure domination

If `ν ≤ c μ`, then `b_ν(z,r) ≤ c b_μ(z,r)` and `S_ν^R(z) ≤ c S_μ^R(z)`.
`fmeas3_betaSq_squareEnergy_le_of_le_ofReal_smul` proves `BetaEnergyDominationStatement`,
the statement of `Foundations.betaSq_squareEnergy_le_of_le_ofReal_smul`. The beta clause is
`fmeas3_betaSq_le_of_le_ofReal_smul`; the energy clause integrates it against `dr/r` on
`(0,R)` (`lintegral_mono`, then `lintegral_const_mul'` with the finite constant `ofReal c`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- Energy domination from beta domination at one centre: if `b_ν(z,r) ≤ c b_μ(z,r)` for
every `r`, then `S_ν^R(z) ≤ c S_μ^R(z)` for a finite `c` (the scale integral is linear in a
finite constant). -/
theorem fmeas3_squareEnergy_le_of_betaSq_le {n : ℕ} {μ ν : Measure (Space n)} (k : ℕ)
    (T : FamilyKind) {c : ℝ≥0∞} (hc : c ≠ ⊤) (z : Space n)
    (h : ∀ r : ℝ, betaSq ν k T z r ≤ c * betaSq μ k T z r) (R : ℝ) :
    squareEnergy ν k T R z ≤ c * squareEnergy μ k T R z := by
  calc squareEnergy ν k T R z = ∫⁻ r in Ioo 0 R, betaSq ν k T z r ∂scaleMeasure := rfl
    _ ≤ ∫⁻ r in Ioo 0 R, c * betaSq μ k T z r ∂scaleMeasure := lintegral_mono h
    _ = c * squareEnergy μ k T R z := lintegral_const_mul' c _ hc

/-- **Beta and energy domination.** If `ν ≤ c μ` with `c > 0`, then
`b_ν(z,r) ≤ c b_μ(z,r)` for all `z, r` and `S_ν^R(z) ≤ c S_μ^R(z)` for all `R, z`
(`BetaEnergyDominationStatement`). -/
theorem fmeas3_betaSq_squareEnergy_le_of_le_ofReal_smul : BetaEnergyDominationStatement := by
  intro n _ k _ _ T μ ν c hc h
  refine ⟨fun z r _ => fmeas3_betaSq_le_of_le_ofReal_smul k T hc h z r, fun R _ z => ?_⟩
  exact fmeas3_squareEnergy_le_of_betaSq_le k T ENNReal.ofReal_ne_top z
    (fmeas3_betaSq_le_of_le_ofReal_smul k T hc h z) R

end ParabolicRectifiability.Foundations
