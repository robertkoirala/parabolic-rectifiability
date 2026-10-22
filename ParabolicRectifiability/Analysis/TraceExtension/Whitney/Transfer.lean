import ParabolicRectifiability.Analysis.TraceExtension.Whitney.DerivBounds
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.TransferFromDerivBounds

/-! # Unconditional micro estimates and Whitney transfer

The implications `whitneyFilling_affineErrorSq_le_micro_proof`,
`whitneyFilling_micro_carleson_le_proof` and `whitney_transfer_proof` take the
derivative-bound statement of `whitneyFilling_deriv_bounds_proof` as a hypothesis. With
that theorem they become unconditional.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

universe u v

/-- The microscopic error bound, unconditional. -/
theorem whitneyFilling_affineErrorSq_le_micro_unconditional (m : ℕ) (D a H b K : ℝ) (N : ℕ)  :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsClosed F₀ → F₀.Nonempty →
      ∀ (P : WhitneyPartition W H b K N) {Y : Type v} [NormedAddCommGroup Y]
        [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0), LipschitzOnWith L g W.nodeSet →
        ∀ (y : Space m) (s : ℝ), 0 < s → 2 * s < Metric.infDist y F₀ →
          affineErrorSq (parabolicVolume m) (whitneyFilling P.toWhitneyWeights g) y s ≤
            ENNReal.ofReal (C * (L : ℝ) ^ 2 * (s / Metric.infDist y F₀) ^ 2) :=
  whitneyFilling_affineErrorSq_le_micro_proof.{u, v} m D a H b K N
    (whitneyFilling_deriv_bounds_proof.{u, v} m D a H b K N)

/-- The integrated microscopic bound, unconditional. -/
theorem whitneyFilling_micro_carleson_le_unconditional (m : ℕ) (D a H b K : ℝ) (N : ℕ)  :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsClosed F₀ → F₀.Nonempty →
      ∀ (P : WhitneyPartition W H b K N) {Y : Type v} [NormedAddCommGroup Y]
        [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0), LipschitzOnWith L g W.nodeSet →
        ∀ (z : Space m) (R : ℝ), 0 < R →
          ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ {s | 2 * s < Metric.infDist y F₀},
              affineErrorSq (parabolicVolume m) (whitneyFilling P.toWhitneyWeights g) y s
                ∂scaleMeasure ∂parabolicVolume m ≤
            ENNReal.ofReal (C * (L : ℝ) ^ 2 * R ^ (m + 2)) :=
  whitneyFilling_micro_carleson_le_of_derivBounds.{u, v} m D a H b K N
    (whitneyFilling_deriv_bounds_proof.{u, v} m D a H b K N)

/-- The full Whitney transfer, unconditional. -/
theorem whitney_transfer_unconditional (m : ℕ) (D a H b K : ℝ) (N : ℕ) (ha : 2 ≤ a) (hH : 0 ≤ H)  :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsCompact F₀ → F₀.Nonempty →
      ∀ (P : WhitneyPartition W H b K N) {Y : Type v} [NormedAddCommGroup Y]
        [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0), LipschitzOnWith L g W.nodeSet →
        ∀ B : ℝ, 0 ≤ B →
        (∀ (z : Space m) (R : ℝ), 0 < R →
          W.nodeCarlesonIntegral g L z R ≤ ENNReal.ofReal (B * R ^ (m + 2))) →
        LipschitzWith (C * L) (whitneyFilling P.toWhitneyWeights g) ∧
          HasAffineCarlesonBound (parabolicVolume m) (whitneyFilling P.toWhitneyWeights g)
            (C * ((L : ℝ) ^ 2 + B)) :=
  whitney_transfer_proof.{u, v} m D a H b K N ha hH
    (whitneyFilling_deriv_bounds_proof.{u, v} m D a H b K N)

end ParabolicRectifiability
