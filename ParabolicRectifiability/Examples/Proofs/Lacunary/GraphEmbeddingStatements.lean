import ParabolicRectifiability.Examples.Lacunary

/-! # The lacunary graph map is a measurable embedding: statement

Proposition definition only.

The graph map `F(t) = (f(t), t)` is a measurable embedding of `ℝ` into `Space 1` for **every**
amplitude `ε`, amplitude sequence `a` and frequency sequence `N`: the series `f` is a `tsum` of
measurable functions (`Measurable.tsum` needs no summability premise), `point` is measurable, and
the time coordinate is a measurable left inverse, so `F` is injective with measurable range. It is
used for the pushforward transfers `ν_E(A) = |E ∩ F⁻¹(A)|` (every `A`) and
`(∀ᵐ z ∂ν_E, P z) ↔ (∀ᵐ t ∂(L¹⌊E), P (F t))` (every `P`, no measurability of `P`).
-/

noncomputable section

open MeasureTheory

namespace ParabolicRectifiability.Examples

/-- **The lacunary graph map is a measurable embedding.** For all `ε`, `a`, `N`, the
lacunary graph map `F = lacunaryGraphMap ε a N : ℝ → Space 1` is a measurable embedding.
No standing hypothesis is needed. -/
def E2LacunaryGraphEmbeddingStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), MeasurableEmbedding (lacunaryGraphMap ε a N)

end ParabolicRectifiability.Examples
