import ParabolicRectifiability.IntegralCanonical.Defs

/-! # Intermediate statements for the integral tests

Statements of the seven intermediate results behind the integral equivalences (at an arbitrary
endpoint `R > 0`): the capped limits, compact exhaustion, positive weight and adaptive gauge
tests (`tendsto_cappedTail_cappedValue_measure_infinite`, `compactExhaustionTest_of_ae_lt_top`,
`positiveWeightTest_of_ae_lt_top`, `adaptiveGaugeTest_of_ae_lt_top`), together with the
gauge series `i2_gaugeSeries` used for the adaptive gauge.

This file contains proposition definitions and one function definition only.

Standing hypotheses of every statement: `n ≥ 1`, `1 ≤ k ≤ n + 2`, `μ` locally Radon, `T`
available, endpoint `R > 0`; `S = S^R_{μ,T} = squareEnergy μ k T R`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

/-- **Tail vanishing** (finite branch of the tail alternative). If `S^R_{μ,T}(z) < ∞` at a
point `z`, the tail `T_ρ(z) = S^ρ_{μ,T}(z)` tends to `0` as `ρ ↓ 0`. (The infinite branch,
`T_ρ(z) = ∞` for every `ρ > 0`, is `squareEnergy_lt_top_iff_of_endpoints_proof`.) -/
def i2_TailVanishingStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ R : ℝ, 0 < R → ∀ z : Space n, squareEnergy μ k T R z < ⊤ →
    Tendsto (fun ρ : ℝ => squareEnergy μ k T ρ z) (𝓝[>] 0) (𝓝 0)

/-- **Capped tail limit.** On a bounded Borel set `A`, the
pointwise limit `min{1, T_ρ(z)} → 1_{S = ∞}(z)` (given as a hypothesis at every point) passes
to `∫_A min{1, T_ρ} dμ → μ(A ∩ {S = ∞})` along `ρ ↓ 0`. -/
def i2_CappedTailLimitStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ R : ℝ, 0 < R →
  ∀ A : Set (Space n), MeasurableSet A → Bornology.IsBounded A →
    (∀ z : Space n, Tendsto (fun ρ : ℝ => min 1 (squareEnergy μ k T ρ z)) (𝓝[>] 0)
      (𝓝 ({z | squareEnergy μ k T R z = ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) z))) →
    Tendsto (fun ρ : ℝ => ∫⁻ z in A, min 1 (squareEnergy μ k T ρ z) ∂μ) (𝓝[>] 0)
      (𝓝 (μ (A ∩ {z | squareEnergy μ k T R z = ⊤})))

/-- **Capped value limit.** On a bounded Borel set `A`,
`L^{-1} ∫_A min{S, L} dμ → μ(A ∩ {S = ∞})` as the real cap `L → ∞`. -/
def i2_CappedValueLimitStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ R : ℝ, 0 < R →
  ∀ A : Set (Space n), MeasurableSet A → Bornology.IsBounded A →
    Tendsto (fun L : ℝ =>
        (ENNReal.ofReal L)⁻¹ * ∫⁻ z in A, min (squareEnergy μ k T R z) (ENNReal.ofReal L) ∂μ)
      atTop (𝓝 (μ (A ∩ {z | squareEnergy μ k T R z = ⊤})))

/-- **Compact exhaustion** (forward direction): `S < ∞` a.e. gives increasing compact `K_j` exhausting `μ` with
`∫_{K_j} S dμ < ∞`. -/
def i2_CompactExhaustionStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ R : ℝ, 0 < R →
    (∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) → CompactExhaustionTest μ k T R

/-- **Positive weight** (forward direction): `S < ∞` a.e. gives one Borel `w : X → (0,1]` with `∫_A w S dμ < ∞` on every
bounded Borel set `A`. -/
def i2_PositiveWeightStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ R : ℝ, 0 < R →
    (∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) →
      PositiveWeightTest μ k T R {A | MeasurableSet A ∧ Bornology.IsBounded A}

/-- The gauge series `Φ_t(u) = Σ_{j ≥ 0} min{1, u / t_j}` of the adaptive gauge test, for a
real sequence `t`. Only its values on `[0, ∞)` are used. -/
def i2_gaugeSeries (t : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑' j : ℕ, min 1 (u / t j)

/-- **Admissibility of the gauge series.** For a positive sequence
`t` with `Σ_j t_j⁻¹ < ∞`, the gauge series is an admissible gauge: continuous, nondecreasing,
concave and unbounded on `[0,∞)`, zero at zero, nonnegative there. -/
def i2_GaugeSeriesAdmissibleStatement : Prop :=
  ∀ t : ℕ → ℝ, (∀ j, 0 < t j) → Summable (fun j => (t j)⁻¹) →
    IsAdmissibleGauge (i2_gaugeSeries t)

/-- **Finite gauge integral.** If `S < ∞`
`μ`-a.e., then for every bounded Borel `A` there is a positive sequence `t` with
`Σ_j t_j⁻¹ < ∞` whose gauge series has finite integral `∫_A Φ_t(S) dμ < ∞` (with
`Φ_t(∞) = ∞`, `extendedGauge`). -/
def i2_GaugeSeriesIntegralStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ R : ℝ, 0 < R →
    (∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) →
  ∀ A : Set (Space n), MeasurableSet A → Bornology.IsBounded A →
    ∃ t : ℕ → ℝ, (∀ j, 0 < t j) ∧ Summable (fun j => (t j)⁻¹) ∧
      ∫⁻ z in A, extendedGauge (i2_gaugeSeries t) (squareEnergy μ k T R z) ∂μ < ⊤

end ParabolicRectifiability.IntegralCanonical
