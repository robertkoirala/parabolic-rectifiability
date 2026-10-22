import ParabolicRectifiability.QuantitativeCharacterization.Coverings
import ParabolicRectifiability.IntegralCanonical.Statements.Canonical

/-! # Intermediate statements for the root approximants

Proposition definitions only. They split the proofs of `exists_root_approximants` and
`approximant_canonical_limits` (the measure approximants of the quantitative characterization)
into named steps.

Notation: `m = 𝒞.multiplicity`, `P₀ = P(a,R)`, `S = Σ_i R_i^k` (as `∑' i, ofReal (R_i) ^ k`).

* `dp2_FactorialMomentStatement`: radius ordering and the same-family local packing give
  `∫_{P₀} m^p dμ ≤ p! A (2^k K)^{p-1} S` from the model-ball growth `μ(P_i) ≤ A R_i^k`.
* `dp2_ExponentialTailStatement`: the factorial moments give
  `μ(P₀ ∩ {m > N}) ≤ e^{-N/s} (μ(P₀) + A S/(s - 2^k K))` for every `s > 2^k K` (Markov).
* `dp2_TypedSplitStatement`: trace carriage gives the typed trace split and the measure identity
  at every level.
* `dp2_LocalAbsoluteContinuityStatement`: the local upper growth hypothesis of
  `exists_root_approximants` gives `μ⌊P₀ ≪ H_P^k`.
* `dp2_ApproximantLimitsStatement`: monotone approximants converging on Borel sets to `μ⌊F`,
  antitone residual with total mass tending to zero, under finite multiplicity almost everywhere
  on the root.
* `dp2_CanonicalIdentificationStatement`: canonical uniqueness identifies typed rectifiable
  `μ⌊F_H`, `μ⌊F_V` carrying `μ⌊P` with `μ_H⌊P`, `μ_V⌊P`. It is stated in implication form over
  the rectifiability of absolutely continuous restrictions and of countable sums, which are
  supplied when the statements are combined.

Trace carriage `dp2_TraceCarriageStatement` and reference-null transfer
`dp2_RestrictCarrierRectifiableStatement` are also used, but are stated with the reference-cover
statements.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- **Factorial moments of the multiplicity.** For every regular
mixed covering of a root and every real `A`, the model-ball growth `μ(P_i) ≤ A R_i^k` gives, for
every integer `p ≥ 1` (repeated indices included),
`∫_{P₀} m^p dμ ≤ p! A (2^k K)^{p-1} Σ_i R_i^k`. Only the model-ball growth and the same-family
local packing (`Σ_{R_j ≤ R_i, P_j ∩ P_i ≠ ∅} R_j^k ≤ 2^k K R_i^k`) are used. -/
def dp2_FactorialMomentStatement : Prop :=
  ∀ (n k : ℕ) (K L A : ℝ) (μ : Measure (Space n)) (a : Space n) (R : ℝ)
    (𝒞 : RegularMixedCovering k K L μ a R),
    (∀ i, μ (𝒞.ball i) ≤ ENNReal.ofReal (A * 𝒞.radius i ^ k)) →
    ∀ p : ℕ, 1 ≤ p →
      ∫⁻ z in Metric.ball a R, (𝒞.multiplicity z : ℝ≥0∞) ^ p ∂μ ≤
        (Nat.factorial p : ℝ≥0∞) * ENNReal.ofReal A * (2 ^ k * ENNReal.ofReal K) ^ (p - 1) *
          ∑' i, ENNReal.ofReal (𝒞.radius i) ^ k

/-- **The exponential tail of the multiplicity.** If `K ≥ 0` and the factorial moments of
`dp2_FactorialMomentStatement` hold for the covering, then for every real
`s > 2^k K` and every level `N`, `e^N(P₀) = μ(P₀ ∩ {m > N}) ≤ e^{-N/s} (μ(P₀) + A S/(s - 2^k K))`.
The relative tail of `exists_root_approximants` uses `s = (2^k + A²) K` with
`S ≤ K R^k ≤ A K μ(P₀)`; the absolute tail uses `s = (2^k + 1) K` with `μ(P₀) ≤ A R^k`; the
bounded-support approximants use the same statement with `S ≤ A K μ(P₀)`. -/
def dp2_ExponentialTailStatement : Prop :=
  ∀ (n k : ℕ) (K L A : ℝ) (μ : Measure (Space n)) (a : Space n) (R : ℝ)
    (𝒞 : RegularMixedCovering k K L μ a R), 0 ≤ K →
    (∀ p : ℕ, 1 ≤ p →
      ∫⁻ z in Metric.ball a R, (𝒞.multiplicity z : ℝ≥0∞) ^ p ∂μ ≤
        (Nat.factorial p : ℝ≥0∞) * ENNReal.ofReal A * (2 ^ k * ENNReal.ofReal K) ^ (p - 1) *
          ∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) →
    ∀ s : ℝ, 2 ^ k * K < s → ∀ N : ℕ,
      𝒞.residual N (Metric.ball a R) ≤
        ENNReal.ofReal (Real.exp (-(N : ℝ) / s)) *
          (μ (Metric.ball a R) +
            ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) /
              ENNReal.ofReal (s - 2 ^ k * K))

/-- **The typed split and the measure identity.** For a covering with `L ≥ 1` (closed carriers) whose traces `P_i ∩ Γ_i` carry `μ⌊P₀`
(the conclusion of `dp2_TraceCarriageStatement`), there are disjoint Borel `F_H, F_V ⊂ P₀` inside the typed traces of
their types, carrying `μ⌊P₀`, with `μ⌊P₀ = μ^N_H + μ^N_V + e^N` at every level `N`. -/
def dp2_TypedSplitStatement : Prop :=
  ∀ (n k : ℕ) (K L : ℝ), 1 ≤ L → ∀ (μ : Measure (Space n)) (a : Space n) (R : ℝ)
    (𝒞 : RegularMixedCovering k K L μ a R),
    μ (Metric.ball a R \ ⋃ i, 𝒞.ball i ∩ (𝒞.reference i).carrier) = 0 →
      ∃ FH FV : Set (Space n), 𝒞.IsTypedTraceSplit FH FV ∧ 𝒞.MeasureIdentity FH FV

/-- **Local absolute continuity.** Upper growth implies absolute continuity: the local upper
growth hypothesis of `exists_root_approximants` gives `μ⌊P₀ ≪ H_P^k`. -/
def dp2_LocalAbsoluteContinuityStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ A L : ℝ, 1 ≤ L →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ (a : Space n) (R : ℝ), 0 < R →
    (∀ b ∈ μ.support ∩ Metric.ball a (2 * L * R), ∀ s : ℝ, 0 < s → s ≤ 2 * L * R →
      μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k)) →
    μ.restrict (Metric.ball a R) ≪ hausdorffP n k

/-- **The limits of the approximants and of the residual.** For a locally finite `μ` whose multiplicity is finite at almost every point of the
root: for every `F ⊆ P₀` the approximants `μ⌊(F ∩ {m ≤ N})` increase and converge on every Borel
set to `μ⌊F`; the residuals `μ⌊(P₀ ∩ {m > N})` decrease and their total mass tends to zero.
No measurability of `F` is needed (with `ν = μ⌊F` and the Borel `H_N = {m ≤ N}`,
`𝒞.approximant F N = ν⌊H_N`). -/
def dp2_ApproximantLimitsStatement : Prop :=
  ∀ (n k : ℕ) (K L : ℝ) (μ : Measure (Space n)) (a : Space n) (R : ℝ)
    (𝒞 : RegularMixedCovering k K L μ a R), IsFiniteMeasureOnCompacts μ →
    (∀ᵐ z ∂μ, z ∈ Metric.ball a R → 𝒞.multiplicity z < ⊤) →
    (∀ F : Set (Space n), F ⊆ Metric.ball a R →
      Monotone (fun N : ℕ => 𝒞.approximant F N) ∧
      ∀ S : Set (Space n), MeasurableSet S →
        Filter.Tendsto (fun N : ℕ => 𝒞.approximant F N S) Filter.atTop
          (nhds (μ.restrict F S))) ∧
    Antitone (fun N : ℕ => 𝒞.residual N) ∧
    Filter.Tendsto (fun N : ℕ => 𝒞.residual N Set.univ) Filter.atTop (nhds 0)

/-- **Canonical identification.** The canonical-decomposition theorem identifies the limits with
the unique horizontal and regular-vertical parts. Given the canonical decomposition of `μ` at
endpoint `1`, a Borel `P` and disjoint Borel `F_H, F_V ⊆ P` carrying `μ⌊P` with `μ⌊F_H`
horizontally and `μ⌊F_V` regularly vertically rectifiable, `μ⌊F_H = μ_H⌊P` and
`μ⌊F_V = μ_V⌊P`, where `μ_T = μ⌊{S^1_{μ,T} < ∞}` (the limits of `HasCanonicalLimits`).

The statement is in implication form over two rectifiability statements: domination by absolute
continuity, and the universe-zero instance of countable sums (sufficient for `Bool`). They are
supplied in `dp2_approximant_canonical_limits` by
`f2i_isRegularlyRectifiableMeasure_of_absolutelyContinuous` and
`f2i_isRegularlyRectifiableMeasure_sum`. -/
def dp2_CanonicalIdentificationStatement : Prop :=
  (∀ {n k : ℕ} (T : FamilyKind) {μ ν : Measure (Space n)},
    IsRegularlyRectifiableMeasure T k μ →
    ν ≪ μ →
    IsRegularlyRectifiableMeasure T k ν) →
  (∀ {n k : ℕ} {ι : Type} [Countable ι]
    (T : FamilyKind) (ν : ι → Measure (Space n)),
    (∀ i, ν i ≠ 0 →
      IsRegularlyRectifiableMeasure T k (ν i)) →
    IsRegularlyRectifiableMeasure T k (Measure.sum ν)) →
  ∀ (n k : ℕ) (μ : Measure (Space n)),
    IntegralCanonical.IsCanonicalDecomposition k μ 1 →
  ∀ P FH FV : Set (Space n),
    MeasurableSet P → MeasurableSet FH → MeasurableSet FV →
    Disjoint FH FV → FH ⊆ P → FV ⊆ P →
    μ (P \ (FH ∪ FV)) = 0 →
    IsRegularlyRectifiableMeasure .horizontal k (μ.restrict FH) →
    IsRegularlyRectifiableMeasure .vertical k (μ.restrict FV) →
      μ.restrict FH =
        (μ.restrict {z | squareEnergy μ k .horizontal 1 z < ⊤}).restrict P ∧
      μ.restrict FV =
        (μ.restrict {z | squareEnergy μ k .vertical 1 z < ⊤}).restrict P

end ParabolicRectifiability.QuantitativeCharacterization
