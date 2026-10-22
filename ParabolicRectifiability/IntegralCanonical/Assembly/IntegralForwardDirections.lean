import ParabolicRectifiability.IntegralCanonical.Defs
import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.IntegralTestsFromFiniteEnergy

/-! # The exact integral tests: forward directions

The substantial (construction or limit) halves of the integral tests of
`IntegralEquivalencesStatement`, and through it of `IntegralCriterionStatement`. None assumes
its own conclusion, a conclusion of those statements, or any density, packing, content or
regularity hypothesis.

**Endpoint convention.** Each statement is made at an arbitrary positive finite endpoint `R`
of `S = S^R_{μ,T}`, not only at `R = 1`: any fixed positive finite endpoint may replace `1`,
because the proofs use only finite annuli (the tail alternative splits at `ρ` inside
`(0,R)`). The endpoint-general equivalences are then assembled in `integralEquivalences_at`;
the case `R = 1` is `IntegralEquivalencesStatement` and the general case feeds the criterion.

The elementary converse halves (a finite integral of a function that is infinite on
`{S = ∞}` makes that set null), the cylinder detection and the reduced testing on `P(0,j)`
are proved in `integralEquivalences_at`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

/-- **Capped-tail and capped-value limits.** For `n ≥ 1`, `1 ≤ k ≤ n+2`, a locally Radon `μ`, an available family `T`,
an endpoint `R > 0` and a bounded Borel `A`,
* `lim_{ρ↓0} ∫_A min{1, S^ρ_{μ,T}} dμ = μ(A ∩ {S^R_{μ,T} = ∞})`, and
* `lim_{L→∞} L^{-1} ∫_A min{S^R_{μ,T}, L} dμ = μ(A ∩ {S^R_{μ,T} = ∞})`.
The proof: finite annuli give the pointwise dichotomy (`S^ρ ↓ 0` where `S^R < ∞`, and
`S^ρ = ∞` for every `ρ > 0` where `S^R = ∞`); dominated convergence on `A`, which has finite
mass, along integer sequences, and monotone bracketing for real parameters.

Used in `integralEquivalences_at` (tests (1) and (2)). -/
theorem tendsto_cappedTail_cappedValue_measure_infinite :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ R : ℝ, 0 < R →
    ∀ A : Set (Space n), MeasurableSet A → Bornology.IsBounded A →
      Tendsto (fun ρ : ℝ => ∫⁻ z in A, min 1 (squareEnergy μ k T ρ z) ∂μ) (𝓝[>] 0)
          (𝓝 (μ (A ∩ {z | squareEnergy μ k T R z = ⊤}))) ∧
        Tendsto (fun L : ℝ =>
            (ENNReal.ofReal L)⁻¹ *
              ∫⁻ z in A, min (squareEnergy μ k T R z) (ENNReal.ofReal L) ∂μ)
          atTop (𝓝 (μ (A ∩ {z | squareEnergy μ k T R z = ⊤}))) := by
  exact ParabolicRectifiability.IntegralCanonical.i2_tendsto_cappedTail_cappedValue_measure_infinite

/-- **Compact exhaustion** (test (3), forward direction). For `n ≥ 1`, `1 ≤ k ≤ n+2`, a locally Radon `μ`, an available family `T` and
an endpoint `R > 0`: if `S^R_{μ,T} < ∞` `μ`-almost everywhere, there are increasing compact
`K_j` with `μ(X \ ⋃_j K_j) = 0` and `∫_{K_j} S^R_{μ,T} dμ < ∞` for every `j`
(`CompactExhaustionTest`). The energy source stays the original `μ`; only the testing
points are restricted. The proof: finite energy levels on `P(0,j)` by continuity from below,
compact inner approximation (Radon inner regularity), finite unions, and continuity from
above inside each `P(0,N)`.

Used in `integralEquivalences_at`. -/
theorem compactExhaustionTest_of_ae_lt_top :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ R : ℝ, 0 < R →
      (∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) → CompactExhaustionTest μ k T R := by
  exact ParabolicRectifiability.IntegralCanonical.i2_compactExhaustionTest_of_ae_lt_top

/-- **Positive weight** (test (4), forward direction). For `n ≥ 1`, `1 ≤ k ≤ n+2`, a locally Radon `μ`, an available family `T` and
an endpoint `R > 0`: if `S^R_{μ,T} < ∞` `μ`-almost everywhere, there is one Borel
`w : X → (0,1]`, strictly positive at every point, with `∫_A w S^R_{μ,T} dμ < ∞` for every
bounded Borel set `A` (`PositiveWeightTest` on the bounded Borel sets; every bounded cylinder
is such a set). The proof: `w = (1 + S)^{-1}` on `{S < ∞}` and `w = 1` elsewhere, so
`w S ≤ 1` off a null set and the integral is at most `μ(A) < ∞`.

Used in `integralEquivalences_at`. -/
theorem positiveWeightTest_of_ae_lt_top :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ R : ℝ, 0 < R →
      (∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) →
        PositiveWeightTest μ k T R {A | MeasurableSet A ∧ Bornology.IsBounded A} := by
  exact ParabolicRectifiability.IntegralCanonical.i2_positiveWeightTest_of_ae_lt_top

/-- **Adaptive gauge** (test (5), forward direction). For `n ≥ 1`, `1 ≤ k ≤ n+2`, a locally Radon `μ`, an available family `T` and
an endpoint `R > 0`: if `S^R_{μ,T} < ∞` `μ`-almost everywhere, then for every bounded Borel
`A` there is an admissible gauge `Φ_A` (continuous, nondecreasing, concave, unbounded on
`[0,∞)`, `Φ_A(0) = 0`, extended by `Φ_A(∞) = ∞`) with `∫_A Φ_A(S^R_{μ,T}) dμ < ∞`
(`AdaptiveGaugeTest` on the bounded Borel sets). The gauge may depend on `μ` and `A`. The
proof: `Φ_A(u) = Σ_j min{1, u/t_j}` with `t_j ≥ 2 t_{j-1}`, `t_{j-1}/t_j ≤ 2^{-j}` and
`μ(A ∩ {S > t_j}) ≤ 2^{-j}`; uniform convergence on every bounded interval `[0, M]` (the tail
after `N` terms is at most `M Σ_{j>N} t_j^{-1} → 0`), concavity of the finite
pointwise limit, unboundedness (`Φ_A(t_N) ≥ N`), and Tonelli with two geometric series. The
convergence is not uniform on all of `[0,∞)`: the partial sums are bounded and the limit is
not.

Used in `integralEquivalences_at`. -/
theorem adaptiveGaugeTest_of_ae_lt_top :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ R : ℝ, 0 < R →
      (∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) →
        AdaptiveGaugeTest μ k T R {A | MeasurableSet A ∧ Bornology.IsBounded A} := by
  exact ParabolicRectifiability.IntegralCanonical.i2_adaptiveGaugeTest_of_ae_lt_top

end ParabolicRectifiability.IntegralCanonical
