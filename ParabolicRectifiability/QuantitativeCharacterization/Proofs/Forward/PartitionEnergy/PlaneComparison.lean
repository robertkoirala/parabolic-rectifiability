import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy
import ParabolicRectifiability.Measure.Neck.PlaneTime.PlaneComparison

/-! # Same-source plane comparison

Proof of `d1a_planeComparison_proof : CovarianceLowerStatement → PlaneComparisonStatement`,
in implication form: `CovarianceLowerStatement` enters as a hypothesis.

Route. Take the constants `a₀, e₀` of the covariance statement
and `C = 36 / a₀`. The measure `ν = μ⌞P(g, r)` is finite by upper ADR at the support point `g`
and agrees with `μ` on `P(g, r)`, so the covariance statement gives the continuation test
`hcont` of the base `ms3_core_comparison` (all ranks, vertical rank zero included). If both
fitting integrals `J₁, J₂` are finite, put `b_i = J_i / r^{k+2}`; the base theorem gives
`d_{x_g, r}(L₁, L₂)² ≤ 36/a₀ (b₁ + b₂)` (`planeComparison` is `affineComparison` by definition).
Otherwise the right side is `∞`.

Helpers carry the prefix `d1acmp_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

/-- The localized source `μ⌞P(g, r)` is finite under local ADR at a support point `g` with
`P(g, r)` inside the buffer and `r ≤ ρ`. -/
theorem d1acmp_restrict_finite {n k : ℕ} {μ : Measure (Space n)} {A : ℝ} {a : Space n} {ρ : ℝ}
    (hADR : LocalADR μ k A a ρ) {g : Space n} (hg : g ∈ μ.support) {r : ℝ} (hr : 0 < r)
    (hga : g ∈ Metric.ball a ρ) (hrρ : r ≤ ρ) :
    IsFiniteMeasure (μ.restrict (Metric.ball g r)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact ((hADR g ⟨hg, hga⟩ r hr hrρ).2).trans_lt ENNReal.ofReal_lt_top

/-- The localized source agrees with `μ` on the test ball. -/
theorem d1acmp_restrict_restrict {n : ℕ} (μ : Measure (Space n)) (g : Space n) (r : ℝ) :
    (μ.restrict (Metric.ball g r)).restrict (Metric.ball g r) = μ.restrict (Metric.ball g r) := by
  rw [Measure.restrict_restrict measurableSet_ball, Set.inter_self]

/-- **Extended-real form of the base comparison.** Under the continuation test at `(g, r)` with
constant `a₀` for a finite `ν`, two planes fitted against measures dominating `ν⌞P(g, r)`
satisfy `d_{x_g, r}(L₁, L₂)² ≤ (36/a₀) r^{-(k+2)} (J₁ + J₂)` in `ℝ≥0∞` (infinite `J_i`
allowed). -/
theorem d1acmp_compare {n k : ℕ} {T : NeckType} (hT : T.Available n k)
    (ν : Measure (Space n)) [IsFiniteMeasure ν] (g : Space n) {r a₀ : ℝ} (hr : 0 < r)
    (ha₀ : 0 < a₀)
    (hcont : (0 < T.rank k ∧ ∃ h : 0 < r,
        a₀ * r ^ (k + 2) ≤ (SpatialSource.ofBall ν g r h).rankEigenvalue (T.rank k)) ∨
      (T.rank k = 0 ∧ ENNReal.ofReal (a₀ * r ^ 2) ≤ ν (Metric.ball g r)))
    (L₁ L₂ : AffineSpatialPlane n (T.rank k)) (μ₁ μ₂ : Measure (Space n))
    (h₁ : ν.restrict (Metric.ball g r) ≤ μ₁) (h₂ : ν.restrict (Metric.ball g r) ≤ μ₂) :
    ENNReal.ofReal (planeComparison g.1 r L₁ L₂ ^ 2) ≤
      ENNReal.ofReal (36 / a₀ / r ^ (k + 2)) *
        (spatialFittingIntegral μ₁ L₁ + spatialFittingIntegral μ₂ L₂) := by
  set J₁ := spatialFittingIntegral μ₁ L₁ with hJ₁
  set J₂ := spatialFittingIntegral μ₂ L₂ with hJ₂
  have hR : 0 < r ^ (k + 2) := pow_pos hr _
  have hCpos : 0 < 36 / a₀ / r ^ (k + 2) := by positivity
  have hCne : ENNReal.ofReal (36 / a₀ / r ^ (k + 2)) ≠ 0 := (ENNReal.ofReal_pos.2 hCpos).ne'
  by_cases hinf₁ : J₁ = ⊤
  · rw [hinf₁, top_add, ENNReal.mul_top hCne]
    exact le_top
  by_cases hinf₂ : J₂ = ⊤
  · rw [hinf₂, add_top, ENNReal.mul_top hCne]
    exact le_top
  have hfit : ∀ J : ℝ≥0∞, J ≠ ⊤ →
      J ≤ ENNReal.ofReal (r ^ (k + 2) * (J.toReal / r ^ (k + 2))) := by
    intro J hJ
    have hRne : r ^ (k + 2) ≠ 0 := hR.ne'
    have h : r ^ (k + 2) * (J.toReal / r ^ (k + 2)) = J.toReal := by
      field_simp
    rw [h, ENNReal.ofReal_toReal hJ]
  have hcore := ms3_core_comparison hT ν g hr ha₀ hcont L₁ L₂ μ₁ μ₂ h₁ h₂
    (div_nonneg ENNReal.toReal_nonneg hR.le) (div_nonneg ENNReal.toReal_nonneg hR.le)
    (hfit J₁ hinf₁) (hfit J₂ hinf₂)
  rw [← ms3_planeComparison_eq] at hcore
  have heq : 36 / a₀ * (J₁.toReal / r ^ (k + 2) + J₂.toReal / r ^ (k + 2)) =
      36 / a₀ / r ^ (k + 2) * (J₁.toReal + J₂.toReal) := by
    ring
  rw [heq] at hcore
  calc ENNReal.ofReal (planeComparison g.1 r L₁ L₂ ^ 2)
      ≤ ENNReal.ofReal (36 / a₀ / r ^ (k + 2) * (J₁.toReal + J₂.toReal)) :=
        ENNReal.ofReal_le_ofReal hcore
    _ = ENNReal.ofReal (36 / a₀ / r ^ (k + 2)) * (J₁ + J₂) := by
        rw [ENNReal.ofReal_mul hCpos.le, ENNReal.ofReal_add ENNReal.toReal_nonneg
          ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hinf₁, ENNReal.ofReal_toReal hinf₂]

/-- **Same-source plane comparison**
(`CovarianceLowerStatement → PlaneComparisonStatement`); `C = 36 / a₀` and the
same `e₀` as the covariance statement. -/
theorem d1a_planeComparison_proof : CovarianceLowerStatement → PlaneComparisonStatement := by
  intro hCov n hn k hk hkn A hA
  obtain ⟨a₀, ha₀, e₀, he₀, hcov⟩ := hCov n hn k hk hkn A hA
  refine ⟨36 / a₀, by positivity, e₀, he₀, ?_⟩
  intro T hT μ a ρ hADR g hg r hr hball h4 hhor L₁ L₂ μ₁ μ₂ h₁ h₂
  have hga : g ∈ Metric.ball a ρ := hball (Metric.mem_ball_self (by linarith))
  have : IsFiniteMeasure (μ.restrict (Metric.ball g r)) :=
    d1acmp_restrict_finite hADR hg hr hga (by linarith)
  have hν := d1acmp_restrict_restrict μ g r
  have hcont := hcov T hT μ a ρ hADR g hg r hr hball h4 hhor (μ.restrict (Metric.ball g r)) hν
  exact d1acmp_compare hT (μ.restrict (Metric.ball g r)) g hr ha₀ hcont L₁ L₂ μ₁ μ₂
    (hν.le.trans h₁) (hν.le.trans h₂)

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
