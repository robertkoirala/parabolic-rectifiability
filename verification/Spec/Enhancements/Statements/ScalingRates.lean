import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Analysis.HalfTimeDerivative.LocalRepresentation
import Spec.Analysis.ParabolicBMO
import Spec.Basic
import Spec.Enhancements.Decomposition
import Spec.Foundations.Density
import Spec.Foundations.GraphDomainCover
import Spec.Foundations.Graphs
import Spec.Foundations.HalfTimeDerivative
import Spec.Foundations.SupportBounds
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.Graphs
import Spec.Geometry.ModelDistance
import Spec.Geometry.SubspaceCoordinates
import Spec.Measure.Beta
import Spec.Measure.BetaLaws
import Spec.Measure.CountableFitting
import Spec.Measure.ScaleEnergy
import Spec.Metric.Hausdorff
import Spec.Metric.Measure
import Spec.Metric.Similarity
import Spec.Metric.Space
import Spec.Specifications.Rectifiability

/-! Specification: the definitions of `ParabolicRectifiability.Enhancements.Statements.ScalingRates` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Enhancements
open ParabolicRectifiability.Foundations
/-- The scaling identities of the scaled rectifiable Reifenberg theorem: for `n ≥ 1`, `1 ≤ k ≤ n+2`,
locally Radon `μ`, `a ∈ X`, `R > 0`, `F(y) = a + δ_R y`, `ν = R^{-k}(F^{-1})_# μ` and
the mixed family or an available fixed family `T`,
`β²_{ν,T}(y,s) = β²_{μ,T}(F y, R s)` for every `y` and radius `s > 0`, and
`S²_{ν,T}(y) = S^{2R}_{μ,T}(F y)` for every `y`. -/
def ScalingIdentitiesStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ (a : Space n) (R : ℝ) (hR : 0 < R),
  ∀ T : FamilyKind, Nonempty (Models n k T) →
    (∀ (y : Space n) (s : ℝ), 0 < s →
      betaSq (rescaledSource μ k a R hR) k T y s =
        betaSq μ k T ((similarity a R hR).symm y) (R * s)) ∧
    (∀ y : Space n,
      squareEnergy (rescaledSource μ k a R hR) k T 2 y =
        squareEnergy μ k T (2 * R) ((similarity a R hR).symm y))

/-- The scaled threshold decomposition with constant `C` in dimension `n`: for `1 ≤ k ≤ n+2`, locally Radon `μ`, `a ∈ X`,
`R > 0`, the mixed family or an available fixed family `T`, and real `M, Γ ≥ 0` with
`μ(P(a,R) ∩ {S^{2R}_{μ,T} > M}) ≤ Γ`, there are retained sets `E_H, E_V` forming the
enhanced restriction decomposition on `P(a,R)` with constant `C`
(`IsLocalEnhancedDecomposition`: all support conclusions at scale `R`, every-tolerance
covers, graph-domain covers for every tolerance and absolute mesh with global charge
`≤ C R^k` and local charge `≤ C s^k` for `0 < s ≤ R`, only the type `T` for a fixed
family) and loss `μ⁺(P(a,R)) ≤ C M R^k + Γ`.

This is a helper proposition, parameterized by the constant; the theorem statements are
the `…Statement` definitions below. -/
def ScaledThresholdProperty (n : ℕ) (C : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ (a : Space n) (R : ℝ), 0 < R →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
    μ (Metric.ball a R ∩ {z | ENNReal.ofReal M < squareEnergy μ k T (2 * R) z}) ≤
      ENNReal.ofReal Γ →
    ∃ EH EV : Set (Space n), IsLocalEnhancedDecomposition k T C a R μ EH EV ∧
      μ.restrict (EH ∪ EV)ᶜ (Metric.ball a R) ≤ ENNReal.ofReal (C * M * R ^ k + Γ)

/-- **Full scaling contract**: the scaling identities,
and, for each `n ≥ 1`, one constant `C > 0` (chosen before `k`, `μ`, `a`, `R`, `T`, `M`,
`Γ`, every tolerance and every mesh) for the scaled threshold decomposition. -/
def ScaledRectifiableReifenbergStatement : Prop :=
  ScalingIdentitiesStatement ∧
    ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧ ScaledThresholdProperty n C

/-- The power-energy rate with core constant `C₀`:

* for `1 ≤ k ≤ n+2`, locally Radon `μ`, `a ∈ X`, `R > 0`, the mixed family or an
  available fixed family `T` (the available fixed-family version with its own energy),
  and a real power `q > 0` with
  `Λ_q = ∫_{P(a,R)} (S^{2R}_{μ,T})^q dμ < ∞`: one decomposition with every conclusion
  of the scaled lemma (constant `C₀`) and
  `μ⁺(P(a,R)) ≤ (C₀ + 1) R^{kq/(q+1)} Λ_q^{1/(q+1)}`, whose remainder is zero on
  `P(a,R)` when `Λ_q = 0`;
* at `k = n+2`, with no energy assumption, a decomposition with every conclusion of the
  scaled lemma and `μ⁺(P(a,R)) = 0`.

The rate is written with real powers of `R` and of `Λ_q.toReal` (finite by hypothesis). -/
def PowerRateProperty (n : ℕ) (C₀ : ℝ) : Prop :=
  (∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ (a : Space n) (R : ℝ), 0 < R →
    ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ q : ℝ, 0 < q →
      powerEnergy μ k T q a R < ⊤ →
      ∃ EH EV : Set (Space n), IsLocalEnhancedDecomposition k T C₀ a R μ EH EV ∧
        μ.restrict (EH ∪ EV)ᶜ (Metric.ball a R) ≤
          ENNReal.ofReal ((C₀ + 1) * R ^ ((k : ℝ) * q / (q + 1)) *
            (powerEnergy μ k T q a R).toReal ^ (1 / (q + 1))) ∧
        (powerEnergy μ k T q a R = 0 → μ.restrict (EH ∪ EV)ᶜ (Metric.ball a R) = 0)) ∧
  (∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ (a : Space n) (R : ℝ), 0 < R →
      ∃ EH EV : Set (Space n), IsLocalEnhancedDecomposition (n + 2) .mixed C₀ a R μ EH EV ∧
        μ.restrict (EH ∪ EV)ᶜ (Metric.ball a R) = 0)

/-- **Power-energy rate, including zero energy.**

Here `C₀` is the unchanged core threshold constant, independent of `q`:
for each `n ≥ 1` there is one `C₀ > 0`, chosen before `k`, `μ`, `a`,
`R`, `T` and `q`, for which the scaled threshold decomposition holds
with constant `C₀` and the power rate holds with loss constant `C₀ + 1` and all support
and graph-domain constants `C₀`. -/
def PowerRateStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C₀ : ℝ, 0 < C₀ ∧
    ScaledThresholdProperty n C₀ ∧ PowerRateProperty n C₀

/-- The gauge rate with core constant `C₀`: for `1 ≤ k ≤ n+2`, locally Radon `μ`, `a ∈ X`,
`R > 0`, and a gauge `Φ : [0,∞] → [0,∞]` that is nondecreasing, Borel and finite on finite
inputs, with `Λ_Φ = ∫_{P(a,R)} Φ(S^{2R}_{μ,A_k}) dμ < ∞`:

* for every real `M > 0` with `Φ(M) > 0`, a decomposition with every support and domain
  conclusion of the scaled lemma (mixed family, constant `C₀`) and
  `μ⁺(P(a,R)) ≤ C₀ M R^k + Λ_Φ / Φ(M)`;
* if some real `M > 0` has `Φ(M) > 0`, then for every `η > 0` a decomposition with the
  same conclusions and
  `μ⁺(P(a,R)) ≤ inf_{M > 0, Φ(M) > 0} (C₀ M R^k + Λ_Φ / Φ(M)) + η`.

The quotient `Λ_Φ / Φ(M)` is the `ℝ≥0∞` quotient by a finite positive number. The
infimum is the `ℝ≥0∞` infimum over the admissible thresholds; on the nonempty admissible
set every cost is finite, so it agrees with the real infimum. The decomposition may depend
on `M` or `η`; attainment is not asserted. -/
def GaugeRateProperty (n : ℕ) (C₀ : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ (a : Space n) (R : ℝ), 0 < R →
  ∀ Φ : ℝ≥0∞ → ℝ≥0∞, Monotone Φ → Measurable Φ → (∀ x : ℝ≥0∞, x ≠ ⊤ → Φ x ≠ ⊤) →
    gaugeEnergy Φ μ k .mixed a R < ⊤ →
    (∀ M : ℝ, 0 < M → 0 < Φ (ENNReal.ofReal M) →
      ∃ EH EV : Set (Space n), IsLocalEnhancedDecomposition k .mixed C₀ a R μ EH EV ∧
        μ.restrict (EH ∪ EV)ᶜ (Metric.ball a R) ≤
          ENNReal.ofReal (C₀ * M * R ^ k) +
            gaugeEnergy Φ μ k .mixed a R / Φ (ENNReal.ofReal M)) ∧
    ((∃ M : ℝ, 0 < M ∧ 0 < Φ (ENNReal.ofReal M)) →
      ∀ η : ℝ, 0 < η →
      ∃ EH EV : Set (Space n), IsLocalEnhancedDecomposition k .mixed C₀ a R μ EH EV ∧
        μ.restrict (EH ∪ EV)ᶜ (Metric.ball a R) ≤
          (⨅ (M : ℝ) (_ : 0 < M) (_ : 0 < Φ (ENNReal.ofReal M)),
              ENNReal.ofReal (C₀ * M * R ^ k) +
                gaugeEnergy Φ μ k .mixed a R / Φ (ENNReal.ofReal M)) +
            ENNReal.ofReal η)

/-- **Gauge rate and an approximated numerical infimum.** As for the power rate,
`C₀` is one constant per `n` for which the scaled threshold decomposition holds, chosen
before `k`, `μ`, `a`, `R`, `Φ`, `M` and `η`. -/
def GaugeRateStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C₀ : ℝ, 0 < C₀ ∧
    ScaledThresholdProperty n C₀ ∧ GaugeRateProperty n C₀

end ParabolicRectifiability.Enhancements
