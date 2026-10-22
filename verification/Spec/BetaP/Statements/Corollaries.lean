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
import Spec.BetaP.Statements.Main
import Spec.Foundations.BetaPow
import Spec.Foundations.Density
import Spec.Foundations.DensityConditions
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
import Spec.Measure.CountableFitting
import Spec.Measure.ScaleEnergy
import Spec.Metric.Hausdorff
import Spec.Metric.Measure
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.BetaP.Statements.Corollaries` used by the headline statements. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace ParabolicRectifiability.BetaP
open ParabolicRectifiability.Foundations
/-- The graph-domain conclusions of the enhancement for the
supports `(K_H, K_V)` at parent radius `R`, with constant `C`: for every tolerance `ε > 0` and
absolute mesh `δ > 0` there is one graph-domain cover with bound `C`, tolerance `ε` and mesh `δ`
(trace estimate and relative global/local bounds, for the union and each
typed subfamily) whose costs also satisfy the absolute bounds
`Σ_α c_α ≤ C R^k` and `Σ_{z_α ∈ P(q,s), ρ_α ≤ s} c_α ≤ C s^k` for every centre `q` and
`0 < s ≤ R`, for the whole family and for each typed subfamily. At `R = 1` these are the bounds
`C` and `C s^k` (`0 < s ≤ 1`); at a parent radius `R₀` they are
`C R₀^k` and `C s^k`. -/
def HasGraphDomainCostBounds {n : ℕ} (k : ℕ) (C R : ℝ) (KH KV : Set (Space n)) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ D : GraphDomainCover n k C ε δ KH KV,
    D.horizontal.totalCharge + D.vertical.totalCharge ≤ ENNReal.ofReal (C * R ^ k) ∧
    D.horizontal.totalCharge ≤ ENNReal.ofReal (C * R ^ k) ∧
    D.vertical.totalCharge ≤ ENNReal.ofReal (C * R ^ k) ∧
    ∀ (q : Space n) (s : ℝ), 0 < s → s ≤ R →
      D.horizontal.localCharge q s + D.vertical.localCharge q s ≤ ENNReal.ofReal (C * s ^ k) ∧
      D.horizontal.localCharge q s ≤ ENNReal.ofReal (C * s ^ k) ∧
      D.vertical.localCharge q s ≤ ENNReal.ofReal (C * s ^ k)

/-- **Graph-domain enhancement of the support theorem.**

Same quantifiers and hypotheses as `BetaPSupportStatement`, with one constant `C = C(n,p)`. Every
decomposition produced (unit, localized and ambient clauses, zero threshold included since
`M ≥ 0`) satisfies all conclusions of the support theorem and, for its own supports
`K_H = supp μ_H`, `K_V = supp μ_V`, the graph-domain conclusions `HasGraphDomainCostBounds` at the
parent radius (`1` in the unit and ambient clauses, `R₀` in the localized clause). The measures
and supports are chosen before `ε` and `δ`. -/
def BetaPGraphEnhancementStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      (∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
        (2 ≤ p →
          μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyS μ k T p 2 z}) ≤
            ENNReal.ofReal Γ →
          ∃ μplus μH μV : Measure (Space n),
            IsBetaPDecomposition k T C (point 0 0) 1 (C * M ^ (p / 2) + Γ) μ μplus μH μV ∧
              HasGraphDomainCostBounds k C 1 μH.support μV.support) ∧
        (p ≤ 2 →
          μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyT μ k T p 2 z}) ≤
            ENNReal.ofReal Γ →
          ∃ μplus μH μV : Measure (Space n),
            IsBetaPDecomposition k T C (point 0 0) 1 (C * M + Γ) μ μplus μH μV ∧
              HasGraphDomainCostBounds k C 1 μH.support μV.support)) ∧
      (∀ (q : Space n) (R₀ : ℝ), 0 < R₀ → ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
        (2 ≤ p →
          μ (Metric.ball q R₀ ∩ {z | ENNReal.ofReal M < energyS μ k T p (2 * R₀) z}) ≤
            ENNReal.ofReal Γ →
          ∃ μplus μH μV : Measure (Space n),
            IsBetaPDecomposition k T C q R₀ (C * M ^ (p / 2) * R₀ ^ k + Γ) μ μplus μH μV ∧
              HasGraphDomainCostBounds k C R₀ μH.support μV.support) ∧
        (p ≤ 2 →
          μ (Metric.ball q R₀ ∩ {z | ENNReal.ofReal M < energyT μ k T p (2 * R₀) z}) ≤
            ENNReal.ofReal Γ →
          ∃ μplus μH μV : Measure (Space n),
            IsBetaPDecomposition k T C q R₀ (C * M * R₀ ^ k + Γ) μ μplus μH μV ∧
              HasGraphDomainCostBounds k C R₀ μH.support μV.support)) ∧
      (k = n + 2 →
        ∃ μplus μH μV : Measure (Space n),
          IsBetaPDecomposition k T C (point 0 0) 1 0 μ μplus μH μV ∧
            HasGraphDomainCostBounds k C 1 μH.support μV.support)

/-- The integrated quadratic beta-`p` energy `ℰ_{p,q,R} = ∫_{P(q,R)} S_{p,μ,T}^{2R} dμ`,
in `ℝ≥0∞`. -/
def integratedEnergyS {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (p : ℝ)
    (q : Space n) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Metric.ball q R, energyS μ k T p (2 * R) z ∂μ

/-- The integrated `p`-power beta-`p` energy `𝒯_{p,q,R} = ∫_{P(q,R)} T_{p,μ,T}^{2R} dμ`,
in `ℝ≥0∞`. -/
def integratedEnergyT {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (p : ℝ)
    (q : Space n) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Metric.ball q R, energyT μ k T p (2 * R) z ∂μ

/-- **Integrated rates.** For `n ≥ 1` and `0 < p < ∞` there is `C = C(n,p) > 0` such that for
`1 ≤ k ≤ n+2`, every mixed or available fixed family, every locally Radon `μ`, every centre `q` and
radius `R > 0`:
* if `2 ≤ p` and `ℰ_{p,q,R} < ∞`, there is a decomposition with every support conclusion of the
  support theorem at `(q,R)` and every graph-domain conclusion at parent radius `R`, with remainder
  `μ⁺(P(q,R)) ≤ C R^{2k/(p+2)} ℰ_{p,q,R}^{p/(p+2)}`;
* if `p ≤ 2` and `𝒯_{p,q,R} < ∞`, the same with remainder `C R^{k/2} 𝒯_{p,q,R}^{1/2}`.
The finite energies enter through `toReal`; the powers are real powers with positive exponents,
so zero energy gives zero local remainder. -/
def BetaPIntegratedRateStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ (q : Space n) (R : ℝ), 0 < R →
      (2 ≤ p → integratedEnergyS μ k T p q R < ⊤ →
        ∃ μplus μH μV : Measure (Space n),
          IsBetaPDecomposition k T C q R
              (C * R ^ (2 * (k : ℝ) / (p + 2)) *
                (integratedEnergyS μ k T p q R).toReal ^ (p / (p + 2))) μ μplus μH μV ∧
            HasGraphDomainCostBounds k C R μH.support μV.support) ∧
      (p ≤ 2 → integratedEnergyT μ k T p q R < ⊤ →
        ∃ μplus μH μV : Measure (Space n),
          IsBetaPDecomposition k T C q R
              (C * R ^ ((k : ℝ) / 2) * (integratedEnergyT μ k T p q R).toReal ^ (1 / 2 : ℝ))
              μ μplus μH μV ∧
            HasGraphDomainCostBounds k C R μH.support μV.support)

/-- **Sharp amplitude powers.** Formulated as a negative statement
about the diffuse witness `ω = L^{n+1}⌊P(0,1/4)` (`parabolicVolume n` restricted to the open ball
`P(0,1/4)`) and its amplitudes `μ_c = c ω`, `c > 0`, at the unit parent `P(0,1)` (endpoint `2`).

For `n ≥ 1`, `1 ≤ k < n+2` and every available family `T`:
* for `2 ≤ p` and every real `C`, `θ` with `θ ≠ p/(p+2)`, it is not the case that every amplitude
  `μ_c` admits a decomposition `μ_c = μ⁺ + μ_G` whose good part is carried by a countable union of
  sets of finite `H_P^k` measure and whose remainder satisfies `μ⁺(P(0,1)) ≤ C ℰ_p(μ_c)^θ`;
* for `0 < p ≤ 2` the same with `𝒯_p` and `θ ≠ 1/2`.

The admissible decompositions are deliberately the weakest form (no compactness, no covers, no
quantitative support bounds, one good measure with a sigma-finite `H_P^k` carrier), so the
negation is the strongest form of "the powers are forced for uniform pure-power bounds over all
source amplitudes". No optimal numerical constant is claimed. -/
def BetaPIntegratedSharpnessStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
    (∀ p : ℝ, 2 ≤ p → ∀ C θ : ℝ, θ ≠ p / (p + 2) →
      ¬ ∀ c : ℝ, 0 < c →
        ∃ (μplus μG : Measure (Space n)) (F : ℕ → Set (Space n)),
          ENNReal.ofReal c • (parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4)) =
              μplus + μG ∧
            (∀ i, hausdorffP n k (F i) < ⊤) ∧ μG (⋃ i, F i)ᶜ = 0 ∧
            μplus (Metric.ball (point 0 0) 1) ≤ ENNReal.ofReal (C *
              (integratedEnergyS (ENNReal.ofReal c •
                (parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))) k T p
                  (point 0 0) 1).toReal ^ θ)) ∧
    (∀ p : ℝ, 0 < p → p ≤ 2 → ∀ C θ : ℝ, θ ≠ 1 / 2 →
      ¬ ∀ c : ℝ, 0 < c →
        ∃ (μplus μG : Measure (Space n)) (F : ℕ → Set (Space n)),
          ENNReal.ofReal c • (parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4)) =
              μplus + μG ∧
            (∀ i, hausdorffP n k (F i) < ⊤) ∧ μG (⋃ i, F i)ᶜ = 0 ∧
            μplus (Metric.ball (point 0 0) 1) ≤ ENNReal.ofReal (C *
              (integratedEnergyT (ENNReal.ofReal c •
                (parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))) k T p
                  (point 0 0) 1).toReal ^ θ))

/-- Mixed regular measure rectifiability together with measure covers of every prescribed positive
slope or regular norm: the conclusion of every sufficiency
entry. The hypothesis of every necessity entry is the weaker `IsRegularlyRectifiableMeasure`. -/
def IsRegularlyRectifiableWithCovers {n : ℕ} (k : ℕ) (μ : Measure (Space n)) : Prop :=
  IsRegularlyRectifiableMeasure .mixed k μ ∧ ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover .mixed k μ ε

/-- Table row `S_p^a`, `0 < p < 2`, "necessary: yes". For `k < n+2`, under the density hypothesis, mixed
regular measure rectifiability implies `S_{p,μ}^a < ∞` `μ`-a.e. (mixed family, full source). -/
def SpBelowTwoNecessaryStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 →
  ∀ p : ℝ, 0 < p → p < 2 → ∀ a : ℝ, 0 < a →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    HasPositiveFiniteUpperDensity k μ → IsRegularlyRectifiableMeasure .mixed k μ →
      ∀ᵐ z ∂μ, energyS μ k .mixed p a z < ⊤

/-- Table row `S_p^a`, `0 < p < 2`, "sufficient: no, `n = 2`, `k = 1`". For each such `p` and
endpoint `a > 0` there is a locally Radon source on `ℝ² × ℝ` with the density hypothesis at
`k = 1` and `S_{p,μ}^a < ∞` `μ`-a.e., which is not regularly `1`-rectifiable. -/
def SpBelowTwoNotSufficientStatement : Prop :=
  ∀ p : ℝ, 0 < p → p < 2 → ∀ a : ℝ, 0 < a →
    ∃ μ : Measure (Space 2), IsFiniteMeasureOnCompacts μ ∧ μ.InnerRegular ∧
      HasPositiveFiniteUpperDensity 1 μ ∧ (∀ᵐ z ∂μ, energyS μ 1 .mixed p a z < ⊤) ∧
      ¬ IsRegularlyRectifiableMeasure .mixed 1 μ

/-- Table row `S_2^a = T_2^a`, "sufficient: yes". For `k < n+2`, under the density hypothesis, finiteness
`μ`-a.e. of `S_{2,μ}^a`, and likewise of `T_{2,μ}^a`, implies mixed regular measure
rectifiability with covers of every positive norm. -/
def SquareSufficientStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ a : ℝ, 0 < a →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    HasPositiveFiniteUpperDensity k μ →
      ((∀ᵐ z ∂μ, energyS μ k .mixed 2 a z < ⊤) → IsRegularlyRectifiableWithCovers k μ) ∧
        ((∀ᵐ z ∂μ, energyT μ k .mixed 2 a z < ⊤) → IsRegularlyRectifiableWithCovers k μ)

/-- Table row `S_2^a = T_2^a`, "necessary: yes". For
`k < n+2`, under the density hypothesis, mixed regular measure rectifiability implies
`S_{2,μ}^a < ∞` and `T_{2,μ}^a < ∞` `μ`-a.e. -/
def SquareNecessaryStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ a : ℝ, 0 < a →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    HasPositiveFiniteUpperDensity k μ → IsRegularlyRectifiableMeasure .mixed k μ →
      (∀ᵐ z ∂μ, energyS μ k .mixed 2 a z < ⊤) ∧ (∀ᵐ z ∂μ, energyT μ k .mixed 2 a z < ⊤)

/-- Table row `S_p^a`, `2 < p < ∞`, "sufficient: yes". -/
def SpAboveTwoSufficientStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 →
  ∀ p : ℝ, 2 < p → ∀ a : ℝ, 0 < a →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    HasPositiveFiniteUpperDensity k μ →
      (∀ᵐ z ∂μ, energyS μ k .mixed p a z < ⊤) → IsRegularlyRectifiableWithCovers k μ

/-- Table row `S_p^a`, `2 < p < ∞`, "necessary: no, `n = 2`, `k = 1`". For each such `p` and
endpoint `a > 0` there is a locally Radon source on `ℝ² × ℝ` with the density hypothesis at
`k = 1`, regularly `1`-rectifiable with covers of every positive slope, for which `S_{p,μ}^a < ∞`
fails on a set of positive `μ` measure. -/
def SpAboveTwoNotNecessaryStatement : Prop :=
  ∀ p : ℝ, 2 < p → ∀ a : ℝ, 0 < a →
    ∃ μ : Measure (Space 2), IsFiniteMeasureOnCompacts μ ∧ μ.InnerRegular ∧
      HasPositiveFiniteUpperDensity 1 μ ∧ IsRegularlyRectifiableWithCovers 1 μ ∧
      ¬ (∀ᵐ z ∂μ, energyS μ 1 .mixed p a z < ⊤)

/-- Table row `T_p^a`, `0 < p < 2`, "sufficient: yes". -/
def TpBelowTwoSufficientStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 →
  ∀ p : ℝ, 0 < p → p < 2 → ∀ a : ℝ, 0 < a →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    HasPositiveFiniteUpperDensity k μ →
      (∀ᵐ z ∂μ, energyT μ k .mixed p a z < ⊤) → IsRegularlyRectifiableWithCovers k μ

/-- Table row `T_p^a`, `0 < p < 2`, "necessary: no, `n = 1`, `k = 2`". For each such `p` and
endpoint `a > 0` there is a locally Radon source on `ℝ × ℝ` with the density hypothesis at
`k = 2`, regularly `2`-rectifiable with covers of every positive norm, for which `T_{p,μ}^a < ∞`
fails on a set of positive `μ` measure. -/
def TpBelowTwoNotNecessaryStatement : Prop :=
  ∀ p : ℝ, 0 < p → p < 2 → ∀ a : ℝ, 0 < a →
    ∃ μ : Measure (Space 1), IsFiniteMeasureOnCompacts μ ∧ μ.InnerRegular ∧
      HasPositiveFiniteUpperDensity 2 μ ∧ IsRegularlyRectifiableWithCovers 2 μ ∧
      ¬ (∀ᵐ z ∂μ, energyT μ 2 .mixed p a z < ⊤)

/-- Table row `T_p^a`, `2 < p < ∞`, "sufficient: no, `n = 1`, `k = 2`". For each such `p` and
endpoint `a > 0` there is a locally Radon source on `ℝ × ℝ` with the density hypothesis at
`k = 2` and `T_{p,μ}^a < ∞` `μ`-a.e., which is not regularly `2`-rectifiable. -/
def TpAboveTwoNotSufficientStatement : Prop :=
  ∀ p : ℝ, 2 < p → ∀ a : ℝ, 0 < a →
    ∃ μ : Measure (Space 1), IsFiniteMeasureOnCompacts μ ∧ μ.InnerRegular ∧
      HasPositiveFiniteUpperDensity 2 μ ∧ (∀ᵐ z ∂μ, energyT μ 2 .mixed p a z < ⊤) ∧
      ¬ IsRegularlyRectifiableMeasure .mixed 2 μ

/-- Table row `T_p^a`, `2 < p < ∞`, "necessary: yes". -/
def TpAboveTwoNecessaryStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 →
  ∀ p : ℝ, 2 < p → ∀ a : ℝ, 0 < a →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    HasPositiveFiniteUpperDensity k μ → IsRegularlyRectifiableMeasure .mixed k μ →
      ∀ᵐ z ∂μ, energyT μ k .mixed p a z < ⊤

/-- The ambient endpoint of the classification. At `k = n+2`, for every finite `p > 0` and endpoint `a > 0` and every locally Radon source with the
density hypothesis: the source is regularly `(n+2)`-rectifiable with covers of every positive norm
(`Foundations.AmbientCharacterizationStatement`); every available `S_p^a` and `T_p^a` vanishes identically; and both
finiteness conditions are sufficient and necessary. -/
def ClassificationAmbientStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 0 < p → ∀ a : ℝ, 0 < a →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    HasPositiveFiniteUpperDensity (n + 2) μ →
      IsRegularlyRectifiableWithCovers (n + 2) μ ∧
      (∀ T : FamilyKind, Nonempty (Models n (n + 2) T) → ∀ z : Space n,
        energyS μ (n + 2) T p a z = 0 ∧ energyT μ (n + 2) T p a z = 0) ∧
      ((∀ᵐ z ∂μ, energyS μ (n + 2) .mixed p a z < ⊤) →
        IsRegularlyRectifiableWithCovers (n + 2) μ) ∧
      (IsRegularlyRectifiableMeasure .mixed (n + 2) μ →
        ∀ᵐ z ∂μ, energyS μ (n + 2) .mixed p a z < ⊤) ∧
      ((∀ᵐ z ∂μ, energyT μ (n + 2) .mixed p a z < ⊤) →
        IsRegularlyRectifiableWithCovers (n + 2) μ) ∧
      (IsRegularlyRectifiableMeasure .mixed (n + 2) μ →
        ∀ᵐ z ∂μ, energyT μ (n + 2) .mixed p a z < ⊤)

/-- Endpoint invariance of finiteness (from the finite annuli of `BetaPowAnnulusStatement`): for a locally Radon source, every family, every `p > 0` and
every centre, finiteness of `S_p^a` and of `T_p^a` does not depend on the endpoint `a > 0`. For an
unavailable family both sides are `⊤`. -/
def BetaPEndpointInvarianceStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind,
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ p : ℝ, 0 < p → ∀ (z : Space n) (a a' : ℝ), 0 < a → 0 < a' →
    (energyS μ k T p a z < ⊤ ↔ energyS μ k T p a' z < ⊤) ∧
      (energyT μ k T p a z < ⊤ ↔ energyT μ k T p a' z < ⊤)

/-- **Qualitative implications, sharp ranges and failure dimensions**: the ten table entries for `k < n+2` (each "yes" an implication for all
sources with the density hypothesis, each "no" a counterexample in exactly the displayed
dimension), the ambient endpoint and the endpoint invariance of finiteness. -/
def BetaPClassificationStatement : Prop :=
  SpBelowTwoNotSufficientStatement ∧ SpBelowTwoNecessaryStatement ∧
    SquareSufficientStatement ∧ SquareNecessaryStatement ∧
    SpAboveTwoSufficientStatement ∧ SpAboveTwoNotNecessaryStatement ∧
    TpBelowTwoSufficientStatement ∧ TpBelowTwoNotNecessaryStatement ∧
    TpAboveTwoNotSufficientStatement ∧ TpAboveTwoNecessaryStatement ∧
    ClassificationAmbientStatement ∧ BetaPEndpointInvarianceStatement

end ParabolicRectifiability.BetaP
