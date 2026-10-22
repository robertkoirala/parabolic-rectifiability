import ParabolicRectifiability.Foundations.Density
import ParabolicRectifiability.Foundations.BetaPow
import ParabolicRectifiability.Measure.BetaLaws

/-! # Statements: measurability, monotonicity, finite annuli, scaling; beta-`p` compatibility

One proposition per clause of the measurability, monotonicity, finite-annulus and scaling
properties of the betas and square energies, together with the compatibility claims for the
beta-`p` quantities.

These are proposition definitions only; the corresponding theorems include
`squareEnergy_rescaledSource_eq`, `lintegral_betaSq_Ioo_le_annulus` and their siblings.

Clauses proved elsewhere are cited, not restated:
* beta fits are Borel: `ParabolicRectifiability.measurable_betaSq` (joint measurability in
  `(z,r)`, every family, any source finite on compacts);
* scale energies are Borel: `ParabolicRectifiability.measurable_squareEnergy` (every real
  endpoint, every family, any source finite on compacts).

Conventions. The standing assumptions `1 ≤ n` and `1 ≤ k ≤ n + 2` are
hypotheses of every statement mentioning `k`.
"Locally Radon" is `IsFiniteMeasureOnCompacts μ` together with `μ.InnerRegular`. The
scale endpoint `T` is written `R`, `A` or `a`, because `T` names the family.
Real constants are compared through `ENNReal.ofReal`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- Density part of the measurability clause: for a
locally Radon source both densities are Borel functions of the centre.
The beta and energy parts of this clause are the existing `measurable_betaSq` and
`measurable_squareEnergy`. -/
def DensityMeasurabilityStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    Measurable (lowerDensity μ k) ∧ Measurable (upperDensity μ k)

/-- The restriction of a
locally Radon source to a Borel set is locally Radon (finite on compacts and inner
regular). -/
def RestrictLocallyRadonStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ E : Set (Space n), MeasurableSet E →
    IsFiniteMeasureOnCompacts (μ.restrict E) ∧ (μ.restrict E).InnerRegular

/-- Domination: if `ν ≤ c μ` with a
real `c > 0`, then `b_ν ≤ c b_μ` at every centre and positive radius, and
`S_ν^R ≤ c S_μ^R` at every centre and positive endpoint. Every family is allowed (an
unavailable family has `b = S = ⊤` on both sides); no regularity of `ν` or `μ` is
assumed. -/
def BetaEnergyDominationStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind,
  ∀ μ ν : Measure (Space n), ∀ c : ℝ, 0 < c → ν ≤ ENNReal.ofReal c • μ →
    (∀ (z : Space n) (r : ℝ), 0 < r →
      betaSq ν k T z r ≤ ENNReal.ofReal c * betaSq μ k T z r) ∧
    (∀ R : ℝ, 0 < R → ∀ z : Space n,
      squareEnergy ν k T R z ≤ ENNReal.ofReal c * squareEnergy μ k T R z)

/-- The finite-annulus bound: for an available family, a locally Radon source and
`0 < a < b < ∞`,
`∫_a^b b_{μ,T}(z,r) dr/r ≤ a^{-k} μ(closed P(z,b)) log(b/a) < ∞`.
The interval is `Ioo a b` against `scaleMeasure`; its endpoints are null, so the choice
of open or closed interval is immaterial. -/
def AnnulusBoundStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ (z : Space n) (a b : ℝ), 0 < a → a < b →
    (∫⁻ r in Ioo a b, betaSq μ k T z r ∂scaleMeasure) ≤
        (ENNReal.ofReal a)⁻¹ ^ k * μ (Metric.closedBall z b) *
          ENNReal.ofReal (Real.log (b / a)) ∧
      (ENNReal.ofReal a)⁻¹ ^ k * μ (Metric.closedBall z b) *
          ENNReal.ofReal (Real.log (b / a)) < ⊤

/-- Endpoint independence: finiteness of the square
energy at a centre does not depend on the finite positive endpoint. Stated for every
family (for an unavailable family both sides are `⊤`, so the equivalence is trivial
there). -/
def SquareFinitenessEndpointStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind,
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ (z : Space n) (R R' : ℝ), 0 < R → 0 < R' →
    (squareEnergy μ k T R z < ⊤ ↔ squareEnergy μ k T R' z < ⊤)

/-- Dilation law of the square function: for
`μ_{q,R} = R^{-k} (δ_{1/R}(· - q))_# μ`, which is the existing `rescaledSource μ k q R hR`,
`S_{μ_{q,R}}^A(z) = S_μ^{RA}(q + δ_R z)`. The point `q + δ_R z` is
`(similarity q R hR).symm z` (`similarity_symm_apply`). Every family; no regularity of
`μ` is assumed. The beta-level identity is the existing
`betaSq_rescaledSource`. -/
def SquareEnergyRescalingStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind,
  ∀ μ : Measure (Space n), ∀ (q : Space n) (R : ℝ) (hR : 0 < R),
  ∀ A : ℝ, 0 < A → ∀ z : Space n,
    squareEnergy (rescaledSource μ k q R hR) k T A z =
      squareEnergy μ k T (R * A) ((similarity q R hR).symm z)

/-- Scalar law of the square function:
`S_{cμ}^A = c S_μ^A` for a real `c > 0`, every family and every positive endpoint.
For available families this is covered by the existing `squareEnergy_smul`
(with `c := ENNReal.ofReal c`); the statement here also includes unavailable families,
where both sides are `⊤`. -/
def SquareEnergySmulStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind,
  ∀ μ : Measure (Space n), ∀ c : ℝ, 0 < c → ∀ A : ℝ, 0 < A → ∀ z : Space n,
    squareEnergy (ENNReal.ofReal c • μ) k T A z = ENNReal.ofReal c * squareEnergy μ k T A z

/-- Compatibility with `p = 2`: at `p = 2` the beta-`p` fitting quantity is literally the natural
`betaSq`, at every centre, radius and family (both vanish at nonpositive radii). -/
def BetaPowTwoStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind,
  ∀ μ : Measure (Space n), ∀ (z : Space n) (r : ℝ),
    betaPow μ k T 2 z r = betaSq μ k T z r

/-- Compatibility with `p = 2`: `S_2^a = T_2^a = S^a`, the
existing `squareEnergy`, for every positive endpoint `a` and every family. -/
def EnergyTwoStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind,
  ∀ μ : Measure (Space n), ∀ a : ℝ, 0 < a → ∀ z : Space n,
    energyS μ k T 2 a z = squareEnergy μ k T a z ∧
      energyT μ k T 2 a z = squareEnergy μ k T a z

/-- Amplitude laws of the beta-`p` energies: for real `p > 0` and real
`c > 0`, `S_{p,cμ}^a = c^{2/p} S_{p,μ}^a` and `T_{p,cμ}^a = c T_{p,μ}^a`, for every
positive endpoint `a` and every family (an unavailable family gives `⊤` on both sides).
The power `c^{2/p}` is the `ℝ≥0∞` real power of `ENNReal.ofReal c`. -/
def EnergyPowSmulStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind,
  ∀ μ : Measure (Space n), ∀ p : ℝ, 0 < p → ∀ c : ℝ, 0 < c → ∀ a : ℝ, 0 < a →
  ∀ z : Space n,
    energyS (ENNReal.ofReal c • μ) k T p a z = ENNReal.ofReal c ^ (2 / p) * energyS μ k T p a z ∧
      energyT (ENNReal.ofReal c • μ) k T p a z = ENNReal.ofReal c * energyT μ k T p a z

end ParabolicRectifiability.Foundations
