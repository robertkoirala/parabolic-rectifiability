import ParabolicRectifiability.Foundations.BetaPow
import ParabolicRectifiability.Foundations.Density
import ParabolicRectifiability.Measure.BetaLaws

/-! # Statements: beta-`p` conventions and normalization/comparison laws

One proposition per convention or law. The proposition definitions specify the public
interfaces; their proofs are the theorems `emptyTestingBall`, `unavailableFamily`,
`betaPow_measurability`, …

Laws already stated in `Foundations` are cited, not restated:
* amplitude laws of the energies, `S_{p,cμ}^a = c^{2/p} S_{p,μ}^a` and `T_{p,cμ}^a = c T_{p,μ}^a`:
  `Foundations.EnergyPowSmulStatement`;
* `B_2 = betaSq` and `S_2^a = T_2^a = squareEnergy`:
  `Foundations.BetaPowTwoStatement`, `Foundations.EnergyTwoStatement`.

Conventions. `B_p` is `Foundations.betaPow`, `S_p^a` is `Foundations.energyS`, `T_p^a` is
`Foundations.energyT`, and `β_p = B_p^{1/p}` is written `betaPow … ^ (1/p)`. The density ratio
`Θ = μ(P(z,r))/r^k` is `Foundations.densityRatio μ k z r`. The standing
assumptions `n ≥ 1`, `1 ≤ k ≤ n+2` and `0 < p` are hypotheses of every
statement. "Locally Radon" is `IsFiniteMeasureOnCompacts μ` together with `μ.InnerRegular`; it is
assumed exactly where a law needs local finiteness (measurability, finite annuli, the density
factor of Hölder), and omitted for the algebraic laws, which hold for every Borel measure. The
availability guard `Nonempty (Models n k T)` is kept for the laws that need it and wherever the law fails for an empty family; the amplitude, dilation and clamping
identities are stated for every family, since an unavailable family gives `⊤` on both sides.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- Empty testing ball: for a nonempty family, a testing
ball of zero source mass has `B_p = 0`. No regularity of `μ` is needed. -/
def EmptyTestingBallStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ μ : Measure (Space n), ∀ p : ℝ, 0 < p → ∀ (z : Space n) (r : ℝ),
    μ (Metric.ball z r) = 0 → betaPow μ k T p z r = 0

/-- Unavailable family: for an empty family
`B_p = +∞` at every positive radius and `S_p^a = T_p^a = +∞` at every positive endpoint, for every
source. -/
def UnavailableFamilyStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ T : FamilyKind, IsEmpty (Models n k T) →
  ∀ μ : Measure (Space n), ∀ p : ℝ, 0 < p → ∀ z : Space n,
    (∀ r : ℝ, 0 < r → betaPow μ k T p z r = ⊤) ∧
      ∀ a : ℝ, 0 < a → energyS μ k T p a z = ⊤ ∧ energyT μ k T p a z = ⊤

/-- Borel measurability: for an available family and a locally Radon source, `(z,r) ↦ B_p(z,r)` is
jointly Borel, and `S_p^a`, `T_p^a` are Borel in the centre for every positive endpoint. -/
def BetaPowMeasurabilityStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ p : ℝ, 0 < p →
    Measurable (fun x : Space n × ℝ => betaPow μ k T p x.1 x.2) ∧
      ∀ a : ℝ, 0 < a → Measurable (energyS μ k T p a) ∧ Measurable (energyT μ k T p a)

/-- Restriction: for an available family, `B_p`, `S_p^a`
and `T_p^a` decrease when the source is restricted to any set. -/
def BetaPowRestrictionStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ μ : Measure (Space n), ∀ E : Set (Space n), ∀ p : ℝ, 0 < p →
    (∀ (z : Space n) (r : ℝ), betaPow (μ.restrict E) k T p z r ≤ betaPow μ k T p z r) ∧
      ∀ a : ℝ, 0 < a → ∀ z : Space n,
        energyS (μ.restrict E) k T p a z ≤ energyS μ k T p a z ∧
          energyT (μ.restrict E) k T p a z ≤ energyT μ k T p a z

/-- Finite annuli: for an
available family and a locally Radon source, both scale integrands have finite integral over every
positive finite annulus `(u,v)`, `0 < u < v`, at every centre. -/
def BetaPowAnnulusStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ p : ℝ, 0 < p → ∀ (z : Space n) (u v : ℝ), 0 < u → u < v →
    (∫⁻ r in Ioo u v, betaPow μ k T p z r ^ (2 / p) ∂scaleMeasure) < ⊤ ∧
      (∫⁻ r in Ioo u v, betaPow μ k T p z r ∂scaleMeasure) < ⊤

/-- Amplitude law of the fitting quantity: `B_{p,cμ} = c B_{p,μ}`
for a real `c > 0`, at every centre and radius, for every family. The energy amplitude laws are
`Foundations.EnergyPowSmulStatement`. -/
def BetaPowSmulStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind,
  ∀ μ : Measure (Space n), ∀ p : ℝ, 0 < p → ∀ c : ℝ, 0 < c → ∀ (z : Space n) (r : ℝ),
    betaPow (ENNReal.ofReal c • μ) k T p z r = ENNReal.ofReal c * betaPow μ k T p z r

/-- Dilation law: for `μ^{q,R} = R^{-k}(z ↦ δ_{1/R}(z-q))_# μ`, which is the existing `rescaledSource μ k q R hR`
(the point `δ_{1/R}(z-q)` is `similarity q R hR z`),
`B_{p,μ^{q,R}}(δ_{1/R}(z-q), s) = B_{p,μ}(z, Rs)` for every `s > 0`, and the scale energies obey
the same identity with endpoint `aR`. Every family; no regularity of `μ`. -/
def BetaPowRescalingStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind,
  ∀ μ : Measure (Space n), ∀ p : ℝ, 0 < p → ∀ (q : Space n) (R : ℝ) (hR : 0 < R),
  ∀ z : Space n,
    (∀ s : ℝ, 0 < s →
      betaPow (rescaledSource μ k q R hR) k T p (similarity q R hR z) s =
        betaPow μ k T p z (R * s)) ∧
      ∀ a : ℝ, 0 < a →
        energyS (rescaledSource μ k q R hR) k T p a (similarity q R hR z) =
            energyS μ k T p (a * R) z ∧
          energyT (rescaledSource μ k q R hR) k T p a (similarity q R hR z) =
            energyT μ k T p (a * R) z

/-- Zero source: for an
available family the zero source has `B_p = 0` and zero energies `S_p^a = T_p^a = 0`. -/
def BetaPowZeroSourceStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ T : FamilyKind, Nonempty (Models n k T) → ∀ p : ℝ, 0 < p → ∀ z : Space n,
    (∀ r : ℝ, betaPow (0 : Measure (Space n)) k T p z r = 0) ∧
      ∀ a : ℝ, 0 < a →
        energyS (0 : Measure (Space n)) k T p a z = 0 ∧
          energyT (0 : Measure (Space n)) k T p a z = 0

/-- Hölder with the density factor. With `Θ = μ(P(z,r))/r^k` (`densityRatio`), for an available family, a
locally Radon source and a positive radius:
1. `β_p ≤ Θ^{1/p - 1/q} β_q` for `0 < p < q < ∞`;
2. `B_2 ≤ Θ^{1-2/p} β_p^2` for `2 ≤ p`, where at `p = 2` the factor is `Θ^0 = 1` (the `ℝ≥0∞`
   power with exponent zero is one even for `Θ = 0` or `Θ = ⊤`).

Edge cases: a ball of zero mass (`Θ = 0`) has `B_p = 0`, so the inequality holds
with both sides zero (the immediate case); `Θ = ⊤` cannot
occur for a locally finite source (balls are relatively compact). The availability guard is needed:
for an empty family and `Θ = 0` the left side is `⊤` and the right side `0`. -/
def BetaPowHolderStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ (z : Space n) (r : ℝ), 0 < r →
    (∀ p q : ℝ, 0 < p → p < q →
      betaPow μ k T p z r ^ (1 / p) ≤
        densityRatio μ k z r ^ (1 / p - 1 / q) * betaPow μ k T q z r ^ (1 / q)) ∧
      ∀ p : ℝ, 2 ≤ p →
        betaPow μ k T 2 z r ≤ densityRatio μ k z r ^ (1 - 2 / p) * betaPow μ k T p z r ^ (2 / p)

/-- Density-free clamping comparisons: `B_2 ≤ 2^{2-p} B_p` for `0 < p ≤ 2` and `B_p ≤ 2^{p-2} B_2` for `2 ≤ p`,
at every centre and radius, for every family and every source; no density bound. -/
def BetaPowClampingStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind,
  ∀ μ : Measure (Space n), ∀ (z : Space n) (r : ℝ),
    (∀ p : ℝ, 0 < p → p ≤ 2 →
      betaPow μ k T 2 z r ≤ (2 : ℝ≥0∞) ^ (2 - p) * betaPow μ k T p z r) ∧
      ∀ p : ℝ, 2 ≤ p → betaPow μ k T p z r ≤ (2 : ℝ≥0∞) ^ (p - 2) * betaPow μ k T 2 z r

end ParabolicRectifiability.BetaP
