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
import Spec.Foundations.ADR
import Spec.Foundations.BetaPow
import Spec.Foundations.Graphs
import Spec.Foundations.HalfTimeDerivative
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
import Spec.QuantitativeCharacterization.Coverings
import Spec.QuantitativeCharacterization.References
import Spec.QuantitativeCharacterization.Statements.Characterization

/-! Specification: the definitions of `ParabolicRectifiability.QuantitativeCharacterization.Statements.Approximants` used by the headline statements. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.QuantitativeCharacterization
open ParabolicRectifiability.Foundations
/-- **Approximants of a covering.** Under the global hypotheses of the quantitative characterization
(`μ ≠ 0` Radon, unbounded support, `A`-ADR) and the equivalent condition `M_β(μ) < ∞`: for
every root `P₀ = P(a,R)`, `a ∈ E`, `R > 0`, and every `(K,L)` covering there, there are
disjoint Borel `F_H, F_V ⊂ P₀` inside the typed traces with `μ(P₀ \ (F_H ∪ F_V)) = 0`, such
that for every `N ≥ 0`
* `μ ⌊ P₀ = μ^N_H + μ^N_V + e^N` and `e^N(P₀) ≤ 2 exp(-N / ((2^k + A²) K)) μ(P₀)`;
* `μ^N_H` is horizontally and `μ^N_V` regularly vertically rectifiable;
and the retained measures increase to the canonical parts `μ_H ⌊ P₀`, `μ_V ⌊ P₀` while the
residual decreases to zero in total variation. -/
def MeasureApproximantsStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ A : ℝ, 1 ≤ A →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular → μ ≠ 0 →
    ¬ Bornology.IsBounded μ.support → IsADR A k μ → carlesonEnergy μ k < ⊤ →
  ∀ L : ℝ, 1 ≤ L → ∀ K : ℝ, 1 ≤ K → ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R →
  ∀ 𝒞 : RegularMixedCovering k K L μ a R,
    ∃ FH FV : Set (Space n), 𝒞.IsTypedTraceSplit FH FV ∧ 𝒞.MeasureIdentity FH FV ∧
      𝒞.RelativeTail ((2 : ℝ) ^ k + A ^ 2) ∧ 𝒞.HasCanonicalLimits FH FV

/-- The forward part of the local statement for given constants `B_loc`, `L₀` and `C`: for a locally Radon `μ`, a root
`P₀ = P(a,R)` with `a ∈ E`, `R > 0`, and a finite `M ≥ 0`, the local ADR and local Carleson
bounds `A⁻¹ s^k ≤ μ(P(b,s)) ≤ A s^k`, `∫_{P(b,s)} ∫_0^s β_μ² dr/r dμ ≤ M s^k` for every
`b ∈ supp μ ∩ P(a, B_loc R)` and `0 < s ≤ B_loc R` give a `(C(1+M), L₀)` covering of `P₀`
and local typed measure approximants: a typed split with the identity and the relative tail
the measure identity and the relative tail, every `μ^N_H` horizontally rectifiable and every `μ^N_V` regularly vertically
rectifiable (the rectifiability of the
approximants is the "typed" part, exported explicitly). No canonical identification is asserted. -/
def LocalForwardBounds (n k : ℕ) (A Bloc L₀ C : ℝ) : Prop :=
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ M : ℝ, 0 ≤ M →
    (∀ b ∈ μ.support ∩ Metric.ball a (Bloc * R), ∀ s : ℝ, 0 < s → s ≤ Bloc * R →
      ENNReal.ofReal (A⁻¹ * s ^ k) ≤ μ (Metric.ball b s) ∧
        μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k) ∧
        (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ) ≤
          ENNReal.ofReal (M * s ^ k)) →
    ∃ 𝒞 : RegularMixedCovering k (C * (1 + M)) L₀ μ a R,
      ∃ FH FV : Set (Space n), 𝒞.IsTypedTraceSplit FH FV ∧ 𝒞.MeasureIdentity FH FV ∧
        𝒞.RelativeTail ((2 : ℝ) ^ k + A ^ 2) ∧
        ∀ N : ℕ,
          IsRegularlyRectifiableMeasure .horizontal k (𝒞.approximant FH N) ∧
            IsRegularlyRectifiableMeasure .vertical k (𝒞.approximant FV N)

/-- **The local forward and converse clauses.**
1. **Forward.** For `n, k, A` there are `B_loc(n,k,A) ≥ 1`, `L₀(n,k,A) ≥ 1` and
   `C(n,k,A) ≥ 1` such that, for a locally Radon `μ`, a root `P₀ = P(a,R)` with `a ∈ E`,
   `R > 0`, and a finite `M ≥ 0`, the local ADR and local Carleson bounds
   `A⁻¹ s^k ≤ μ(P(b,s)) ≤ A s^k`, `∫_{P(b,s)} ∫_0^s β_μ² dr/r dμ ≤ M s^k` for every
   `b ∈ supp μ ∩ P(a, B_loc R)` and `0 < s ≤ B_loc R` give a `(C(1+M), L₀)` covering of `P₀`
   (a covering with `K ≤ C(1+M)`) and local typed approximants satisfying the measure identity and the relative tail, with
   `μ^N_H` horizontally and `μ^N_V` regularly vertically rectifiable for every `N`
   (`LocalForwardBounds`). Every beta uses the whole original `μ`.
2. **Converse.** For every `L ≥ 1` there is `B_rev(n,k,L) ≥ 1` (independent of `A`) and, for
   every `A ≥ 1`, a constant `C(n,k,A,L)` such that a `(K,L)` covering at `P(a,R)` and the
   upper growth `μ(P(b,s)) ≤ A s^k` for `b ∈ E ∩ P(a, B_rev R)`, `0 < s ≤ B_rev R` give
   `∫_{P(a,R)} ∫_0^R β_μ² dr/r dμ ≤ C K R^k`.
The closing sentence of the corollary (uniform coverings over local roots give the local
Carleson bound) is the converse applied root by root; it is not restated. -/
def UniformLocalStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    (∀ A : ℝ, 1 ≤ A →
      ∃ Bloc : ℝ, 1 ≤ Bloc ∧ ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∃ C : ℝ, 1 ≤ C ∧
        LocalForwardBounds n k A Bloc L₀ C) ∧
    (∀ L : ℝ, 1 ≤ L → ∃ Brev : ℝ, 1 ≤ Brev ∧ ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 < C ∧
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ K : ℝ, 1 ≤ K →
        Nonempty (RegularMixedCovering k K L μ a R) →
        (∀ b ∈ μ.support ∩ Metric.ball a (Brev * R), ∀ s : ℝ, 0 < s → s ≤ Brev * R →
          μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k)) →
        (∫⁻ z in Metric.ball a R, squareEnergy μ k .mixed R z ∂μ) ≤
          ENNReal.ofReal (C * K * R ^ k))

/-- The conclusion of the bounded-support statement for given constants `C(A,k) = Cabs`, `L₀`
and `C`; the clauses are listed in the docstring of `BoundedSupportStatement`.

This predicate only names the body of `BoundedSupportStatement` so that the same `L₀, C` can be
exported jointly (`QuantitativeCommonConstantsStatement`). -/
def BoundedSupportBounds (n k : ℕ) (A Cabs L₀ C : ℝ) : Prop :=
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular → μ ≠ 0 →
    Bornology.IsBounded μ.support → 0 < Metric.diam μ.support →
    (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)) →
    (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → r ≤ Metric.diam μ.support →
      ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball z r)) →
    ((carlesonEnergy μ k < ⊤ ↔
          ∃ K : ℝ, 1 ≤ K ∧ IsQuantitativelyMixedRectifiable k K L₀ μ) ∧
        (carlesonEnergy μ k < ⊤ →
          IsQuantitativelyMixedRectifiable k (C * (1 + (carlesonEnergy μ k).toReal)) L₀ μ) ∧
        (∀ K : ℝ, 1 ≤ K → IsQuantitativelyMixedRectifiable k K L₀ μ →
          carlesonEnergy μ k ≤ ENNReal.ofReal (C * K))) ∧
    (∀ L : ℝ, 1 ≤ L → ∀ K : ℝ, 1 ≤ K → ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R →
      ∀ 𝒞 : RegularMixedCovering k K L μ a R,
        ∃ FH FV : Set (Space n), 𝒞.IsTypedTraceSplit FH FV ∧ 𝒞.MeasureIdentity FH FV ∧
          (R ≤ Metric.diam μ.support → 𝒞.RelativeTail ((2 : ℝ) ^ k + A ^ 2)) ∧
          (∀ N : ℕ, 𝒞.residual N (Metric.ball a R) ≤
            ENNReal.ofReal (Cabs * R ^ k * Real.exp (-(N : ℝ) / (Cabs * K)))) ∧
          𝒞.HasCanonicalLimits FH FV) ∧
    (carlesonEnergy μ k < ⊤ → ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R →
      ∃ 𝒞 : RegularMixedCovering k (C * (1 + (carlesonEnergy μ k).toReal)) L₀ μ a R,
        ∃ FH FV : Set (Space n), 𝒞.IsTypedTraceSplit FH FV ∧ 𝒞.MeasureIdentity FH FV ∧
          𝒞.RelativeTail ((2 : ℝ) ^ k + A ^ 2)) ∧
    (∀ K : ℝ, 1 ≤ K → IsQuantitativelyMixedRectifiable k K L₀ μ →
      ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R →
        ∃ 𝒞 : RegularMixedCovering k (C * K) L₀ μ a R,
          ∃ FH FV : Set (Space n), 𝒞.IsTypedTraceSplit FH FV ∧ 𝒞.MeasureIdentity FH FV ∧
            𝒞.RelativeTail ((2 : ℝ) ^ k + A ^ 2))

/-- **The bounded-support case.** For `μ ≠ 0` locally Radon with `0 < D_E = diam_P E < ∞`,
upper growth `μ(P(z,r)) ≤ A r^k` for `z ∈ E` and all `r > 0`, and lower growth
`A⁻¹ r^k ≤ μ(P(z,r))` for `z ∈ E` and `0 < r ≤ D_E`:
1. the equivalence and the bounds of the quantitative characterization hold, with all roots;
2. for every prescribed covering at every root: typed approximants with the identity, the
   relative tail when `R ≤ D_E`, the unconditional tail
   `e^N(P₀) ≤ C(A,k) R^k exp(-N/(C(A,k) K))` at every radius, and all canonical conclusions;
3. if `M_β < ∞`, at every root a chosen `(C(1+M_β), L₀)` covering with approximants and the
   relative tail;
4. from a uniform `(K,L₀)` property, at every root a chosen `(CK, L₀)` covering (`K' ≤ CK`)
   with approximants and the relative tail for `K' = CK` (denominator `CK` after a
   fixed change of constant).
The constant `C(A,k)` of the unconditional tail depends only on `A` and `k`, so it is chosen
before `n`; `L₀` and `C` depend on `(n,k,A)`. -/
def BoundedSupportStatement : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 ≤ A → ∃ Cabs : ℝ, 0 < Cabs ∧
  ∀ n : ℕ, 1 ≤ n → k ≤ n + 2 →
  ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∃ C : ℝ, 1 ≤ C ∧ BoundedSupportBounds n k A Cabs L₀ C

/-- **The ambient case.** Let `k = n + 2` and `μ` be locally Radon.
* every admissible model is `X` itself, and `β_μ = 0`;
* under upper ambient growth `μ(P(z,r)) ≤ A r^{n+2}` (`z ∈ E`, `r > 0`), `μ ≪ H_P^{n+2}`;
* at every root `P(a,R)`, `a ∈ E`, `R > 0`, the single model ball `P(a,2R)` gives a
  covering with `K = 2^k` and `L = 2`, and with `F_H = ∅`, `F_V = P₀` the approximants are
  `μ^N_V = μ ⌊ P₀` and `μ^N_H = e^N = 0` for every `N ≥ 1`. -/
def AmbientEndpointStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    (∀ M : Models n (n + 2) .mixed, modelSet M = Set.univ) ∧
    (∀ (z : Space n) (r : ℝ), betaSq μ (n + 2) .mixed z r = 0) ∧
    ((∃ A : ℝ, ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r →
        μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ (n + 2))) →
      μ ≪ hausdorffP n (n + 2)) ∧
    (∀ a ∈ μ.support, ∀ R : ℝ, 0 < R →
      ∃ 𝒞 : RegularMixedCovering (n + 2) ((2 : ℝ) ^ (n + 2)) 2 μ a R,
        𝒞.index = {0} ∧ (∀ i, 𝒞.center i = a ∧ 𝒞.radius i = 2 * R) ∧
        𝒞.IsTypedTraceSplit ∅ (Metric.ball a R) ∧
        ∀ N : ℕ, 1 ≤ N →
          𝒞.approximant (Metric.ball a R) N = μ.restrict (Metric.ball a R) ∧
            𝒞.approximant ∅ N = 0 ∧ 𝒞.residual N = 0)

/-- **Common constants of the quantitative characterization and its corollaries**.
The constants `L₀ = L₀(n,k,A)` and `C = C(n,k,A)` of the quantitative characterization are used again in its corollaries: the local forward
version (a `(K,L₀)` covering with `K ≤ C(1+M)`), the bounded-support version
(the equivalence and the constants remain valid) and the beta-`p`
forward clause (the corresponding forward bound `K ≤ C(1+M_β)`). The
standalone statements `QuantitativeCharacterizationStatement`, `UniformLocalStatement`,
`BoundedSupportStatement` and `BetaPowCarlesonComparisonStatement` each choose their own
`∃ L₀ C`. This statement exports one choice of `L₀, C` (and of `B_loc`) for all four:

for `k ≥ 1` and `A ≥ 1` there is `C(A,k) > 0` (the bounded absolute-tail constant, chosen
before `n` as in `BoundedSupportStatement`) such that for every `n ≥ 1` with `k ≤ n + 2` there
are `L₀ ≥ 1`, `C ≥ 1` and `B_loc ≥ 1` with
`MainTheoremBounds n k A L₀ C`, `BetaPowForwardBounds n k A L₀ C`,
`LocalForwardBounds n k A B_loc L₀ C` and `BoundedSupportBounds n k A C(A,k) L₀ C`.

Every hypothesis is that of the corresponding standalone statement: the four predicates are the
bodies of those statements. The arbitrary-`L` converses (`C_rev(n,k,A,L)` of the quantitative characterization and
`B_rev(n,k,L)`, `C(n,k,A,L)` of the local converse) have their own constants and stay in the
standalone statements. The forward parts of the standalone statements are projections of this
one. -/
def QuantitativeCommonConstantsStatement : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 ≤ A → ∃ Cabs : ℝ, 0 < Cabs ∧
  ∀ n : ℕ, 1 ≤ n → k ≤ n + 2 →
  ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∃ C : ℝ, 1 ≤ C ∧ ∃ Bloc : ℝ, 1 ≤ Bloc ∧
    MainTheoremBounds n k A L₀ C ∧ BetaPowForwardBounds n k A L₀ C ∧
      LocalForwardBounds n k A Bloc L₀ C ∧ BoundedSupportBounds n k A Cabs L₀ C

end ParabolicRectifiability.QuantitativeCharacterization
