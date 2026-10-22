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
import Spec.BetaP.Proofs.Counterexamples.Euclidean
import Spec.Foundations.BetaPow
import Spec.Foundations.EuclideanBeta
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

/-! Specification: the definitions of `ParabolicRectifiability.BetaP.Statements.Failures` used by the headline statements. -/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace ParabolicRectifiability.BetaP
open ParabolicRectifiability.Foundations
/-- The constant-time transfer. At
`n = 2`, `k = 1`, with `ι = timeSlice`:
1. for every measure `ν` on `ℝ²`, every `p > 0`, the horizontal or mixed family, every `x ∈ ℝ²`:
   `B_{p,ι_#ν}(ιx, r) = (β_{p,ν}^E(x,r))^p` at every radius, and
   `S_{p,ι_#ν}^a(ιx) = S_{p,ν}^{a,E}(x)` at every endpoint `a > 0`;
2. Hausdorff sources are preserved: `ι_#(H¹⌊E) = H_P^1⌊ι(E)` for every Borel `E ⊆ ℝ²`. -/
def TimeSliceTransferStatement : Prop :=
  (∀ (ν : Measure Plane) (p : ℝ), 0 < p → ∀ T : FamilyKind, (T = .horizontal ∨ T = .mixed) →
    ∀ x : Plane,
      (∀ r : ℝ, betaPow (ν.map timeSlice) 1 T p (timeSlice x) r = euclideanBetaPow ν 1 p x r) ∧
        ∀ a : ℝ, 0 < a →
          energyS (ν.map timeSlice) 1 T p a (timeSlice x) = euclideanEnergyS ν 1 p a x) ∧
  ∀ E : Set Plane, MeasurableSet E →
    (μH[1].restrict E).map timeSlice = (hausdorffP 2 1).restrict (timeSlice '' E)

/-- The direct witness below two (part (a)). There is `E₋ ⊆ ℝ²` with `λ₋ = H¹⌊E₋` such that:
* `E₋` is compact, `H¹(E₋) = 1`, and `E₋` is purely one-unrectifiable;
* at every point of `E₋`, `1/2 ≤ limsup_{r↓0} λ₋(B(z,r))/r ≤ 2`;
* for every `0 < p < 2` and finite `a > 0`, `S_{p,λ₋}^{a,E}` is bounded on `E₋` by a finite
  constant depending on `p` and `a` only (finite everywhere, uniformly in the centre);
* on one common `λ₋`-full set, `S_{2,λ₋}^{a,E} = ∞` for every `a > 0` and the lower one-density is
  zero;
* transferred to `n = 2`, `k = 1`, `ι(E₋)` has `H_P^1`-null intersection with every horizontal
  graph of every finite slope, hence with every regular carrier (at `k = 1` there are no vertical
  graphs, and countable unions and Hausdorff-null residuals preserve nullity).
A "full-measure set" is any `G` with `λ₋(Gᶜ) = 0`; it may be shrunk to a Borel subset of `E₋`. -/
def DirectWitnessMinusStatement : Prop :=
  ∃ E : Set Plane, IsCompact E ∧ μH[1] E = 1 ∧ IsPurelyUnrectifiable E ∧
    (∀ z ∈ E, (2 : ℝ≥0∞)⁻¹ ≤ planarUpperDensity (μH[1].restrict E) z ∧
      planarUpperDensity (μH[1].restrict E) z ≤ 2) ∧
    (∀ p : ℝ, 0 < p → p < 2 → ∀ a : ℝ, 0 < a →
      ∃ B : ℝ, ∀ z ∈ E, euclideanEnergyS (μH[1].restrict E) 1 p a z ≤ ENNReal.ofReal B) ∧
    (∃ G : Set Plane, μH[1].restrict E Gᶜ = 0 ∧
      ∀ z ∈ G, (∀ a : ℝ, 0 < a → euclideanEnergyS (μH[1].restrict E) 1 2 a z = ⊤) ∧
        planarLowerDensity (μH[1].restrict E) z = 0) ∧
    ∀ (ε : ℝ) (G : HorizontalGraph 2 1 ε), hausdorffP 2 1 (timeSlice '' E ∩ G.image) = 0

/-- The direct witness above two (part (b)). There is `E₊ ⊆ ℝ²` with
`λ₊ = H¹⌊E₊` such that:
* `E₊` is a bounded Borel set which is a countable union of nondegenerate closed horizontal
  segments `[u_i,v_i] × {b_i}`;
* `1 ≤ H¹(E₊) ≤ 100/99`;
* `λ₊(B(z,r))/r → 2` as `r ↓ 0` for `λ₊`-almost every `z`;
* outside one countable set `Z`, every `z ∈ E₊` has `S_{p,λ₊}^{a,E}(z) = ∞` simultaneously for
  every `p > 2` and every `a > 0`;
* transferred to `n = 2`, `k = 1`, `ι(E₊)` is covered exactly (with no exceptional set) by
  countably many horizontal graphs of slope zero. -/
def DirectWitnessPlusStatement : Prop :=
  ∃ E : Set Plane, MeasurableSet E ∧ Bornology.IsBounded E ∧
    (∃ (I : Set ℕ) (u v b : I → ℝ), (∀ i, u i < v i) ∧
      E = ⋃ i, horizontalSegment (u i) (v i) (b i)) ∧
    1 ≤ μH[1] E ∧ μH[1] E ≤ ENNReal.ofReal (100 / 99) ∧
    (∀ᵐ z ∂(μH[1].restrict E),
      Tendsto (planarDensityRatio (μH[1].restrict E) z) (𝓝[>] 0) (𝓝 2)) ∧
    (∃ Z : Set Plane, Z.Countable ∧
      ∀ z ∈ E \ Z, ∀ p : ℝ, 2 < p → ∀ a : ℝ, 0 < a →
        euclideanEnergyS (μH[1].restrict E) 1 p a z = ⊤) ∧
    ∃ (I : Set ℕ) (G : I → HorizontalGraph 2 1 0), timeSlice '' E ⊆ ⋃ i, (G i).image

/-- **Direct Hausdorff-source counterexamples**: the two witnesses and the constant-time
transfer. -/
def DirectWitnessesStatement : Prop :=
  DirectWitnessMinusStatement ∧ DirectWitnessPlusStatement ∧ TimeSliceTransferStatement

/-- First failure. For `0 < p < 2` at `n = 2`, `k = 1` there is no nonnegative `Φ` with
`Φ(M) → 0` as `M ↓ 0` such that every locally Radon source with
`μ(P(0,1) ∩ {S_p^2 > M}) ≤ Γ` (`M > 0`, `Γ ≥ 0`) admits a nonnegative decomposition
`μ = μ⁺ + μ_G` with `μ⁺(P(0,1)) ≤ Φ(M) + Γ` and `μ_G` on a horizontally rectifiable compact
support. In particular no bound `C M^{p/2} + Γ` holds there. -/
def SpBelowTwoNoVanishingRemainderStatement : Prop :=
  ∀ p : ℝ, 0 < p → p < 2 →
    ¬ ∃ Φ : ℝ → ℝ, (∀ M, 0 ≤ Φ M) ∧ Tendsto Φ (𝓝[>] 0) (𝓝 0) ∧
      ∀ μ : Measure (Space 2), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 < M → 0 ≤ Γ →
        μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyS μ 1 .mixed p 2 z}) ≤
          ENNReal.ofReal Γ →
        ∃ (μplus μG : Measure (Space 2)) (K : Set (Space 2)),
          μ = μplus + μG ∧ μplus (Metric.ball (point 0 0) 1) ≤ ENNReal.ofReal (Φ M + Γ) ∧
          IsCompact K ∧ μG Kᶜ = 0 ∧
          ∃ (I : Set ℕ) (ε : I → ℝ) (G : ∀ i, HorizontalGraph 2 1 (ε i)),
            hausdorffP 2 1 (K \ ⋃ i, (G i).image) = 0

/-- Second failure. For `p > 2` at `n = 1`, `k = 2` there is no nonnegative `Φ` with
`Φ(M) → 0` as `M ↓ 0` such that every locally Radon source with
`μ(P(0,1) ∩ {T_p^2 > M}) ≤ Γ` (`M > 0`, `Γ ≥ 0`) admits a nonnegative decomposition
`μ = μ⁺ + μ_G` with `μ⁺(P(0,1)) ≤ Φ(M) + Γ` and `μ_G` carried by an arbitrary countably regular
carrier modulo an `H_P^2`-null set. -/
def TpAboveTwoNoVanishingRemainderStatement : Prop :=
  ∀ p : ℝ, 2 < p →
    ¬ ∃ Φ : ℝ → ℝ, (∀ M, 0 ≤ Φ M) ∧ Tendsto Φ (𝓝[>] 0) (𝓝 0) ∧
      ∀ μ : Measure (Space 1), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 < M → 0 ≤ Γ →
        μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyT μ 2 .mixed p 2 z}) ≤
          ENNReal.ofReal Γ →
        ∃ (μplus μG : Measure (Space 1)) (F : Set (Space 1)),
          μ = μplus + μG ∧ μplus (Metric.ball (point 0 0) 1) ≤ ENNReal.ofReal (Φ M + Γ) ∧
          μG Fᶜ = 0 ∧
          ∃ (I J : Set ℕ) (εH : I → ℝ) (H : ∀ i, HorizontalGraph 1 2 (εH i))
            (εV : J → ℝ) (V : ∀ j, GeneralRegularVerticalGraph 1 2 (εV j)),
            hausdorffP 1 2 (F \ ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)) = 0

/-- Third failure. For `p > 2` at `n = 1`, `k = 2` there is no nonnegative `Ψ` with
`Ψ(e) → 0` as `e ↓ 0` such that every locally Radon source with finite actual integrated energy
`e = ∫_{P(0,1)} T_{p,μ}^2 dμ` admits a decomposition of the kind in the second assertion with
`μ⁺(P(0,1)) ≤ Ψ(e)`. No monotonicity or value at zero is imposed on `Ψ`. -/
def TpAboveTwoNoIntegratedRemainderStatement : Prop :=
  ∀ p : ℝ, 2 < p →
    ¬ ∃ Ψ : ℝ → ℝ, (∀ e, 0 ≤ Ψ e) ∧ Tendsto Ψ (𝓝[>] 0) (𝓝 0) ∧
      ∀ μ : Measure (Space 1), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
        (∫⁻ z in Metric.ball (point 0 0) 1, energyT μ 2 .mixed p 2 z ∂μ) < ⊤ →
        ∃ (μplus μG : Measure (Space 1)) (F : Set (Space 1)),
          μ = μplus + μG ∧
          μplus (Metric.ball (point 0 0) 1) ≤
            ENNReal.ofReal (Ψ (∫⁻ z in Metric.ball (point 0 0) 1, energyT μ 2 .mixed p 2 z ∂μ).toReal) ∧
          μG Fᶜ = 0 ∧
          ∃ (I J : Set ℕ) (εH : I → ℝ) (H : ∀ i, HorizontalGraph 1 2 (εH i))
            (εV : J → ℝ) (V : ∀ j, GeneralRegularVerticalGraph 1 2 (εV j)),
            hausdorffP 1 2 (F \ ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)) = 0

/-- **Remainder failures outside the support ranges**:
the three negative statements, each in its stated dimension. -/
def BetaPFailuresStatement : Prop :=
  SpBelowTwoNoVanishingRemainderStatement ∧ TpAboveTwoNoVanishingRemainderStatement ∧
    TpAboveTwoNoIntegratedRemainderStatement

end ParabolicRectifiability.BetaP
