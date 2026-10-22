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

/-! Specification: the definitions of `ParabolicRectifiability.Examples.Statements.Reductions` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace ParabolicRectifiability.Examples
open ParabolicRectifiability.Foundations
/-- Reductions, time slice. For `1 ≤ k ≤ n`, `p > 0`, a spatial Radon source `ν`, a time `t₀` and
`μ = (y ↦ (y,t₀))_# ν`, both the mixed and the horizontal beta-`p` satisfy
`B_{p,μ}((x,t₀),r) = r^{-k-p} inf_{U^k} ∫_{B(x,r)} dist(y,U)^p dν(y)` for every `x` and
`r > 0`; and the scale energies `S_p`, `T_p` at `(x,t₀)` equal their Euclidean counterparts
at every endpoint, finite (`0 < a`) or infinite (the supremum over endpoints). -/
def TimeSliceStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n → ∀ p : ℝ, 0 < p →
  ∀ ν : Measure (Spatial n), IsFiniteMeasureOnCompacts ν → ν.InnerRegular →
  ∀ t₀ : ℝ, ∀ T : FamilyKind, (T = .mixed ∨ T = .horizontal) →
    (∀ (x : Spatial n) (r : ℝ), 0 < r →
      betaPow (Measure.map (fun y : Spatial n => point y t₀) ν) k T p (point x t₀) r =
        Foundations.euclideanBetaPow ν k p x r) ∧
    (∀ a : ℝ, 0 < a → ∀ x : Spatial n,
      energyS (Measure.map (fun y : Spatial n => point y t₀) ν) k T p a (point x t₀) =
          Foundations.euclideanEnergyS ν k p a x ∧
        energyT (Measure.map (fun y : Spatial n => point y t₀) ν) k T p a (point x t₀) =
          Foundations.euclideanEnergyT ν k p a x) ∧
    (∀ x : Spatial n,
      (⨆ a : ℝ, energyS (Measure.map (fun y : Spatial n => point y t₀) ν) k T p a
          (point x t₀)) = ⨆ a : ℝ, Foundations.euclideanEnergyS ν k p a x ∧
        (⨆ a : ℝ, energyT (Measure.map (fun y : Spatial n => point y t₀) ν) k T p a
          (point x t₀)) = ⨆ a : ℝ, Foundations.euclideanEnergyT ν k p a x)

/-- Reductions, tube identity: for every spatial set `A`, every `t₀` and every `r > 0`,
`|{z : d_P(z, A × {t₀}) < r}| = 2 r² |{y : dist(y,A) < r}|`, with ambient volume
`L^{n+1} = parabolicVolume n` on the left and spatial Lebesgue measure on the right. -/
def TimeSliceTubeStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (A : Set (Spatial n)) (t₀ r : ℝ), 0 < r →
    parabolicVolume n
        {z | Metric.infEDist z ((fun y : Spatial n => point y t₀) '' A) < ENNReal.ofReal r} =
      ENNReal.ofReal (2 * r ^ 2) * volume {y : Spatial n | Metric.infEDist y A < ENNReal.ofReal r}

/-- Reductions, stationary product. For `0 ≤ m ≤ n - 1`, `k = m + 2`, a spatial Radon source `ν` and
`μ = ν ⊗ (L¹⌊[-1,1])` on `Space n`, at every `x`, `t ∈ [-1,1]` and `0 < r ≤ 2`, with
`ℓ = |(t-r², t+r²) ∩ [-1,1]|` and `b^E = b^E_{2,ν,m}(x,r)`:
`B_{2,μ,V}((x,t),r) = (ℓ / r²) b^E` and `(1/16) b^E ≤ B_{2,μ}((x,t),r) ≤ 2 b^E`. -/
def StationaryProductStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, m + 1 ≤ n →
  ∀ ν : Measure (Spatial n), IsFiniteMeasureOnCompacts ν → ν.InnerRegular →
  ∀ (x : Spatial n) (t r : ℝ), t ∈ Icc (-1 : ℝ) 1 → 0 < r → r ≤ 2 →
    betaSq (Measure.map (fun q : Spatial n × ℝ => point q.1 q.2)
          (ν.prod (volume.restrict (Icc (-1 : ℝ) 1)))) (m + 2) .vertical (point x t) r =
        volume (Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1) / ENNReal.ofReal r ^ 2 *
          Foundations.euclideanBetaPow ν m 2 x r ∧
      ENNReal.ofReal (1 / 16) * Foundations.euclideanBetaPow ν m 2 x r ≤
        betaSq (Measure.map (fun q : Spatial n × ℝ => point q.1 q.2)
          (ν.prod (volume.restrict (Icc (-1 : ℝ) 1)))) (m + 2) .mixed (point x t) r ∧
      betaSq (Measure.map (fun q : Spatial n × ℝ => point q.1 q.2)
          (ν.prod (volume.restrict (Icc (-1 : ℝ) 1)))) (m + 2) .mixed (point x t) r ≤
        2 * Foundations.euclideanBetaPow ν m 2 x r

/-- Reductions, stationary graphs. Let `W ⊆ ℝⁿ` be a linear subspace of dimension
`m ≤ n - 1` and `g : E → W^⊥` an `L`-Lipschitz map on an arbitrary subset `E ⊆ W` (a spatial
subset-domain graph piece). Then `g` has a full normal-valued spatial extension
`g̃ : W → W^⊥` with Lipschitz bound `√(n-m) L`, and its time-independent extension
`G(u,t) = g̃(u)` on `W × ℝ`
* has parabolic Lipschitz bound `√(n-m) L`;
* has zero homogeneous half-time derivative (the zero function represents it) with BMO
  seminorm zero;
* is general regular with norm at most `√(n-m) L`;
* and its graph `{(u + G(u,t), t)}` is the image of a full general regular vertical graph of
  dimension `k = m + 2` and norm at most `√(n-m) L`.
No nonemptiness is imposed on `E` (the McShane extension formula needs `E ≠ ∅`; for
`E = ∅` any constant extension works). -/
def StationaryGraphExtensionStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ W : Submodule ℝ (Spatial n), Module.finrank ℝ W + 1 ≤ n →
  ∀ (E : Set W) (g : E → Wᗮ) (L : ℝ≥0), LipschitzWith L g →
    ∃ g' : W → Wᗮ, (∀ u : E, g' u = g u) ∧
      LipschitzWith (NNReal.sqrt ((n - Module.finrank ℝ W : ℕ) : ℝ≥0) * L) g' ∧
      LipschitzWith (NNReal.sqrt ((n - Module.finrank ℝ W : ℕ) : ℝ≥0) * L)
        (fun q : SubspaceSpace W => g' q.1) ∧
      RepresentsGeneralHalfTimeDerivative W (fun q : SubspaceSpace W => g' q.1) (fun _ => 0) ∧
      HasParabolicBMOBound W (fun _ => 0) 0 ∧
      IsGeneralRegularVerticalFunction W (fun q : SubspaceSpace W => g' q.1)
        ((NNReal.sqrt ((n - Module.finrank ℝ W : ℕ) : ℝ≥0) * L : ℝ≥0) : ℝ) ∧
      ∃ Γ : GeneralRegularVerticalGraph n (Module.finrank ℝ W + 2)
          ((NNReal.sqrt ((n - Module.finrank ℝ W : ℕ) : ℝ≥0) * L : ℝ≥0) : ℝ),
        Γ.image = range (fun q : SubspaceSpace W => ((q.1 : Spatial n) + (g' q.1 : Spatial n), q.2))

/-- The exact reductions: the time-slice
identity and its tube identity, the stationary-product comparison, and the stationary graph
extensions. -/
def ReductionsStatement : Prop :=
  TimeSliceStatement ∧ TimeSliceTubeStatement ∧ StationaryProductStatement ∧
    StationaryGraphExtensionStatement

end ParabolicRectifiability.Examples
