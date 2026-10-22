import ParabolicRectifiability.BetaP.Proofs.Counterexamples.Euclidean
import ParabolicRectifiability.Geometry.Graphs

/-! # Graph necessity and pure unrectifiability for the digit graph

Proposition definitions only. Target: `BetaP.belowTwoDigitWitness_pure_of_graphSource`, whose
inputs are `GraphSourceStatement`, the transfer `TimeSliceTransferStatement` and
`EnergyTwoStatement`. They are consumed as hypotheses (only `E2sbSliceGraphNull` takes
them); nothing here restates them.

The nine statements:
1. `E2sbSliceSource`: the time-zero image of a finite planar measure is locally Radon.
2. `E2sbSliceGraphNull`: where the planar `S_2^1` is infinite, the transfer (`p = 2`,
   horizontal family), `S_2 = S` and graph-source necessity make the time-zero image `H_P^1`-null
   on every horizontal graph of every finite slope.
3. `E2sbSliceHausdorff`: `ι = timeSlice` preserves one-dimensional Hausdorff measure of every set
   (the null rest of `E` has null image).
4. `E2sbLipschitzExtend` (scalar Lipschitz extension): a map Lipschitz on `A ⊆ ℝ`
   extends to a globally Lipschitz map `ℝ → ℝ²`.
5. `E2sbLipschitzNondiff` (Rademacher): the image of the nondifferentiability set is
   `H¹`-null.
6. `E2sbZeroDerivImage`: the image of the zero-derivative set is `H¹`-null.
7. `E2sbSmallSlopePieces`: the nonzero-derivative parameters split into countably
   many pieces whose images are `θ`-graphs over lines.
8. `E2sbSlopeGraph`: a planar `θ`-graph over a line, placed at time zero, lies in one
   horizontal graph of slope `θ`.
9. `E2sbPurity`: graph-intersection nullity gives pure one-unrectifiability.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.BetaP (Plane timeSlice IsPurelyUnrectifiable)

/-- **`E2sbSliceSource`.** For every finite measure `ν` on `ℝ²`, the time-zero
image `ι_#ν` on `ℝ² × ℝ` is finite on compacts and inner regular (the "locally Radon" hypotheses
of `GraphSourceStatement`). -/
def E2sbSliceSource : Prop :=
  ∀ ν : Measure Plane, IsFiniteMeasure ν →
    IsFiniteMeasureOnCompacts (ν.map timeSlice) ∧ (ν.map timeSlice).InnerRegular

/-- **`E2sbSliceGraphNull`.** For a finite
planar measure `ν` and a set `S` on which the planar `S_{2,ν}^{1,E}` is infinite, `ι(S)` meets
every horizontal graph `Γ` of every finite slope (at `n = 2`, `k = 1`) in an `H_P^1`-null set. -/
def E2sbSliceGraphNull : Prop :=
  ∀ ν : Measure Plane, IsFiniteMeasure ν → ∀ S : Set Plane,
    (∀ z ∈ S, euclideanEnergyS ν 1 2 1 z = ⊤) →
    ∀ (ε : ℝ) (Γ : HorizontalGraph 2 1 ε), hausdorffP 2 1 (timeSlice '' S ∩ Γ.image) = 0

/-- **`E2sbSliceHausdorff`.** `H_P^1(ι(S)) = H¹(S)` for every `S ⊆ ℝ²`. -/
def E2sbSliceHausdorff : Prop :=
  ∀ S : Set Plane, hausdorffP 2 1 (timeSlice '' S) = μH[1] S

/-- **`E2sbLipschitzExtend`.** Every map `f : ℝ → ℝ²` that is Lipschitz
on `A` agrees on `A` with a globally Lipschitz map. -/
def E2sbLipschitzExtend : Prop :=
  ∀ (A : Set ℝ) (f : ℝ → Plane) (K : ℝ≥0), LipschitzOnWith K f A →
    ∃ (F : ℝ → Plane) (K' : ℝ≥0), LipschitzWith K' F ∧ EqOn F f A

/-- **`E2sbLipschitzNondiff`.** For Lipschitz `F : ℝ → ℝ²`, the image
of the set where `F` is not differentiable is `H¹`-null. -/
def E2sbLipschitzNondiff : Prop :=
  ∀ (F : ℝ → Plane) (K : ℝ≥0), LipschitzWith K F →
    μH[1] (F '' {s | ¬ DifferentiableAt ℝ F s}) = 0

/-- **`E2sbZeroDerivImage`.** For every `F : ℝ → ℝ²`, the image of
`{s | F'(s) = 0}` is `H¹`-null (no Lipschitz hypothesis is needed). -/
def E2sbZeroDerivImage : Prop :=
  ∀ F : ℝ → Plane, μH[1] (F '' {s | HasDerivAt F 0 s}) = 0

/-- **`E2sbSmallSlopePieces`.** For every `F : ℝ → ℝ²` and `θ > 0`,
the parameters with a nonzero derivative are covered by countably many pieces `P i`, each with a
line direction `V i` such that, for `s, t ∈ P i`, the component of `F t - F s` normal to `V i` is
at most `θ` times its component along `V i`. -/
def E2sbSmallSlopePieces : Prop :=
  ∀ (F : ℝ → Plane) (θ : ℝ), 0 < θ →
    ∃ (P : ℕ → Set ℝ) (V : ℕ → Submodule ℝ Plane), (∀ i, Module.finrank ℝ (V i) = 1) ∧
      {s | ∃ v : Plane, v ≠ 0 ∧ HasDerivAt F v s} ⊆ ⋃ i, P i ∧
      ∀ i, ∀ s ∈ P i, ∀ t ∈ P i,
        ‖(V i)ᗮ.starProjection (F t - F s)‖ ≤ θ * ‖(V i).starProjection (F t - F s)‖

/-- **`E2sbSlopeGraph`.** A set `S ⊆ ℝ²` whose differences have normal
component at most `θ` times their component along a line direction `V` lies, at time zero, in
one horizontal graph over `V` of slope `θ` (`n = 2`, `k = 1`; zero time map). -/
def E2sbSlopeGraph : Prop :=
  ∀ (S : Set Plane) (V : Submodule ℝ Plane) (θ : ℝ), Module.finrank ℝ V = 1 → 0 ≤ θ →
    (∀ x ∈ S, ∀ y ∈ S, ‖Vᗮ.starProjection (x - y)‖ ≤ θ * ‖V.starProjection (x - y)‖) →
    ∃ Γ : HorizontalGraph 2 1 θ, timeSlice '' S ⊆ Γ.image

/-- **`E2sbPurity`.** A planar set whose time-zero image meets every
horizontal graph of every finite slope in an `H_P^1`-null set is purely one-unrectifiable. -/
def E2sbPurity : Prop :=
  ∀ E : Set Plane, (∀ (ε : ℝ) (Γ : HorizontalGraph 2 1 ε),
      hausdorffP 2 1 (timeSlice '' E ∩ Γ.image) = 0) → IsPurelyUnrectifiable E

end ParabolicRectifiability.Examples
