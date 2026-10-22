import ParabolicRectifiability.IntegralCanonical.Defs

/-! # Statements: the canonical decomposition, its density bridge, type separation, guards

The `Prop`-valued statements `IntrinsicSourceOfDensityStatement` (density bridge),
`CanonicalDecompositionStatement`, `TypeSeparationStatement` and `CanonicalGuardsStatement`.
Their proofs are `isIntrinsicSource_of_upperDensity`, `canonical_decomposition`,
`type_separation` and `canonical_guards`.

Conventions. The standing assumptions `1 ≤ n`, `1 ≤ k ≤ n + 2`, `μ` locally Radon
(`IsFiniteMeasureOnCompacts μ` and `μ.InnerRegular`) and `0 < R` are hypotheses. `E_H`, `E_V`, `G` are `finiteEnergySet μ k T R` for
`T = .horizontal, .vertical, .mixed`, `E_+ = pureSet μ k R`, and `μ_H, μ_V, μ_+` are
`horizontalPart`, `verticalPart`, `purePart`. Typed rectifiable measures are Foundations'
`IsRegularlyRectifiableMeasure .horizontal/.vertical`; covers at a tolerance are
`HasTypedMeasureCover`. The examples accompanying the guard remarks are not formalized.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

/-- **Density bridge.** For a locally Radon `μ`,
`0 < Θ^{k,*}(μ,z) < ∞` at `μ`-almost every `z` implies the intrinsic source class. No finite-square hypothesis is used. -/
def IntrinsicSourceOfDensityStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    HasPositiveFiniteUpperDensity k μ → IsIntrinsicSource k μ

/-- The conclusions of the canonical decomposition theorem for the source `μ`, dimension `k` and
endpoint `R`. Every field is a conclusion of the corollary.
* `measurable_*`, `*_locallyRadon`: the restrictions are locally Radon Borel restrictions.
* `overlap_null`, `exhaustion_null`: `μ(E_H ∩ E_V) = 0`, `μ(G \ (E_H ∪ E_V)) = 0`.
* `measure_eq`, `singular_*`: `μ = μ_H + μ_V + μ_+`, pairwise mutually singular.
* `horizontal_rectifiable`, `vertical_rectifiable`: horizontally, respectively regularly
  vertically, rectifiable.
* `horizontal_covers`, `vertical_covers`: for every `ε > 0` a countable cover of the measure
  by graphs of its type with slope, respectively total seminorm, at most `ε`.
* `pure_graphPure`, `pure_null_union`: `μ_+` gives outer measure zero to every finite-slope
  horizontal graph and every finite-norm full general regular vertical graph, hence to
  every countable union of such graphs.
* `unique`: any nonnegative decomposition `μ = ρ_H + ρ_V + ρ_P` into a horizontally
  rectifiable, a regularly vertically rectifiable and a graph-pure measure equals
  `(μ_H, μ_V, μ_+)`; mutual singularity of the competitor is not assumed.
* `endpoint_independent`: the canonical measures do not depend on the positive finite
  endpoint. -/
structure IsCanonicalDecomposition {n : ℕ} (k : ℕ) (μ : Measure (Space n)) (R : ℝ) :
    Prop where
  measurable_horizontal : MeasurableSet (finiteEnergySet μ k .horizontal R)
  measurable_vertical : MeasurableSet (finiteEnergySet μ k .vertical R)
  measurable_pure : MeasurableSet (pureSet μ k R)
  overlap_null :
    μ (finiteEnergySet μ k .horizontal R ∩ finiteEnergySet μ k .vertical R) = 0
  exhaustion_null :
    μ (finiteEnergySet μ k .mixed R \
      (finiteEnergySet μ k .horizontal R ∪ finiteEnergySet μ k .vertical R)) = 0
  horizontal_locallyRadon :
    IsFiniteMeasureOnCompacts (horizontalPart μ k R) ∧ (horizontalPart μ k R).InnerRegular
  vertical_locallyRadon :
    IsFiniteMeasureOnCompacts (verticalPart μ k R) ∧ (verticalPart μ k R).InnerRegular
  pure_locallyRadon :
    IsFiniteMeasureOnCompacts (purePart μ k R) ∧ (purePart μ k R).InnerRegular
  measure_eq : μ = horizontalPart μ k R + verticalPart μ k R + purePart μ k R
  singular_horizontal_vertical : horizontalPart μ k R ⟂ₘ verticalPart μ k R
  singular_horizontal_pure : horizontalPart μ k R ⟂ₘ purePart μ k R
  singular_vertical_pure : verticalPart μ k R ⟂ₘ purePart μ k R
  horizontal_rectifiable : IsRegularlyRectifiableMeasure .horizontal k (horizontalPart μ k R)
  vertical_rectifiable : IsRegularlyRectifiableMeasure .vertical k (verticalPart μ k R)
  horizontal_covers :
    ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover .horizontal k (horizontalPart μ k R) ε
  vertical_covers :
    ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover .vertical k (verticalPart μ k R) ε
  pure_graphPure : IsGraphPure k (purePart μ k R)
  pure_null_union :
    ∀ (I J : Set ℕ) (εH : I → ℝ) (H : ∀ i, HorizontalGraph n k (εH i))
      (εV : J → ℝ) (V : ∀ j, GeneralRegularVerticalGraph n k (εV j)),
      purePart μ k R ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image) = 0
  unique :
    ∀ ρH ρV ρP : Measure (Space n), μ = ρH + ρV + ρP →
      IsRegularlyRectifiableMeasure .horizontal k ρH →
      IsRegularlyRectifiableMeasure .vertical k ρV →
      IsGraphPure k ρP →
        ρH = horizontalPart μ k R ∧ ρV = verticalPart μ k R ∧ ρP = purePart μ k R
  endpoint_independent :
    ∀ R' : ℝ, 0 < R' →
      horizontalPart μ k R' = horizontalPart μ k R ∧
        verticalPart μ k R' = verticalPart μ k R ∧ purePart μ k R' = purePart μ k R

/-- **Canonical decomposition**, with its density
formulation: for `n ≥ 1`, `1 ≤ k ≤ n+2` and a locally Radon `μ` in the intrinsic source
class or with `0 < Θ^{k,*}(μ,·) < ∞` `μ`-a.e., every positive finite endpoint
`R` gives the canonical decomposition `IsCanonicalDecomposition k μ R`. -/
def CanonicalDecompositionStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    (IsIntrinsicSource k μ ∨ HasPositiveFiniteUpperDensity k μ) →
    ∀ R : ℝ, 0 < R → IsCanonicalDecomposition k μ R

/-- **Type separation.** The geometric separation of types.

For `2 ≤ k ≤ n`, an ordinary full vertical graph `V` over `W × ℝ`, `dim W = k - 2`, with
parabolic Lipschitz constant (at most) `L` (Foundations' `OrdinaryVerticalGraph n k L`), and
a horizontal graph `H` of slope (at most) `ε` with `ε ≤ 1` and `L ε ≤ 1/2`:
* the spatial projection `P_W` (`Submodule.orthogonalProjectionOnto`) is injective on
  `H ∩ V`;
* its inverse has `d_P`-Lipschitz constant at most `2(1+L)`, from the Euclidean distance on
  `W` to `d_P`: `d_P(p,q) ≤ 2(1+L) |P_W p - P_W q|` on `H ∩ V`;
* `H_P^k(H ∩ V) = 0` (outer measure; no measurability of the intersection is assumed);
* if `k = 2`, the intersection has at most one point. -/
def TypeSeparationStatement : Prop :=
  ∀ n k : ℕ, 2 ≤ k → k ≤ n →
  ∀ (L : ℝ) (V : OrdinaryVerticalGraph n k L) (ε : ℝ) (H : HorizontalGraph n k ε),
    ε ≤ 1 → L * ε ≤ 1 / 2 →
      Set.InjOn (fun p : Space n => V.direction.orthogonalProjectionOnto p.1)
          (H.image ∩ V.image) ∧
        (∀ p ∈ H.image ∩ V.image, ∀ q ∈ H.image ∩ V.image,
          dist p q ≤ 2 * (1 + L) *
            dist (V.direction.orthogonalProjectionOnto p.1)
              (V.direction.orthogonalProjectionOnto q.1)) ∧
        hausdorffP n k (H.image ∩ V.image) = 0 ∧
        (k = 2 → (H.image ∩ V.image).Subsingleton)

/-- **Guards**, precise claims only. In the standing setting
(`n ≥ 1`, `1 ≤ k ≤ n+2`, `μ` locally Radon, `0 < R`):
* at `k = 1`, `E_V = ∅`;
* at `k = n+1`, `E_H = ∅`;
* at `k = n+2`, under the source-class assumption, `(μ_H, μ_V, μ_+) = (0, μ, 0)`;
* for `μ = 0`, the overlap `E_H ∩ E_V` has source mass zero, although the finite-energy
  sets may overlap literally: when both families are available
  (`2 ≤ k ≤ n`), `E_H ∩ E_V = X`.
The remark's examples are not formalized. -/
def CanonicalGuardsStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ R : ℝ, 0 < R →
    (k = 1 → finiteEnergySet μ k .vertical R = ∅) ∧
    (k = n + 1 → finiteEnergySet μ k .horizontal R = ∅) ∧
    (k = n + 2 → IsIntrinsicSource k μ →
      horizontalPart μ k R = 0 ∧ verticalPart μ k R = μ ∧ purePart μ k R = 0) ∧
    (μ = 0 →
      μ (finiteEnergySet μ k .horizontal R ∩ finiteEnergySet μ k .vertical R) = 0 ∧
        (2 ≤ k → k ≤ n →
          finiteEnergySet μ k .horizontal R ∩ finiteEnergySet μ k .vertical R = univ))

end ParabolicRectifiability.IntegralCanonical
