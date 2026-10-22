import ParabolicRectifiability.IntegralCanonical.Statements.Canonical

/-! # Auxiliary statements for the canonical decomposition

Statements of the intermediate results behind the density bridge
(`isIntrinsicSource_of_hasPositiveFiniteUpperDensity`) and the type separation
(`horizontalGraph_inter_ordinaryVerticalGraph_separation`) of the canonical decomposition:
a Borel sigma-finite carrier from positive upper density, the separation inequality on the
intersection of a horizontal and an ordinary vertical graph, and the nullity of sets on which
the parabolic distance is controlled by a projection to a `(k-2)`-dimensional subspace.

This file contains proposition definitions only.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

/-- **Carrier from positive density.** For a locally Radon `μ` with `Θ^{k,*}(μ,·) > 0`
`μ`-a.e., there is a Borel sigma-finite `H_P^k` carrier. This is the conclusion of
`Characterization.hasBorelSigmaFiniteHausdorffCarrier_of_upperDensity_pos` once its two
hypotheses are supplied by `Foundations.fupdom_upper_density_domination` and
`Foundations.fmeas1_density_measurability`. -/
def i2_UpperDensityCarrierStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    (∀ᵐ z ∂μ, 0 < upperDensity μ k z) → HasBorelSigmaFiniteHausdorffCarrier k μ

/-- **Separation inequality.** For `2 ≤ k ≤ n`,
an ordinary full vertical graph `V` with parabolic Lipschitz constant at most `L` and a
horizontal graph `H` of slope at most `ε` with `ε ≤ 1` and `L ε ≤ 1/2` (no sign condition on
`ε`): any two points `p, q` of `H ∩ V` satisfy
`d_P(p,q) ≤ 2(1+L) |P_W p_x - P_W q_x|`, `W = V.direction`. -/
def i2_SeparationInequalityStatement : Prop :=
  ∀ n k : ℕ, 2 ≤ k → k ≤ n →
  ∀ (L : ℝ) (V : OrdinaryVerticalGraph n k L) (ε : ℝ) (H : HorizontalGraph n k ε),
    ε ≤ 1 → L * ε ≤ 1 / 2 →
      ∀ p ∈ H.image ∩ V.image, ∀ q ∈ H.image ∩ V.image,
        dist p q ≤ 2 * (1 + L) *
          dist (V.direction.orthogonalProjectionOnto p.1)
            (V.direction.orthogonalProjectionOnto q.1)

/-- **Projection-Lipschitz sets are null.** A set `S ⊆ X` on which the parabolic
distance is bounded by a constant times the Euclidean distance of the spatial projections to a
subspace `W` of dimension `k - 2` is `H_P^k`-null (outer measure; no measurability of `S`, no
sign condition on `C`). -/
def i2_ProjectionLipschitzNullStatement : Prop :=
  ∀ (n k : ℕ) (W : Submodule ℝ (Spatial n)), Module.finrank ℝ W + 2 = k →
  ∀ (S : Set (Space n)) (C : ℝ),
    (∀ p ∈ S, ∀ q ∈ S,
      dist p q ≤ C * dist (W.orthogonalProjectionOnto p.1) (W.orthogonalProjectionOnto q.1)) →
    hausdorffP n k S = 0

end ParabolicRectifiability.IntegralCanonical
