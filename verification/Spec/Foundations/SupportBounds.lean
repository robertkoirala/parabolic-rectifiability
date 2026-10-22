import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Analysis.HalfTimeDerivative.LocalRepresentation
import Spec.Analysis.ParabolicBMO
import Spec.Basic
import Spec.Foundations.Graphs
import Spec.Foundations.HalfTimeDerivative
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.Graphs
import Spec.Geometry.SubspaceCoordinates
import Spec.Metric.Hausdorff
import Spec.Metric.Measure
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Foundations.SupportBounds` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace ParabolicRectifiability.Foundations
/-- The support conclusions at centre `a` and scale `R`, with constant `C`, for the typed
supports `K_H`, `K_V` and `K = K_H ∪ K_V`: compact supports in the closed ball
`P̄(a,R)`, empty supports for unavailable types, typed graph covers at every positive
tolerance (vertical covers in the general regular class), the global Hausdorff bound
`C R^k`, and the local Hausdorff, separated-set, finite and countable packing bounds at
every scale `0 < s ≤ R`, and the tube bound `C R^k r^{n+2-k}` for `0 < r ≤ R`.

It contains no measure identity, no loss and no identification of `K_H`, `K_V` with
actual supports; see the module documentation. -/
structure HasRegularSupportBounds {n : ℕ} (k : ℕ) (C : ℝ) (a : Space n) (R : ℝ)
    (KH KV : Set (Space n)) : Prop where
  horizontal_compact : IsCompact KH
  vertical_compact : IsCompact KV
  horizontal_subset : KH ⊆ Metric.closedBall a R
  vertical_subset : KV ⊆ Metric.closedBall a R
  horizontal_unavailable : ¬ (1 ≤ k ∧ k ≤ n) → KH = ∅
  vertical_unavailable : ¬ (2 ≤ k ∧ k ≤ n + 2) → KV = ∅
  horizontal_graphs : ∀ ε : ℝ, 0 < ε → HasHorizontalGraphCover k KH ε
  vertical_graphs : ∀ ε : ℝ, 0 < ε → HasGeneralRegularVerticalGraphCover k KV ε
  hausdorff_total : hausdorffP n k (KH ∪ KV) ≤ ENNReal.ofReal (C * R ^ k)
  hausdorff_local : ∀ q s, 0 < s → s ≤ R →
    hausdorffP n k ((KH ∪ KV) ∩ Metric.ball q s) ≤ ENNReal.ofReal (C * s ^ k)
  separated : ∀ q s r, 0 < s → s ≤ R → 0 < r → r ≤ s →
    ∀ F : Finset (Space n), (↑F : Set (Space n)) ⊆ (KH ∪ KV) ∩ Metric.ball q s →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r ≤ dist x y) →
        (F.card : ℝ) ≤ C * (s / r) ^ k
  minkowski : ∀ r, 0 < r → r ≤ R →
    parabolicVolume n {z | Metric.infEDist z (KH ∪ KV) < ENNReal.ofReal r} ≤
      ENNReal.ofReal (C * R ^ k * r ^ (n + 2 - k))
  finite_packing : ∀ q s, 0 < s → s ≤ R →
    ∀ (l : ℕ) (z : Fin l → Space n) (r : Fin l → ℝ),
      (∀ i, z i ∈ (KH ∪ KV) ∩ Metric.ball q s) →
      (∀ i, 0 < r i ∧ r i ≤ s) →
      (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
      (∑ i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C * s ^ k)
  countable_packing : ∀ q s, 0 < s → s ≤ R →
    ∀ (I : Set ℕ) (z : I → Space n) (r : I → ℝ),
      (∀ i, z i ∈ (KH ∪ KV) ∩ Metric.ball q s) →
      (∀ i, 0 < r i ∧ r i ≤ s) →
      (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
      (∑' i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C * s ^ k)

end ParabolicRectifiability.Foundations
