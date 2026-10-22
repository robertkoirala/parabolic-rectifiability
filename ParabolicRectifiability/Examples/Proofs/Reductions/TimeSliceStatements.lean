import ParabolicRectifiability.Examples.Statements.Reductions

/-! # Named statements of the shared time-slice identity

Definitions and proposition definitions only; the proofs are given separately.

The slice identity is shared: the time-slice transfer for the sharpness statements
specializes it at `n = 2`, `k = 1`, `t₀ = 0`, and `TimeSliceStatement` assembles it at every
endpoint. The tube identity is the `TimeSliceTubeStatement` itself (proved as
`e2_timeSlice_tube`).

Statements:
1. `E2AffineEnlargementStatement`: every affine spatial `q`-plane lies in an affine spatial
   `m`-plane for `q ≤ m ≤ n`.
2. `E2TimeSliceBetaPowStatement` (the statement of `e2_timeSlice_betaPow`): for **every** measure `ν` on `ℝⁿ`, `1 ≤ k ≤ n`, `p > 0`, every `t₀`, the
   horizontal or mixed family, every `x` and **every real** `r`,
   `B_{p,ι_#ν}(ιx, r) = b^E_{p,ν,k}(x,r)` with `ι y = (y,t₀)`. It is stated in
   implication form over 1.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- **Affine enlargement.** For `q ≤ m ≤ n`, every affine spatial
`q`-plane of `ℝⁿ` is contained in some affine spatial `m`-plane. -/
def E2AffineEnlargementStatement : Prop :=
  ∀ (n q m : ℕ), q ≤ m → m ≤ n → ∀ U : AffineSpatialPlane n q,
    ∃ U' : AffineSpatialPlane n m, U.toSet ⊆ U'.toSet

/-- **The shared slice identity.**
Arbitrary measure `ν` (no finiteness or regularity), `1 ≤ k ≤ n`, `p > 0`, any time `t₀`, the
horizontal or mixed family, every centre `x` and every real radius `r` (both sides vanish for
`r ≤ 0`). -/
def E2TimeSliceBetaPowStatement : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → k ≤ n → ∀ (ν : Measure (Spatial n)) (p : ℝ), 0 < p →
    ∀ (t₀ : ℝ) (T : FamilyKind), (T = .horizontal ∨ T = .mixed) →
    ∀ (x : Spatial n) (r : ℝ),
      betaPow (ν.map (fun y : Spatial n => point y t₀)) k T p (point x t₀) r =
        euclideanBetaPow ν k p x r

end ParabolicRectifiability.Examples
