import ParabolicRectifiability.Examples.Proofs.DigitGraph.PureUnrectifiabilityStatements
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The image of the zero-derivative set has zero length

For a bounded part of the critical set, Gouëzel's measurable ambient partition
in Mathlib gives restrictions approximating the zero linear map to any prescribed
positive precision. Each restriction is therefore Lipschitz with that precision.
The disjoint ambient pieces bound the sum of their domain lengths by the length
of the bounding interval, without requiring the critical set to be measurable.
Letting the precision tend to zero and exhausting the real line finishes the proof.
-/

open MeasureTheory MeasureTheory.Measure Metric Filter Set
open scoped ENNReal NNReal Topology

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.BetaP (Plane)

private theorem bounded_zero_deriv_image_le (F : ℝ → Plane) (s : Set ℝ)
    (hF : ∀ x ∈ s, HasDerivAt F 0 x) (R : ℝ)
    (hs : s ⊆ closedBall 0 R) (ε : ℝ≥0) (hε : 0 < ε) :
    μH[1] (F '' s) ≤ ε * volume (closedBall (0 : ℝ) R) := by
  rcases eq_empty_or_nonempty s with rfl | hne
  · simp
  have hderiv : ∀ x ∈ s, HasFDerivWithinAt F (0 : ℝ →L[ℝ] Plane) s x := by
    intro x hx
    simpa using (hF x hx).hasFDerivAt.hasFDerivWithinAt
  obtain ⟨t, A, hdisj, hmeas, hcover, happ, hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F s
      (fun _ => (0 : ℝ →L[ℝ] Plane)) hderiv (fun _ => ε) (fun _ => hε.ne')
  have hlip (n : ℕ) : LipschitzOnWith ε F (s ∩ t n) := by
    obtain ⟨y, hy, heq⟩ := hA hne n
    have h := (happ n).lipschitzOnWith
    simpa [heq] using h
  calc
    μH[1] (F '' s) ≤ μH[1] (⋃ n, F '' (s ∩ t n)) := by
      apply measure_mono
      rw [← image_iUnion, ← inter_iUnion]
      exact image_mono (subset_inter Subset.rfl hcover)
    _ ≤ ∑' n, μH[1] (F '' (s ∩ t n)) := measure_iUnion_le _
    _ ≤ ∑' n, (ε : ℝ≥0∞) * volume (s ∩ t n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      simpa only [ENNReal.rpow_one, hausdorffMeasure_real] using
        (hlip n).hausdorffMeasure_image_le (d := 1) zero_le_one
    _ ≤ ε * ∑' n, volume (closedBall (0 : ℝ) R ∩ t n) := by
      rw [ENNReal.tsum_mul_left]
      gcongr
    _ = ε * volume (⋃ n, closedBall (0 : ℝ) R ∩ t n) := by
      rw [measure_iUnion]
      · exact pairwise_disjoint_mono hdisj fun n => inter_subset_right
      · intro n
        exact measurableSet_closedBall.inter (hmeas n)
    _ ≤ ε * volume (closedBall (0 : ℝ) R) := by
      grw [← inter_iUnion, inter_subset_left]

private theorem bounded_zero_deriv_image_null (F : ℝ → Plane) (s : Set ℝ)
    (hF : ∀ x ∈ s, HasDerivAt F 0 x) (R : ℝ) (hs : s ⊆ closedBall 0 R) :
    μH[1] (F '' s) = 0 := by
  have hlim : Tendsto
      (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * volume (closedBall (0 : ℝ) R))
      (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto
        (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * volume (closedBall (0 : ℝ) R))
        (𝓝 0) (𝓝 (((0 : ℝ≥0) : ℝ≥0∞) * volume (closedBall (0 : ℝ) R))) :=
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id)
        (Or.inr MeasureTheory.measure_closedBall_lt_top.ne)
    simp only [zero_mul, ENNReal.coe_zero] at h
    exact Tendsto.mono_left h nhdsWithin_le_nhds
  rw [← nonpos_iff_eq_zero]
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact bounded_zero_deriv_image_le F s hF R hs ε hε

/-- Every real-parameter planar map sends its zero-derivative set to a set of
zero one-dimensional Hausdorff measure, without a global regularity assumption. -/
theorem e2_sb_zeroDerivImage_proof : E2sbZeroDerivImage := by
  intro F
  let s : Set ℝ := {x | HasDerivAt F 0 x}
  change μH[1] (F '' s) = 0
  rw [← iUnion_inter_closedBall_nat s 0, image_iUnion]
  apply measure_iUnion_null
  intro n
  exact bounded_zero_deriv_image_null F (s ∩ closedBall 0 n)
    (fun x hx => hx.1) n inter_subset_right

end ParabolicRectifiability.Examples
