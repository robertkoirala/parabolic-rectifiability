import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Statements
import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTestStatements
import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.GraphHausdorffFinite

/-! # Dense atoms: the closed cylinder is not regularly rectifiable

Finite Hausdorff measure on bounded graph patches implies ambient nullity. Countable
unions give nullity of each graph and of the mixed cover; the Hausdorff-null residual
is ambient null as well. This contradicts the supplied positive cylinder volume.
All measures are evaluated as outer measures; graph domains need not be measurable.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- A set with finite Hausdorff measure in each ball is ambient null under the
nonambient finite-Hausdorff nullity principle. -/
theorem e2_ambientNull_of_locallyFinite_hausdorffP {n k : ℕ}
    (hnull : ∀ K : Set (Space n), hausdorffP n k K < ⊤ → parabolicVolume n K = 0)
    (S : Set (Space n))
    (hfinite : ∀ R : ℝ, hausdorffP n k (S ∩ Metric.ball (point 0 0) R) < ⊤) :
    parabolicVolume n S = 0 := by
  apply measure_mono_null (t := ⋃ m : ℕ, S ∩ Metric.ball (point 0 0) (m : ℝ))
  · intro x hx
    obtain ⟨m, hm⟩ := exists_nat_gt (dist x (point (0 : Spatial n) 0))
    exact mem_iUnion.mpr ⟨m, hx, hm⟩
  · exact measure_iUnion_null fun m => hnull _ (hfinite m)

/-- The non-rectifiability implication, using only ambient nullity and cylinder volume. -/
theorem e2_dense_notRectifiable_proof :
    E2AmbientNullStatement → E2DenseVolumeStatement → E2DenseNotRectifiableStatement := by
  intro hamb hvol n _hn k _hk hkn hrect
  obtain ⟨I, J, H, V, hres⟩ := hrect 1 one_pos
  have hnull := (hamb n k hkn).1
  have hH : ∀ i : I, parabolicVolume n (H i).image = 0 := by
    intro i
    exact e2_ambientNull_of_locallyFinite_hausdorffP hnull _
      (fun R => fgenv_horizontal_hausdorffP_inter_ball_lt_top_proof n k 1 (H i) (point 0 0) R)
  have hV : ∀ j : J, parabolicVolume n (V j).image = 0 := by
    intro j
    exact e2_ambientNull_of_locallyFinite_hausdorffP hnull _
      (fun R => fgenv_vertical_hausdorffP_inter_ball_lt_top_proof n k 1 (V j) (point 0 0) R)
  have hcover : parabolicVolume n ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image) = 0 :=
    measure_union_null (measure_iUnion_null hH) (measure_iUnion_null hV)
  have hrem : parabolicVolume n
      (Metric.closedBall (point (0 : Spatial n) 0) (1 / 4) \
        ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)) = 0 := by
    apply hnull
    rw [hres]
    exact ENNReal.zero_lt_top
  have hD : parabolicVolume n (Metric.closedBall (point (0 : Spatial n) 0) (1 / 4)) = 0 := by
    apply measure_mono_null (t :=
      (Metric.closedBall (point (0 : Spatial n) 0) (1 / 4) \
        ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)) ∪
          ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image))
    · intro x hx
      by_cases hc : x ∈ (⋃ i, (H i).image) ∪ ⋃ j, (V j).image
      · exact Or.inr hc
      · exact Or.inl ⟨hx, hc⟩
    · exact measure_union_null hrem hcover
  exact (ne_of_gt (hvol n)) hD

end ParabolicRectifiability.Examples
