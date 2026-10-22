import ParabolicRectifiability.Analysis.TraceExtension.DensityTracePieces
import ParabolicRectifiability.Geometry.SubspaceCoordinates

/-! # Density pieces on the intrinsic base

`exists_density_pieces_intrinsic_proof` decomposes a compact set `K` of the intrinsic base,
up to a null set, into compact pieces on which the density is controlled.

Route: the coordinate theorem `exists_density_trace_pieces_proof` applied
to `Φ K` and `Φ G`, `Φ = subspaceParabolicIsometry W`, and pulled back along `Φ`. The map
`Φ` is a measure-preserving isometric equivalence, so it carries balls, closed balls and
the measure of arbitrary sets.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability

variable {n : ℕ}

/-- Preimages under `Φ` of arbitrary sets carry the same mass. -/
theorem rx1_intrinsicParabolicVolume_preimage (W : Submodule ℝ (Spatial n))
    (T : Set (Space (Module.finrank ℝ W))) :
    intrinsicParabolicVolume W (subspaceParabolicIsometry W ⁻¹' T) =
      parabolicVolume (Module.finrank ℝ W) T :=
  (subspaceParabolic_measurePreserving W).measure_preimage_equiv T

/-- Images under `Φ` of arbitrary sets carry the same mass. -/
theorem rx1_parabolicVolume_image (W : Submodule ℝ (Spatial n)) (S : Set (SubspaceSpace W)) :
    parabolicVolume (Module.finrank ℝ W) (subspaceParabolicIsometry W '' S) =
      intrinsicParabolicVolume W S := by
  rw [← rx1_intrinsicParabolicVolume_preimage,
    (subspaceParabolicIsometry W).injective.preimage_image]

/-- **Density pieces on the intrinsic base** (`exists_density_pieces_intrinsic`). -/
theorem exists_density_pieces_intrinsic_proof {n : ℕ} (W : Submodule ℝ (Spatial n))
    (K G : Set (SubspaceSpace W)) (hK : IsCompact K)
    (hG : intrinsicParabolicVolume W (K \ G) = 0) :
    ∃ (I : Set ℕ) (P : I → Set (SubspaceSpace W)) (x₀ : I → SubspaceSpace W) (ρ : I → ℝ),
      (∀ j, IsCompact (P j) ∧ P j ⊆ K ∩ G ∧ P j ⊆ Metric.closedBall (x₀ j) (ρ j) ∧
        0 < ρ j ∧ ρ j ≤ 1 / 64 ∧
        ∀ p ∈ P j, ∀ r : ℝ, 0 < r → r ≤ 64 * ρ j →
          intrinsicParabolicVolume W (Metric.ball p r) ≤
            2 * intrinsicParabolicVolume W (K ∩ Metric.ball p r)) ∧
      intrinsicParabolicVolume W (K \ ⋃ j, P j) = 0 := by
  set Φ := subspaceParabolicIsometry W with hΦ
  have hinj : Function.Injective Φ := Φ.injective
  have hG' : parabolicVolume (Module.finrank ℝ W) (Φ '' K \ Φ '' G) = 0 := by
    rw [← image_sdiff hinj, rx1_parabolicVolume_image]
    exact hG
  obtain ⟨I, P, x₀, ρ, hP, hnull⟩ :=
    exists_density_trace_pieces_proof (Module.finrank ℝ W) (Φ '' K) (Φ '' G)
      (hK.image Φ.continuous) hG'
  refine ⟨I, fun j => Φ ⁻¹' P j, fun j => Φ.symm (x₀ j), ρ, fun j => ?_, ?_⟩
  · obtain ⟨hc, hsub, hball, hρ, hρ', hdens⟩ := hP j
    refine ⟨Φ.toHomeomorph.isCompact_preimage.2 hc, ?_, ?_, hρ, hρ', ?_⟩
    · intro q hq
      have hq' := hsub hq
      exact ⟨hinj.mem_set_image.1 hq'.1, hinj.mem_set_image.1 hq'.2⟩
    · intro q hq
      rw [← Φ.preimage_closedBall]
      exact hball hq
    · intro q hq r hr hrρ
      have h := hdens (Φ q) hq r hr hrρ
      have hb : Φ ⁻¹' Metric.ball (Φ q) r = Metric.ball q r := Φ.isometry.preimage_ball q r
      have hKb : Φ ⁻¹' (Φ '' K ∩ Metric.ball (Φ q) r) = K ∩ Metric.ball q r := by
        rw [preimage_inter, hinj.preimage_image, hb]
      rw [← hKb, ← hb, rx1_intrinsicParabolicVolume_preimage,
        rx1_intrinsicParabolicVolume_preimage]
      exact h
  · have hset : K \ ⋃ j, Φ ⁻¹' P j = Φ ⁻¹' (Φ '' K \ ⋃ j, P j) := by
      rw [preimage_sdiff, preimage_iUnion, hinj.preimage_image]
    rw [hset, rx1_intrinsicParabolicVolume_preimage]
    exact hnull

end ParabolicRectifiability
