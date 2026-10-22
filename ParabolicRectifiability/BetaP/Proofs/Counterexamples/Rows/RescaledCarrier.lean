import ParabolicRectifiability.BetaP.Proofs.Counterexamples.RowStatements
import ParabolicRectifiability.Foundations.Proofs.Similarity.CoverTransport
import ParabolicRectifiability.Foundations.Proofs.Similarity.MeasureTransport

/-! # Carrier nullity after rescaling

`C2RescaledCarrierNullStatement`. The rescaled source is
`(ofReal R)⁻¹ ^ 1 • (H_P^1⌊A).map S`. For compact (hence Borel) `K` its mass is
`R⁻¹ · H(A ∩ S⁻¹' K)`. Cover `S⁻¹' K` by `S⁻¹'(K \ ⋃ G_i)` (null by `H(S⁻¹' N) = R · H(N)`) and the
countably many `S⁻¹'(G_i.image) = (fsimb5_horizontalGraph …).image`, each null against `A` by the
hypothesis. -/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.BetaP

theorem c2_rescaled_carrier_null_proof : C2RescaledCarrierNullStatement := by
  intro A hA hnull q R hR K hK ⟨I, ε, G, hres⟩
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hmeas : Measurable (similarity q R hR) := (similarity q R hR).continuous.measurable
  have hres' : hausdorffP 2 1 (similarity q R hR ⁻¹' (K \ ⋃ i, (G i).image)) = 0 := by
    rw [Foundations.fsim_hausdorffP_preimage_similarity_proof, hres, mul_zero]
  have hG : ∀ i : I, hausdorffP 2 1 (similarity q R hR ⁻¹' (G i).image ∩ A) = 0 := by
    intro i
    have h := hnull (ε i) (Foundations.fsimb5_horizontalGraph q R hR (G i))
    rw [Foundations.fsimb5_horizontalGraph_image, Homeomorph.image_symm] at h
    rwa [inter_comm]
  have hsub : similarity q R hR ⁻¹' K ∩ A ⊆
      similarity q R hR ⁻¹' (K \ ⋃ i, (G i).image) ∪ ⋃ i : I, (similarity q R hR ⁻¹' (G i).image ∩ A) := by
    intro x ⟨hxK, hxA⟩
    by_cases hx : similarity q R hR x ∈ ⋃ i, (G i).image
    · right
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, hi, hxA⟩
    · left
      exact ⟨hxK, hx⟩
  have hnullA : hausdorffP 2 1 (similarity q R hR ⁻¹' K ∩ A) = 0 :=
    measure_mono_null hsub (measure_union_null hres' (measure_iUnion_null hG))
  unfold rescaledSource
  rw [Measure.smul_apply, Measure.map_apply hmeas hKm, Measure.restrict_apply (hmeas hKm), hnullA,
    smul_zero]

end ParabolicRectifiability.BetaP
