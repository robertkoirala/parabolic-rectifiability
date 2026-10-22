import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Horizontal graph cover of the decorated segment set

Every labelled horizontal segment is contained in a horizontal graph over the first
coordinate line with slope zero, so the decorated segment set is covered by countably many
such graphs (`e2_sap_cover_proof`).
-/

noncomputable section

open Set

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.BetaP (Plane horizontalSegment timeSlice)

/-- Each genuine labelled segment has slope zero along the first coordinate line. -/
theorem e2_sap_cover_proof (hSG : E2sbSlopeGraph) : E2sapCover := by
  classical
  let e₀ : Plane := !₂[1, 0]
  let V : Submodule ℝ Plane := ℝ ∙ e₀
  have he₀ : e₀ ≠ 0 := by
    intro h
    have := congrArg (fun x : Plane => x 0) h
    norm_num [e₀] at this
  have hdim : Module.finrank ℝ V = 1 := finrank_span_singleton he₀
  have hsegment (u v b : ℝ) :
      ∃ Γ : HorizontalGraph 2 1 0, timeSlice '' horizontalSegment u v b ⊆ Γ.image := by
    apply hSG (horizontalSegment u v b) V 0 hdim (le_refl 0)
    intro x hx y hy
    have hxy : x - y ∈ V := by
      apply Submodule.mem_span_singleton.mpr
      refine ⟨x 0 - y 0, ?_⟩
      ext j
      fin_cases j
      · simp [e₀]
      · simp [e₀, hx.2.2, hy.2.2]
    rw [Submodule.starProjection_orthogonal_apply_eq_zero hxy]
    simp
  choose G hG using fun i : e2_sapIndex =>
    hsegment (e2_sapLeft i) (e2_sapRight i) (e2_sapHeight i)
  refine ⟨e2_sapIndex, G, ?_⟩
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨i, hG i (mem_image_of_mem timeSlice hi)⟩

end ParabolicRectifiability.Examples
