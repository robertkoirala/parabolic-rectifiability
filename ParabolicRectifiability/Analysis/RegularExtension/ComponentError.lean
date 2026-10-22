import ParabolicRectifiability.Analysis.TraceExtension.AffineError

/-! # Coordinate affine errors are bounded by the vector affine error

`affineErrorSq_component_le_proof` bounds the affine error of `ℓ ∘ f`, for a linear map `ℓ` of
norm at most one, by that of `f`. Every competitor `a + B u` for `f` gives the competitor `ℓ a + (ℓ ∘ B) u` for
`ℓ ∘ f`, pointwise no worse because `‖ℓ‖ ≤ 1`; integrate, then take infima. Nonpositive
radii give zero on both sides.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-- A continuous linear map of norm at most one does not increase extended norms. -/
theorem rx3_enorm_apply_le {Y Y' : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] (ℓ : Y →L[ℝ] Y') (hℓ : ‖ℓ‖ ≤ 1)
    (v : Y) : ‖ℓ v‖ₑ ≤ ‖v‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (by simpa using ℓ.le_of_opNorm_le hℓ v)

/-- **`affineErrorSq_component_le`**: the affine error of `ℓ ∘ f` is at most that of `f`
when `‖ℓ‖ ≤ 1`. -/
theorem affineErrorSq_component_le_proof {E Y Y' : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] (μ : Measure (E × Time))
    (ℓ : Y →L[ℝ] Y') (hℓ : ‖ℓ‖ ≤ 1) (f : E × Time → Y) (y : E × Time) (s : ℝ) :
    affineErrorSq μ (fun q => ℓ (f q)) y s ≤ affineErrorSq μ f y s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [affineErrorSq_of_nonpos μ _ y hs]
    exact zero_le
  · rw [affineErrorSq_of_pos μ _ y hs, affineErrorSq_of_pos μ f y hs]
    gcongr _ * ?_
    refine le_iInf fun a => le_iInf fun B => ?_
    refine iInf_le_of_le (ℓ a) (iInf_le_of_le (ℓ.comp B) ?_)
    unfold affineFitIntegral
    refine lintegral_mono fun q => ?_
    have hq : ℓ (f q) - (ℓ a + (ℓ.comp B) q.1) = ℓ (f q - (a + B q.1)) := by
      simp only [ContinuousLinearMap.comp_apply, map_sub, map_add]
    rw [hq]
    gcongr
    exact rx3_enorm_apply_le ℓ hℓ _

end ParabolicRectifiability
