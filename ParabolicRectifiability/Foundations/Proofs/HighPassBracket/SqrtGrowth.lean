import Mathlib

/-! # Proof of `fhpa_integrable_sqrtGrowth_mul_decay`

Pure real analysis: split `ℝ` into `Iio (-S)`, `Icc (-S) S`, `Ioi S`. On the middle piece the
integrand is bounded and the measure finite; on the two tails it is dominated by
`C (|a| s^(-5/2) + |b| s^(-2))`, `s = |t|`, integrable on `Ioi S` and, by reflection, on
`Iio (-S)`. -/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Foundations

theorem fhpab5_sqrt_mul_rpow {s : ℝ} (hs : 0 < s) :
    Real.sqrt s * s ^ (-5 / 2 : ℝ) = s ^ (-2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs]
  norm_num

/-- The tail domination at `s = |t| > S`. -/
theorem fhpab5_tail_bound (g : ℝ → ℝ) (a b : ℝ)
    (hgrowth : ∀ t : ℝ, |g t| ≤ a + b * Real.sqrt |t|) (f : ℝ → ℂ) (C S : ℝ) (hS : 0 < S)
    (htail : ∀ t : ℝ, S < |t| → ‖f t‖ ≤ C * |t| ^ (-5 / 2 : ℝ)) (t : ℝ) (ht : S < |t|) :
    ‖(g t : ℂ) * f t‖ ≤
      C * |a| * |t| ^ (-5 / 2 : ℝ) + C * |b| * |t| ^ (-2 : ℝ) := by
  have hs : 0 < |t| := hS.trans ht
  have hg : |g t| ≤ |a| + |b| * Real.sqrt |t| := by
    refine (hgrowth t).trans ?_
    have h1 : a ≤ |a| := le_abs_self a
    have h2 : b * Real.sqrt |t| ≤ |b| * Real.sqrt |t| :=
      mul_le_mul_of_nonneg_right (le_abs_self b) (Real.sqrt_nonneg _)
    linarith
  have hf := htail t ht
  have hp : 0 ≤ |t| ^ (-5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |g t| * ‖f t‖ ≤ (|a| + |b| * Real.sqrt |t|) * (C * |t| ^ (-5 / 2 : ℝ)) :=
        mul_le_mul hg hf (norm_nonneg _) (by positivity)
    _ = C * |a| * |t| ^ (-5 / 2 : ℝ) + C * |b| * (Real.sqrt |t| * |t| ^ (-5 / 2 : ℝ)) := by
        ring
    _ = _ := by rw [fhpab5_sqrt_mul_rpow hs]

theorem fhpa_integrable_sqrtGrowth_mul_decay_proof (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ)
    (hgrowth : ∀ t : ℝ, |g t| ≤ a + b * Real.sqrt |t|) (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f) (C S : ℝ) (hS : 0 < S) (hbound : ∀ t : ℝ, ‖f t‖ ≤ C)
    (htail : ∀ t : ℝ, S < |t| → ‖f t‖ ≤ C * |t| ^ (-5 / 2 : ℝ)) :
    Integrable (fun t : ℝ => (g t : ℂ) * f t) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound 0)
  have hFm : AEStronglyMeasurable (fun t : ℝ => (g t : ℂ) * f t) :=
    (Complex.continuous_ofReal.comp hg).aestronglyMeasurable.mul hf
  set M : ℝ → ℝ := fun s => C * |a| * s ^ (-5 / 2 : ℝ) + C * |b| * s ^ (-2 : ℝ) with hM
  have hMI : IntegrableOn M (Ioi S) :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-5 / 2 : ℝ) < -1) hS).const_mul
        (C * |a|)).add
      ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hS).const_mul (C * |b|))
  have hMI' : IntegrableOn (fun t => M (-t)) (Iio (-S)) := by
    have h : IntegrableOn M (Ioi (-(-S))) := by rwa [neg_neg]
    exact h.comp_neg_Iio
  have hbd := fhpab5_tail_bound g a b hgrowth f C S hS htail
  have hpos : IntegrableOn (fun t : ℝ => (g t : ℂ) * f t) (Ioi S) := by
    refine Integrable.mono' hMI hFm.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have h1 : S < |t| := by rwa [abs_of_pos (hS.trans ht)]
    have := hbd t h1
    rwa [abs_of_pos (hS.trans ht)] at this
  have hneg : IntegrableOn (fun t : ℝ => (g t : ℂ) * f t) (Iio (-S)) := by
    refine Integrable.mono' hMI' hFm.restrict ?_
    refine (ae_restrict_iff' measurableSet_Iio).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : t < 0 := lt_trans ht (by linarith)
    have h1 : S < |t| := by rw [abs_of_neg ht']; exact lt_neg.1 ht
    have := hbd t h1
    rwa [abs_of_neg ht'] at this
  have hmid : IntegrableOn (fun t : ℝ => (g t : ℂ) * f t) (Icc (-S) S) := by
    refine Measure.integrableOn_of_bounded (M := (|a| + |b| * Real.sqrt S) * C)
      (by simp) hFm ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have hts : |t| ≤ S := abs_le.2 ⟨ht.1, ht.2⟩
    have hg1 : |g t| ≤ |a| + |b| * Real.sqrt S := by
      refine (hgrowth t).trans ?_
      have h1 : a ≤ |a| := le_abs_self a
      have h2 : b * Real.sqrt |t| ≤ |b| * Real.sqrt S :=
        mul_le_mul (le_abs_self b) (Real.sqrt_le_sqrt hts) (Real.sqrt_nonneg _) (abs_nonneg _)
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hg1 (hbound t) (norm_nonneg _) (by positivity)
  have hU : (univ : Set ℝ) = Iio (-S) ∪ Icc (-S) S ∪ Ioi S := by
    ext t
    simp only [mem_univ, mem_union, mem_Iio, mem_Icc, mem_Ioi, true_iff]
    rcases lt_or_ge t (-S) with h | h
    · exact Or.inl (Or.inl h)
    · rcases le_or_gt t S with h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr h'
  rw [← integrableOn_univ, hU, integrableOn_union, integrableOn_union]
  exact ⟨⟨hneg, hmid⟩, hpos⟩

end ParabolicRectifiability.Foundations
