import ParabolicRectifiability.Decomposition.Interfaces
import ParabolicRectifiability.Measure.FittingMinimum

/-! # Zero all-scale energy and an attained plane

The tail law for natural beta numbers and its use in the zero-threshold case of the
decomposition theorem. For a localized source whose support has diameter less
than one, every scale `r ≥ 1` sees the whole support, so on `(1,2)` the natural beta
is the global fitting error times `r^(-k-2)`. Zero all-scale energy at one support
point therefore forces the global fitting error to vanish, and the attained
minimizer contains the entire actual support. The zero source uses only the
availability of the family.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability

/-- If the all-scale square vanishes at a support point of a source with compact
support of diameter less than one, then the global fitting error vanishes. -/
theorem globalFittingError_eq_zero_of_allScaleEnergy_le_zero {n : ℕ}
    (ν : Measure (Space n)) (k : ℕ) (T : FamilyKind) (hc : IsCompact ν.support)
    (hd : Metric.diam ν.support < 1) {z : Space n} (hz : z ∈ ν.support)
    (hzero : allScaleEnergy ν k T z ≤ 0) :
    globalFittingError ν k T = 0 := by
  have hA := lintegral_betaSq_of_support_diam ν k T hc hd hz (Ioo (1 : ℝ) 2)
    measurableSet_Ioo (fun r hr => hr.1.le)
  rw [lintegral_inv_pow_Ioo_scaleMeasure (k + 2) (by omega) zero_lt_one one_le_two] at hA
  have hall : ∫⁻ r in Ioi (0 : ℝ), betaSq ν k T z r ∂scaleMeasure ≤ 0 := hzero
  have hsub : Ioo (1 : ℝ) 2 ⊆ Ioi 0 := fun r hr => zero_lt_one.trans hr.1
  have hann : ∫⁻ r in Ioo (1 : ℝ) 2, betaSq ν k T z r ∂scaleMeasure = 0 :=
    le_antisymm ((lintegral_mono_set hsub).trans hall) zero_le
  rw [hann] at hA
  have hpos : (0 : ℝ) <
      (((1 : ℝ) ^ (k + 2))⁻¹ - ((2 : ℝ) ^ (k + 2))⁻¹) / ((k + 2 : ℕ) : ℝ) := by
    have h2 : (1 : ℝ) < 2 ^ (k + 2) := one_lt_pow₀ (by norm_num) (by omega)
    have h3 : ((2 : ℝ) ^ (k + 2))⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2
    rw [one_pow, inv_one]
    exact div_pos (by linarith) (by positivity)
  rcases mul_eq_zero.mp hA.symm with h | h
  · exact absurd h (ENNReal.ofReal_pos.mpr hpos).ne'
  · exact h

/-- The statement `exists_model_containing_support_of_zero_energy`: zero all-scale energy
forces the actual compact localized support into one attained admissible model.
The zero source is covered by the availability of the family. -/
theorem modelContainingSupport_of_zeroEnergy {n k : ℕ}
    (_hk : 1 ≤ k) (_hkn : k ≤ n + 2) (T : FamilyKind)
    (hT : Nonempty (Models n k T)) (ν : Measure (Space n))
    (hν : IsFiniteMeasure ν) (_hreg : ν.InnerRegular)
    (c : Space n) (hc : ν.support ⊆ Metric.closedBall c (1 / 64))
    (henergy : ∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ 0) :
    ∃ L : Models n k T, ν.support ⊆ modelSet L := by
  have hK : IsCompact ν.support :=
    (isCompact_closedBall c (1 / 64)).of_isClosed_subset Measure.isClosed_support hc
  have hd : Metric.diam ν.support < 1 :=
    (Metric.diam_mono hc Metric.isBounded_closedBall).trans_lt
      ((Metric.diam_closedBall (by norm_num : (0 : ℝ) ≤ 1 / 64)).trans_lt (by norm_num))
  by_cases h0 : ν = 0
  · obtain ⟨L⟩ := hT
    refine ⟨L, ?_⟩
    rw [h0, Measure.support_zero]
    exact empty_subset _
  · have : (ae ν).NeBot := ae_neBot.mpr h0
    obtain ⟨z, hzE, hzS⟩ := (henergy.and ν.support_mem_ae).exists
    exact exists_modelSet_support_of_globalFittingError_eq_zero ν hT hK ν.support_mem_ae
      (globalFittingError_eq_zero_of_allScaleEnergy_le_zero ν k T hK hd hzS hzE)

end ParabolicRectifiability
