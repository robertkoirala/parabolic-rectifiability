import ParabolicRectifiability.Geometry.CompactModels
import ParabolicRectifiability.Measure.BetaTail

/-! # Attained fitting error for compact-carried sources

Clamping anchors and horizontal times to a box containing the source decreases
every fitting cost. The continuous fitting functional therefore has a minimum
on the compact bounded model family, and that minimum is global.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability

/-- A compact carrier supplies one positive testing radius and bounds for both
ordinary coordinates, including when the carrier is empty. -/
theorem compact_carrier_bounds {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) :
    ∃ R > 0, K ⊆ Metric.ball (point (0 : Spatial n) 0) R ∧
      ∀ z ∈ K, ‖z.1‖ ≤ R ∧ |z.2.val| ≤ R ^ 2 := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (point (0 : Spatial n) 0)
  refine ⟨R, hR, hKR, ?_⟩
  intro z hz
  have hb := (mem_ball_point (0 : Spatial n) z.1 0 z.2.val R hR).mp (hKR hz)
  simpa only [sub_zero] using And.intro hb.1.le hb.2.le

/-- Every available family attains the full original-measure fitting error.
No nonzero-mass or unique-minimizer hypothesis is needed. -/
theorem exists_globalFittingError_minimizer {n k : ℕ} {F : FamilyKind}
    (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (hF : Nonempty (Models n k F)) {K : Set (Space n)}
    (hK : IsCompact K) (hμK : ∀ᵐ z ∂μ, z ∈ K) :
    ∃ L : Models n k F,
      (∫⁻ z, modelCost L z ∂μ) = globalFittingError μ k F ∧
      (∫⁻ z, modelCost L z ∂μ) < ⊤ := by
  obtain ⟨R, hR, hKR, hbounds⟩ := compact_carrier_bounds hK
  have hball : ∀ᵐ z ∂μ, z ∈ Metric.ball (point (0 : Spatial n) 0) R :=
    hμK.mono fun z hz => hKR hz
  have heq (L : Models n k F) :=
    fit_eq_global_of_ae_mem_ball μ L (point (0 : Spatial n) 0) R hball
  obtain ⟨L, hL, hmin⟩ := (isCompact_boundedModels n k F R (R ^ 2)).exists_isMinOn
    (boundedModels_nonempty hF R (R ^ 2) hR.le (sq_nonneg R))
    (continuous_fit μ (point (0 : Spatial n) 0) R).continuousOn
  have hglobal (Q : Models n k F) :
      (∫⁻ z, modelCost L z ∂μ) ≤ ∫⁻ z, modelCost Q z ∂μ := by
    let Q' := clampModel Q R (R ^ 2) (sq_nonneg R)
    have hQ' : Q' ∈ boundedModels n k F R (R ^ 2) :=
      clampModel_mem_bounded Q R (R ^ 2) hR.le (sq_nonneg R)
    calc
      (∫⁻ z, modelCost L z ∂μ) ≤ ∫⁻ z, modelCost Q' z ∂μ := by
        have hh := hmin hQ'
        change fit μ L (point (0 : Spatial n) 0) R ≤
          fit μ Q' (point (0 : Spatial n) 0) R at hh
        simpa only [heq] using hh
      _ ≤ ∫⁻ z, modelCost Q z ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hμK] with z hz
        exact modelCost_clampModel_le Q R (R ^ 2) hR.le (sq_nonneg R) z
          (hbounds z hz).1 (hbounds z hz).2
  refine ⟨L, le_antisymm (le_iInf hglobal) (iInf_le _ L), ?_⟩
  rw [← heq L]
  exact (fit_ne_top μ L (point (0 : Spatial n) 0) R).lt_top

theorem globalFittingError_lt_top_of_compact_carrier {n k : ℕ} {F : FamilyKind}
    (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (hF : Nonempty (Models n k F)) {K : Set (Space n)}
    (hK : IsCompact K) (hμK : ∀ᵐ z ∂μ, z ∈ K) :
    globalFittingError μ k F < ⊤ := by
  obtain ⟨L, hL, hfin⟩ := exists_globalFittingError_minimizer μ hF hK hμK
  rwa [← hL]

/-- Zero integral of the actual squared distance forces the entire support into
the closed model, including source atoms on Hausdorff-null sets. -/
theorem support_subset_modelSet_of_integral_eq_zero {n k : ℕ} {F : FamilyKind}
    (μ : Measure (Space n)) (L : Models n k F)
    (hzero : (∫⁻ z, modelCost L z ∂μ) = 0) : μ.support ⊆ modelSet L := by
  have hm : Measurable (modelCost L) := Metric.continuous_infEDist.measurable.pow_const 2
  have hae := (lintegral_eq_zero_iff hm).mp hzero
  apply μ.support_subset_of_isClosed (modelSet_isClosed L)
  filter_upwards [hae] with z hz
  apply (Metric.mem_iff_infEDist_zero_of_closed (modelSet_isClosed L)).mpr
  exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hz

theorem exists_modelSet_support_of_globalFittingError_eq_zero
    {n k : ℕ} {F : FamilyKind} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (hF : Nonempty (Models n k F)) {K : Set (Space n)}
    (hK : IsCompact K) (hμK : ∀ᵐ z ∂μ, z ∈ K)
    (hzero : globalFittingError μ k F = 0) :
    ∃ L : Models n k F, μ.support ⊆ modelSet L := by
  obtain ⟨L, hL, _⟩ := exists_globalFittingError_minimizer μ hF hK hμK
  exact ⟨L, support_subset_modelSet_of_integral_eq_zero μ L (hL.trans hzero)⟩

theorem exists_globalFittingError_minimizer_of_compact_support
    {n k : ℕ} {F : FamilyKind} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (hF : Nonempty (Models n k F)) (hμ : IsCompact μ.support) :
    ∃ L : Models n k F,
      (∫⁻ z, modelCost L z ∂μ) = globalFittingError μ k F ∧
      (∫⁻ z, modelCost L z ∂μ) < ⊤ :=
  exists_globalFittingError_minimizer μ hF hμ μ.support_mem_ae

end ParabolicRectifiability
