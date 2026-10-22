import ParabolicRectifiability.Foundations.Proofs.Similarity.RegularClassCovariance
import ParabolicRectifiability.Foundations.Proofs.HighPassBracket.Assembly
import ParabolicRectifiability.Enhancements.Statements.ScaledCore

/-! # Local core decomposition of a rescaled source

`sc2c_isLocalCoreDecomposition_of_rescaledSource` has exactly the type of
`Enhancements.isLocalCoreDecomposition_of_rescaledSource`: if a source is decomposed on
`P(a,R)`, its rescaling by the similarity `S` is decomposed at scale `1`. It has no external
hypothesis: the regular-class covariance uses `fhpa_halfTimeBracketIntegrable`.

The measure-theoretic fields and the loss identity are assembled from elementary facts on
pushforwards of measures under the similarity, proved below with the prefix `sc2c_` and
without any graph-domain data.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Enhancements.ScaledCoreTree

open ParabolicRectifiability.Foundations

/-! ## Elementary measure-theoretic facts (prefix `sc2c_`) -/

/-- Evaluation of `ν = R^{-k} S_# μ` on any set. -/
theorem sc2c_measure_rescaledSource_apply {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (a : Space n) (R : ℝ) (hR : 0 < R) (A : Set (Space n)) :
    rescaledSource μ k a R hR A = (ENNReal.ofReal R)⁻¹ ^ k * μ (similarity a R hR ⁻¹' A) := by
  rw [rescaledSource, Measure.smul_apply, smul_eq_mul]
  congr 1
  exact (similarity a R hR).toMeasurableEquiv.map_apply A

theorem sc2c_similarity_apply_self {n : ℕ} (a : Space n) (R : ℝ) (hR : 0 < R) :
    similarity a R hR a = point 0 0 := by
  simp [similarity_apply]

/-- `S⁻¹' P(0,1) = P(a,R)`. -/
theorem sc2c_preimage_similarity_unitBall {n : ℕ} (a : Space n) (R : ℝ) (hR : 0 < R) :
    similarity a R hR ⁻¹' Metric.ball (point 0 0) 1 = Metric.ball a R := by
  rw [← sc2c_similarity_apply_self a R hR, preimage_similarity_ball, mul_one]

/-- `S.symm 0 = a`. -/
theorem sc2c_similarity_symm_zero {n : ℕ} (a : Space n) (R : ℝ) (hR : 0 < R) :
    (similarity a R hR).symm (point 0 0) = a := by
  rw [← sc2c_similarity_apply_self a R hR, Homeomorph.symm_apply_apply]

/-- The restriction decomposition for two disjoint Borel sets. -/
theorem sc2c_restrict_partition {n : ℕ} (μ : Measure (Space n)) {EH EV : Set (Space n)}
    (hH : MeasurableSet EH) (hV : MeasurableSet EV) (hd : Disjoint EH EV) :
    μ = μ.restrict (EH ∪ EV)ᶜ + μ.restrict EH + μ.restrict EV := by
  rw [add_assoc, ← Measure.restrict_union hd hV, add_comm,
    Measure.restrict_add_restrict_compl (hH.union hV)]

/-- A pulled-back restriction vanishes exactly when the rescaled restriction does. -/
theorem sc2c_restrict_preimage_eq_zero_iff {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (a : Space n) (R : ℝ) (hR : 0 < R) (A : Set (Space n)) :
    μ.restrict (similarity a R hR ⁻¹' A) = 0 ↔ (rescaledSource μ k a R hR).restrict A = 0 := by
  rw [Measure.restrict_eq_zero, Measure.restrict_eq_zero, sc2c_measure_rescaledSource_apply]
  have h0 : (ENNReal.ofReal R)⁻¹ ^ k ≠ 0 :=
    pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    exact (mul_eq_zero.mp h).resolve_left h0

/-! ## The rescaled decomposition -/

/-- **Local core decomposition of a rescaled source.** Exactly the type of
`Enhancements.isLocalCoreDecomposition_of_rescaledSource`. The pulled-back sets are Borel,
disjoint and inside `P(a,R)`; the restriction decomposition holds for any two disjoint Borel
sets; the vanishing clauses transfer because `μ⌊S⁻¹'(A)` vanishes exactly when `ν⌊A` does and
the actual supports are identified; the support bundle, the Hausdorff and time laws and the
covers are transported through the similarity at `b = 0`, `ρ = 1` (with the regular-class
covariance, using `fhpa_halfTimeBracketIntegrable`); the loss identity is
`μ(S⁻¹'(B)) = R^k ν(B)`. -/
theorem sc2c_isLocalCoreDecomposition_of_rescaledSource {n k : ℕ}
    (_hn : 1 ≤ n) (_hk : 1 ≤ k) (hkn : k ≤ n + 2)
    (μ : Measure (Space n)) (_hμ : IsFiniteMeasureOnCompacts μ) (_hreg : μ.InnerRegular)
    (a : Space n) (R : ℝ) (hR : 0 < R) (T : FamilyKind) (C : ℝ) (D : RetainedSets n)
    (hunH : ¬ (1 ≤ k ∧ k ≤ n) →
      D.horizontalMeasure (rescaledSource μ k a R hR) = 0 ∧
        D.horizontalSupport (rescaledSource μ k a R hR) = ∅)
    (hunV : ¬ (2 ≤ k ∧ k ≤ n + 2) →
      D.verticalMeasure (rescaledSource μ k a R hR) = 0 ∧
        D.verticalSupport (rescaledSource μ k a R hR) = ∅)
    (honlyH : T = .horizontal →
      D.verticalMeasure (rescaledSource μ k a R hR) = 0 ∧
        D.verticalSupport (rescaledSource μ k a R hR) = ∅)
    (honlyV : T = .vertical →
      D.horizontalMeasure (rescaledSource μ k a R hR) = 0 ∧
        D.horizontalSupport (rescaledSource μ k a R hR) = ∅)
    (hS : HasRegularSupportBounds k C (point 0 0) 1
      (D.horizontalSupport (rescaledSource μ k a R hR))
      (D.verticalSupport (rescaledSource μ k a R hR))) :
    Enhancements.IsLocalCoreDecomposition k T C a R μ
        (similarity a R hR ⁻¹' D.horizontal) (similarity a R hR ⁻¹' D.vertical) ∧
      μ.restrict (similarity a R hR ⁻¹' D.horizontal ∪ similarity a R hR ⁻¹' D.vertical)ᶜ
          (Metric.ball a R) =
        ENNReal.ofReal R ^ k *
          D.remainderMeasure (rescaledSource μ k a R hR) (Metric.ball (point 0 0) 1) := by
  have hH := fsim_hausdorffP_preimage_similarity n k a R hR
  have hT := fsim_parabolicVolume_thickening_preimage_similarity a R hR
  have hregS : ∀ (W : Submodule ℝ (Spatial n)) (F : SubspaceSpace W → W.orthogonal) (ε : ℝ),
      IsGeneralRegularVerticalFunction W F ε →
        IsGeneralRegularVerticalFunction W
          (fun p => R • F (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking a.2.val)
            R p)) ε :=
    fun W F ε h => fsim_isGeneralRegularVerticalFunction_baseSimilarity
      fhpa_halfTimeBracketIntegrable W R hR a.2.val F ε h
  have eH : (μ.restrict (similarity a R hR ⁻¹' D.horizontal)).support =
      similarity a R hR ⁻¹' D.horizontalSupport (rescaledSource μ k a R hR) :=
    fsim_support_restrict_preimage_similarity μ k a R hR D.horizontal
  have eV : (μ.restrict (similarity a R hR ⁻¹' D.vertical)).support =
      similarity a R hR ⁻¹' D.verticalSupport (rescaledSource μ k a R hR) :=
    fsim_support_restrict_preimage_similarity μ k a R hR D.vertical
  have hmH : MeasurableSet (similarity a R hR ⁻¹' D.horizontal) :=
    D.measurable_horizontal.preimage (similarity a R hR).continuous.measurable
  have hmV : MeasurableSet (similarity a R hR ⁻¹' D.vertical) :=
    D.measurable_vertical.preimage (similarity a R hR).continuous.measurable
  have hdisj : Disjoint (similarity a R hR ⁻¹' D.horizontal) (similarity a R hR ⁻¹' D.vertical) :=
    D.disjoint.preimage (similarity a R hR)
  have hball := sc2c_preimage_similarity_unitBall a R hR
  have hzeroH : (rescaledSource μ k a R hR).restrict D.horizontal = 0 →
      D.horizontalSupport (rescaledSource μ k a R hR) = ∅ →
      μ.restrict (similarity a R hR ⁻¹' D.horizontal) = 0 ∧
        (μ.restrict (similarity a R hR ⁻¹' D.horizontal)).support = ∅ := by
    intro h1 h2
    refine ⟨(sc2c_restrict_preimage_eq_zero_iff μ k a R hR _).mpr h1, ?_⟩
    rw [eH, h2, preimage_empty]
  have hzeroV : (rescaledSource μ k a R hR).restrict D.vertical = 0 →
      D.verticalSupport (rescaledSource μ k a R hR) = ∅ →
      μ.restrict (similarity a R hR ⁻¹' D.vertical) = 0 ∧
        (μ.restrict (similarity a R hR ⁻¹' D.vertical)).support = ∅ := by
    intro h1 h2
    refine ⟨(sc2c_restrict_preimage_eq_zero_iff μ k a R hR _).mpr h1, ?_⟩
    rw [eV, h2, preimage_empty]
  have hbundle : HasRegularSupportBounds k C a R
      (similarity a R hR ⁻¹' D.horizontalSupport (rescaledSource μ k a R hR))
      (similarity a R hR ⁻¹' D.verticalSupport (rescaledSource μ k a R hR)) := by
    have h := fsim_hasRegularSupportBounds_preimage_similarity hkn C a R hR hH hT (point 0 0) 1
      _ _ hS
      (fun ε hε => fsim_hasHorizontalGraphCover_preimage_similarity a R hR hH _ ε
        (hS.horizontal_graphs ε hε))
      (fun ε hε => fsim_hasGeneralRegularVerticalGraphCover_preimage_similarity a R hR hH hregS
        _ ε (hS.vertical_graphs ε hε))
    rwa [sc2c_similarity_symm_zero, mul_one] at h
  refine ⟨
    { measurable_horizontal := hmH
      measurable_vertical := hmV
      disjoint := hdisj
      horizontal_subset := (preimage_mono D.horizontal_subset).trans hball.subset
      vertical_subset := (preimage_mono D.vertical_subset).trans hball.subset
      measure_eq := sc2c_restrict_partition μ hmH hmV hdisj
      horizontal_unavailable := fun hu => hzeroH (hunH hu).1 (hunH hu).2
      vertical_unavailable := fun hu => hzeroV (hunV hu).1 (hunV hu).2
      horizontal_only := fun hT' => hzeroV (honlyH hT').1 (honlyH hT').2
      vertical_only := fun hT' => hzeroH (honlyV hT').1 (honlyV hT').2
      supports := by
        rw [eH, eV]
        exact hbundle }, ?_⟩
  have key := sc2c_measure_rescaledSource_apply μ k a R hR
    (Metric.ball (point 0 0) 1 ∩ (D.horizontal ∪ D.vertical)ᶜ)
  have hpre : similarity a R hR ⁻¹' (Metric.ball (point 0 0) 1 ∩ (D.horizontal ∪ D.vertical)ᶜ) =
      Metric.ball a R ∩
        (similarity a R hR ⁻¹' D.horizontal ∪ similarity a R hR ⁻¹' D.vertical)ᶜ := by
    rw [preimage_inter, preimage_compl, preimage_union, hball]
  have h0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  rw [Measure.restrict_apply measurableSet_ball, RetainedSets.remainderMeasure,
    Measure.restrict_apply measurableSet_ball, key, hpre, ← mul_assoc, ← mul_pow,
    ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top, one_pow, one_mul]

end ParabolicRectifiability.Enhancements.ScaledCoreTree
