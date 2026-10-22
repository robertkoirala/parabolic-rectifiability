import ParabolicRectifiability.Enhancements.Proofs.Scaling.RescaledCoreDecomposition
import ParabolicRectifiability.Foundations.Proofs.Similarity.DomainData

/-! # Local enhanced decomposition of a rescaled source

`isLocalEnhancedDecomposition_of_rescaledSource_of_leaves` has exactly the type of
`Enhancements.isLocalEnhancedDecomposition_of_rescaledSource`. It has no external hypothesis.

Ingredients:
* every field except `graph_domains`, and the loss identity, come from
  `ScaledCoreTree.sc2c_isLocalCoreDecomposition_of_rescaledSource`;
* the actual supports are identified by `fsim_support_restrict_preimage_similarity`; the
  Hausdorff law is `fsim_hausdorffP_preimage_similarity`; the regular-class covariance is
  `fsim_isGeneralRegularVerticalFunction_baseSimilarity`, using `fhpa_halfTimeBracketIntegrable`.

`hasScaledGraphDomainCover_preimage_similarity` is the cover transport: from a cover with mesh
`δ/R` and absolute charges at scale `1`, and the exact identities of the transported typed data,
it gives a cover of the pulled-back supports with mesh `δ`, the same bound `C`, unchanged
relative estimates and absolute charges at scale `R`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Enhancements.ScalingTree

open ParabolicRectifiability.Foundations

/-! ## Graph-domain covers at scale `R` -/

/-- **Graph-domain covers of the pulled-back supports.** From a cover of `(K_H, K_V)` with
mesh `δ/R`, bound `C` and absolute charges at scale `1`, and the exact scaling identities of the
transported typed data and of the Hausdorff measure, one obtains a cover of
`(S⁻¹' K_H, S⁻¹' K_V)` with mesh `δ`, the same bound `C`, unchanged relative estimates, and
absolute charges `C R^k` and `C s^k` for `0 < s ≤ R`. (For the mesh one uses `δ/R` in the unit
construction.) -/
theorem hasScaledGraphDomainCover_preimage_similarity {n k : ℕ} {C ε δ : ℝ} (a : Space n)
    (R : ℝ) (hR : 0 < R)
    (hH : ∀ A : Set (Space n),
      hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
    {KH KV : Set (Space n)}
    (hdataH : ∀ D : HorizontalDomainData n k ε (δ / R) KH,
      ∃ D' : HorizontalDomainData n k ε δ (similarity a R hR ⁻¹' KH),
        (∀ U : Set (Space n),
          D'.traceVolume U = ENNReal.ofReal R ^ k * D.traceVolume (similarity a R hR '' U)) ∧
        D'.totalCharge = ENNReal.ofReal R ^ k * D.totalCharge ∧
        ∀ (q : Space n) (s : ℝ),
          D'.localCharge q s = ENNReal.ofReal R ^ k * D.localCharge (similarity a R hR q) (s / R))
    (hdataV : ∀ D : VerticalDomainData n k ε (δ / R) KV,
      ∃ D' : VerticalDomainData n k ε δ (similarity a R hR ⁻¹' KV),
        (∀ U : Set (Space n),
          D'.traceVolume U = ENNReal.ofReal R ^ k * D.traceVolume (similarity a R hR '' U)) ∧
        D'.totalCharge = ENNReal.ofReal R ^ k * D.totalCharge ∧
        ∀ (q : Space n) (s : ℝ),
          D'.localCharge q s = ENNReal.ofReal R ^ k * D.localCharge (similarity a R hR q) (s / R))
    (h : HasScaledGraphDomainCover k KH KV C ε (δ / R) 1) :
    HasScaledGraphDomainCover k (similarity a R hR ⁻¹' KH) (similarity a R hR ⁻¹' KV)
      C ε δ R := by
  obtain ⟨G, hT, hTH, hTV, hloc⟩ := h
  obtain ⟨Dh, hDht, hDhc, hDhl⟩ := hdataH G.horizontal
  obtain ⟨Dv, hDvt, hDvc, hDvl⟩ := hdataV G.vertical
  have hU : ∀ U : Set (Space n),
      (similarity a R hR ⁻¹' KH ∪ similarity a R hR ⁻¹' KV) ∩ U =
        similarity a R hR ⁻¹' ((KH ∪ KV) ∩ similarity a R hR '' U) := by
    intro U
    rw [preimage_inter, preimage_union, (similarity a R hR).preimage_image]
  have hK : similarity a R hR ⁻¹' KH ∪ similarity a R hR ⁻¹' KV =
      similarity a R hR ⁻¹' (KH ∪ KV) := preimage_union.symm
  have hball : ∀ (q : Space n) (s : ℝ),
      (similarity a R hR ⁻¹' KH ∪ similarity a R hR ⁻¹' KV) ∩ Metric.ball q (2 * s) =
        similarity a R hR ⁻¹'
          ((KH ∪ KV) ∩ Metric.ball (similarity a R hR q) (2 * (s / R))) := by
    intro q s
    have hRs : R * (2 * (s / R)) = 2 * s := by
      field_simp
    rw [preimage_inter, preimage_union, preimage_similarity_ball, hRs]
  have hrel : ∀ A : Set (Space n),
      ENNReal.ofReal R ^ k * (ENNReal.ofReal C * hausdorffP n k A) =
        ENNReal.ofReal C * hausdorffP n k (similarity a R hR ⁻¹' A) := by
    intro A
    rw [hH A, mul_left_comm]
  have habs : ∀ x : ℝ≥0∞, x ≤ ENNReal.ofReal (C * 1 ^ k) →
      ENNReal.ofReal R ^ k * x ≤ ENNReal.ofReal (C * R ^ k) := by
    intro x hx
    calc ENNReal.ofReal R ^ k * x ≤ ENNReal.ofReal R ^ k * ENNReal.ofReal (C * 1 ^ k) :=
          mul_le_mul' le_rfl hx
      _ = ENNReal.ofReal (C * R ^ k) := by
        rw [one_pow, mul_one, ← ENNReal.ofReal_pow hR.le,
          ← ENNReal.ofReal_mul (pow_nonneg hR.le k), mul_comm]
  have habsl : ∀ (s : ℝ) (x : ℝ≥0∞), x ≤ ENNReal.ofReal (C * (s / R) ^ k) →
      ENNReal.ofReal R ^ k * x ≤ ENNReal.ofReal (C * s ^ k) := by
    intro s x hx
    have hRk : R ^ k ≠ 0 := pow_ne_zero k hR.ne'
    calc ENNReal.ofReal R ^ k * x ≤ ENNReal.ofReal R ^ k * ENNReal.ofReal (C * (s / R) ^ k) :=
          mul_le_mul' le_rfl hx
      _ = ENNReal.ofReal (C * s ^ k) := by
        rw [← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul (pow_nonneg hR.le k)]
        congr 1
        rw [div_pow]
        field_simp
  let G' : GraphDomainCover n k C ε δ (similarity a R hR ⁻¹' KH) (similarity a R hR ⁻¹' KV) :=
    { horizontal := Dh
      vertical := Dv
      trace_le := fun U hU' => by
        rw [hDht U, hDvt U, ← mul_add, hU U, ← hrel]
        exact mul_le_mul' le_rfl
          (G.trace_le _ ((similarity a R hR).measurableEmbedding.measurableSet_image.mpr hU'))
      totalCharge_le := by
        rw [hDhc, hDvc, ← mul_add, hK, ← hrel]
        exact mul_le_mul' le_rfl G.totalCharge_le
      horizontal_totalCharge_le := by
        rw [hDhc, hK, ← hrel]
        exact mul_le_mul' le_rfl G.horizontal_totalCharge_le
      vertical_totalCharge_le := by
        rw [hDvc, hK, ← hrel]
        exact mul_le_mul' le_rfl G.vertical_totalCharge_le
      localCharge_le := fun q s hs => by
        rw [hDhl, hDvl, ← mul_add, hball q s, ← hrel]
        exact mul_le_mul' le_rfl (G.localCharge_le _ _ (div_pos hs hR))
      horizontal_localCharge_le := fun q s hs => by
        rw [hDhl, hball q s, ← hrel]
        exact mul_le_mul' le_rfl (G.horizontal_localCharge_le _ _ (div_pos hs hR))
      vertical_localCharge_le := fun q s hs => by
        rw [hDvl, hball q s, ← hrel]
        exact mul_le_mul' le_rfl (G.vertical_localCharge_le _ _ (div_pos hs hR)) }
  refine ⟨G', ?_, ?_, ?_, fun q s hs hsR => ?_⟩
  · show Dh.totalCharge + Dv.totalCharge ≤ _
    rw [hDhc, hDvc, ← mul_add]
    exact habs _ hT
  · show Dh.totalCharge ≤ _
    rw [hDhc]
    exact habs _ hTH
  · show Dv.totalCharge ≤ _
    rw [hDvc]
    exact habs _ hTV
  · obtain ⟨h1, h2, h3⟩ :=
      hloc (similarity a R hR q) (s / R) (div_pos hs hR) ((div_le_one hR).mpr hsR)
    refine ⟨?_, ?_, ?_⟩
    · show Dh.localCharge q s + Dv.localCharge q s ≤ _
      rw [hDhl, hDvl, ← mul_add]
      exact habsl s _ h1
    · show Dh.localCharge q s ≤ _
      rw [hDhl]
      exact habsl s _ h2
    · show Dv.localCharge q s ≤ _
      rw [hDvl]
      exact habsl s _ h3

/-! ## The rescaled decomposition -/

/-- **Local enhanced decomposition of a rescaled source.** Exactly the type of
`Enhancements.isLocalEnhancedDecomposition_of_rescaledSource`.

Every field of `IsLocalEnhancedDecomposition` except `graph_domains`, and the loss identity,
come from `ScaledCoreTree.sc2c_isLocalCoreDecomposition_of_rescaledSource`
(the two predicates have the same fields apart from `graph_domains`). The actual supports are
rewritten by `fsim_support_restrict_preimage_similarity`; `graph_domains` at `(ε, δ)` is the
cover transport above applied to the unit cover at `(ε, δ/R)`, with the identities for the
transported typed data (including the regular-class covariance). -/
theorem isLocalEnhancedDecomposition_of_rescaledSource_of_leaves {n k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    (μ : Measure (Space n)) (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
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
      (D.verticalSupport (rescaledSource μ k a R hR)))
    (hG : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      HasScaledGraphDomainCover k (D.horizontalSupport (rescaledSource μ k a R hR))
        (D.verticalSupport (rescaledSource μ k a R hR)) C ε δ 1) :
    IsLocalEnhancedDecomposition k T C a R μ
        (similarity a R hR ⁻¹' D.horizontal) (similarity a R hR ⁻¹' D.vertical) ∧
      μ.restrict (similarity a R hR ⁻¹' D.horizontal ∪ similarity a R hR ⁻¹' D.vertical)ᶜ
          (Metric.ball a R) =
        ENNReal.ofReal R ^ k *
          D.remainderMeasure (rescaledSource μ k a R hR) (Metric.ball (point 0 0) 1) := by
  obtain ⟨hc, hloss⟩ := ScaledCoreTree.sc2c_isLocalCoreDecomposition_of_rescaledSource hn hk
    hkn μ hμ hreg a R hR T C D hunH hunV honlyH honlyV hS
  have hH := fsim_hausdorffP_preimage_similarity n k a R hR
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
  refine ⟨
    { measurable_horizontal := hc.measurable_horizontal
      measurable_vertical := hc.measurable_vertical
      disjoint := hc.disjoint
      horizontal_subset := hc.horizontal_subset
      vertical_subset := hc.vertical_subset
      measure_eq := hc.measure_eq
      horizontal_unavailable := hc.horizontal_unavailable
      vertical_unavailable := hc.vertical_unavailable
      horizontal_only := hc.horizontal_only
      vertical_only := hc.vertical_only
      supports := hc.supports
      graph_domains := fun ε δ hε hδ => by
        rw [eH, eV]
        exact hasScaledGraphDomainCover_preimage_similarity a R hR hH
          (fun Dh => fsim_horizontalDomainData_preimage_similarity a R hR hH _ ε δ Dh)
          (fun Dv => fsim_verticalDomainData_preimage_similarity a R hR hH hregS _ ε δ Dv)
          (hG ε (δ / R) hε (div_pos hδ hR)) }, hloss⟩

end ParabolicRectifiability.Enhancements.ScalingTree
