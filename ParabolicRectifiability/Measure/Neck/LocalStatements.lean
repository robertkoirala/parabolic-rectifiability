import ParabolicRectifiability.Measure.Neck.CountableDecomposition
import ParabolicRectifiability.Measure.Neck.Packing
import ParabolicRectifiability.Measure.Neck.DensitySelection

/-!
# Geometric extraction, density refinement and finite ball packing

This file assembles three local statements from the neck decomposition:

* `exists_geometric_extraction_proof` (geometric extraction),
* `exists_density_refinement_proof` (density refinement, with `a = M`),
* `exists_finite_ball_packing_constant_proof` (the variable-radius packing transfer).

The route is: neck of a source → contracting step → countable decomposition → discrete
packing → (density selection, variable-radius packing):

* `discrete_packing_proof`: `discrete_packing_of_decomposition` applied to
  `IsCertifiedCore` and `exists_countable_neck_decomposition_proof`;
* `density_selection_proof`: `density_selection_of_discrete` applied to
  `discrete_packing_proof`;
* `variable_radius_packing_proof`: `variable_radius_packing_of_discrete` applied to
  `discrete_packing_proof`;
* the three local statements are obtained from these. The last two apply density selection
  and variable-radius packing to the unchanged source `ν|G` with `L = 2M` and `a = M`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-! ## Discrete packing, density selection and variable-radius packing -/

/-- The statement `discrete_packing` (truncated form): the countable decomposition implies
discrete packing. -/
theorem discrete_packing_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (T : FamilyKind), 1 ≤ k → k < n + 2 →
      Nonempty (Models n k T) →
      ∀ (q : Space n) (R b B : ℝ) (l : ℕ) (z : Fin l → Space n) (r w : Fin l → ℝ),
        0 < R → 0 < b → 0 ≤ B →
        (∀ i, 0 < r i ∧ Metric.ball (z i) (r i) ⊆ Metric.ball q R) →
        (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
        (∀ i, 0 < w i ∧ w i ≤ b) →
        (∀ i, ∫⁻ s in Ioi (r i), betaSq (truncatedAtomicSource k z r w s) k T (z i) s
            ∂scaleMeasure ≤ ENNReal.ofReal B) →
        ∑ i, ENNReal.ofReal (w i * r i ^ k) ≤ ENNReal.ofReal (C * (b + B) * R ^ k) :=
  discrete_packing_of_decomposition n IsCertifiedCore
    (exists_countable_neck_decomposition_proof n)

/-- The statement `density_selection`. -/
theorem density_selection_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (T : FamilyKind), 1 ≤ k → k < n + 2 →
      Nonempty (Models n k T) →
      ∀ (ν : Measure (Space n)) (c : Space n) (L a : ℝ), IsFiniteMeasure ν →
        ν.support ⊆ Metric.closedBall c (1 / 16) → 0 ≤ L → 0 < a →
        (∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ ENNReal.ofReal L) →
        IsCompact (densityCarrier ν k a) ∧
          ν (densityCarrier ν k a)ᶜ ≤ ENNReal.ofReal (C * (a + L)) ∧
          HasMetricContentBounds k (C * (1 + L / a)) (densityCarrier ν k a) ∧
          (hausdorffP n k).restrict (densityCarrier ν k a) ≤ ENNReal.ofReal (C / a) • ν :=
  density_selection_of_discrete n (discrete_packing_proof n)

/-- The statement `variable_radius_packing` (the variable-radius packing transfer). -/
theorem variable_radius_packing_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (T : FamilyKind), 1 ≤ k → k < n + 2 →
      Nonempty (Models n k T) →
      ∀ (ν : Measure (Space n)) (L a : ℝ) (K : Set (Space n)), IsFiniteMeasure ν →
        0 ≤ L → 0 < a →
        (∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ ENNReal.ofReal L) →
        HasUniformLowerMass ν k a K →
        HasFiniteBallPacking k (C * (1 + L / a)) K :=
  variable_radius_packing_of_discrete n (discrete_packing_proof n)

/-! ## The local statements -/

/-- The statement `exists_geometric_extraction`, from the countable decomposition. The square-good points of `ν` are localized to a Borel `S ⊆ P(c, 1/32)`, the
decomposition is applied with `B = 2M`, the carrier is kept inside `supp ν`, and each vertex core is
certified by its retained neck. -/
theorem exists_geometric_extraction_proof (n : ℕ) (_hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k < n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν.InnerRegular →
      ∀ c : Space n, ν.support ⊆ Metric.closedBall c (1 / 64) →
      ∀ M : ℝ, 0 < M →
      (∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ ENNReal.ofReal (2 * M)) →
      Nonempty (GeometricExtraction ν k T M C) := by
  obtain ⟨_E, Cdec, L, _hE, hCdec, hL, hdec⟩ := exists_countable_neck_decomposition_proof n
  refine ⟨2 * Cdec, by linarith, ?_⟩
  intro k hk hkn T hT ν hν _hreg c hsupp M hM hae
  have := hν
  -- A Borel square-good set carrying `ν`, inside the container `P(c, 1/32)`.
  obtain ⟨S, hSm, hSb, hSn, hSg⟩ : ∃ S : Set (Space n), MeasurableSet S ∧
      S ⊆ Metric.ball c (1 / 32) ∧ ν Sᶜ = 0 ∧
      ∀ z ∈ S, allScaleEnergy ν k T z ≤ ENNReal.ofReal (2 * M) := by
    refine ⟨Metric.closedBall c (1 / 64) ∩
        {z | allScaleEnergy ν k T z ≤ ENNReal.ofReal (2 * M)},
      measurableSet_closedBall.inter
        (measurableSet_le (measurable_allScaleEnergy ν k T) measurable_const),
      fun z hz => Metric.closedBall_subset_ball (by norm_num) hz.1, ?_, fun z hz => hz.2⟩
    have h1 : ν (Metric.closedBall c (1 / 64))ᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr hsupp) Measure.measure_compl_support
    have h2 : ν {z | ¬ allScaleEnergy ν k T z ≤ ENNReal.ofReal (2 * M)} = 0 :=
      ae_iff.mp hae
    refine measure_mono_null (fun z hz => ?_) (measure_union_null h1 h2)
    by_cases hb : z ∈ Metric.closedBall c (1 / 64)
    · exact Or.inr fun hg => hz ⟨hb, hg⟩
    · exact Or.inl hb
  obtain ⟨D, hD⟩ := hdec k T hk hkn hT c (1 / 32) (2 * M) ν S (by norm_num) (by linarith)
    hν hSm hSb hSn hSg
  have hcore_supp : ∀ v ∈ D.vertices, D.core v ⊆ ν.support := fun v hv =>
    ((hD v hv).subset_support (D.radius_pos v hv) (by linarith) (by linarith)).trans
      (Measure.support_mono Measure.restrict_le_self)
  have hpow : (1 / 32 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hloss : ν (D.carrier ∩ ν.support)ᶜ ≤ ENNReal.ofReal (2 * Cdec * M) := by
    rw [compl_inter]
    refine (measure_union_le _ _).trans ?_
    rw [Measure.measure_compl_support, add_zero]
    refine D.measure_compl_carrier_le.trans (ENNReal.ofReal_le_ofReal ?_)
    calc Cdec * (2 * M) * (1 / 32 : ℝ) ^ k ≤ Cdec * (2 * M) * 1 :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg hCdec.le (by linarith))
      _ = 2 * Cdec * M := by ring
  exact ⟨{
    carrier := D.carrier ∩ ν.support
    compact := D.isCompact_carrier.inter_right ν.isClosed_support
    subset_support := inter_subset_right
    loss := hloss
    horizontalIndex := D.typeIndex .horizontal
    verticalIndex := D.typeIndex .vertical
    horizontalCore := fun i => D.core (Denumerable.ofNat (List ℕ) i)
    verticalCore := fun i => D.core (Denumerable.ofNat (List ℕ) i)
    horizontal_certificate := fun i => by
      obtain ⟨hv, hty⟩ := D.mem_typeIndex.mp i.2
      have hcert := hD _ hv
      rw [hty] at hcert
      exact hcert.isHorizontalCore (by linarith)
    vertical_certificate := fun i => by
      obtain ⟨hv, hty⟩ := D.mem_typeIndex.mp i.2
      have hcert := hD _ hv
      rw [hty] at hcert
      exact hcert.isVerticalCore hkn (by linarith)
    horizontal_subset := fun i => by
      obtain ⟨hv, -⟩ := D.mem_typeIndex.mp i.2
      exact subset_inter (D.core_subset_carrier _ hv) (hcore_supp _ hv)
    vertical_subset := fun i => by
      obtain ⟨hv, -⟩ := D.mem_typeIndex.mp i.2
      exact subset_inter (D.core_subset_carrier _ hv) (hcore_supp _ hv)
    null_remainder := measure_mono_null
      (sdiff_subset_sdiff inter_subset_left D.iUnion_core_subset) D.null_remainder
    horizontal_unavailable := D.typeIndex_horizontal_eq_empty
    vertical_unavailable := D.typeIndex_vertical_eq_empty }⟩

/-- The statement `exists_density_refinement`: density selection applied
to the unchanged source `ν|G` with `L = 2M`, `a = M`, so `1 + L/a = 3`. -/
theorem exists_density_refinement_proof (n : ℕ) (_hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k < n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν.InnerRegular →
      ∀ c : Space n, ν.support ⊆ Metric.closedBall c (1 / 64) →
      ∀ M : ℝ, 0 < M →
      (∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ ENNReal.ofReal (2 * M)) →
      ∀ G : Set (Space n), IsCompact G → G ⊆ ν.support →
      Nonempty (DensityRefinement ν k M C G) := by
  obtain ⟨C, hC, hsel⟩ := density_selection_proof n
  refine ⟨3 * C, by linarith, ?_⟩
  intro k hk hkn T hT ν hν _hreg c hsupp M hM hae G hG _hGsupp
  have := hν
  have hsuppG : (ν.restrict G).support ⊆ Metric.closedBall c (1 / 16) :=
    (Measure.support_mono Measure.restrict_le_self).trans
      (hsupp.trans (Metric.closedBall_subset_closedBall (by norm_num)))
  have haeG : ∀ᵐ z ∂ν.restrict G,
      allScaleEnergy (ν.restrict G) k T z ≤ ENNReal.ofReal (2 * M) :=
    (ae_restrict_of_ae hae).mono fun z hz =>
      (allScaleEnergy_restrict_le_original ν G k T z).trans hz
  obtain ⟨hcpt, hloss, hcontent, -⟩ := hsel k T hk hkn hT (ν.restrict G) c (2 * M) M
    inferInstance hsuppG (by linarith) hM haeG
  have h3 : C * (1 + 2 * M / M) = 3 * C := by
    rw [mul_div_assoc, div_self hM.ne', mul_one]
    ring
  exact ⟨{
    set := densityCarrier (ν.restrict G) k M
    compact := hcpt
    subset := fun z hz => hG.isClosed.closure_subset (Measure.support_restrict_subset hz.1).1
    loss := hloss.trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
    lower_mass := fun z hz r hr hr1 => hz.2 r hr hr1
    content := h3 ▸ hcontent }⟩

/-- The statement `exists_finite_ball_packing_constant`: variable-radius packing
applied to the unchanged source `ν|G` with `L = 2M`, `a = M`, using the lower mass for `ν|G` (never
for a retained restriction). -/
theorem exists_finite_ball_packing_constant_proof (n : ℕ) (_hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k < n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν.InnerRegular →
      ∀ c : Space n, ν.support ⊆ Metric.closedBall c (1 / 64) →
      ∀ M : ℝ, 0 < M →
      (∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ ENNReal.ofReal (2 * M)) →
      ∀ G : Set (Space n), IsCompact G → G ⊆ ν.support →
      ∀ K : Set (Space n), K ⊆ G → HasUniformLowerMass (ν.restrict G) k M K →
      HasFiniteBallPacking k C K := by
  obtain ⟨C, hC, htr⟩ := variable_radius_packing_proof n
  refine ⟨3 * C, by linarith, ?_⟩
  intro k hk hkn T hT ν hν _hreg _c _hsupp M hM hae G _hG _hGsupp K _hKG hK
  have := hν
  have haeG : ∀ᵐ z ∂ν.restrict G,
      allScaleEnergy (ν.restrict G) k T z ≤ ENNReal.ofReal (2 * M) :=
    (ae_restrict_of_ae hae).mono fun z hz =>
      (allScaleEnergy_restrict_le_original ν G k T z).trans hz
  have h3 : C * (1 + 2 * M / M) = 3 * C := by
    rw [mul_div_assoc, div_self hM.ne', mul_one]
    ring
  exact h3 ▸ htr k T hk hkn hT (ν.restrict G) (2 * M) M K inferInstance (by linarith) hM
    haeG hK

end ParabolicRectifiability
