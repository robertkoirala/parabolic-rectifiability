import ParabolicRectifiability.Measure.Neck.NeckOfSource
import ParabolicRectifiability.Measure.Neck.Selection.CertificateNormalize
import ParabolicRectifiability.Measure.Neck.ContractingStep.TypeSelection
import ParabolicRectifiability.Measure.Neck.ContractingStep.Children
import ParabolicRectifiability.Measure.Neck.ContractingStep.Prune
import ParabolicRectifiability.Measure.Neck.ContractingStep.Recursion
import ParabolicRectifiability.Measure.Neck.DecompositionTree.TreeDepth
import ParabolicRectifiability.Measure.Neck.DecompositionTree.GlobalIdentity
import ParabolicRectifiability.Measure.Neck.DecompositionTree.ClosureIdentity
import ParabolicRectifiability.Measure.Neck.DecompositionTree.VertexAssignment
import ParabolicRectifiability.Measure.Neck.DecompositionTree.CenterPacking
import ParabolicRectifiability.Measure.Neck.DecompositionTree.SeparatedMinkowski

/-!
# The contracting step and the countable decomposition into necks

This file assembles the proofs of the one-step statement `exists_contracting_step` and of
`exists_countable_neck_decomposition` from the auxiliary statements proved in the
neighboring files; it adds no new mathematics.

* the reductions `contractingStep_of_holes_proof`, `exists_stepTree_proof`,
  `StepTree.residual_null_proof`, `StepTree.carrier_facts_proof` and `stepTree_packing_proof`
  prove the statements `contractingStep_of_holes`, `exists_stepTree`,
  `StepTree.residual_null`, `StepTree.carrier_facts` and `stepTree_packing`;
* `exists_contracting_step_proof` and `exists_countable_neck_decomposition_proof` prove
  `exists_contracting_step` and `exists_countable_neck_decomposition`, using
  `exists_neck_of_source_proof` for the neck of a source.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-! ## Reductions to the auxiliary statements -/

/-- The statement `contractingStep_of_holes`, from the existence and the estimates of the step children. -/
theorem contractingStep_of_holes_proof (n : ℕ) :
    ∀ {k : ℕ} {T : NeckType} {ι : Type} {q : Space n} {R Cs σ δ E κ θ γ : ℝ}
      (N : NeckRegion n k T ι q R (1 / 20) 4 Cs σ δ E κ θ γ) (ν : Measure (Space n))
      (S : Set (Space n)) (f : Space n → ℝ) (Pa : NeckSourcePartition S f N)
      (B B' A C₁ C₂ Ccol Cter Cb ρ ε θ₀ Eerr : ℝ) (rad : N.stopping → ℝ)
      (H : ∀ c : N.stopping, HoleChildren ν (Pa.assignment c) (rad c)),
      IsFiniteMeasure ν → 0 < R → 0 < B → B ≤ B' → B' ≤ Cb * B → 0 < A → 0 < θ₀ →
      0 ≤ C₁ → 0 ≤ C₂ → 0 ≤ Ccol → 0 ≤ Cter →
      ν Pa.errorSet ≤ ENNReal.ofReal (C₁ * B' * R ^ k / θ₀ ^ 2) →
      N.HasTotalContentBound C₁ →
      0 < ρ → 12 * ρ ≤ 1 / 2 → 0 < ε → 2 * ε ≤ 1 / 2 →
      C₁ * (3 ^ k * Ccol * ρ + 2 ^ k * Cter * ε ^ 2) ≤ 1 / 2 →
      (∀ c : N.stopping, HoleFacts Pa B B' (A * B') C₁ C₂ Ccol Cter ρ ε c (rad c) (H c)) →
      C₁ * Cb / θ₀ ^ 2 + C₁ * (4 * C₁ * (A + 1) * Cb / ρ ^ 2 + 2 * C₂ / ε ^ 2 + A * Cb) ≤
        Eerr →
      ν = ν.restrict Pa.errorSet + ν.restrict Pa.coreSet +
        Measure.sum (fun c : N.stopping => ν.restrict (Pa.assignment c)) →
      ∃ D : ContractingStep ν S N B Eerr ρ ε,
        ν = ν.restrict D.errorSet + ν.restrict D.coreSet +
            Measure.sum (fun w : D.childIndex => ν.restrict (D.childSource w)) ∧
          ∀ w ∈ D.childIndex, D.childParent w ∉ Pa.terminal →
            D.childRadius w = 3 * ρ * N.radius (D.childParent w) := by
  intro k T ι q R Cs σ δ E κ θ γ N ν S f Pa B B' A C₁ C₂ Ccol Cter Cb ρ ε θ₀ Eerr rad H hν hR
    hB hBB' hB'le hA hθ₀ hC₁ hC₂ hCcol hCter herr htot hρ hρ12 hε hε2 hsmall hH hEerr hid
  have hrad : ∀ c : N.stopping, ((c : Space n) ∈ Pa.terminal → rad c = 2 * ε * N.radius c) ∧
      ((c : Space n) ∉ Pa.terminal → rad c = 3 * ρ * N.radius c) := by
    intro c
    obtain ⟨h1, h2⟩ := hH c
    exact ⟨fun h => (h1 h).1, fun h => (h2 h).1⟩
  obtain ⟨SC⟩ := exists_stepChildren_proof n N ν S f Pa ρ ε rad H hν hrad hid
  obtain ⟨herrSC, hradSC, hcontSC⟩ := stepChildren_estimates_proof n N ν S f Pa B B' A C₁ C₂ Ccol
    Cter Cb ρ ε θ₀ Eerr rad H SC hν hR hB hBB' hB'le hA hθ₀ hC₁ hC₂ hCcol hCter herr htot hρ
    hρ12 hε hε2 hsmall hH hEerr
  exact ⟨
    { errorSet := SC.errorSet
      coreSet := SC.coreSet
      childIndex := SC.childIndex
      childSource := SC.childSource
      childCenter := SC.childCenter
      childRadius := SC.childRadius
      childParent := SC.childParent
      measurableSet_errorSet := SC.measurableSet_errorSet
      measurableSet_coreSet := SC.measurableSet_coreSet
      measurableSet_childSource := SC.measurableSet_childSource
      errorSet_subset := SC.errorSet_subset
      coreSet_subset := SC.coreSet_subset
      childSource_subset := SC.childSource_subset
      cover := SC.cover
      disjoint_errorSet_coreSet := SC.disjoint_errorSet_coreSet
      disjoint_errorSet_child := SC.disjoint_errorSet_child
      disjoint_coreSet_child := SC.disjoint_coreSet_child
      disjoint_children := SC.disjoint_children
      coreSet_subset_core := SC.coreSet_subset_core
      errorSet_le := herrSC
      childParent_mem := SC.childParent_mem
      childSource_subset_hole := SC.childSource_subset_hole
      childSource_subset_ball := SC.childSource_subset_ball
      childRadius_eq := SC.childRadius_eq
      finite_children := SC.finite_children
      childRadius_le := hradSC
      child_content_le := hcontSC }, SC.measure_eq, SC.childRadius_collapsed⟩

/-- The statement `exists_stepTree`, from the pruning of children and the recursive construction of the tree. -/
theorem exists_stepTree_proof (n : ℕ) :
    ∀ (Eerr ρ ε L : ℝ) (k : ℕ) (F : FamilyKind),
      (∀ (q : Space n) (R B : ℝ) (ν : Measure (Space n)) (S : Set (Space n)),
        0 < R → 0 < B → IsFiniteMeasure ν → MeasurableSet S → S ⊆ Metric.ball q R →
        ν Sᶜ = 0 →
        (∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B) →
        ∃ (T : NeckType) (ι : Type) (Cd Cs σ δ E κ θ γ : ℝ)
          (N : NeckRegion n k T ι q R (1 / 20) Cd Cs σ δ E κ θ γ)
          (D : ContractingStep ν S N B Eerr ρ ε),
          (F = .mixed ∨ F = T.toFamilyKind) ∧
            ν = ν.restrict D.errorSet + ν.restrict D.coreSet +
              Measure.sum (fun w : D.childIndex => ν.restrict (D.childSource w)) ∧
            N.IsCertified ν B B L ∧
            (F ≠ .mixed →
              ∀ w ∈ D.childIndex, D.childRadius w = 3 * ρ * N.radius (D.childParent w))) →
      ∀ (q : Space n) (R B : ℝ) (ν : Measure (Space n)) (S : Set (Space n)),
        0 < R → 0 < B → IsFiniteMeasure ν → MeasurableSet S → S ⊆ Metric.ball q R →
        ν Sᶜ = 0 → (∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B) →
        ∃ Tr : StepTree ν k F S q R B Eerr ρ ε,
          ∀ v ∈ Tr.vertices, (Tr.vneck v).neck.IsCertified (ν.restrict (Tr.source v)) B B L := by
  intro Eerr ρ ε L k F hstep
  refine exists_stepTree_of_positive_proof n Eerr ρ ε L k F ?_
  intro q R B ν S hR hB hν hSm hSq hSn hSB
  obtain ⟨T, ι, Cd, Cs, σ, δ, E, κ, θ, γ, N, D, hFT, hid, hcert, hrad⟩ :=
    hstep q R B ν S hR hB hν hSm hSq hSn hSB
  obtain ⟨D', hpos, hsub, hid'⟩ := D.exists_prune_proof
  refine ⟨T, ι, Cd, Cs, σ, δ, E, κ, θ, γ, N, D', hFT, hid' hid, hcert, ?_, hpos⟩
  intro hF w hw
  obtain ⟨hw₁, hr, hp⟩ := hsub w hw
  rw [hr, hp]
  exact hrad hF w hw₁

/-- The statement `StepTree.residual_null`, from `StepTree.closedContainer_null_proof`. -/
theorem StepTree.residual_null_proof {n k : ℕ} {F : FamilyKind} {S : Set (Space n)} {q : Space n}
    {R B Eerr ρ ε : ℝ} {ν : Measure (Space n)} (Tr : StepTree ν k F S q R B Eerr ρ ε)
    (hR : 0 < R) : hausdorffP n k (treeResidual Tr.vertices Tr.source) = 0 := by
  refine measure_mono_null ?_ (Tr.closedContainer_null_proof hR)
  intro z hz
  unfold treeResidual at hz ⊢
  rw [Set.mem_iInter] at hz ⊢
  intro j
  obtain ⟨v, hv, hz'⟩ := Set.mem_iUnion₂.mp (hz j)
  obtain ⟨hlen, hzv⟩ := Set.mem_iUnion.mp hz'
  exact Set.mem_iUnion₂.mpr ⟨v, hv, Set.mem_iUnion.mpr
    ⟨hlen, Metric.ball_subset_closedBall (Tr.source_subset_ball v hv hzv)⟩⟩

/-- The statement `StepTree.carrier_facts`, from the closure identity, the closure inclusion and
the null closed container. -/
theorem StepTree.carrier_facts_proof {n k : ℕ} {F : FamilyKind} {S : Set (Space n)} {q : Space n}
    {R B Eerr ρ ε L : ℝ} {ν : Measure (Space n)} (Tr : StepTree ν k F S q R B Eerr ρ ε)
    (hR : 0 < R) (hB : 0 < B) (hL : 0 < L)
    (hcert : ∀ v ∈ Tr.vertices,
      (Tr.vneck v).neck.IsCertified (ν.restrict (Tr.source v)) B B L) :
    IsCompact Tr.carrier ∧ Tr.carrier ⊆ Metric.closedBall q R ∧
      hausdorffP n k (Tr.carrier \ ⋃ v ∈ Tr.vertices, (Tr.vneck v).neck.core) = 0 := by
  exact Tr.carrier_facts_of_subtree_proof hR (Tr.subtreeSet_closure_subset_proof hR hB hL hcert)
    (Tr.subtreeSet_closure_identity_proof hR hB hL hcert) (Tr.closedContainer_null_proof hR)

/-- The statement `stepTree_packing`, from the vertex assignment and the packing of centers. -/
theorem stepTree_packing_proof (n : ℕ) (Eerr ρ ε L : ℝ) (hρ : 0 < ρ) (hε : 0 < ε) (hL : 1 ≤ L) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ {k : ℕ} {F : FamilyKind} {S : Set (Space n)} {q : Space n}
      {R B : ℝ} {ν : Measure (Space n)} (Tr : StepTree ν k F S q R B Eerr ρ ε),
      1 ≤ k → k < n + 2 → 0 < R → 0 < B →
      (∀ v ∈ Tr.vertices,
        (Tr.vneck v).neck.IsCertified (ν.restrict (Tr.source v)) B B L) →
      ∀ (I : Type) [Countable I] (z : I → Space n) (r : I → ℝ),
        (∀ i, z i ∈ Tr.carrier) → (∀ i, 0 < r i ∧ r i ≤ R) →
        (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
        ∑' i, ENNReal.ofReal (r i) ^ k ≤ ENNReal.ofReal (Cp * R ^ k) := by
  have hη : 0 < min (1 / 200 : ℝ) (min (3 * ρ) (2 * ε) / 200) :=
    lt_min (by norm_num) (div_pos (lt_min (by linarith) (by linarith)) (by norm_num))
  obtain ⟨Cv, hCv, hpack⟩ := certified_center_packing_proof n L _ hL hη
  obtain ⟨Cp, hCp, hglob⟩ := stepTree_packing_of_assignment_proof n Eerr ρ ε _ Cv hη hCv
  refine ⟨Cp, hCp, ?_⟩
  intro k F S q R B ν Tr hk hkn hR hB hcert
  refine hglob Tr hk hkn hR hB
    (Tr.exists_vertex_center_proof hR hB (by linarith) hρ hε hcert _ hη (min_le_left _ _)
      (min_le_right _ _)) ?_
  intro v hv I _ c r hc hr hsep
  exact hpack (Tr.vneck v).neck (ν.restrict (Tr.source v)) B hk hkn (hcert v hv) I c r hc hr
    hsep

/-! ## The one-step statement -/

/-- The one-step statement `exists_contracting_step`. -/
theorem exists_contracting_step_proof (n : ℕ) :
    ∃ Eerr ρ ε L : ℝ, 0 < Eerr ∧ 0 < ρ ∧ 0 < ε ∧ 1 ≤ L ∧
      ∀ (k : ℕ) (F : FamilyKind), 1 ≤ k → k < n + 2 → Nonempty (Models n k F) →
      ∀ (q : Space n) (R B : ℝ) (ν : Measure (Space n)) (S : Set (Space n)),
        0 < R → 0 < B → IsFiniteMeasure ν → MeasurableSet S → S ⊆ Metric.ball q R →
        ν Sᶜ = 0 →
        (∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B) →
        ∃ (T : NeckType) (ι : Type) (Cd Cs σ δ E κ θ γ : ℝ)
          (N : NeckRegion n k T ι q R (1 / 20) Cd Cs σ δ E κ θ γ)
          (D : ContractingStep ν S N B Eerr ρ ε),
          (F = .mixed ∨ F = T.toFamilyKind) ∧
            ν = ν.restrict D.errorSet + ν.restrict D.coreSet +
              Measure.sum (fun w : D.childIndex => ν.restrict (D.childSource w)) ∧
            N.IsCertified ν B B L ∧
            (F ≠ .mixed →
              ∀ w ∈ D.childIndex, D.childRadius w = 3 * ρ * N.radius (D.childParent w)) := by
  obtain ⟨C₁, θ₀, A, Cs₁, hC₁, hθ₀, hA, -, hneck⟩ := exists_neck_of_source_proof n
  obtain ⟨C₂, hC₂, hsel⟩ := exists_step_type_proof n
  obtain ⟨Ccol, hCcol, hcolch⟩ := ChargeCollapse.collapsed_children n
  obtain ⟨Cter, hCter, htermch⟩ := ChargeCollapse.terminal_children n
  obtain ⟨ρ, ε, hρ, hρ1, hρ12, hε, hε1, hε2, hsmall⟩ :=
    exists_child_scales_proof n C₁ Ccol Cter (by linarith) hCcol.le hCter.le
  have hCb : (1 : ℝ) ≤ 4 ^ (n + 4) + 1 := by
    have : (0 : ℝ) ≤ 4 ^ (n + 4) := pow_nonneg (by norm_num) _
    linarith
  obtain ⟨L, hL, hnorm⟩ := isCertified_normalize_proof C₁ A (4 ^ (n + 4) + 1) hC₁ hA hCb
  have hC₁pos : 0 < C₁ := by linarith
  have hEerr : 0 < C₁ * (4 ^ (n + 4) + 1) / θ₀ ^ 2 +
      C₁ * (4 * C₁ * (A + 1) * (4 ^ (n + 4) + 1) / ρ ^ 2 + 2 * C₂ / ε ^ 2 +
        A * (4 ^ (n + 4) + 1)) := by positivity
  refine ⟨_, ρ, ε, L, hEerr, hρ, hε, hL, ?_⟩
  intro k F hk hkn hF q R B ν S hR hB hν hSm hSq hSn hSB
  have := hν
  obtain ⟨T, f, B', hT, hFT, hf, hBB', hB'le, htail, hfzero, htubes⟩ :=
    hsel k F hk hkn hF q R B ν S hR hB hν hSm hSq hSn hSB
  have hB' : 0 < B' := lt_of_lt_of_le hB hBB'
  obtain ⟨ι, N, Pa, hid, herr, hcert, hcoll⟩ := hneck k T hT hkn q R ν S f B' θ₀ (A * B') hR hν
    hSm hSq hSn hf hB' htail hθ₀ le_rfl le_rfl
  have hhole : ∀ c : N.stopping, ∃ (r : ℝ) (Hc : HoleChildren ν (Pa.assignment c) r),
      HoleFacts Pa B B' (A * B') C₁ C₂ Ccol Cter ρ ε c r Hc := by
    intro c
    have hdpos : 0 < N.radius c := c.2.2
    have hAm : MeasurableSet (Pa.assignment c) := Pa.measurableSet_assignment c c.2
    have hAball : Pa.assignment c ⊆ Metric.ball (c : Space n) (N.radius c) :=
      Pa.assignment_subset_ball c c.2
    by_cases hterm : (c : Space n) ∈ Pa.terminal
    · obtain ⟨hcS, hrf⟩ := Pa.terminal_radius c hterm
      have hfpos : 0 < f c := by
        rw [← hrf]
        exact hdpos
      obtain ⟨hk2, hkn', LH, LV, hint⟩ := htubes c hcS hfpos
      have hsub : Pa.assignment c ⊆ Metric.ball (c : Space n) (f c) := by
        rw [← hrf]
        exact hAball
      have hint' : ∫⁻ z in Pa.assignment c,
          (modelCost (T := .horizontal) LH z + modelCost (T := .vertical) LV z) ∂ν ≤
            ENNReal.ofReal (C₂ * B * N.radius c ^ (k + 2)) := by
        rw [hrf]
        exact le_trans (lintegral_mono_set hsub) hint
      obtain ⟨Hc, hdisc, hcount⟩ := htermch hk2 hkn' ν (Pa.assignment c) hAm c (N.radius c)
        hdpos hAball LH LV (C₂ * B) hint' ε hε hε1
      have hdR : N.radius c ≤ R := by
        rw [hrf]
        exact hf.le_radius c hcS
      exact ⟨2 * ε * N.radius c, Hc, fun _ => ⟨rfl, hdR, hk2, hdisc, hcount⟩,
        fun h => absurd hterm h⟩
    · obtain ⟨hbd1, hbd2⟩ := hcoll c c.2 hterm
      by_cases hr : 0 < T.rank k
      · obtain ⟨L₀, τ, hL₀⟩ := hbd1 hr
        rw [← NeckType.collapseModelSet_eq_lowerModelSet] at hL₀
        obtain ⟨Hc, hdisc, hcount⟩ := hcolch hT (Nat.succ_le_of_lt hr) ν (Pa.assignment c) hAm
          c (N.radius c) hdpos hAball L₀ τ (C₁ * (A * B' + B')) hL₀ ρ hρ hρ1
        exact ⟨3 * ρ * N.radius c, Hc, fun h => absurd h hterm,
          fun _ => ⟨rfl, Or.inl ⟨hr, hdisc, hcount⟩⟩⟩
      · have hr0 : T.rank k = 0 := Nat.eq_zero_of_not_pos hr
        exact ⟨3 * ρ * N.radius c, HoleChildren.discardAll ν (Pa.assignment c) hAm _,
          fun h => absurd h hterm, fun _ => ⟨rfl, Or.inr ⟨hr0, rfl, hbd2 hr0⟩⟩⟩
  choose rad H hH using hhole
  obtain ⟨Dst, hDid, hDrad⟩ := contractingStep_of_holes_proof n N ν S f Pa B B' A C₁ C₂ Ccol Cter
    (4 ^ (n + 4) + 1) ρ ε θ₀ _ rad H hν hR hB hBB' hB'le hA hθ₀ hC₁pos.le hC₂.le hCcol.le
    hCter.le herr hcert.totalContent hρ hρ12 hε hε2 (hsmall k hkn.le) hH le_rfl hid
  refine ⟨T, ι, 4, Cs₁, T.sourceSeparation, _, _, _, θ₀, _, N, Dst, hFT, hDid,
    hnorm N ν B B' hB hBB' hB'le hcert, ?_⟩
  intro hFm w hw
  refine hDrad w hw fun hmem => ?_
  obtain ⟨hcS, hrf⟩ := Pa.terminal_radius _ hmem
  have hpos : 0 < N.radius (Dst.childParent w) := (Pa.terminal_subset hmem).2
  rw [hrf, hfzero hFm _ hcS] at hpos
  exact lt_irrefl 0 hpos

/-! ## The countable decomposition -/

/-- The statement `exists_countable_neck_decomposition`. -/
theorem exists_countable_neck_decomposition_proof (n : ℕ) :
    ∃ E C L : ℝ, 0 < E ∧ 0 < C ∧ 1 ≤ L ∧
      ∀ (k : ℕ) (F : FamilyKind), 1 ≤ k → k < n + 2 → Nonempty (Models n k F) →
      ∀ (q : Space n) (R B : ℝ) (ν : Measure (Space n)) (S : Set (Space n)),
        0 < R → 0 < B → IsFiniteMeasure ν → MeasurableSet S → S ⊆ Metric.ball q R →
        ν Sᶜ = 0 →
        (∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B) →
        ∃ D : NeckDecomposition ν k F S q R B E C,
          ∀ v ∈ D.vertices, IsCertifiedCore k (D.coreType v) (D.center v) (D.radius v)
            B B L (ν.restrict (D.source v)) (D.core v) := by
  obtain ⟨Eerr, ρ, ε, L, hE, hρ, hε, hL, hstep⟩ := exists_contracting_step_proof n
  obtain ⟨Cp, hCp, hpack⟩ := stepTree_packing_proof n Eerr ρ ε L hρ hε hL
  obtain ⟨Csm, hCsm, hsm⟩ := separated_minkowski_of_packing_proof n
  have hm : 0 ≤ Csm * Cp := mul_nonneg hCsm.le hCp.le
  obtain ⟨Cdec, hCdec, h2E, hCpC, hCsmC⟩ :
      ∃ C : ℝ, 0 < C ∧ 2 * Eerr ≤ C ∧ Cp ≤ C ∧ Csm * Cp ≤ C :=
    ⟨2 * Eerr + Cp + Csm * Cp + 1, by linarith, by linarith, by linarith, by linarith⟩
  refine ⟨Eerr, Cdec, L, hE, hCdec, hL, ?_⟩
  intro k F hk hkn hF q R B ν S hR hB hν hSm hSq hSn hSB
  obtain ⟨Tr, hcert⟩ := exists_stepTree_proof n Eerr ρ ε L k F (hstep k F hk hkn hF) q R B ν S hR hB
    hν hSm hSq hSn hSB
  obtain ⟨hmeq, herr, hcompl⟩ := Tr.measure_eq_error_proof hν hSn hR hB
  have hrad := Tr.radius_total_le_proof hR
  obtain ⟨hKc, hKsub, hKnull⟩ := Tr.carrier_facts_proof hR hB (by linarith) hcert
  have hres := Tr.residual_null_proof hR
  have hpk := hpack Tr hk hkn hR hB hcert
  obtain ⟨hsep, hmink⟩ := hsm k hkn.le Tr.carrier R Cp hR hCp.le hpk
  have hRk : 0 ≤ R ^ k := pow_nonneg hR.le k
  have hEB : 2 * Eerr * B * R ^ k ≤ Cdec * B * R ^ k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2E hB.le) hRk
  refine ⟨
    { vertices := Tr.vertices
      root_mem := Tr.root_mem
      parent_mem := Tr.parent_mem
      source := Tr.source
      center := Tr.center
      radius := Tr.radius
      errorSet := fun v => (Tr.step v).errorSet
      coreSet := fun v => (Tr.step v).coreSet
      core := fun v => (Tr.vneck v).neck.core
      coreType := fun v => (Tr.vneck v).type
      source_root := Tr.source_root
      center_root := Tr.center_root
      radius_root := Tr.radius_root
      measurableSet_source := Tr.measurableSet_source
      measurableSet_errorSet := fun v _ => (Tr.step v).measurableSet_errorSet
      measurableSet_coreSet := fun v _ => (Tr.step v).measurableSet_coreSet
      radius_pos := Tr.radius_pos
      source_subset_ball := Tr.source_subset_ball
      errorSet_subset := fun v _ => (Tr.step v).errorSet_subset
      coreSet_subset := fun v _ => (Tr.step v).coreSet_subset
      child_subset := Tr.child_subset
      cover := Tr.cover
      disjoint_errorSet_coreSet := fun v _ => (Tr.step v).disjoint_errorSet_coreSet
      disjoint_errorSet_child := Tr.disjoint_errorSet_child
      disjoint_coreSet_child := Tr.disjoint_coreSet_child
      disjoint_children := Tr.disjoint_children
      errorSet_le := Tr.errorSet_le
      child_radius_le := Tr.child_radius_le
      child_content_le := Tr.child_content_le
      coreSet_subset_core := fun v _ => (Tr.step v).coreSet_subset_core
      coreType_available := fun v _ => (Tr.vneck v).neck.available
      coreType_family := Tr.family
      measure_eq := hmeq
      error_total := le_trans herr (ENNReal.ofReal_le_ofReal hEB)
      radius_total := hrad
      carrier := Tr.carrier
      isCompact_carrier := hKc
      carrier_subset := hKsub
      core_subset_carrier := fun v hv => Tr.core_subset_carrier hv
      residual_subset_carrier := Tr.residual_subset_carrier
      measure_compl_carrier_le := le_trans hcompl (ENNReal.ofReal_le_ofReal hEB)
      null_remainder := hKnull
      residual_null := hres
      packing := by
        intro I _ z r hz hr hd
        exact le_trans (hpk I z r hz hr hd)
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCpC hRk))
      separated := by
        intro r hr hrR P hP hsepP
        exact le_trans (hsep r hr hrR P hP hsepP)
          (mul_le_mul_of_nonneg_right hCsmC (pow_nonneg (div_nonneg hR.le hr.le) k))
      minkowski := by
        intro r hr hrR
        exact le_trans (hmink r hr hrR) (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsmC hRk)
            (pow_nonneg hr.le _))) }, ?_⟩
  intro v hv
  exact ⟨(Tr.vneck v).ι, (Tr.vneck v).Cd, (Tr.vneck v).Cs, (Tr.vneck v).σ, (Tr.vneck v).δ,
    (Tr.vneck v).E, (Tr.vneck v).κ, (Tr.vneck v).θ, (Tr.vneck v).γ, (Tr.vneck v).neck, rfl,
    hcert v hv⟩

end ParabolicRectifiability
