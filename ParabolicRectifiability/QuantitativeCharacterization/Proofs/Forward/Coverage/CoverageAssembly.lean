import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Coverage.SlabBasics
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Coverage.SlabCover
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Coverage.SlabDisjoint
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Coverage.SlabFamily
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Coverage.SlabPartition
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Coverage.Indexing
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Coverage.ModelBall
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Coverage.BadCost
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Coverage.Coverage
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Coverage.GoodSlabCover

/-! # Assembly of the slab covering, implication form

`d1fcomp_coverageAssembly_of` derives `CoverageAssemblyStatement` from the intermediate
statements of the slab covering (indexing, model balls, slab basics, cover, disjointness, families,
partition, bad cost, coverage, good slab cover). `d1fcomp_coverageAssembly_of_input` applies it to
their proofs (slab cover, bad cost, coverage, good slab cover, disjointness,
families, indexing, basics, partition, model balls). The only remaining hypothesis is the
stopping-scale Lipschitz statement `Terminal.StopScaleLipschitzStatement`, discharged in
`d1comp_exists_local_forward_covering` by `d1c_stopScaleLipschitz_proof`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Coverage

open scoped Classical in
/-- **Assembly of the covering.** The intermediate statements give `CoverageAssemblyStatement` with
`C = 3`, `L₀ = 9`. -/
theorem d1fcomp_coverageAssembly_of (hIdx : IndexingStatement) (hModel : ModelBallStatement)
    (hFam : SlabFamilyStatement) (hPart : SlabPartitionStatement)
    (hGood : GoodSlabCoverStatement) (hBad : BadCostStatement) (hlog : Real.log 10 ≤ 3) :
    CoverageAssemblyStatement := by
  intro n _hn k _hk _hkn
  refine ⟨3, by norm_num, 9, by norm_num, ?_⟩
  intro L hL μ _hfin _hreg a _ha R hR Λ b K hK P SD δ κ θ γ tn ref href
  obtain ⟨I, ⟨r⟩⟩ := hIdx n μ a R P k Λ b K SD
  obtain ⟨hmeasB, hmeasG, hsubB, hsubG⟩ := hFam n μ a R P k Λ b K SD
  obtain ⟨hdisjBG, hdisjGG, hcover⟩ := hPart n μ a R P k Λ b K SD
  have hball := fun i : I =>
    hModel n μ a R P k Λ b K SD (r i) δ κ θ γ (tn (r i)) (ref (r i)).carrier (href (r i))
  have hKR : 0 ≤ K * R ^ k := mul_nonneg hK (pow_nonneg hR.le k)
  have hK3 : K * R ^ k ≤ 3 * K * R ^ k := by
    calc K * R ^ k ≤ 3 * (K * R ^ k) := by linarith
      _ = 3 * K * R ^ k := by ring
  have hlogK : Real.log 10 * (K * R ^ k) ≤ 3 * K * R ^ k := by
    calc Real.log 10 * (K * R ^ k) ≤ 3 * (K * R ^ k) := mul_le_mul_of_nonneg_right hlog hKR
      _ = 3 * K * R ^ k := by ring
  have h9 : 9 * R ≤ L * R := mul_le_mul_of_nonneg_right hL hR.le
  have hL99 : (10 : ℝ) / 99 ≤ L := by linarith
  have hroot : (∑' i : I, ENNReal.ofReal (4 * P.scale (r i).1.1) ^ k) ≤
      ENNReal.ofReal (3 * K * R ^ k) :=
    (le_of_eq (r.tsum_eq (fun S : SD.roots => ENNReal.ofReal (4 * P.scale S.1.1) ^ k))).trans
      (SD.root_packing.trans (ENNReal.ofReal_le_ofReal hK3))
  have hlocal : ∀ (w : Space n) (s : ℝ), 0 < s →
      (∑' i : I, if (r i).1.2 ∈ Metric.ball w s ∧ 4 * P.scale (r i).1.1 ≤ s then
          ENNReal.ofReal (4 * P.scale (r i).1.1) ^ k else 0) ≤
        ENNReal.ofReal (3 * K * s ^ k) := by
    intro w s hs
    have hKs0 : 0 ≤ K * s ^ k := mul_nonneg hK (pow_nonneg hs.le k)
    have hKs : K * s ^ k ≤ 3 * K * s ^ k := by
      calc K * s ^ k ≤ 3 * (K * s ^ k) := by linarith
        _ = 3 * K * s ^ k := by ring
    exact (le_of_eq (r.tsum_eq (fun S : SD.roots =>
      if S.1.2 ∈ Metric.ball w s ∧ 4 * P.scale S.1.1 ≤ s then
        ENNReal.ofReal (4 * P.scale S.1.1) ^ k else 0))).trans
      ((SD.local_packing w s hs).trans (ENNReal.ofReal_le_ofReal hKs))
  have hBG : ∀ i : I, pointScaleMeasure μ (badSlabs SD ∩ goodSlabs SD (r i)) = 0 := by
    intro i
    rw [(hdisjBG (r i)).inter_eq]
    exact measure_empty
  have hGG : ∀ i j : I, i ≠ j →
      pointScaleMeasure μ (goodSlabs SD (r i) ∩ goodSlabs SD (r j)) = 0 := by
    intro i j hij
    rw [(hdisjGG (r i) (r j) (r.injective.ne hij)).inter_eq]
    exact measure_empty
  have hempty : rootPairs μ a R \ (badSlabs SD ∪ ⋃ i : I, goodSlabs SD (r i)) = ∅ := by
    rw [Set.sdiff_eq_empty]
    intro p hp
    rcases hcover hp with h | h
    · exact Or.inl h
    · obtain ⟨S, hS⟩ := mem_iUnion.mp h
      exact Or.inr (mem_iUnion.mpr ⟨r.symm S, by rw [Equiv.apply_symm_apply]; exact hS⟩)
  have hnull : pointScaleMeasure μ
      (rootPairs μ a R \ (badSlabs SD ∪ ⋃ i : I, goodSlabs SD (r i))) = 0 := by
    rw [hempty]
    exact measure_empty
  have hsc : ∀ i : I, goodSlabs SD (r i) ⊆
      {p : Space n × ℝ | p.1 ∈ Metric.ball a R ∩ Metric.ball (r i).1.2 (4 * P.scale (r i).1.1) ∧
        L⁻¹ * Metric.infDist p.1 (ref (r i)).carrier ≤ p.2 ∧ p.2 < 4 * P.scale (r i).1.1} :=
    fun i => hGood n μ a R P k Λ b K SD (r i) δ κ θ γ (tn (r i)) (ref (r i)).carrier
      (href (r i)) L hL99
  have hbad : pointScaleMeasure μ (badSlabs SD) ≤ ENNReal.ofReal (3 * K * R ^ k) :=
    (hBad n μ a R P k Λ b K SD).trans (ENNReal.ofReal_le_ofReal hlogK)
  exact ⟨{
    index := I
    reference := fun i => ref (r i)
    center := fun i => (r i).1.2
    radius := fun i => 4 * P.scale (r i).1.1
    badSet := badSlabs SD
    scaleSet := fun i => goodSlabs SD (r i)
    center_mem_support := fun i => (hball i).1
    radius_pos := fun i => (hball i).2.1
    ball_subset := fun i => Set.Subset.trans (hball i).2.2.1 (Metric.ball_subset_ball h9)
    ball_meets_carrier := fun i => (hball i).2.2.2
    root_packing := hroot
    local_packing := hlocal
    measurable_badSet := hmeasB
    measurable_scaleSet := fun i => hmeasG (r i)
    badSet_subset := hsubB
    scaleSet_subset := fun i => hsubG (r i)
    bad_inter_scale_null := hBG
    scale_inter_scale_null := hGG
    cover_null := hnull
    scaleSet_cover := hsc
    bad_bound := hbad }⟩

/-- **The covering assembly in implication form.** The ten proofs of the intermediate covering
statements, with `Terminal.StopScaleLipschitzStatement` as the one premise, give
`CoverageAssemblyStatement`. -/
theorem d1fcomp_coverageAssembly_of_input :
    Terminal.StopScaleLipschitzStatement → CoverageAssemblyStatement :=
  fun hL => d1fcomp_coverageAssembly_of (d1f_indexing_proof d1f_slabBasics_proof)
    d1f_modelBall_proof (d1f_slabFamily_proof d1f_slabBasics_proof)
    (d1f_slabPartition_proof d1f_slabCover_proof d1f_slabDisjoint_proof)
    (d1f_goodSlabCover_proof (d1f_coverage_proof hL)) (d1f_badCost_proof d1f_slabBasics_proof)
    d1f_logTen_le_three_proof

end Coverage

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
