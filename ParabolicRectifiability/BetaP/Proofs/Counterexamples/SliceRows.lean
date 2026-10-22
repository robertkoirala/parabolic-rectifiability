import ParabolicRectifiability.BetaP.Proofs.Counterexamples.RowLemmas
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.RowSupport
import ParabolicRectifiability.BetaP.Proofs.Laws.Basic
import ParabolicRectifiability.BetaP.Proofs.Laws.ScaleThreshold
import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.RestrictionLowerDensity

/-! # The `S_p` rows and failure at `n = 2`, `k = 1`

The `S_p` rows and failure at `n = 2`, `k = 1`, through the constant-time slice. Each theorem
named `c2_…_of_witness` proves the corresponding statement:

* `c2_spBelowTwo_notSufficient_of_witness` proves `spBelowTwo_notSufficient_of_witness`;
* `c2_spAboveTwo_notNecessary_of_witness` proves `spAboveTwo_notNecessary_of_witness`;
* `c2_spBelowTwo_noVanishingRemainder_of_witness` proves
  `spBelowTwo_noVanishingRemainder_of_witness`, from the uniform tails, rescaled carrier
  nullity, time slice and rescaled mass statements.

The inputs are used exactly as their hypotheses give them: the witness statements
`DirectWitnessMinusStatement` / `DirectWitnessPlusStatement` and the transfer
`TimeSliceTransferStatement` (the `B_p` and `S_p` clause at every endpoint; the Hausdorff-source
clause). The generic restricted-Hausdorff density lemmas are not used: the witnesses' own density
clauses transfer through the ball identity of the time slice. The results used by name are
`claws_restriction_proof` (restriction law), `cscale_rescaledSource_betaP_threshold_proof` (scale
threshold) and `Characterization.b4_hausdorff_restrict_ball_lower_bound_proof` (lower mass for the
same restricted Hausdorff source).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## Slice bookkeeping -/

/-- The parabolic density ratio of a slice source at `ιx` is the planar ratio at `x`. -/
theorem c2_slice_densityRatio
    (hball : ∀ (ν : Measure Plane) (x : Plane) (r : ℝ),
      (ν.map timeSlice) (Metric.ball (timeSlice x) r) = ν (Metric.ball x r))
    (ν : Measure Plane) (x : Plane) :
    densityRatio (ν.map timeSlice) 1 (timeSlice x) = planarDensityRatio ν x := by
  funext r
  simp only [densityRatio, planarDensityRatio, hball, pow_one]

/-- The parabolic upper `1`-density of a slice source at `ιx` is the planar upper density at `x`. -/
theorem c2_slice_upperDensity
    (hball : ∀ (ν : Measure Plane) (x : Plane) (r : ℝ),
      (ν.map timeSlice) (Metric.ball (timeSlice x) r) = ν (Metric.ball x r))
    (ν : Measure Plane) (x : Plane) :
    upperDensity (ν.map timeSlice) 1 (timeSlice x) = planarUpperDensity ν x := by
  unfold upperDensity planarUpperDensity
  rw [c2_slice_densityRatio hball ν x]

/-- At `n = 2`, `k = 1` a measure carried by zero-slope horizontal graphs covering a full set is
carried by finitely-normed mixed graphs and has mixed measure covers of every positive slope (the
vertical family is empty at `k = 1`; a slope-`0` graph has every slope `ε ≥ 0`). -/
theorem c2_zeroSlope_cover {μ : Measure (Space 2)} {A : Set (Space 2)} (hA : μ Aᶜ = 0)
    (I : Set ℕ) (G : I → HorizontalGraph 2 1 0) (hcov : A ⊆ ⋃ i, (G i).image) :
    IsCarriedByFiniteNormGraphs .mixed 1 μ ∧
      ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover .mixed 1 μ ε := by
  refine ⟨⟨I, ∅, fun _ => 0, G, fun _ => 0,
    fun j => ((Set.mem_empty_iff_false _).mp j.2).elim, ?_⟩, fun ε hε => ?_⟩
  · exact measure_mono_null (compl_subset_compl.mpr (hcov.trans subset_union_left)) hA
  · let G' : I → HorizontalGraph 2 1 ε := fun i =>
      { direction := (G i).direction
        rank_eq := (G i).rank_eq
        domain := (G i).domain
        offset := (G i).offset
        normal := (G i).normal
        time := (G i).time
        small_slope := fun u v => ((G i).small_slope u v).trans
          (by rw [zero_mul]; exact mul_nonneg hε.le (norm_nonneg _)) }
    have hcov' : A ⊆ ⋃ i, (G' i).image := fun x hx => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
      exact mem_iUnion.mpr ⟨i, hi⟩
    exact ⟨I, ∅, G', fun j => ((Set.mem_empty_iff_false _).mp j.2).elim,
      measure_mono_null (compl_subset_compl.mpr (hcov'.trans subset_union_left)) hA⟩

/-- Divergence off a countable set: if `P` fails on `E \ Z` with `Z` countable and `H¹(E) ≠ 0`,
then `P` does not hold `H¹⌊E`-almost everywhere. -/
theorem c2_countable_divergence {E Z : Set Plane} {P : Plane → Prop} (hE : MeasurableSet E)
    (hE0 : μH[1] E ≠ 0) (hZ : Z.Countable) (hP : ∀ x ∈ E \ Z, ¬ P x) :
    ¬ ∀ᵐ x ∂(μH[1].restrict E), P x := by
  intro h
  have : NullSingletonClass (μH[1] : Measure Plane) :=
    Measure.nullSingletonClass_hausdorff Plane one_pos
  have h1 : (μH[1].restrict E) (E \ Z) = 0 :=
    measure_mono_null (fun x hx => hP x hx) (ae_iff.mp h)
  rw [Measure.restrict_apply' hE, Set.inter_eq_left.mpr Set.sdiff_subset] at h1
  have h2 : μH[1] Z = 0 := hZ.measure_zero _
  apply hE0
  refine le_antisymm ?_ zero_le
  calc μH[1] E ≤ μH[1] ((E \ Z) ∪ Z) := measure_mono fun x hx => by
        by_cases hz : x ∈ Z
        · exact Or.inr hz
        · exact Or.inl ⟨hx, hz⟩
    _ ≤ μH[1] (E \ Z) + μH[1] Z := measure_union_le _ _
    _ = 0 := by rw [h1, h2, add_zero]

/-! ## `S_p` is not sufficient below two -/

/-- **`S_p` is not sufficient below two**, from the witness: the statement
`spBelowTwo_notSufficient_of_witness`. The source is `μ = ι_#(H¹⌊E₋)`: finite
(mass `H¹(E₋) = 1`), hence locally Radon; its upper `1`-density at `ιx` is the planar one, in
`[1/2, 2]` on `E₋` (ball identity of the time slice); `S_p^a(ιx) = S_p^{a,E}(x) ≤ B` (by
`TimeSliceTransferStatement`); and a mixed carrier
would be horizontal only (no vertical graph at `k = 1`), every horizontal graph meets `ι(E₋)` in an
`H_P^1`-null set, and `μ = H_P^1⌊ι(E₋)` (Hausdorff clause of the transfer) would vanish. -/
theorem c2_spBelowTwo_notSufficient_of_witness (hW : DirectWitnessMinusStatement)
    (hTS : TimeSliceTransferStatement) : SpBelowTwoNotSufficientStatement := by
  obtain ⟨hME, hball⟩ := c2_timeSlice_measure
  obtain ⟨E, hEc, hE1, -, hdens, hSp, -, hnull⟩ := hW
  intro p hp hp2 a ha
  have hEm : MeasurableSet E := hEc.isClosed.measurableSet
  have hfin : IsFiniteMeasure (μH[1].restrict E) :=
    ⟨by rw [Measure.restrict_apply_univ, hE1]; exact ENNReal.one_lt_top⟩
  refine ⟨(μH[1].restrict E).map timeSlice, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · refine hME.ae_map_iff.mpr ((ae_restrict_mem hEm).mono fun x hx => ?_)
    rw [c2_slice_upperDensity hball]
    exact ⟨lt_of_lt_of_le (by simp) (hdens x hx).1, lt_of_le_of_lt (hdens x hx).2 (by simp)⟩
  · obtain ⟨B, hB⟩ := hSp p hp hp2 a ha
    refine hME.ae_map_iff.mpr ((ae_restrict_mem hEm).mono fun x hx => ?_)
    rw [(hTS.1 (μH[1].restrict E) p hp .mixed (Or.inr rfl) x).2 a ha]
    exact (hB x hx).trans_lt ENNReal.ofReal_lt_top
  · rintro ⟨-, I, J, εH, H, εV, V, hcarr⟩
    have hHs := hTS.2 E hEm
    have hAm : MeasurableSet (timeSlice '' E) := hME.measurableSet_image' hEm
    have hV : (⋃ j, (V j).image) = ∅ :=
      Set.iUnion_eq_empty.mpr fun j => absurd (V j).vertical_dimension (by norm_num)
    have hH : (μH[1].restrict E).map timeSlice (⋃ i, (H i).image) = 0 :=
      measure_iUnion_null fun i => by
        rw [hHs, Measure.restrict_apply' hAm, Set.inter_comm]
        exact hnull (εH i) (H i)
    have huniv : (μH[1].restrict E).map timeSlice univ = 0 := by
      refine le_antisymm ?_ zero_le
      calc (μH[1].restrict E).map timeSlice univ
          ≤ (μH[1].restrict E).map timeSlice ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image) +
              (μH[1].restrict E).map timeSlice ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)ᶜ :=
            measure_univ_le_add_compl _
        _ = 0 := by rw [hcarr, hV, Set.union_empty, hH, add_zero]
    rw [hME.map_apply, Set.preimage_univ, Measure.restrict_apply_univ, hE1] at huniv
    exact one_ne_zero huniv

/-! ## `S_p` is not necessary above two -/

/-- **`S_p` is not necessary above two**, from the witness: the statement
`spAboveTwo_notNecessary_of_witness`. The source is
`μ = ι_#(H¹⌊E₊)`: finite (`H¹(E₊) ≤ 100/99`); the planar density limit `2` of the witness
transfers through the ball identity of the time slice; `μ = H_P^1⌊ι(E₊) ≪ H_P^1` (Hausdorff clause
of the transfer); the exact zero-slope cover of the witness gives the carrier and covers of every
positive slope; divergence of `S_p^{a,E}` on `E₊ \ Z`, `Z` countable, transfers and kills a.e.
finiteness (`H¹(Z) = 0`, `H¹(E₊) ≥ 1`). -/
theorem c2_spAboveTwo_notNecessary_of_witness (hW : DirectWitnessPlusStatement)
    (hTS : TimeSliceTransferStatement) : SpAboveTwoNotNecessaryStatement := by
  obtain ⟨hME, hball⟩ := c2_timeSlice_measure
  obtain ⟨E, hEm, -, -, hE1, hE2, hdens, ⟨Z, hZ, hdiv⟩, I, G, hcov⟩ := hW
  intro p hp a ha
  have hfin : IsFiniteMeasure (μH[1].restrict E) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hE2.trans_lt ENNReal.ofReal_lt_top⟩
  have hnull : (μH[1].restrict E).map timeSlice (timeSlice '' E)ᶜ = 0 := by
    rw [hME.map_apply, Set.preimage_compl, hME.injective.preimage_image,
      Measure.restrict_apply hEm.compl, Set.compl_inter_self, measure_empty]
  have hcarr := c2_zeroSlope_cover hnull I G hcov
  refine ⟨(μH[1].restrict E).map timeSlice, inferInstance, inferInstance, ?_,
    ⟨⟨?_, hcarr.1⟩, hcarr.2⟩, ?_⟩
  · refine hME.ae_map_iff.mpr (hdens.mono fun x hx => ?_)
    have h2 : upperDensity ((μH[1].restrict E).map timeSlice) 1 (timeSlice x) = 2 := by
      rw [c2_slice_upperDensity hball]
      exact hx.limsup_eq
    rw [h2]
    exact ⟨by simp, by simp⟩
  · rw [hTS.2 E hEm]
    exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  · intro hfin'
    have h1 := hME.ae_map_iff.mp hfin'
    have h2 : ∀ᵐ x ∂(μH[1].restrict E), euclideanEnergyS (μH[1].restrict E) 1 p a x < ⊤ :=
      h1.mono fun x hx => by
        rwa [(hTS.1 (μH[1].restrict E) p (by linarith) .mixed (Or.inr rfl) x).2 a ha] at hx
    exact c2_countable_divergence hEm (zero_lt_one.trans_le hE1).ne' hZ
      (fun x hx => by rw [hdiv x hx p hp a ha]; exact lt_irrefl _) h2

/-! ## No vanishing `S_p` remainder below two -/

/-- **No vanishing `S_p` remainder below two**, from the witness: the statement
`spBelowTwo_noVanishingRemainder_of_witness`. The argument uses the same restricted source
throughout:
`ω = ι_#(H¹⌊E₋) = H_P^1⌊ι(E₋)` (by the transfer) has finite `S_p^1` on `ι(E₋)` (witness bound
and transfer); `c2_uniform_tails` gives a compact `K ⊆ ι(E₋)` of positive mass with uniformly
small tails, inherited by `ν = ω⌊K = H_P^1⌊K` (restriction law); the lower-mass theorem
`b4_hausdorff_restrict_ball_lower_bound_proof` gives `c₁` and a point `z ∈ K` with arbitrarily
small lower-mass radii; `M > 0` with `Φ(M) < c₁`, `h` from the tails, `r < h/2` from that
theorem; the rescaled source `ν̃ = rescaledSource ν 1 z r` is locally Radon with zero exceptional
mass (scale threshold identity, `S_{p,ν}^{2r} ≤ S_{p,ν}^h ≤ M` on `K`) and
unit-ball mass `≥ c₁` (`c2_rescaled_mass`); `c2_rescaled_carrier_null` kills every horizontally
rectifiable compact support, so the good measure vanishes and `c₁ ≤ Φ(M)`, a contradiction. -/
theorem c2_spBelowTwo_noVanishingRemainder_of_witness (hW : DirectWitnessMinusStatement)
    (hTS : TimeSliceTransferStatement) : SpBelowTwoNoVanishingRemainderStatement := by
  obtain ⟨hME, -⟩ := c2_timeSlice_measure
  obtain ⟨E, hEc, hE1, -, -, hSp, -, hnull⟩ := hW
  rintro p hp hp2 ⟨Φ, hΦ0, hΦlim, hΦ⟩
  have hEm : MeasurableSet E := hEc.isClosed.measurableSet
  have hT : Nonempty (Models 2 1 .mixed) :=
    AdmissibleModel.nonempty_of_range (by norm_num) le_rfl (by norm_num)
  have hfin : IsFiniteMeasure (μH[1].restrict E) :=
    ⟨by rw [Measure.restrict_apply_univ, hE1]; exact ENNReal.one_lt_top⟩
  -- the slice source `ω = ι_#(H¹⌊E₋) = H_P^1⌊ι(E₋)`
  have hHs : (μH[1].restrict E).map timeSlice = (hausdorffP 2 1).restrict (timeSlice '' E) :=
    hTS.2 E hEm
  have hωA : (μH[1].restrict E).map timeSlice (timeSlice '' E)ᶜ = 0 := by
    rw [hME.map_apply, Set.preimage_compl, hME.injective.preimage_image,
      Measure.restrict_apply hEm.compl, Set.compl_inter_self, measure_empty]
  have hωpos : 0 < (μH[1].restrict E).map timeSlice (timeSlice '' E) := by
    rw [hME.map_apply, hME.injective.preimage_image, Measure.restrict_apply hEm, Set.inter_self,
      hE1]
    exact zero_lt_one
  obtain ⟨B, hB⟩ := hSp p hp hp2 1 one_pos
  have hfinS : ∀ y ∈ timeSlice '' E,
      energyS ((μH[1].restrict E).map timeSlice) 1 .mixed p 1 y < ⊤ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [(hTS.1 (μH[1].restrict E) p hp .mixed (Or.inr rfl) x).2 1 one_pos]
    exact (hB x hx).trans_lt ENNReal.ofReal_lt_top
  -- a compact `K ⊆ ι(E₋)` of positive mass with uniformly small tails
  obtain ⟨K, hKc, hKA, hKpos, hKtail⟩ :=
    c2_uniform_tails 2 (by norm_num) 1 le_rfl (by norm_num) .mixed hT
      ((μH[1].restrict E).map timeSlice) inferInstance p hp (timeSlice '' E) hωA hωpos hfinS
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  -- the same restricted source `ν = ω⌊K = H_P^1⌊K`
  have hνH : ((μH[1].restrict E).map timeSlice).restrict K = (hausdorffP 2 1).restrict K := by
    rw [hHs, Measure.restrict_restrict hKm, Set.inter_eq_left.mpr hKA]
  have hνK : ((μH[1].restrict E).map timeSlice).restrict K Kᶜ = 0 := by
    rw [Measure.restrict_apply hKm.compl, Set.compl_inter_self, measure_empty]
  have hHK : hausdorffP 2 1 K < ⊤ := by
    have h1 : hausdorffP 2 1 K = (μH[1].restrict E).map timeSlice K := by
      rw [hHs, Measure.restrict_apply hKm, Set.inter_eq_left.mpr hKA]
    rw [h1]
    exact measure_lt_top _ K
  have hνc : IsFiniteMeasureOnCompacts (((μH[1].restrict E).map timeSlice).restrict K) :=
    inferInstance
  have hνr : (((μH[1].restrict E).map timeSlice).restrict K).InnerRegular := inferInstance
  -- uniform tails of `ν` on `K` (restriction law, proved)
  have hνtail : ∀ M : ℝ, 0 < M → ∃ h : ℝ, 0 < h ∧ ∀ y ∈ K,
      energyS (((μH[1].restrict E).map timeSlice).restrict K) 1 .mixed p h y ≤
        ENNReal.ofReal M := by
    intro M hM
    obtain ⟨h, hh, hK⟩ := hKtail M hM
    refine ⟨h, hh, fun y hy => ?_⟩
    exact ((claws_restriction_proof 2 (by norm_num) 1 le_rfl (by norm_num) .mixed hT
      ((μH[1].restrict E).map timeSlice) K p hp).2 h hh y).1.trans (hK y hy)
  -- lower mass for the restricted Hausdorff source: a point `z ∈ K` with arbitrarily small
  -- lower-mass radii for the same `ν`
  obtain ⟨c₁, hc₁, hLR⟩ :=
    Characterization.b4_hausdorff_restrict_ball_lower_bound_proof 2 (by norm_num) 1 le_rfl
      (by norm_num)
  have hLRK := hLR K hKm hHK
  rw [← hνH] at hLRK
  have hν0 : ((μH[1].restrict E).map timeSlice).restrict K ≠ 0 := by
    intro h0
    have h1 : ((μH[1].restrict E).map timeSlice).restrict K univ = 0 := by simp [h0]
    rw [Measure.restrict_apply_univ] at h1
    exact hKpos.ne' h1
  have : (ae (((μH[1].restrict E).map timeSlice).restrict K)).NeBot := ae_neBot.mpr hν0
  obtain ⟨z, -, hzLR⟩ :=
    ((Filter.eventually_mem_set.mpr (mem_ae_iff.mpr hνK)).and hLRK).exists
  -- a threshold `M > 0` with `Φ(M) < c₁`
  obtain ⟨M, hM, hΦM⟩ : ∃ M : ℝ, 0 < M ∧ Φ M < c₁ :=
    (eventually_mem_nhdsWithin.and (hΦlim.eventually (gt_mem_nhds hc₁))).exists
  obtain ⟨h, hh, hνh⟩ := hνtail M hM
  obtain ⟨r, hr, hrh, hrmass⟩ := hzLR (h / 2) (half_pos hh)
  -- the normalized rescaling at the lower-mass radius (`cscale_rescaledSource_betaP_threshold_proof`)
  obtain ⟨hνtc, hνtr, hthr, -⟩ :=
    cscale_rescaledSource_betaP_threshold_proof (by norm_num : 1 ≤ 2) (le_rfl : 1 ≤ 1)
      (by norm_num : 1 ≤ 2 + 2) .mixed (((μH[1].restrict E).map timeSlice).restrict K) hνc hνr
      z r hr p hp M
  have hexc : (rescaledSource (((μH[1].restrict E).map timeSlice).restrict K) 1 z r hr)
      (Metric.ball (point 0 0) 1 ∩ {w | ENNReal.ofReal M <
        energyS (rescaledSource (((μH[1].restrict E).map timeSlice).restrict K) 1 z r hr)
          1 .mixed p 2 w}) ≤ ENNReal.ofReal 0 := by
    rw [hthr, ENNReal.ofReal_zero]
    have h0 : ((μH[1].restrict E).map timeSlice).restrict K (Metric.ball z r ∩
        {w | ENNReal.ofReal M <
          energyS (((μH[1].restrict E).map timeSlice).restrict K) 1 .mixed p (2 * r) w}) = 0 := by
      refine measure_mono_null ?_ hνK
      intro w hw
      rw [Set.mem_compl_iff]
      intro hwK
      have hmono : energyS (((μH[1].restrict E).map timeSlice).restrict K) 1 .mixed p (2 * r) w ≤
          energyS (((μH[1].restrict E).map timeSlice).restrict K) 1 .mixed p h w := by
        unfold energyS
        exact lintegral_mono_set (Set.Ioo_subset_Ioo_right (by linarith))
      exact absurd hw.2 (not_lt.mpr (hmono.trans (hνh w hwK)))
    rw [h0, mul_zero]
  have hmass : ENNReal.ofReal c₁ ≤
      (rescaledSource (((μH[1].restrict E).map timeSlice).restrict K) 1 z r hr)
        (Metric.ball (point 0 0) 1) :=
    c2_rescaled_mass 2 1 _ z r hr c₁ hc₁.le hrmass
  -- the decomposition supplied by `Φ`; its good measure vanishes
  obtain ⟨μplus, μG, K', hdec, hrem, hK'c, hG, hcov⟩ := hΦ _ hνtc hνtr M 0 hM le_rfl hexc
  have hK'0 : rescaledSource (((μH[1].restrict E).map timeSlice).restrict K) 1 z r hr K' = 0 := by
    have h := c2_rescaled_carrier_null K hKm
      (fun ε G => measure_mono_null (Set.inter_subset_inter_left _ hKA) (hnull ε G))
      z r hr K' hK'c hcov
    rwa [← hνH] at h
  rw [c2_eq_of_good_null hdec hG hK'0, add_zero] at hrem
  have hc := hmass.trans hrem
  rw [ENNReal.ofReal_le_ofReal_iff (hΦ0 M)] at hc
  linarith

end ParabolicRectifiability.BetaP
