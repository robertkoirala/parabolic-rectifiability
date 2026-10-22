import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Divergence outside the common set of segment endpoints

The proof uses the weight bounds, the divergence of fractional weight powers, the label
bounds, the band beta bound, the nearest cell midpoint and the band-energy estimate. A
point outside all labelled
endpoints has a positive margin in any containing segment. At every sufficiently fine
scale, its baseline and a nearby labelled child lie in the same fixed source. The band
lower bound and the divergent weight series then give the genuine Euclidean energy.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.BetaP (Plane horizontalSegment)

private theorem sap_child_mem_index (n j m : ℕ) (hn : n ∈ e2_sapIndex)
    (hj : 1 ≤ j) (hm : m < e2_sapN j) :
    Encodable.encode ((j, m) :: e2_sapLabel n) ∈ e2_sapIndex := by
  change e2_sapValid (e2_sapLabel (Encodable.encode ((j, m) :: e2_sapLabel n)))
  rw [e2_sapLabel, Denumerable.ofNat_encode]
  intro q hq
  rcases List.mem_cons.mp hq with hq | hq
  · subst q
    exact ⟨hj, hm⟩
  · exact hn q hq

private theorem sap_child_segment_subset (n j m : ℕ) (hn : n ∈ e2_sapIndex)
    (hj : 1 ≤ j) (hm : m < e2_sapN j) :
    horizontalSegment
      (e2_sapLeft n + ((m : ℝ) + 1 / 2) * (e2_sapLength n / (e2_sapN j : ℝ)) -
        e2_sapDelta j * (e2_sapLength n / (e2_sapN j : ℝ)) / 2)
      (e2_sapLeft n + ((m : ℝ) + 1 / 2) * (e2_sapLength n / (e2_sapN j : ℝ)) +
        e2_sapDelta j * (e2_sapLength n / (e2_sapN j : ℝ)) / 2)
      (e2_sapHeight n + e2_sapLength n / (e2_sapN j : ℝ)) ⊆ e2_sapSet := by
  let k := Encodable.encode ((j, m) :: e2_sapLabel n)
  have hk : k ∈ e2_sapIndex := sap_child_mem_index n j m hn hj hm
  have heq : e2_sapLabel k = (j, m) :: e2_sapLabel n :=
    Denumerable.ofNat_encode _
  have hseg := Set.subset_iUnion
    (fun i : e2_sapIndex =>
      horizontalSegment (e2_sapLeft i) (e2_sapRight i) (e2_sapHeight i)) ⟨k, hk⟩
  change horizontalSegment _ _ _ ⊆ e2_sapSet at hseg
  convert hseg using 1
  simp only [e2_sapLeft, e2_sapRight, e2_sapLength, e2_sapHeight, heq,
    e2_sapSeg, e2_sapChild]
  congr 1
  ring

private theorem sap_eventually_small (L ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j ≥ J, L / (e2_sapN j : ℝ) < ε := by
  have hpow : Tendsto (fun j : ℕ => (8 : ℝ) ^ (j + 1)) atTop atTop :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hlim : Tendsto (fun j : ℕ => L / (e2_sapN j : ℝ)) atTop (𝓝 0) := by
    simpa only [e2_sapN, Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_const_nhds.div_atTop hpow :
        Tendsto (fun j : ℕ => L / (8 : ℝ) ^ (j + 1)) atTop (𝓝 0))
  exact Filter.eventually_atTop.1 (hlim.eventually (gt_mem_nhds hε))

/-- Off the common set of segment endpoints, the energy of the decorated segment source
diverges; the same endpoint set serves all exponents and cutoffs. -/
theorem e2_sap_divergence_proof (hW : E2sapWeights) (hD : E2sapWeightsDiverge)
    (hG : E2sapLabelBounds) (hB : E2sapBandBeta) (hC : E2sapCell) (hE : E2sapBandEnergy) :
    E2sapDivergenceOff := by
  intro z hz p hp a ha
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.1 hz.1
  change e2_sapLeft i ≤ z 0 ∧ z 0 ≤ e2_sapRight i ∧ z 1 = e2_sapHeight i at hzi
  have hzpt : z = e2_sapPt (z 0) (e2_sapHeight i) := by
    ext k
    fin_cases k <;> simp [e2_sapPt, hzi.2.2]
  have hleft : e2_sapLeft i < z 0 := by
    by_contra h
    have heq : z 0 = e2_sapLeft i := le_antisymm (le_of_not_gt h) hzi.1
    apply hz.2
    exact Set.mem_iUnion.2 ⟨i, Or.inl (by rw [hzpt, heq])⟩
  have hright : z 0 < e2_sapRight i := by
    by_contra h
    have heq : z 0 = e2_sapRight i := le_antisymm hzi.2.1 (le_of_not_gt h)
    apply hz.2
    exact Set.mem_iUnion.2 ⟨i, Or.inr (by rw [hzpt, heq]; rfl)⟩
  have hL : 0 < e2_sapLength i := by
    have h := (hG i i.property).1
    unfold e2_sapRight at h
    linarith
  have hmargin : 0 < min (z 0 - e2_sapLeft i) (e2_sapRight i - z 0) :=
    lt_min (sub_pos.mpr hleft) (sub_pos.mpr hright)
  obtain ⟨J, hJ⟩ := sap_eventually_small (e2_sapLength i) _ hmargin
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  have hq0 : 0 < 2 / p := div_pos (by norm_num) hp0
  have hq1 : 2 / p < 1 := (div_lt_one hp0).2 hp
  have hA : 0 < e2_sapFitConst p * (4 : ℝ) ^ (-p - 1) := by
    unfold e2_sapFitConst
    apply mul_pos
    · exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
        (lt_min (by norm_num) (div_pos (by norm_num) (by linarith)))
    · exact Real.rpow_pos_of_pos (by norm_num) _
  unfold euclideanEnergyS
  apply hE (fun r => euclideanBetaPow (μH[1].restrict e2_sapSet) 1 p z r)
    e2_sapDelta (e2_sapLength i) (e2_sapFitConst p * (4 : ℝ) ^ (-p - 1)) p a (max J 1)
    hL hA hp ha (fun j => (hW.1 j).1.le) (hD (2 / p) hq0 hq1)
  intro j hj r hrlo hrhi
  have hjJ : J ≤ j := (le_max_left J 1).trans hj
  have hj1 : 1 ≤ j := (le_max_right J 1).trans hj
  have hsmall := hJ j hjJ
  have hhleft : e2_sapLength i / (e2_sapN j : ℝ) < z 0 - e2_sapLeft i :=
    lt_of_lt_of_le hsmall (min_le_left _ _)
  have hhright : e2_sapLength i / (e2_sapN j : ℝ) < e2_sapRight i - z 0 :=
    lt_of_lt_of_le hsmall (min_le_right _ _)
  have hN : (0 : ℝ) < (e2_sapN j : ℝ) := by
    exact_mod_cast (show 0 < e2_sapN j by unfold e2_sapN; positivity)
  have hh : 0 < e2_sapLength i / (e2_sapN j : ℝ) := div_pos hL hN
  obtain ⟨m, hm, hmid⟩ := hC (e2_sapLeft i) (e2_sapLength i) (z 0) j
    hL hzi.1 hright
  have hbase : horizontalSegment
      (z 0 - e2_sapLength i / (e2_sapN j : ℝ))
      (z 0 + e2_sapLength i / (e2_sapN j : ℝ)) (e2_sapHeight i) ⊆ e2_sapSet := by
    intro w hw
    apply Set.mem_iUnion.2
    refine ⟨i, ?_⟩
    change e2_sapLeft i ≤ w 0 ∧ w 0 ≤ e2_sapRight i ∧ w 1 = e2_sapHeight i
    exact ⟨by linarith [hw.1], by linarith [hw.2.1], hw.2.2⟩
  have hchild := sap_child_segment_subset i j m i.property hj1 hm
  have hbound := hB e2_sapSet p hp (z 0) (e2_sapHeight i)
    (e2_sapLength i / (e2_sapN j : ℝ)) (e2_sapDelta j)
    (e2_sapLeft i + ((m : ℝ) + 1 / 2) * (e2_sapLength i / (e2_sapN j : ℝ)) - z 0)
    hh (hW.1 j).1 (hW.1 j).2.le hmid hbase
  have hcancel : z 0 +
      (e2_sapLeft i + ((m : ℝ) + 1 / 2) * (e2_sapLength i / (e2_sapN j : ℝ)) - z 0) =
      e2_sapLeft i + ((m : ℝ) + 1 / 2) * (e2_sapLength i / (e2_sapN j : ℝ)) := by ring
  rw [hcancel] at hbound
  simpa only [← hzpt] using hbound hchild r hrlo hrhi

end ParabolicRectifiability.Examples
