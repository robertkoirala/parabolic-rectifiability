import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Density at a good point of a countable family of horizontal levels

The finite head disappears off the selected level. The remaining mass is bounded
by the integral of the tail. We first divide by the real closed-ball volume, so
all estimates stay in `ℝ≥0∞`; the planar normalization then contributes `2`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace ParabolicRectifiability.Examples
open ParabolicRectifiability.BetaP (Plane planarDensityRatio)

private lemma level_dist (u s b : ℝ) :
    dist (e2_sapPt u b) (e2_sapPt s b) = dist u s := by
  simp [EuclideanSpace.dist_eq, e2_sapPt, Fin.sum_univ_two]

private lemma level_measurable (b : ℝ) : Measurable (fun u => e2_sapPt u b) := by
  have h : Isometry (fun u => e2_sapPt u b) :=
    Isometry.of_dist_eq (fun u s => level_dist u s b)
  exact h.continuous.measurable

private lemma level_ball_subset (u s b d r : ℝ)
    (h : e2_sapPt u b ∈ Metric.ball (e2_sapPt s d) r) :
    u ∈ Metric.closedBall s r := by
  exact (show dist u s ≤ dist (e2_sapPt u b) (e2_sapPt s d) by
    simpa [e2_sapPt] using PiLp.dist_apply_le (e2_sapPt u b) (e2_sapPt s d) 0).trans
      (le_of_lt h)

private lemma level_ball_miss (s b d r : ℝ) (h : r < dist b d) :
    (fun u => e2_sapPt u b) ⁻¹' Metric.ball (e2_sapPt s d) r = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have hd : dist b d ≤ dist (e2_sapPt u b) (e2_sapPt s d) := by
    simpa [e2_sapPt] using PiLp.dist_apply_le (e2_sapPt u b) (e2_sapPt s d) 1
  exact (not_lt_of_ge hd) (lt_trans hu h)

private lemma level_ball_mass (A : Set ℝ) (s b r : ℝ) :
    ((volume.restrict A).map (fun u => e2_sapPt u b))
      (Metric.ball (e2_sapPt s b) r) = volume (A ∩ Metric.closedBall s r) := by
  rw [Measure.map_apply (level_measurable b) measurableSet_ball]
  have hp : (fun u => e2_sapPt u b) ⁻¹' Metric.ball (e2_sapPt s b) r =
      Metric.ball s r := by
    ext u
    simp only [mem_preimage, Metric.mem_ball, level_dist]
  rw [hp, Measure.restrict_apply measurableSet_ball, inter_comm]
  apply measure_congr
  have he : Metric.ball s r =ᵐ[volume] Metric.closedBall s r := by
    simpa only [Real.ball_eq_Ioo, Real.closedBall_eq_Icc] using
      (Ioo_ae_eq_Icc : Ioo (s-r) (s+r) =ᵐ[volume] Icc (s-r) (s+r))
  filter_upwards [he] with u hu
  simp only [mem_inter_iff, hu]

private lemma level_ball_le (A : Set ℝ) (s b d r : ℝ) :
    ((volume.restrict A).map (fun u => e2_sapPt u b))
      (Metric.ball (e2_sapPt s d) r) ≤ volume (A ∩ Metric.closedBall s r) := by
  rw [Measure.map_apply (level_measurable b) measurableSet_ball,
    Measure.restrict_apply ((level_measurable b) measurableSet_ball)]
  apply measure_mono
  intro u hu
  exact ⟨hu.2, level_ball_subset u s b d r hu.1⟩

private lemma tail_integral (A : ℕ → Set ℝ) (hA : ∀ k, MeasurableSet (A k))
    (N : ℕ) (s r : ℝ) :
    (∫⁻ u in Metric.closedBall s r, e2_sapTail A N u) =
      ∑' k : ℕ, volume (A (N + 1 + k) ∩ Metric.closedBall s r) := by
  simp only [e2_sapTail]
  rw [lintegral_tsum]
  · congr 1
    funext k
    rw [lintegral_indicator (hA _)]
    simp only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, Measure.restrict_apply (hA _)]
  · intro k
    exact (measurable_const.indicator (hA _)).aemeasurable

private lemma eventually_level_upper (c : ℕ → ℝ) (A : ℕ → Set ℝ)
    (hc : Function.Injective c) (hA : ∀ k, MeasurableSet (A k))
    (m N : ℕ) (hmN : m ≤ N) (s : ℝ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      e2_sapLevelMeasure c A (Metric.ball (e2_sapPt s (c m)) r) ≤
        volume (Metric.closedBall s r) +
          ∫⁻ u in Metric.closedBall s r, e2_sapTail A N u := by
  classical
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ k ∈ Finset.range (N+1),
      k ≠ m → r < dist (c k) (c m) := by
    apply (Finset.eventually_all _).2
    intro k hk
    by_cases hkm : k = m
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hkm))
    · exact ((eventually_lt_nhds (dist_pos.mpr (fun h => hkm (hc h)))).filter_mono
        nhdsWithin_le_nhds).mono (fun _ h _ => h)
  filter_upwards [he] with r hr
  let f : ℕ → ℝ≥0∞ := fun k =>
    ((volume.restrict (A k)).map (fun u => e2_sapPt u (c k)))
      (Metric.ball (e2_sapPt s (c m)) r)
  have hhead : ∑ k ∈ Finset.range (N+1), f k = f m := by
    apply Finset.sum_eq_single m
    · intro k hk hkm
      dsimp [f]
      rw [Measure.map_apply (level_measurable _) measurableSet_ball,
        level_ball_miss s (c k) (c m) r (hr k hk hkm), measure_empty]
    · intro h
      exact False.elim (h (Finset.mem_range.mpr (by omega)))
  have hsplit : (∑' k, f k) = f m + ∑' k, f (N+1+k) := by
    have hs : Summable (fun k => f (k + (N+1))) := ENNReal.summable
    simpa only [hhead, Nat.add_comm] using hs.sum_add_tsum_nat_add'.symm
  rw [e2_sapLevelMeasure, Measure.sum_apply _ measurableSet_ball]
  change (∑' k, f k) ≤ _
  rw [hsplit, tail_integral A hA]
  apply add_le_add
  · exact (level_ball_le (A m) s (c m) (c m) r).trans (measure_mono inter_subset_right)
  · exact ENNReal.tsum_le_tsum (fun k => level_ball_le (A (N+1+k)) s _ _ r)

/-- The exact deterministic level-density statement, with no membership or
finite-total-mass hypothesis. The cutoff is fixed before the radius tends to zero. -/
theorem e2_sap_levelPoint_proof : E2sapLevelPoint := by
  intro c A hc hA m s hd hleb htail
  let F : ℝ → ℝ≥0∞ := fun r =>
    e2_sapLevelMeasure c A (Metric.ball (e2_sapPt s (c m)) r) /
      volume (Metric.closedBall s r)
  have hlow (r : ℝ) :
      volume (A m ∩ Metric.closedBall s r) / volume (Metric.closedBall s r) ≤ F r := by
    apply ENNReal.div_le_div_right
    rw [← level_ball_mass (A m) s (c m) r]
    exact Measure.le_sum (fun k => (volume.restrict (A k)).map
      (fun u => e2_sapPt u (c k))) m _
  have hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact ((tendsto_order.mp hd).1 a ha).mono (fun r hr => hr.trans_le (hlow r))
    · intro a ha
      have hn : Tendsto (fun N => 1 + e2_sapTail A N s) atTop (𝓝 (1 : ℝ≥0∞)) := by
        simpa only [add_zero] using tendsto_const_nhds.add htail
      obtain ⟨N, hNm, hNa⟩ := ((eventually_ge_atTop m).and
        ((tendsto_order.mp hn).2 a ha)).exists
      have hav : Tendsto (fun r => 1 +
          (∫⁻ u in Metric.closedBall s r, e2_sapTail A N u) /
            volume (Metric.closedBall s r)) (𝓝[>] (0 : ℝ))
          (𝓝 (1 + e2_sapTail A N s)) := tendsto_const_nhds.add (hleb N)
      filter_upwards [eventually_level_upper c A hc hA m N hNm s,
        (tendsto_order.mp hav).2 a hNa, self_mem_nhdsWithin] with r hr hra hrpos
      have hv0 : volume (Metric.closedBall s r) ≠ 0 := by
        rw [Real.volume_closedBall, ENNReal.ofReal_ne_zero_iff]
        exact mul_pos (by norm_num) hrpos
      have hvtop : volume (Metric.closedBall s r) ≠ ⊤ := by
        rw [Real.volume_closedBall]; exact ENNReal.ofReal_ne_top
      apply lt_of_le_of_lt _ hra
      calc
        F r ≤ (volume (Metric.closedBall s r) +
            ∫⁻ u in Metric.closedBall s r, e2_sapTail A N u) /
              volume (Metric.closedBall s r) := ENNReal.div_le_div_right hr _
        _ = _ := by rw [ENNReal.add_div, ENNReal.div_self hv0 hvtop]
  have htwice := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hF (Or.inl one_ne_zero)
  simp only [mul_one] at htwice
  apply htwice.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  dsimp [F, planarDensityRatio]
  rw [Real.volume_closedBall, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [← mul_div_assoc]
  exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)

end ParabolicRectifiability.Examples
