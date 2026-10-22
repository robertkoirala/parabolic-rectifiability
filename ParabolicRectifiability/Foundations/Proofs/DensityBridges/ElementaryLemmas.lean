import ParabolicRectifiability.Foundations.Density
import ParabolicRectifiability.Metric.ProperSpace

/-! # Four elementary density-bridge lemmas

Proofs of `fpack_exists_good_radius`, `fpack_tsum_le_of_finite_packing`,
`fupdom_exists_ratio_gt` and `fupdom_exists_open_measure_le`, each with the type of the
corresponding statement. Only the definitions `Space`, `densityRatio`, `lowerDensity` and
`upperDensity` are needed. Helper prefix `fbfb1_`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- At a positive radius the ratio bound `densityRatio < c` gives the mass bound. -/
theorem fbfb1_mass_le_of_ratio_lt {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n)
    (r : ℝ) (hr : 0 < r) (c : ℝ≥0∞) (h : densityRatio μ k z r < c) :
    μ (Metric.ball z r) ≤ c * ENNReal.ofReal r ^ k := by
  have h0 : ENNReal.ofReal r ^ k ≠ 0 :=
    pow_ne_zero _ (ENNReal.ofReal_pos.2 hr).ne'
  have ht : ENNReal.ofReal r ^ k ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  exact (ENNReal.div_le_iff h0 ht).1 h.le

/-- At a positive radius the ratio bound `c < densityRatio` gives the mass bound. -/
theorem fbfb1_mass_gt_of_ratio_gt {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n)
    (r : ℝ) (hr : 0 < r) (c : ℝ≥0∞) (h : c < densityRatio μ k z r) :
    c * ENNReal.ofReal r ^ k < μ (Metric.ball z r) := by
  have h0 : ENNReal.ofReal r ^ k ≠ 0 :=
    pow_ne_zero _ (ENNReal.ofReal_pos.2 hr).ne'
  have ht : ENNReal.ofReal r ^ k ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  exact (ENNReal.lt_div_iff_mul_lt (Or.inl h0) (Or.inl ht)).1 h

theorem fpack_exists_good_radius_proof {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n)
    (A : ℝ) (hA : 0 ≤ A) (hz : lowerDensity μ k z ≤ ENNReal.ofReal A)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r < δ ∧ μ (Metric.ball z r) ≤ ENNReal.ofReal ((A + ε) * r ^ k) := by
  have hlt : lowerDensity μ k z < ENNReal.ofReal (A + ε) :=
    lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
  have hfreq : ∃ᶠ r in 𝓝[>] (0 : ℝ), densityRatio μ k z r < ENNReal.ofReal (A + ε) :=
    Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Set.Ioo 0 δ := Ioo_mem_nhdsGT hδ
  obtain ⟨r, hr, hrI⟩ := (hfreq.and_eventually hev).exists
  refine ⟨r, hrI.1, hrI.2, ?_⟩
  have hm := fbfb1_mass_le_of_ratio_lt μ k z r hrI.1 _ hr
  rw [ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_pow hrI.1.le]
  exact hm

theorem fpack_tsum_le_of_finite_packing_proof {n : ℕ} (k : ℕ) (K : Set (Space n)) (C_K : ℝ)
    (q : Space n) (ρ : ℝ)
    (hpack : ∀ (l : ℕ) (z : Fin l → Space n) (r : Fin l → ℝ),
      (∀ i, z i ∈ K ∩ Metric.ball q ρ) →
      (∀ i, 0 < r i ∧ r i ≤ ρ) →
      (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
      (∑ i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C_K * ρ ^ k))
    {ι : Type} (z : ι → Space n) (r : ι → ℝ)
    (hz : ∀ i, z i ∈ K ∩ Metric.ball q ρ) (hr : ∀ i, 0 < r i ∧ r i ≤ ρ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) :
    (∑' i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C_K * ρ ^ k) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have h := hpack s.card (fun i => z ((s.equivFin.symm i : s) : ι))
    (fun i => r ((s.equivFin.symm i : s) : ι)) (fun i => hz _) (fun i => hr _)
    (fun i j hij => hdisj _ _ (fun h => hij (s.equivFin.symm.injective (Subtype.ext h))))
  calc ∑ i ∈ s, ENNReal.ofReal (r i) ^ k
      = ∑ i : s, ENNReal.ofReal (r i) ^ k := (Finset.sum_coe_sort s _).symm
    _ = ∑ i : Fin s.card, ENNReal.ofReal (r ((s.equivFin.symm i : s) : ι)) ^ k :=
        (Equiv.sum_comp s.equivFin.symm (fun i : s => ENNReal.ofReal (r i) ^ k)).symm
    _ ≤ _ := h

theorem fupdom_exists_ratio_gt_proof {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n)
    (a : ℝ) (ha : 0 < a) (hz : ENNReal.ofReal a ≤ upperDensity μ k z)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (a / 2 * r ^ k) < μ (Metric.ball z r) := by
  have hlt : ENNReal.ofReal (a / 2) < upperDensity μ k z :=
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff ha).2 (by linarith)) hz
  have hfreq : ∃ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal (a / 2) < densityRatio μ k z r :=
    Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) hlt
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Set.Ioo 0 δ := Ioo_mem_nhdsGT hδ
  obtain ⟨r, hr, hrI⟩ := (hfreq.and_eventually hev).exists
  refine ⟨r, hrI.1, hrI.2, ?_⟩
  have hm := fbfb1_mass_gt_of_ratio_gt μ k z r hrI.1 _ hr
  rw [ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_pow hrI.1.le]
  exact hm

theorem fupdom_exists_open_measure_le_proof {n : ℕ} (ρ : Measure (Space n))
    (hρ : IsFiniteMeasureOnCompacts ρ) (E O : Set (Space n)) (hO : IsOpen O) (hEO : E ⊆ O)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ V : Set (Space n), IsOpen V ∧ E ⊆ V ∧ V ⊆ O ∧ ρ V ≤ ρ E + ε := by
  have := hρ
  have : ρ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ρ
  obtain ⟨U, hEU, hU, hρU⟩ := Set.exists_isOpen_le_add E ρ hε
  exact ⟨U ∩ O, hU.inter hO, subset_inter hEU hEO, inter_subset_right,
    (measure_mono inter_subset_left).trans hρU⟩

end ParabolicRectifiability.Foundations
