import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # Descendant sum versus integrated square energy

For any direct partition of any set, any source and `Λ ≥ 1`, every cell `T` has
`∑_{Q ⊂ T} a_Q μ(Q) ≤ 2·6^{k+2} ∫_T S^{2(Λ+2)ℓ_T}_{μ,𝒜_k}(x) dμ(x)`. The
coefficient-to-annulus comparison enters as the hypothesis
`CoeffAnnulusStatement` (implication form).

Route: `a_Q μ(Q) = ∫_T a_Q 1_Q dμ` (cells below `T` lie in `T`); the cell
indicators of constants are measurable, so `tsum` and `lintegral` exchange
(`lintegral_tsum`, the address type is countable); pointwise, at most one cell per level contains
`x` (`cell_disjoint`), the comparison bounds its coefficient by the integral over its window
`W_j = ((Λ+2)ℓ_j, 2(Λ+2)ℓ_j)`, and the windows of the levels `j ≥ j_T` are pairwise disjoint
(ratio `2 < 10`) and lie in `(0, 2(Λ+2)ℓ_T)` (`lintegral_iUnion`, `lintegral_mono_set`). No
measurability in `x` of the beta integrand is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal Function

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

open ParabolicRectifiability.Foundations

/-! ## Scales and windows -/

theorem d1adesc_scale_pos {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (j : ℕ) : 0 < coherentScale ℓ₀ j := by
  unfold coherentScale
  exact div_pos hℓ₀ (by positivity)

theorem d1adesc_scale_le_of_le {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {i j : ℕ} (hij : i ≤ j) :
    coherentScale ℓ₀ j ≤ coherentScale ℓ₀ i := by
  unfold coherentScale
  exact div_le_div_of_nonneg_left hℓ₀.le (by positivity) (pow_le_pow_right₀ (by norm_num) hij)

theorem d1adesc_ten_mul_scale_le {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {i j : ℕ} (hij : i < j) :
    10 * coherentScale ℓ₀ j ≤ coherentScale ℓ₀ i := by
  unfold coherentScale
  have h10 : (10 : ℝ) ^ (i + 1) ≤ 10 ^ j := pow_le_pow_right₀ (by norm_num) hij
  rw [pow_succ] at h10
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left h10 hℓ₀.le
  linarith

/-- The scale window `W_j = ((Λ+2)ℓ_j, 2(Λ+2)ℓ_j)` of level `j`. -/
def d1adesc_window (Λ ℓ₀ : ℝ) (j : ℕ) : Set ℝ :=
  Ioo ((Λ + 2) * coherentScale ℓ₀ j) (2 * ((Λ + 2) * coherentScale ℓ₀ j))

/-- The window of level `j` if `j₀ ≤ j`, and `∅` otherwise. -/
def d1adesc_levelWindow (Λ ℓ₀ : ℝ) (j₀ j : ℕ) : Set ℝ :=
  if j₀ ≤ j then d1adesc_window Λ ℓ₀ j else ∅

theorem d1adesc_levelWindow_of_le {Λ ℓ₀ : ℝ} {j₀ j : ℕ} (h : j₀ ≤ j) :
    d1adesc_levelWindow Λ ℓ₀ j₀ j = d1adesc_window Λ ℓ₀ j := by
  unfold d1adesc_levelWindow
  simp [h]

theorem d1adesc_levelWindow_subset (Λ ℓ₀ : ℝ) (j₀ j : ℕ) :
    d1adesc_levelWindow Λ ℓ₀ j₀ j ⊆ d1adesc_window Λ ℓ₀ j := by
  unfold d1adesc_levelWindow
  split_ifs
  · exact Subset.rfl
  · exact empty_subset _

theorem d1adesc_measurableSet_levelWindow (Λ ℓ₀ : ℝ) (j₀ j : ℕ) :
    MeasurableSet (d1adesc_levelWindow Λ ℓ₀ j₀ j) := by
  unfold d1adesc_levelWindow d1adesc_window
  split_ifs
  · exact measurableSet_Ioo
  · exact MeasurableSet.empty

/-- Windows of a coarser and a finer level are disjoint (multiplicative width `2 < 10`). -/
theorem d1adesc_window_disjoint_of_lt {Λ ℓ₀ : ℝ} (hΛ : 1 ≤ Λ) (hℓ₀ : 0 < ℓ₀) {i j : ℕ}
    (h : i < j) : Disjoint (d1adesc_window Λ ℓ₀ i) (d1adesc_window Λ ℓ₀ j) := by
  rw [Set.disjoint_left]
  intro r hri hrj
  have hri' : (Λ + 2) * coherentScale ℓ₀ i < r ∧ r < 2 * ((Λ + 2) * coherentScale ℓ₀ i) := hri
  have hrj' : (Λ + 2) * coherentScale ℓ₀ j < r ∧ r < 2 * ((Λ + 2) * coherentScale ℓ₀ j) := hrj
  have hΛ2 : 0 < Λ + 2 := by linarith
  have h1 : (Λ + 2) * (10 * coherentScale ℓ₀ j) ≤ (Λ + 2) * coherentScale ℓ₀ i :=
    mul_le_mul_of_nonneg_left (d1adesc_ten_mul_scale_le hℓ₀ h) hΛ2.le
  have h2 : 0 < (Λ + 2) * coherentScale ℓ₀ j := mul_pos hΛ2 (d1adesc_scale_pos hℓ₀ j)
  linarith [hri'.1, hrj'.2]

/-- Windows of distinct levels are disjoint. -/
theorem d1adesc_window_disjoint {Λ ℓ₀ : ℝ} (hΛ : 1 ≤ Λ) (hℓ₀ : 0 < ℓ₀) {i j : ℕ}
    (hij : i ≠ j) : Disjoint (d1adesc_window Λ ℓ₀ i) (d1adesc_window Λ ℓ₀ j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact d1adesc_window_disjoint_of_lt hΛ hℓ₀ h
  · exact (d1adesc_window_disjoint_of_lt hΛ hℓ₀ h).symm

theorem d1adesc_levelWindow_disjoint {Λ ℓ₀ : ℝ} (hΛ : 1 ≤ Λ) (hℓ₀ : 0 < ℓ₀) (j₀ : ℕ) :
    Pairwise (Disjoint on d1adesc_levelWindow Λ ℓ₀ j₀) := by
  intro i j hij
  exact (d1adesc_window_disjoint hΛ hℓ₀ hij).mono (d1adesc_levelWindow_subset Λ ℓ₀ j₀ i)
    (d1adesc_levelWindow_subset Λ ℓ₀ j₀ j)

/-- The windows of the levels `j ≥ j₀` lie in `(0, 2(Λ+2)ℓ_{j₀})`. -/
theorem d1adesc_iUnion_levelWindow_subset {Λ ℓ₀ : ℝ} (hΛ : 1 ≤ Λ) (hℓ₀ : 0 < ℓ₀) (j₀ : ℕ) :
    (⋃ j, d1adesc_levelWindow Λ ℓ₀ j₀ j) ⊆
      Ioo 0 (2 * ((Λ + 2) * coherentScale ℓ₀ j₀)) := by
  intro r hr
  obtain ⟨j, hj⟩ := mem_iUnion.mp hr
  unfold d1adesc_levelWindow at hj
  split_ifs at hj with hle
  · have hj' : (Λ + 2) * coherentScale ℓ₀ j < r ∧ r < 2 * ((Λ + 2) * coherentScale ℓ₀ j) := hj
    have hΛ2 : 0 < Λ + 2 := by linarith
    have h1 : 0 < (Λ + 2) * coherentScale ℓ₀ j := mul_pos hΛ2 (d1adesc_scale_pos hℓ₀ j)
    have h2 : (Λ + 2) * coherentScale ℓ₀ j ≤ (Λ + 2) * coherentScale ℓ₀ j₀ :=
      mul_le_mul_of_nonneg_left (d1adesc_scale_le_of_le hℓ₀ hle) hΛ2.le
    exact ⟨h1.trans hj'.1, by linarith [hj'.2]⟩
  · simp at hj

/-! ## Countability of the descendant addresses -/

theorem d1adesc_countable_isBelow {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}
    (P : DirectPartition E ℓ₀) (T : ℕ × Space n) :
    ({Q : ℕ × Space n | P.IsBelow Q T} : Set (ℕ × Space n)).Countable := by
  refine Set.Countable.mono (s₂ := ⋃ j : ℕ, ({j} : Set ℕ) ×ˢ P.center j) ?_
    (countable_iUnion fun j => (countable_singleton j).prod (P.center_countable j))
  intro Q hQ
  obtain ⟨hcell, -, -⟩ := hQ
  exact mem_iUnion.mpr ⟨Q.1, Set.mem_prod.mpr ⟨mem_singleton _, hcell⟩⟩

/-! ## The pointwise bound -/

/-- For every `x`, the descendant indicator sum at `x` is at most `2·6^{k+2} S^{2(Λ+2)ℓ_T}(x)`:
only one cell per level contains `x`, and the windows are disjoint. -/
theorem d1adesc_pointwise (hA : CoeffAnnulusStatement) {n k : ℕ} (μ : Measure (Space n))
    {E : Set (Space n)} {ℓ₀ Λ : ℝ} (P : DirectPartition E ℓ₀) (hΛ : 1 ≤ Λ)
    (T : ℕ × Space n) (x : Space n) :
    (∑' Q : {Q : ℕ × Space n // P.IsBelow Q T},
        (P.cellOf Q.1).indicator (fun _ => P.coeff μ k Λ Q.1) x) ≤
      ENNReal.ofReal (2 * 6 ^ (k + 2)) *
        squareEnergy μ k .mixed (2 * ((Λ + 2) * P.scale T.1)) x := by
  classical
  have hsupp : Function.support (fun Q : {Q : ℕ × Space n // P.IsBelow Q T} =>
      (P.cellOf Q.1).indicator (fun _ => P.coeff μ k Λ Q.1) x) ⊆
      {Q : {Q : ℕ × Space n // P.IsBelow Q T} | x ∈ P.cellOf Q.1} := by
    intro Q hQ
    by_contra hx
    have hx' : x ∉ P.cellOf Q.1 := hx
    exact hQ (Set.indicator_of_notMem hx' _)
  have hinj : Function.Injective
      (fun Q : {Q : {Q : ℕ × Space n // P.IsBelow Q T} | x ∈ P.cellOf Q.1} => Q.1.1.1) := by
    rintro ⟨⟨⟨j, z⟩, hQT⟩, hxQ⟩ ⟨⟨⟨j', z'⟩, hQ'T⟩, hxQ'⟩ hjeq
    have hjj : j = j' := hjeq
    subst hjj
    have hz : z = z' := by
      by_contra hne
      have hb : P.IsCell (j, z) ∧ T.1 ≤ j ∧ P.cellOf (j, z) ⊆ P.cellOf T := hQT
      have hb' : P.IsCell (j, z') ∧ T.1 ≤ j ∧ P.cellOf (j, z') ⊆ P.cellOf T := hQ'T
      have hc : z ∈ P.center j := hb.1
      have hc' : z' ∈ P.center j := hb'.1
      have hx1 : x ∈ P.cell j z := hxQ
      have hx2 : x ∈ P.cell j z' := hxQ'
      exact Set.disjoint_left.mp (P.cell_disjoint j z hc z' hc' hne) hx1 hx2
    subst hz
    rfl
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  calc (∑' Q : {Q : {Q : ℕ × Space n // P.IsBelow Q T} | x ∈ P.cellOf Q.1},
        (P.cellOf Q.1.1).indicator (fun _ => P.coeff μ k Λ Q.1.1) x)
      ≤ ∑' Q : {Q : {Q : ℕ × Space n // P.IsBelow Q T} | x ∈ P.cellOf Q.1},
          ENNReal.ofReal (2 * 6 ^ (k + 2)) *
            ∫⁻ r in d1adesc_levelWindow Λ ℓ₀ T.1 Q.1.1.1, betaSq μ k .mixed x r ∂scaleMeasure := by
        apply ENNReal.tsum_le_tsum
        rintro ⟨⟨⟨j, z⟩, hQT⟩, hxQ⟩
        have hb : P.IsCell (j, z) ∧ T.1 ≤ j ∧ P.cellOf (j, z) ⊆ P.cellOf T := hQT
        have hc : z ∈ P.center j := hb.1
        have hlev' : T.1 ≤ j := hb.2.1
        have hx' : x ∈ P.cellOf (j, z) := hxQ
        have hxc : x ∈ P.cell j z := hxQ
        show (P.cellOf (j, z)).indicator (fun _ => P.coeff μ k Λ (j, z)) x ≤
          ENNReal.ofReal (2 * 6 ^ (k + 2)) *
            ∫⁻ r in d1adesc_levelWindow Λ ℓ₀ T.1 j, betaSq μ k .mixed x r ∂scaleMeasure
        rw [Set.indicator_of_mem hx', d1adesc_levelWindow_of_le hlev']
        have hdist : dist x z < 2 * P.scale j :=
          Metric.mem_ball.mp (P.cell_subset_ball j z hc hxc)
        exact hA n k μ .mixed Λ (P.scale j) z x hΛ (d1adesc_scale_pos P.scale_pos j) hdist
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (2 * 6 ^ (k + 2)) *
          ∫⁻ r in d1adesc_levelWindow Λ ℓ₀ T.1 j, betaSq μ k .mixed x r ∂scaleMeasure :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj (fun j => ENNReal.ofReal (2 * 6 ^ (k + 2)) *
          ∫⁻ r in d1adesc_levelWindow Λ ℓ₀ T.1 j, betaSq μ k .mixed x r ∂scaleMeasure)
    _ = ENNReal.ofReal (2 * 6 ^ (k + 2)) *
          ∫⁻ r in ⋃ j, d1adesc_levelWindow Λ ℓ₀ T.1 j, betaSq μ k .mixed x r ∂scaleMeasure := by
        rw [ENNReal.tsum_mul_left, lintegral_iUnion (d1adesc_measurableSet_levelWindow Λ ℓ₀ T.1)
          (d1adesc_levelWindow_disjoint hΛ P.scale_pos T.1)]
    _ ≤ ENNReal.ofReal (2 * 6 ^ (k + 2)) *
          squareEnergy μ k .mixed (2 * ((Λ + 2) * P.scale T.1)) x :=
        mul_le_mul' le_rfl
          (lintegral_mono_set (d1adesc_iUnion_levelWindow_subset hΛ P.scale_pos T.1))

/-! ## The statement -/

/-- **Descendant sum versus integrated square energy** (`CoeffAnnulusStatement →
DescendantIntegralStatement`). -/
theorem d1a_descendantIntegral_proof : CoeffAnnulusStatement → DescendantIntegralStatement := by
  intro hA n k μ E ℓ₀ Λ P hΛ T _hT
  have : Countable {Q : ℕ × Space n // P.IsBelow Q T} :=
    (d1adesc_countable_isBelow P T).to_subtype
  have hterm : ∀ Q : {Q : ℕ × Space n // P.IsBelow Q T},
      P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) =
        ∫⁻ x in P.cellOf T, (P.cellOf Q.1).indicator (fun _ => P.coeff μ k Λ Q.1) x ∂μ := by
    intro Q
    have hmQ : MeasurableSet (P.cellOf Q.1) := P.measurable_cell Q.1.1 Q.1.2
    have hb : P.IsBelow Q.1 T := Q.2
    obtain ⟨-, -, hsub⟩ := hb
    rw [lintegral_indicator_const hmQ, Measure.restrict_apply hmQ, inter_eq_left.mpr hsub]
  calc P.descendantEnergy μ k Λ T
      = ∑' Q : {Q : ℕ × Space n // P.IsBelow Q T},
          P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) := rfl
    _ = ∑' Q : {Q : ℕ × Space n // P.IsBelow Q T},
          ∫⁻ x in P.cellOf T, (P.cellOf Q.1).indicator (fun _ => P.coeff μ k Λ Q.1) x ∂μ :=
        tsum_congr hterm
    _ = ∫⁻ x in P.cellOf T, ∑' Q : {Q : ℕ × Space n // P.IsBelow Q T},
          (P.cellOf Q.1).indicator (fun _ => P.coeff μ k Λ Q.1) x ∂μ :=
        (lintegral_tsum fun (Q : {Q : ℕ × Space n // P.IsBelow Q T}) =>
          (measurable_const.indicator (P.measurable_cell Q.1.1 Q.1.2)).aemeasurable).symm
    _ ≤ ∫⁻ x in P.cellOf T, ENNReal.ofReal (2 * 6 ^ (k + 2)) *
          squareEnergy μ k .mixed (2 * ((Λ + 2) * P.scale T.1)) x ∂μ :=
        lintegral_mono fun x => d1adesc_pointwise hA μ P hΛ T x
    _ = ENNReal.ofReal (2 * 6 ^ (k + 2)) *
          ∫⁻ x in P.cellOf T, squareEnergy μ k .mixed (2 * ((Λ + 2) * P.scale T.1)) x ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
