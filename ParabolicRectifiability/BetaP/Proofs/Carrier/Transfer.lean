import ParabolicRectifiability.BetaP.Proofs.Carrier.CarrierStatements

/-! # The fixed-model `p`-power barycenter transfer

Proves `ccar_cells_fit_transfer : CellsFitTransferStatement`.

Proof: for one fixed model `L`, the real squared cost `q_L = modelRealCost L` is
convex in ordinary coordinates (`convexOn_modelRealCost`), and `u ↦ u^{p/2}` is convex and
increasing on `[0,∞)` for `p ≥ 2`, so `q_L^{p/2}` is convex. Jensen against the normalized
restriction of `ν` to a cell gives `ν(C) d_P(bar_C, L)^p ≤ ∫_C d_P(w, L)^p dν`, because
`d_P(w,L)^p = (d_P(w,L)^2)^{p/2} = ofReal (q_L(w)^{p/2})`. With `w_j ≤ A ν(C_j)`, the disjoint
contributing cells inside `P(y_i, 2s)` (`contributing_cell_subset_ball`) and finite additivity
the atomic fit is bounded by `A · fit_p(ν; L, y_i, 2s)`. The model is fixed throughout: no infimum.

This is the `p`-version of the quadratic barycenter transfer; helpers are prefixed `ccart_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP.CarrierTree

open ParabolicRectifiability.Foundations

variable {n k : ℕ} {T : FamilyKind}

/-- Distance conversion: `d_P(w,L)^p = ofReal (q_L(w)^{p/2})` for `p ≥ 0`, where
`d_P(w,L)^2 = modelCost L w = ofReal (modelRealCost L w)`. -/
theorem ccart_infEDist_rpow_eq {p : ℝ} (hp : 0 ≤ p) (L : Models n k T) (w : Space n) :
    Metric.infEDist w (modelSet L) ^ p = ENNReal.ofReal (modelRealCost L w ^ (p / 2)) := by
  have h2 : Metric.infEDist w (modelSet L) ^ (2 : ℝ) = ENNReal.ofReal (modelRealCost L w) := by
    rw [ENNReal.rpow_two]
    exact modelCost_eq_ofReal L w
  calc Metric.infEDist w (modelSet L) ^ p
      = Metric.infEDist w (modelSet L) ^ ((2 : ℝ) * (p / 2)) := by congr 1; ring
    _ = (Metric.infEDist w (modelSet L) ^ (2 : ℝ)) ^ (p / 2) := ENNReal.rpow_mul _ _ _
    _ = _ := by
      rw [h2, ENNReal.ofReal_rpow_of_nonneg (modelRealCost_nonneg L w) (by linarith)]

/-- Continuity of the powered real cost `w ↦ q_L(w)^{p/2}`. -/
theorem ccart_continuous_powCost (L : Models n k T) {p : ℝ} (hp : 0 ≤ p) :
    Continuous (fun w : Space n => modelRealCost L w ^ (p / 2)) := by
  have hc : Continuous (modelRealCost L) :=
    continuous_modelRealCost.comp (continuous_const.prodMk continuous_id)
  exact hc.rpow_const (fun _ => Or.inr (by linarith))

/-- Convexity of the powered cost `q_L^{p/2}` in ordinary coordinates for one fixed model,
`p ≥ 2`: `q_L` is convex and `u ↦ u^{p/2}` is convex and increasing on `[0,∞)`. -/
theorem ccart_convexOn_powCost (L : Models n k T) {p : ℝ} (hp : 2 ≤ p) :
    ConvexOn ℝ univ (fun y : Coordinates n =>
      modelRealCost L ((coordinatesHomeomorph n).symm y) ^ (p / 2)) := by
  have hc := convexOn_modelRealCost L
  have hr : ConvexOn ℝ (Ici 0) (fun x : ℝ => x ^ (p / 2)) := convexOn_rpow (by linarith)
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h1 := hc.2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at h1 ⊢
  have hx := modelRealCost_nonneg L ((coordinatesHomeomorph n).symm x)
  have hy := modelRealCost_nonneg L ((coordinatesHomeomorph n).symm y)
  have hxy := modelRealCost_nonneg L ((coordinatesHomeomorph n).symm (a • x + b • y))
  calc modelRealCost L ((coordinatesHomeomorph n).symm (a • x + b • y)) ^ (p / 2)
      ≤ (a * modelRealCost L ((coordinatesHomeomorph n).symm x) +
          b * modelRealCost L ((coordinatesHomeomorph n).symm y)) ^ (p / 2) :=
        Real.rpow_le_rpow hxy h1 (by linarith)
    _ ≤ a * modelRealCost L ((coordinatesHomeomorph n).symm x) ^ (p / 2) +
          b * modelRealCost L ((coordinatesHomeomorph n).symm y) ^ (p / 2) := by
        simpa only [smul_eq_mul] using hr.2 (mem_Ici.mpr hx) (mem_Ici.mpr hy) ha hb hab

/-- Powered Jensen against the probability normalization of a bounded cell (one fixed model). -/
theorem ccart_powCost_barycenter_le_normalizedIntegral
    (ν : Measure (Space n)) {C : Set (Space n)} (hC : MeasurableSet C)
    (hbound : Bornology.IsBounded C) (h0 : ν C ≠ 0) (hfin : ν C ≠ ⊤)
    (L : Models n k T) {p : ℝ} (hp : 2 ≤ p) :
    modelRealCost L (spaceTimeBarycenter ν C) ^ (p / 2) ≤
      ∫ w, modelRealCost L w ^ (p / 2) ∂normalizedRestriction ν C := by
  let _ := isProbabilityMeasure_normalizedRestriction ν C h0 hfin
  have hcont := ccart_continuous_powCost L (p := p) (by linarith)
  have hi : Integrable (coordinatesHomeomorph n) (normalizedRestriction ν C) :=
    (integrableOn_coordinates ν hC hbound hfin).smul_measure (ENNReal.inv_ne_top.mpr h0)
  have hgi : Integrable (fun w => modelRealCost L w ^ (p / 2)) (normalizedRestriction ν C) :=
    (integrableOn_continuous_of_bounded ν hC hbound hfin hcont).smul_measure
      (ENNReal.inv_ne_top.mpr h0)
  have hc : Continuous (fun y : Coordinates n =>
      modelRealCost L ((coordinatesHomeomorph n).symm y) ^ (p / 2)) :=
    hcont.comp (coordinatesHomeomorph n).symm.continuous
  have h := (ccart_convexOn_powCost L hp).map_integral_le
    (μ := normalizedRestriction ν C) hc.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => mem_univ _) hi
    (by simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hgi)
  simpa only [integral_coordinates_normalizedRestriction,
    Homeomorph.symm_apply_apply] using h

/-- Unnormalized powered Jensen with real mass and real powered cost. -/
theorem ccart_mass_mul_powCost_le
    (ν : Measure (Space n)) {C : Set (Space n)} (hC : MeasurableSet C)
    (hbound : Bornology.IsBounded C) (h0 : ν C ≠ 0) (hfin : ν C ≠ ⊤)
    (L : Models n k T) {p : ℝ} (hp : 2 ≤ p) :
    (ν C).toReal * modelRealCost L (spaceTimeBarycenter ν C) ^ (p / 2) ≤
      ∫ w in C, modelRealCost L w ^ (p / 2) ∂ν := by
  have h := ccart_powCost_barycenter_le_normalizedIntegral ν hC hbound h0 hfin L hp
  rw [integral_normalizedRestriction, smul_eq_mul] at h
  have hm : 0 < (ν C).toReal := ENNReal.toReal_pos h0 hfin
  calc (ν C).toReal * modelRealCost L (spaceTimeBarycenter ν C) ^ (p / 2)
      ≤ (ν C).toReal * ((ν C).toReal⁻¹ * ∫ w in C, modelRealCost L w ^ (p / 2) ∂ν) :=
        mul_le_mul_of_nonneg_left h hm.le
    _ = ∫ w in C, modelRealCost L w ^ (p / 2) ∂ν := by
        rw [← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]

/-- Fixed-model `p`-Jensen on one cell in the extended convention of `fitPow`:
`ν(C) · d_P(bar_C, L)^p ≤ ∫_C d_P(w, L)^p dν`. -/
theorem ccart_mass_mul_rpow_infEDist_le
    (ν : Measure (Space n)) {C : Set (Space n)} (hC : MeasurableSet C)
    (hbound : Bornology.IsBounded C) (h0 : ν C ≠ 0) (hfin : ν C ≠ ⊤)
    (L : Models n k T) {p : ℝ} (hp : 2 ≤ p) :
    ν C * Metric.infEDist (spaceTimeBarycenter ν C) (modelSet L) ^ p ≤
      ∫⁻ w in C, Metric.infEDist w (modelSet L) ^ p ∂ν := by
  have hp0 : 0 ≤ p := by linarith
  have hcont := ccart_continuous_powCost L (p := p) hp0
  have h := ENNReal.ofReal_le_ofReal (ccart_mass_mul_powCost_le ν hC hbound h0 hfin L hp)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin,
    ofReal_integral_eq_lintegral_ofReal
      (integrableOn_continuous_of_bounded ν hC hbound hfin hcont)
      (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (modelRealCost_nonneg L w) _)] at h
  simpa only [ccart_infEDist_rpow_eq hp0] using h

/-- Weighted form for one barycenter cell: `w_j d_P(c_j, L)^p ≤ A ∫_{C_j} d_P(·, L)^p dν`. -/
theorem ccart_weighted_rpow_le {ν : Measure (Space n)} {ι : Type*} [Fintype ι]
    (D : FiniteBarycenterCells ν ι) (j : ι) (L : Models n k T) {p : ℝ} (hp : 2 ≤ p) :
    ENNReal.ofReal (D.weight j) * Metric.infEDist (D.barycenter j) (modelSet L) ^ p ≤
      ENNReal.ofReal D.A * ∫⁻ w in D.cell j, Metric.infEDist w (modelSet L) ^ p ∂ν := by
  have hw : ENNReal.ofReal (D.weight j) ≤ ENNReal.ofReal D.A * ν (D.cell j) := by
    have h := ENNReal.ofReal_le_ofReal (D.weight_le j)
    rwa [ENNReal.ofReal_mul D.A_nonneg, ENNReal.ofReal_toReal (D.mass_ne_top j)] at h
  calc
    _ ≤ (ENNReal.ofReal D.A * ν (D.cell j)) *
        Metric.infEDist (D.barycenter j) (modelSet L) ^ p :=
      mul_le_mul_of_nonneg_right hw zero_le
    _ = ENNReal.ofReal D.A * (ν (D.cell j) *
        Metric.infEDist (D.barycenter j) (modelSet L) ^ p) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (ccart_mass_mul_rpow_infEDist_le ν (D.measurable_cell j)
        (D.cell_bounded j) (D.mass_ne_zero j) (D.mass_ne_top j) L hp) zero_le

/-- Evaluation of the fixed-model `p`-fit of the finite cutoff atomic source. -/
theorem ccart_fitPow_finiteCutoffAtomicMeasure {ι : Type*} [Fintype ι]
    (c : ι → Space n) (ρ a : ι → ℝ) (p : ℝ) (L : Models n k T) (z : Space n) (s : ℝ) :
    fitPow (finiteCutoffAtomicMeasure c ρ a s) p L z s =
      (by classical exact
        ∑ j ∈ Finset.univ.filter (fun j => ρ j ≤ s ∧ c j ∈ Metric.ball z s),
          ENNReal.ofReal (a j) * Metric.infEDist (c j) (modelSet L) ^ p) := by
  classical
  unfold fitPow finiteCutoffAtomicMeasure
  rw [← lintegral_indicator measurableSet_ball, lintegral_finsetSum_measure]
  simp_rw [lintegral_smul_measure, lintegral_dirac]
  simp only [Finset.sum_filter, Set.indicator_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hρ : ρ j ≤ s <;> by_cases hc : c j ∈ Metric.ball z s <;> simp [hρ, hc]

/-- **Fixed-model `p`-power transfer** for barycenter cells: weighted `p`-Jensen and finite
disjoint additivity, before any infimum over the family. -/
theorem ccart_fitPow_atomicMeasure_le {ν : Measure (Space n)} {ι : Type*} [Fintype ι]
    (D : FiniteBarycenterCells ν ι) (i : ι) {s : ℝ} (hs : D.cutoff i ≤ s)
    (L : Models n k T) {p : ℝ} (hp : 2 ≤ p) :
    fitPow (D.atomicMeasure s) p L (D.barycenter i) s ≤
      ENNReal.ofReal D.A * fitPow ν p L (D.sample i) (2 * s) := by
  classical
  let J := Finset.univ.filter (fun j => D.cutoff j ≤ s ∧
    D.barycenter j ∈ Metric.ball (D.barycenter i) s)
  have hd : Set.PairwiseDisjoint (↑J : Set ι) D.cell := by
    intro j _ l _ hjl
    exact D.disjoint_cell hjl
  have hsub : (⋃ j ∈ J, D.cell j) ⊆ Metric.ball (D.sample i) (2 * s) := by
    apply iUnion_subset
    intro j
    apply iUnion_subset
    intro hj
    have h := (Finset.mem_filter.mp hj).2
    exact D.contributing_cell_subset_ball i j hs h.1 h.2
  calc
    _ = ∑ j ∈ J, ENNReal.ofReal (D.weight j) *
        Metric.infEDist (D.barycenter j) (modelSet L) ^ p :=
      ccart_fitPow_finiteCutoffAtomicMeasure _ _ _ p L _ s
    _ ≤ ∑ j ∈ J, ENNReal.ofReal D.A *
        ∫⁻ w in D.cell j, Metric.infEDist w (modelSet L) ^ p ∂ν :=
      Finset.sum_le_sum fun j _ => ccart_weighted_rpow_le D j L hp
    _ = ENNReal.ofReal D.A *
        ∑ j ∈ J, ∫⁻ w in D.cell j, Metric.infEDist w (modelSet L) ^ p ∂ν := by
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal D.A *
        ∫⁻ w in ⋃ j ∈ J, D.cell j, Metric.infEDist w (modelSet L) ^ p ∂ν := by
      rw [lintegral_biUnion_finset hd (fun j _ => D.measurable_cell j)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (lintegral_mono_set hsub) zero_le

/-- **Fixed-model `p`-power barycenter transfer** (`CellsFitTransferStatement`). -/
theorem ccar_cells_fit_transfer_proof : CellsFitTransferStatement := by
  intro n k T p hp ν l D i s hs L
  exact ccart_fitPow_atomicMeasure_le D i hs L hp

end ParabolicRectifiability.BetaP.CarrierTree
