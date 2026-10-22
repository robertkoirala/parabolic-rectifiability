import ParabolicRectifiability.Measure.BarycenterTransfer
import ParabolicRectifiability.Measure.BetaLaws
import ParabolicRectifiability.Measure.ScaleIntegrals

/-!
# Transfer from disjoint source cells to cutoff barycenter atoms

Cells are given source data. Their actual ordinary barycenters are computed,
and the varying atomic source retains precisely the cutoffs `radius / 2 ≤ s`.
Fixed-model Jensen and disjoint additivity precede the fitting infimum. The
natural radius normalization gives exactly `2^(k+2)`; scale energy uses `ds/s`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal

variable {n k : ℕ} {T : FamilyKind} {ι : Type*} [Fintype ι]

/-- The actual finite atomic source at scale `s`, with a closed cutoff condition. -/
def finiteCutoffAtomicMeasure (c : ι → Space n) (ρ a : ι → ℝ) (s : ℝ) :
    Measure (Space n) := by
  classical
  exact ∑ j ∈ Finset.univ.filter (fun j => ρ j ≤ s),
    ENNReal.ofReal (a j) • Measure.dirac (c j)

theorem finiteCutoffAtomicMeasure_mono (c : ι → Space n) (ρ a : ι → ℝ) :
    Monotone (finiteCutoffAtomicMeasure c ρ a) := by
  classical
  intro s t hst
  unfold finiteCutoffAtomicMeasure
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.trans hst⟩
  · intro j _ _
    exact Measure.zero_le _

theorem isFiniteMeasure_finiteCutoffAtomicMeasure (c : ι → Space n)
    (ρ a : ι → ℝ) (s : ℝ) : IsFiniteMeasure (finiteCutoffAtomicMeasure c ρ a s) := by
  classical
  constructor
  simp only [finiteCutoffAtomicMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.mpr (fun j _ => ENNReal.ofReal_lt_top)

theorem fit_finiteCutoffAtomicMeasure (c : ι → Space n) (ρ a : ι → ℝ)
    (L : Models n k T) (z : Space n) (s : ℝ) :
    fit (finiteCutoffAtomicMeasure c ρ a s) L z s =
      (by classical exact
        ∑ j ∈ Finset.univ.filter (fun j => ρ j ≤ s ∧ c j ∈ Metric.ball z s),
          ENNReal.ofReal (a j) * modelCost L (c j)) := by
  classical
  unfold fit finiteCutoffAtomicMeasure
  rw [← lintegral_indicator measurableSet_ball, lintegral_finsetSum_measure]
  simp_rw [lintegral_smul_measure, lintegral_dirac]
  simp only [Finset.sum_filter, Set.indicator_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hρ : ρ j ≤ s <;> by_cases hc : c j ∈ Metric.ball z s <;> simp [hρ, hc]

/-- One-dimensional monotonicity supplies measurable radius dependence even for
an arbitrary Borel source of infinite total or local mass. -/
theorem measurable_betaSq_monotone_source (μ : ℝ → Measure (Space n)) (hμ : Monotone μ)
    (k : ℕ) (T : FamilyKind) (z : Space n) :
    Measurable (fun r => betaSq (μ r) k T z r) := by
  have hfit : Monotone (fun r => ⨅ L : Models n k T, fit (μ r) L z r) := by
    intro r s hrs
    apply iInf_mono
    intro L
    exact (fit_mono_measure (hμ hrs) L z r).trans
      (fit_mono_ball (μ s) L (Metric.ball_subset_ball hrs))
  unfold betaSq
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    ((measurable_id.ennreal_ofReal.inv.pow_const (k + 2)).mul hfit.measurable)
    measurable_const

theorem measurable_betaSq_radius (ν : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (z : Space n) : Measurable (fun r => betaSq ν k T z r) :=
  measurable_betaSq_monotone_source (fun _ => ν) (fun _ _ _ => le_rfl) k T z

theorem measurable_betaSq_finiteCutoffAtomicMeasure (c : ι → Space n) (ρ a : ι → ℝ)
    (k : ℕ) (T : FamilyKind) (z : Space n) :
    Measurable (fun r => betaSq (finiteCutoffAtomicMeasure c ρ a r) k T z r) :=
  measurable_betaSq_monotone_source _ (finiteCutoffAtomicMeasure_mono c ρ a) k T z

/-- Disjoint source cells with radii and weights; containment of the barycenters and
the Jensen inequality are not fields of this record; they are consequences proved below. -/
structure FiniteBarycenterCells (ν : Measure (Space n)) (ι : Type*) [Fintype ι] where
  cell : ι → Set (Space n)
  measurable_cell : ∀ j, MeasurableSet (cell j)
  disjoint_cell : Pairwise (fun i j => Disjoint (cell i) (cell j))
  mass_ne_zero : ∀ j, ν (cell j) ≠ 0
  mass_ne_top : ∀ j, ν (cell j) ≠ ⊤
  center : ι → Space n
  radius : ι → ℝ
  radius_pos : ∀ j, 0 < radius j
  ε : ℝ
  ε_pos : 0 < ε
  ε_le : ε ≤ 1 / 10
  cell_subset : ∀ j, cell j ⊆ Metric.closedBall (center j) (ε * radius j)
  sample : ι → Space n
  sample_mem : ∀ j, sample j ∈ cell j
  weight : ι → ℝ
  weight_pos : ∀ j, 0 < weight j
  A : ℝ
  A_nonneg : 0 ≤ A
  weight_le : ∀ j, weight j ≤ A * (ν (cell j)).toReal

namespace FiniteBarycenterCells

variable {ν : Measure (Space n)}

def barycenter (D : FiniteBarycenterCells ν ι) (j : ι) : Space n :=
  spaceTimeBarycenter ν (D.cell j)

def cutoff (D : FiniteBarycenterCells ν ι) (j : ι) : ℝ := D.radius j / 2

def atomicMeasure (D : FiniteBarycenterCells ν ι) (s : ℝ) : Measure (Space n) :=
  finiteCutoffAtomicMeasure D.barycenter D.cutoff D.weight s

theorem cutoff_pos (D : FiniteBarycenterCells ν ι) (j : ι) : 0 < D.cutoff j :=
  div_pos (D.radius_pos j) (by norm_num)

theorem cell_bounded (D : FiniteBarycenterCells ν ι) (j : ι) :
    Bornology.IsBounded (D.cell j) := Metric.isBounded_closedBall.subset (D.cell_subset j)

theorem barycenter_mem_closedBall (D : FiniteBarycenterCells ν ι) (j : ι) :
    D.barycenter j ∈ Metric.closedBall (D.center j) (D.ε * D.radius j) :=
  spaceTimeBarycenter_mem_closedBall ν (D.measurable_cell j) (D.mass_ne_zero j)
    (D.mass_ne_top j) _ (mul_pos D.ε_pos (D.radius_pos j)).le (D.cell_subset j)

theorem dist_barycenter_cell_le (D : FiniteBarycenterCells ν ι) (j : ι)
    {w : Space n} (hw : w ∈ D.cell j) :
    dist (D.barycenter j) w ≤ 2 * D.ε * D.radius j := by
  have hc := Metric.mem_closedBall.mp (D.barycenter_mem_closedBall j)
  have hwc := Metric.mem_closedBall.mp (D.cell_subset j hw)
  calc
    _ ≤ dist (D.barycenter j) (D.center j) + dist (D.center j) w := dist_triangle _ _ _
    _ ≤ D.ε * D.radius j + D.ε * D.radius j :=
      add_le_add hc (by simpa only [dist_comm] using hwc)
    _ = _ := by ring

theorem dist_barycenter_cell_le_scale (D : FiniteBarycenterCells ν ι) (j : ι)
    {s : ℝ} (hs : D.cutoff j ≤ s) {w : Space n} (hw : w ∈ D.cell j) :
    dist (D.barycenter j) w ≤ 4 * D.ε * s := by
  have hr : D.radius j ≤ 2 * s := by dsimp [cutoff] at hs; linarith
  calc
    _ ≤ 2 * D.ε * D.radius j := D.dist_barycenter_cell_le j hw
    _ ≤ (2 * D.ε) * (2 * s) :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) D.ε_pos.le)
    _ = _ := by ring

/-- Every cell whose cutoff atom contributes to the open testing ball lies in
the original source ball at twice the radius, with the testing sample retained. -/
theorem contributing_cell_subset_ball (D : FiniteBarycenterCells ν ι) (i j : ι)
    {s : ℝ} (hi : D.cutoff i ≤ s) (hj : D.cutoff j ≤ s)
    (hc : D.barycenter j ∈ Metric.ball (D.barycenter i) s) :
    D.cell j ⊆ Metric.ball (D.sample i) (2 * s) := by
  have hs : 0 < s := (D.cutoff_pos i).trans_le hi
  have hci := D.dist_barycenter_cell_le_scale i hi (D.sample_mem i)
  have hcj : dist (D.barycenter j) (D.barycenter i) < s := Metric.mem_ball.mp hc
  intro w hw
  have hwj := D.dist_barycenter_cell_le_scale j hj hw
  have heps := mul_le_mul_of_nonneg_right D.ε_le hs.le
  apply Metric.mem_ball.mpr
  have ht : dist w (D.sample i) ≤ dist w (D.barycenter j) +
      dist (D.barycenter j) (D.barycenter i) + dist (D.barycenter i) (D.sample i) := by
    calc
      _ ≤ dist w (D.barycenter j) + dist (D.barycenter j) (D.sample i) := dist_triangle _ _ _
      _ ≤ dist w (D.barycenter j) + (dist (D.barycenter j) (D.barycenter i) +
          dist (D.barycenter i) (D.sample i)) :=
        add_le_add le_rfl (dist_triangle (D.barycenter j) (D.barycenter i) (D.sample i))
      _ = _ := by ring
  rw [dist_comm w (D.barycenter j)] at ht
  nlinarith

theorem weighted_modelCost_le (D : FiniteBarycenterCells ν ι) (j : ι)
    (L : Models n k T) :
    ENNReal.ofReal (D.weight j) * modelCost L (D.barycenter j) ≤
      ENNReal.ofReal D.A * ∫⁻ w in D.cell j, modelCost L w ∂ν := by
  have hw : ENNReal.ofReal (D.weight j) ≤ ENNReal.ofReal D.A * ν (D.cell j) := by
    have h := ENNReal.ofReal_le_ofReal (D.weight_le j)
    rwa [ENNReal.ofReal_mul D.A_nonneg, ENNReal.ofReal_toReal (D.mass_ne_top j)] at h
  calc
    _ ≤ (ENNReal.ofReal D.A * ν (D.cell j)) * modelCost L (D.barycenter j) :=
      mul_le_mul_of_nonneg_right hw zero_le
    _ = ENNReal.ofReal D.A * (ν (D.cell j) * modelCost L (D.barycenter j)) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mass_mul_modelCost_spaceTimeBarycenter_le ν (D.measurable_cell j)
        (D.cell_bounded j) (D.mass_ne_zero j) (D.mass_ne_top j) L) zero_le

/-- Fixed-model transfer: weighted Jensen and finite disjoint additivity are
completed before the infimum over the unchanged family is considered. -/
theorem fit_atomicMeasure_le (D : FiniteBarycenterCells ν ι) (i : ι)
    {s : ℝ} (hs : D.cutoff i ≤ s) (L : Models n k T) :
    fit (D.atomicMeasure s) L (D.barycenter i) s ≤
      ENNReal.ofReal D.A * fit ν L (D.sample i) (2 * s) := by
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
    _ = ∑ j ∈ J, ENNReal.ofReal (D.weight j) * modelCost L (D.barycenter j) :=
      fit_finiteCutoffAtomicMeasure _ _ _ L _ s
    _ ≤ ∑ j ∈ J, ENNReal.ofReal D.A * ∫⁻ w in D.cell j, modelCost L w ∂ν :=
      Finset.sum_le_sum fun j _ => D.weighted_modelCost_le j L
    _ = ENNReal.ofReal D.A * ∑ j ∈ J, ∫⁻ w in D.cell j, modelCost L w ∂ν := by
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal D.A * ∫⁻ w in ⋃ j ∈ J, D.cell j, modelCost L w ∂ν := by
      rw [lintegral_biUnion_finset hd (fun j _ => D.measurable_cell j) (modelCost L)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (lintegral_mono_set hsub) zero_le

theorem fittingInfimum_atomicMeasure_le (D : FiniteBarycenterCells ν ι) (i : ι)
    {s : ℝ} (hs : D.cutoff i ≤ s) [Nonempty (Models n k T)] :
    (⨅ L : Models n k T, fit (D.atomicMeasure s) L (D.barycenter i) s) ≤
      ENNReal.ofReal D.A * ⨅ L : Models n k T, fit ν L (D.sample i) (2 * s) := by
  rw [ENNReal.mul_iInf (fun h => (ENNReal.ofReal_ne_top h).elim)]
  exact iInf_mono fun L => D.fit_atomicMeasure_le i hs L

/-- The exact natural-beta transfer with the cutoff `r_j/2 ≤ s` and open testing balls. -/
theorem betaSq_atomicMeasure_le (D : FiniteBarycenterCells ν ι) (i : ι)
    {s : ℝ} (hs : D.cutoff i ≤ s) (k : ℕ) (T : FamilyKind)
    [Nonempty (Models n k T)] :
    betaSq (D.atomicMeasure s) k T (D.barycenter i) s ≤
      ENNReal.ofReal D.A * 2 ^ (k + 2) * betaSq ν k T (D.sample i) (2 * s) := by
  have hs0 : 0 < s := (D.cutoff_pos i).trans_le hs
  have hs2 : 0 < 2 * s := mul_pos (by norm_num) hs0
  have hn := radius_ratio_normalization hs0 hs2 (k + 2)
    (⨅ L : Models n k T, fit ν L (D.sample i) (2 * s))
  have hr : (2 * s) / s = 2 := by field_simp
  norm_num only [hr, ENNReal.ofReal_ofNat] at hn
  rw [betaSq_of_pos _ _ _ _ hs0, betaSq_of_pos _ _ _ _ hs2]
  calc
    _ ≤ (ENNReal.ofReal s)⁻¹ ^ (k + 2) *
        (ENNReal.ofReal D.A * ⨅ L : Models n k T, fit ν L (D.sample i) (2 * s)) :=
      mul_le_mul_of_nonneg_left (D.fittingInfimum_atomicMeasure_le i hs) zero_le
    _ = ENNReal.ofReal D.A * ((ENNReal.ofReal s)⁻¹ ^ (k + 2) *
        ⨅ L : Models n k T, fit ν L (D.sample i) (2 * s)) := by ac_rfl
    _ = ENNReal.ofReal D.A * (2 ^ (k + 2) * ((ENNReal.ofReal (2 * s))⁻¹ ^ (k + 2) *
        ⨅ L : Models n k T, fit ν L (D.sample i) (2 * s))) := by rw [hn]
    _ = _ := by ac_rfl

theorem measurable_betaSq_atomicMeasure (D : FiniteBarycenterCells ν ι) (i : ι)
    (k : ℕ) (T : FamilyKind) :
    Measurable (fun s => betaSq (D.atomicMeasure s) k T (D.barycenter i) s) :=
  measurable_betaSq_finiteCutoffAtomicMeasure _ _ _ k T _

end FiniteBarycenterCells

/-- The change of variable `u=2s` preserves the actual scale measure `ds/s`,
and doubles the positive lower cutoff. No integrability or finite-energy
hypothesis is needed for this extended nonnegative identity. -/
theorem lintegral_comp_two_Ioi_scaleMeasure {b : ℝ} (hb : 0 < b)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ s in Ioi b, g (2 * s) ∂scaleMeasure) =
      ∫⁻ u in Ioi (2 * b), g u ∂scaleMeasure := by
  have hpre : (fun s : ℝ => 2 * s) ⁻¹' Ioi (2 * b) = Ioi b := by
    ext s
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  have hf : Measurable (fun u : ℝ => ENNReal.ofReal (1 / u) * g u) :=
    measurable_scaleDensity.mul hg
  have he := setLIntegral_map (μ := (volume : Measure ℝ))
    (g := fun s : ℝ => 2 * s) (s := Ioi (2 * b)) measurableSet_Ioi hf
    (measurable_const_mul 2)
  rw [hpre, Real.map_volume_mul_left (by norm_num : (2 : ℝ) ≠ 0),
    setLIntegral_smul_measure] at he
  simp only [smul_eq_mul] at he
  have hcoef : (2 : ℝ≥0∞) * ENNReal.ofReal |(2 : ℝ)⁻¹| = 1 := by
    rw [abs_of_pos (inv_pos.mpr (by norm_num : (0 : ℝ) < 2)),
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  calc
    _ = ∫⁻ s in Ioi b, ENNReal.ofReal (1 / s) * g (2 * s) ∂volume :=
      setLIntegral_scaleMeasure measurableSet_Ioi (Ioi_subset_Ioi hb.le) _
        (hg.comp (measurable_const_mul 2))
    _ = (2 : ℝ≥0∞) * ∫⁻ s in Ioi b,
        ENNReal.ofReal (1 / (2 * s)) * g (2 * s) ∂volume := by
      rw [← lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num)]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s hs
      dsimp only
      have hsd : 1 / s = 2 * (1 / (2 * s)) := by field_simp [ne_of_gt (hb.trans hs)]
      rw [hsd, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num only [ENNReal.ofReal_ofNat]
      ac_rfl
    _ = (2 : ℝ≥0∞) * (ENNReal.ofReal |(2 : ℝ)⁻¹| *
        ∫⁻ u in Ioi (2 * b), ENNReal.ofReal (1 / u) * g u ∂volume) := by rw [← he]
    _ = ∫⁻ u in Ioi (2 * b), ENNReal.ofReal (1 / u) * g u ∂volume := by
      rw [← mul_assoc, hcoef, one_mul]
    _ = _ := (setLIntegral_scaleMeasure measurableSet_Ioi
      (Ioi_subset_Ioi (mul_pos (by norm_num) hb).le) g hg).symm

namespace FiniteBarycenterCells

variable {ν : Measure (Space n)}

/-- The actual varying-source energy above the cell's positive cutoff. -/
def atomicEnergy (D : FiniteBarycenterCells ν ι) (i : ι) (k : ℕ) (T : FamilyKind) : ℝ≥0∞ :=
  ∫⁻ s in Ioi (D.cutoff i), betaSq (D.atomicMeasure s) k T (D.barycenter i) s ∂scaleMeasure

theorem atomicEnergy_le (D : FiniteBarycenterCells ν ι) (i : ι)
    (k : ℕ) (T : FamilyKind) [Nonempty (Models n k T)] :
    D.atomicEnergy i k T ≤ ENNReal.ofReal D.A * 2 ^ (k + 2) *
      ∫⁻ u in Ioi 0, betaSq ν k T (D.sample i) u ∂scaleMeasure := by
  have hcoeff : ENNReal.ofReal D.A * (2 : ℝ≥0∞) ^ (k + 2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by finiteness)
  calc
    _ ≤ ∫⁻ s in Ioi (D.cutoff i), ENNReal.ofReal D.A * 2 ^ (k + 2) *
        betaSq ν k T (D.sample i) (2 * s) ∂scaleMeasure :=
      setLIntegral_mono' measurableSet_Ioi fun s hs => D.betaSq_atomicMeasure_le i hs.le k T
    _ = ENNReal.ofReal D.A * 2 ^ (k + 2) * ∫⁻ s in Ioi (D.cutoff i),
        betaSq ν k T (D.sample i) (2 * s) ∂scaleMeasure :=
      lintegral_const_mul' _ _ hcoeff
    _ = ENNReal.ofReal D.A * 2 ^ (k + 2) * ∫⁻ u in Ioi (2 * D.cutoff i),
        betaSq ν k T (D.sample i) u ∂scaleMeasure := by
      rw [lintegral_comp_two_Ioi_scaleMeasure (D.cutoff_pos i) _
        (measurable_betaSq_radius ν k T (D.sample i))]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (lintegral_mono_set (Ioi_subset_Ioi (mul_pos (by norm_num) (D.cutoff_pos i)).le)) zero_le

theorem atomicEnergy_le_of_source_bound (D : FiniteBarycenterCells ν ι) (i : ι)
    (k : ℕ) (T : FamilyKind) [Nonempty (Models n k T)] {L : ℝ≥0∞}
    (hL : (∫⁻ u in Ioi 0, betaSq ν k T (D.sample i) u ∂scaleMeasure) ≤ L) :
    D.atomicEnergy i k T ≤ ENNReal.ofReal D.A * 2 ^ (k + 2) * L :=
  (D.atomicEnergy_le i k T).trans (mul_le_mul_of_nonneg_left hL zero_le)

end FiniteBarycenterCells
end ParabolicRectifiability
