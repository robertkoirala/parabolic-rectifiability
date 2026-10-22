import ParabolicRectifiability.Metric.Hausdorff
import ParabolicRectifiability.Geometry.SubspaceCoordinates
import Mathlib.MeasureTheory.Covering.Vitali

/-!
# Hausdorff measure and intrinsic base volume

The lower comparison uses the actual closed-ball volume. The upper comparison
uses disjoint open balls whose fixed enlargements cover the whole open set.
No null-set comparison is assumed before it has been proved.
-/
noncomputable section
open MeasureTheory Set EMetric Metric
open scoped ENNReal

namespace ParabolicRectifiability

section GeneralMetricSpace
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
/-- A finite-diameter set lies in a closed ball about any one of its points. -/
theorem measure_le_ediam_pow_of_closedBall (μ : Measure X) (k : ℕ) (v : ℝ≥0∞)
    (hball : ∀ x r, 0 ≤ r → μ (closedBall x r) ≤ v * ENNReal.ofReal r ^ k)
    {A : Set X} (hA : ediam A ≠ ∞) : μ A ≤ v * ediam A ^ k := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  have hsub : A ⊆ closedBall x (diam A) := fun y hy =>
    dist_le_diam_of_mem' hA hy hx
  calc
    μ A ≤ μ (closedBall x (diam A)) := measure_mono hsub
    _ ≤ v * ENNReal.ofReal (diam A) ^ k := hball x _ diam_nonneg
    _ = v * ediam A ^ k := by rw [diam, ENNReal.ofReal_toReal hA]

/-- The lower Hausdorff comparison requires only the stated closed-ball bound. -/
theorem smul_measure_le_hausdorff_of_closedBall (μ : Measure X) (k : ℕ) (v : ℝ≥0∞)
    (hv : 0 < v) (hvfin : v ≠ ∞)
    (hball : ∀ x r, 0 ≤ r → μ (closedBall x r) ≤ v * ENNReal.ofReal r ^ k) :
    v⁻¹ • μ ≤ Measure.hausdorffMeasure (k : ℝ) := by
  apply Measure.le_hausdorffMeasure (k : ℝ) (v⁻¹ • μ) 1 (by norm_num)
  intro A hA
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.rpow_natCast]
  have hfin : ediam A ≠ ∞ := ne_top_of_le_ne_top (by norm_num) hA
  calc
    v⁻¹ * μ A ≤ v⁻¹ * (v * ediam A ^ k) :=
      mul_le_mul_right (measure_le_ediam_pow_of_closedBall μ k v hball hfin) _
    _ = ediam A ^ k := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hv.ne' hvfin, one_mul]

/-- Disjoint small balls yield a cover of every point, with controlled diameter-power cost. -/
private theorem exists_small_ball_cover [TopologicalSpace.SeparableSpace X]
    (μ : Measure X) (k : ℕ) (v : ℝ≥0∞) (hv : 0 < v) (hvfin : v ≠ ∞)
    (hball : ∀ x r, 0 < r → μ (ball x r) = v * ENNReal.ofReal r ^ k)
    (U : Set X) (hU : IsOpen U) (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : U → ℝ) (u : Set U), u.Countable ∧
      (∀ i : u, ediam (ball (i.1.1 : X) (5 * r i.1)) ≤ ENNReal.ofReal ε) ∧
      (U ⊆ ⋃ i : u, ball (i.1.1 : X) (5 * r i.1)) ∧
      (∑' i : u, ediam (ball (i.1.1 : X) (5 * r i.1)) ^ (k : ℝ)) ≤
        ((10 : ℝ≥0∞) ^ k * v⁻¹) * μ U := by
  classical
  have hx : ∀ x : U, ∃ δ : ℝ, 0 < δ ∧ ball (x : X) δ ⊆ U :=
    fun x => Metric.isOpen_iff.mp hU x x.property
  choose δ hδpos hδsub using hx
  let r : U → ℝ := fun x => min (δ x) (ε / 10)
  have hrpos (x : U) : 0 < r x := lt_min (hδpos x) (by positivity)
  have hrsub (x : U) : ball (x : X) (r x) ⊆ U :=
    (ball_subset_ball (min_le_left _ _)).trans (hδsub x)
  obtain ⟨u, _, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball (univ : Set U)
      (fun x => (x : X)) r (ε / 10) (fun x _ => min_le_right _ _) 5 (by norm_num)
  have hcount : u.Countable := hdisj.countable_of_isOpen
    (fun _ _ => isOpen_ball) (fun x _ => ⟨(x : X), mem_ball_self (hrpos x)⟩)
  let : Countable u := hcount.to_subtype
  have hd (x : U) : ediam (ball (x : X) (5 * r x)) ≤ ENNReal.ofReal (10 * r x) := by
    apply ediam_le_of_forall_dist_le
    intro y hy z hz
    have hy' := mem_ball.mp hy
    have hz' := mem_ball.mp hz
    have ht := dist_triangle_right y z (x : X)
    linarith
  refine ⟨r, u, hcount, ?_, ?_, ?_⟩
  · intro i
    exact (hd i.1).trans (ENNReal.ofReal_le_ofReal (by
      have h := min_le_right (δ i.1) (ε / 10); change r i.1 ≤ ε / 10 at h; linarith))
  · intro x hxU
    obtain ⟨b, hb, hxb⟩ := hcover ⟨x, hxU⟩ (mem_univ _)
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, hxb (mem_ball_self (hrpos ⟨x, hxU⟩))⟩
  · have hcost (i : u) : ediam (ball (i.1.1 : X) (5 * r i.1)) ^ (k : ℝ) ≤
        ((10 : ℝ≥0∞) ^ k * v⁻¹) * μ (ball (i.1.1 : X) (r i.1)) := by
      rw [ENNReal.rpow_natCast, hball _ _ (hrpos _)]
      calc
        _ ≤ ENNReal.ofReal (10 * r i.1) ^ k := pow_le_pow_left' (hd i.1) k
        _ = _ := by
          rw [ENNReal.ofReal_mul (by norm_num), mul_pow]
          norm_num only [ENNReal.ofReal_ofNat]
          rw [mul_assoc, ← mul_assoc v⁻¹ v, ENNReal.inv_mul_cancel hv.ne' hvfin, one_mul]
    calc
      _ ≤ ∑' i : u, ((10 : ℝ≥0∞) ^ k * v⁻¹) * μ (ball (i.1.1 : X) (r i.1)) :=
        ENNReal.tsum_le_tsum hcost
      _ = ((10 : ℝ≥0∞) ^ k * v⁻¹) * μ (⋃ i : u, ball (i.1.1 : X) (r i.1)) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion]
        · exact hdisj.subtype _ _
        · intro i; exact measurableSet_ball
      _ ≤ ((10 : ℝ≥0∞) ^ k * v⁻¹) * μ U :=
        mul_le_mul_right (measure_mono (iUnion_subset fun i : u => hrsub i.1)) _

/-- Upper comparison on open sets, using covers of all points rather than a.e. covers. -/
theorem hausdorff_le_mul_measure_of_ball [TopologicalSpace.SeparableSpace X]
    (μ : Measure X) (k : ℕ) (v : ℝ≥0∞) (hv : 0 < v) (hvfin : v ≠ ∞)
    (hball : ∀ x r, 0 < r → μ (ball x r) = v * ENNReal.ofReal r ^ k)
    (U : Set X) (hU : IsOpen U) :
    Measure.hausdorffMeasure (k : ℝ) U ≤ ((10 : ℝ≥0∞) ^ k * v⁻¹) * μ U := by
  classical
  have hex (j : ℕ) := exists_small_ball_cover μ k v hv hvfin hball U hU
    (1 / (j + 1 : ℝ)) (by positivity)
  choose r u hc hd hcover hcost using hex
  let (j : ℕ) : Countable (u j) := (hc j).to_subtype
  have hlim : Filter.Tendsto (fun j : ℕ => ENNReal.ofReal (1 / (j + 1 : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun j : ℕ => (1 : ℝ) / (j + 1)) Filter.atTop (nhds 0))
  have H := Measure.hausdorffMeasure_le_liminf_tsum (k : ℝ) U _ hlim
    (fun j (i : u j) => ball (i.1.1 : X) (5 * r j i.1))
    (Filter.Eventually.of_forall hd) (Filter.Eventually.of_forall hcover)
  exact H.trans (Filter.liminf_le_of_frequently_le (Filter.Frequently.of_forall hcost))

/-- Outer regularity extends the open-set estimate to arbitrary sets. -/
theorem hausdorff_le_mul_measure_of_ball_outerRegular [TopologicalSpace.SeparableSpace X]
    (μ : Measure X) [Measure.OuterRegular μ] (k : ℕ) (v : ℝ≥0∞)
    (hv : 0 < v) (hvfin : v ≠ ∞)
    (hball : ∀ x r, 0 < r → μ (ball x r) = v * ENNReal.ofReal r ^ k) (E : Set X) :
    Measure.hausdorffMeasure (k : ℝ) E ≤ ((10 : ℝ≥0∞) ^ k * v⁻¹) * μ E := by
  have hc0 : (10 : ℝ≥0∞) ^ k * v⁻¹ ≠ 0 :=
    (ENNReal.mul_pos (by positivity) (ENNReal.inv_ne_zero.mpr hvfin)).ne'
  have hcfin : (10 : ℝ≥0∞) ^ k * v⁻¹ ≠ ∞ := by
    exact ENNReal.mul_ne_top (by finiteness) (ENNReal.inv_ne_top.mpr hv.ne')
  rw [E.measure_eq_iInf_isOpen μ]
  simp only [ENNReal.mul_iInf_of_ne hc0 hcfin, le_iInf_iff]
  intro U hEU hU
  exact (measure_mono hEU).trans (hausdorff_le_mul_measure_of_ball μ k v hv hvfin hball U hU)

end GeneralMetricSpace

/-- The exact reciprocal-unit-ball lower coefficient in parabolic space. -/
theorem parabolicVolume_smul_le_hausdorff (m : ℕ) :
    (2 * omega m)⁻¹ • parabolicVolume m ≤ hausdorffP m (m + 2) := by
  apply smul_measure_le_hausdorff_of_closedBall
  · exact ENNReal.mul_pos (by norm_num) (omega_pos m).ne'
  · exact ENNReal.mul_ne_top (by norm_num) (omega_lt_top m).ne
  · intro x r hr
    exact le_of_eq (parabolicVolume_closedBall x r hr)

/-- Ordinary Euclidean ball volume, including the rank-zero case for positive radii. -/
theorem volume_spatial_ball {d : ℕ} (x : Spatial d) {r : ℝ} (hr : 0 < r) :
    volume (ball x r) = omega d * ENNReal.ofReal r ^ d := by
  simpa [omega, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr.le, mul_comm] using
    Measure.addHaar_ball_of_pos (volume : Measure (Spatial d)) x hr

theorem volume_spatial_closedBall {d : ℕ} (x : Spatial d) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) = omega d * ENNReal.ofReal r ^ d := by
  simpa [omega, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr, mul_comm] using
    Measure.addHaar_closedBall (volume : Measure (Spatial d)) x hr

theorem spatialVolume_smul_le_hausdorff (d : ℕ) :
    (omega d)⁻¹ • (volume : Measure (Spatial d)) ≤ Measure.hausdorffMeasure (d : ℝ) := by
  apply smul_measure_le_hausdorff_of_closedBall
  · exact omega_pos d
  · exact (omega_lt_top d).ne
  · intro x r hr; exact le_of_eq (volume_spatial_closedBall x hr)

/-- A fixed positive finite coefficient, chosen before the measured set. -/
def horizontalHausdorffConstant (d : ℕ) : ℝ≥0∞ := (10 : ℝ≥0∞) ^ d * (omega d)⁻¹

def verticalHausdorffConstant (m : ℕ) : ℝ≥0∞ :=
  (10 : ℝ≥0∞) ^ (m + 2) * (2 * omega m)⁻¹

theorem horizontalHausdorffConstant_pos (d : ℕ) : 0 < horizontalHausdorffConstant d := by
  unfold horizontalHausdorffConstant
  exact ENNReal.mul_pos (by positivity) (ENNReal.inv_ne_zero.mpr (omega_lt_top d).ne)

theorem horizontalHausdorffConstant_lt_top (d : ℕ) : horizontalHausdorffConstant d < ∞ := by
  unfold horizontalHausdorffConstant
  exact ENNReal.mul_lt_top (by finiteness) (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (omega_pos d).ne'))

theorem verticalHausdorffConstant_pos (m : ℕ) : 0 < verticalHausdorffConstant m := by
  unfold verticalHausdorffConstant
  exact ENNReal.mul_pos (by positivity)
    (ENNReal.inv_ne_zero.mpr (ENNReal.mul_ne_top (by norm_num) (omega_lt_top m).ne))

theorem verticalHausdorffConstant_lt_top (m : ℕ) : verticalHausdorffConstant m < ∞ := by
  unfold verticalHausdorffConstant
  exact ENNReal.mul_lt_top (by finiteness)
    (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr
      (ENNReal.mul_pos (by norm_num) (omega_pos m).ne').ne'))

/-- Diameter-power Hausdorff measure and inner-product volume, for all sets. -/
theorem spatial_hausdorff_comparison (d : ℕ) (E : Set (Spatial d)) :
    (omega d)⁻¹ * volume E ≤ Measure.hausdorffMeasure (d : ℝ) E ∧
      Measure.hausdorffMeasure (d : ℝ) E ≤ horizontalHausdorffConstant d * volume E := by
  constructor
  · simpa only [Measure.smul_apply, smul_eq_mul] using
      Measure.le_iff'.mp (spatialVolume_smul_le_hausdorff d) E
  · exact hausdorff_le_mul_measure_of_ball_outerRegular volume d (omega d)
      (omega_pos d) (omega_lt_top d).ne (fun x r hr => volume_spatial_ball x hr) E

/-- Parabolic diameter-power Hausdorff measure and reference volume, for all sets. -/
theorem parabolic_hausdorff_comparison (m : ℕ) (E : Set (Space m)) :
    (2 * omega m)⁻¹ * parabolicVolume m E ≤ hausdorffP m (m + 2) E ∧
      hausdorffP m (m + 2) E ≤ verticalHausdorffConstant m * parabolicVolume m E := by
  constructor
  · simpa only [Measure.smul_apply, smul_eq_mul] using
      Measure.le_iff'.mp (parabolicVolume_smul_le_hausdorff m) E
  · exact hausdorff_le_mul_measure_of_ball_outerRegular (parabolicVolume m) (m + 2)
      (2 * omega m) (ENNReal.mul_pos (by norm_num) (omega_pos m).ne')
      (ENNReal.mul_ne_top (by norm_num) (omega_lt_top m).ne)
      (fun x r hr => parabolicVolume_ball x r hr) E

/-- The horizontal base uses intrinsic subspace volume, not ambient restriction. -/
theorem horizontal_base_hausdorff_comparison {n : ℕ} (W : Submodule ℝ (Spatial n)) (E : Set W) :
    (omega (Module.finrank ℝ W))⁻¹ * volume E ≤
        Measure.hausdorffMeasure (Module.finrank ℝ W : ℝ) E ∧
      Measure.hausdorffMeasure (Module.finrank ℝ W : ℝ) E ≤
        horizontalHausdorffConstant (Module.finrank ℝ W) * volume E := by
  let e := subspaceCoordinates W
  have hm := (subspaceCoordinates_spatial_measurePreserving W).measure_preimage_equiv (e '' E)
  have hv : (volume : Measure W) E = volume (e '' E) := by
    change volume (e ⁻¹' (e '' E)) = volume (e '' E) at hm
    simpa only [e.injective.preimage_image] using hm
  have hh := e.toIsometryEquiv.hausdorffMeasure_image (Module.finrank ℝ W : ℝ) E
  change Measure.hausdorffMeasure (Module.finrank ℝ W : ℝ) (e '' E) =
    Measure.hausdorffMeasure (Module.finrank ℝ W : ℝ) E at hh
  have H := spatial_hausdorff_comparison (Module.finrank ℝ W) (e '' E)
  rwa [hh, ← hv] at H

/-- The vertical base uses the actual parabolic metric and intrinsic reference volume. -/
theorem vertical_base_hausdorff_comparison {n : ℕ} (W : Submodule ℝ (Spatial n))
    (E : Set (SubspaceSpace W)) :
    (2 * omega (Module.finrank ℝ W))⁻¹ * intrinsicParabolicVolume W E ≤
        Measure.hausdorffMeasure ((Module.finrank ℝ W + 2 : ℕ) : ℝ) E ∧
      Measure.hausdorffMeasure ((Module.finrank ℝ W + 2 : ℕ) : ℝ) E ≤
        verticalHausdorffConstant (Module.finrank ℝ W) * intrinsicParabolicVolume W E := by
  let e := subspaceParabolicIsometry W
  have hm := (subspaceParabolic_measurePreserving W).measure_preimage_equiv (e '' E)
  have hv : intrinsicParabolicVolume W E = parabolicVolume (Module.finrank ℝ W) (e '' E) := by
    change intrinsicParabolicVolume W (e ⁻¹' (e '' E)) =
      parabolicVolume (Module.finrank ℝ W) (e '' E) at hm
    simpa only [e.injective.preimage_image] using hm
  have hh := e.hausdorffMeasure_image ((Module.finrank ℝ W + 2 : ℕ) : ℝ) E
  have H := parabolic_hausdorff_comparison (Module.finrank ℝ W) (e '' E)
  change _ ≤ Measure.hausdorffMeasure ((Module.finrank ℝ W + 2 : ℕ) : ℝ) (e '' E) ∧
    Measure.hausdorffMeasure ((Module.finrank ℝ W + 2 : ℕ) : ℝ) (e '' E) ≤ _ at H
  rwa [hh, ← hv] at H

end ParabolicRectifiability
