import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Defect

/-! # Local finiteness of the full node measure

Let `ν = vol⌞F₀ + Σ_j r_j^k δ_{p_j}`
be the full node measure of Whitney data, `k = m + 2`, `δ = d_P(·,F₀)`.

A center `p_j ∈ P(z,R)` satisfies `a r_j ≤ δ(p_j) ≤ δ(z) + d_P(p_j,z) < δ(z) + R`, so
its cell lies in the fixed ball `P(z, R + D(δ(z)+R)/a)`. The disjoint cells there have
total volume `Σ r_j^k` at most the volume of that ball, while the continuous part is
at most `|P(z,R)|`. Hence `ν(P(z,R)) < ∞`; for `R ≤ 0` the ball is empty. Compact sets
lie in balls, so `ν` is finite on compacts, locally finite and sigma-finite. Only the
cell data are used; no Whitney upper-distance bound is needed.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

namespace WhitneyData

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a : ℝ}

/-- The node measure of a measurable set: continuous part plus the weights of the
centers it contains. -/
theorem nodeMeasure_apply (W : WhitneyData m ι F₀ D a) {S : Set (Space m)}
    (hS : MeasurableSet S) :
    W.nodeMeasure S = parabolicVolume m (S ∩ F₀) +
      ∑' j, S.indicator (fun _ => ENNReal.ofReal (W.radius j ^ (m + 2))) (W.center j) := by
  rw [nodeMeasure, Measure.add_apply, Measure.restrict_apply hS, Measure.sum_apply _ hS]
  congr 1
  refine tsum_congr fun j => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul]
  by_cases h : W.center j ∈ S
  · rw [indicator_of_mem h, indicator_of_mem h, Pi.one_apply, mul_one]
  · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]

/-- A center in `P(z,R)` has `a r_j < δ(z) + R`. -/
theorem mul_radius_lt_of_center_mem_ball (W : WhitneyData m ι F₀ D a) {z : Space m} {R : ℝ}
    {j : ι} (hj : W.center j ∈ Metric.ball z R) :
    a * W.radius j < Metric.infDist z F₀ + R := by
  have h := Metric.mem_ball.mp hj
  calc
    a * W.radius j ≤ Metric.infDist (W.center j) F₀ := W.le_infDist j _ (W.center_mem j)
    _ ≤ Metric.infDist z F₀ + dist (W.center j) z := Metric.infDist_le_infDist_add_dist
    _ < Metric.infDist z F₀ + R := by linarith

/-- The cell of a center in `P(z,R)` lies in `P(z, R + D(δ(z)+R)/a)`. -/
theorem cell_subset_ball_of_center_mem_ball (W : WhitneyData m ι F₀ D a) {z : Space m}
    {R : ℝ} {j : ι} (hj : W.center j ∈ Metric.ball z R) :
    W.cell j ⊆ Metric.ball z (R + D * (Metric.infDist z F₀ + R) / a) := by
  intro q hq
  have ha : 0 < a := W.a_pos
  have hD : 0 ≤ D := zero_le_one.trans W.one_le_D
  have h1 := W.mul_radius_lt_of_center_mem_ball hj
  have h2 : W.radius j < (Metric.infDist z F₀ + R) / a := by
    rw [lt_div_iff₀ ha]
    linarith
  have h3 : D * W.radius j ≤ D * ((Metric.infDist z F₀ + R) / a) :=
    mul_le_mul_of_nonneg_left h2.le hD
  have h4 : dist q (W.center j) ≤ D * W.radius j :=
    Metric.mem_closedBall.mp (W.cell_subset j hq)
  have h5 : dist (W.center j) z < R := Metric.mem_ball.mp hj
  have h6 : D * ((Metric.infDist z F₀ + R) / a) = D * (Metric.infDist z F₀ + R) / a := by
    ring
  rw [Metric.mem_ball]
  calc
    dist q z ≤ dist q (W.center j) + dist (W.center j) z := dist_triangle _ _ _
    _ < R + D * (Metric.infDist z F₀ + R) / a := by linarith

/-- **Local finiteness of the full node measure**, derived from the cell data alone. -/
theorem nodeMeasure_ball_lt_top_proof {m : ℕ} {ι : Type*} [Countable ι]
    {F₀ : Set (Space m)} {D a : ℝ} (W : WhitneyData m ι F₀ D a) (z : Space m) (R : ℝ) :
    W.nodeMeasure (Metric.ball z R) < ⊤ := by
  rw [W.nodeMeasure_apply measurableSet_ball]
  refine ENNReal.add_lt_top.mpr ⟨(measure_mono inter_subset_left).trans_lt
    (measure_ball_lt_top (parabolicVolume m) z R), ?_⟩
  calc
    ∑' j, (Metric.ball z R).indicator (fun _ => ENNReal.ofReal (W.radius j ^ (m + 2)))
        (W.center j) ≤
        ∑' j, {j | W.cell j ⊆ Metric.ball z (R + D * (Metric.infDist z F₀ + R) / a)}.indicator
          (fun j => ENNReal.ofReal (W.radius j ^ (m + 2))) j := by
      refine ENNReal.tsum_le_tsum fun j => ?_
      by_cases hj : W.center j ∈ Metric.ball z R
      · rw [indicator_of_mem hj,
          indicator_of_mem (show j ∈ {j | W.cell j ⊆
            Metric.ball z (R + D * (Metric.infDist z F₀ + R) / a)} from
            W.cell_subset_ball_of_center_mem_ball hj)]
      · rw [indicator_of_notMem hj]
        exact zero_le
    _ ≤ parabolicVolume m (Metric.ball z (R + D * (Metric.infDist z F₀ + R) / a)) :=
      W.tsum_indicator_radius_le _
    _ < ⊤ := measure_ball_lt_top (parabolicVolume m) z _

/-- The full node measure is finite on compact sets. -/
instance isFiniteMeasureOnCompacts_nodeMeasure [Countable ι] (W : WhitneyData m ι F₀ D a) :
    IsFiniteMeasureOnCompacts W.nodeMeasure where
  lt_top_of_isCompact K hK := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (point 0 0)).mp hK.isBounded
    exact (measure_mono hR).trans_lt (W.nodeMeasure_ball_lt_top_proof _ _)

/-- The full node measure is locally finite. -/
theorem isLocallyFiniteMeasure_nodeMeasure [Countable ι] (W : WhitneyData m ι F₀ D a) :
    IsLocallyFiniteMeasure W.nodeMeasure :=
  inferInstance

/-- The full node measure is sigma-finite. -/
theorem sigmaFinite_nodeMeasure [Countable ι] (W : WhitneyData m ι F₀ D a) :
    SigmaFinite W.nodeMeasure :=
  inferInstance

end WhitneyData

end ParabolicRectifiability
