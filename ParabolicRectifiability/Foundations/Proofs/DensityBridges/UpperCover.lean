import ParabolicRectifiability.Foundations.Statements.DensityBridges
import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.ElementaryLemmas

/-! # The fivefold covering bound for Hausdorff measure

Proof of `fupdom_hausdorffP_le_of_fivefold`. The fivefold selection
`Characterization.FivefoldSelectionStatement` stays the first hypothesis.

* `fupdom_hausdorffP_le_of_fivefold_proof_of` is the conditional form: its first premise is the
  complete type of `fupdom_exists_ratio_gt`.
* `fupdom_hausdorffP_le_of_fivefold_proof` has exactly the type of
  `fupdom_hausdorffP_le_of_fivefold`; it applies the conditional form to
  `fupdom_exists_ratio_gt_proof`.

Route: at each mesh `δ`,
index the balls `P(z,r)` with `z ∈ E`, `r > 0`, `10 r ≤ δ`, `P(z,5r) ⊆ V` and
`ρ(P(z,r)) > (a/2) r^k`; the fivefold selection gives a countable disjoint subfamily `J δ`
whose fivefold dilates cover all centres, hence `E` (every `z ∈ E` is a centre by
`fupdom_exists_ratio_gt`). Each
dilate has `ediam ≤ 10 r ≤ δ`, and
`∑ ediam(P(z_j,5r_j))^k ≤ (2·10^k/a) ∑ ρ(P(z_j,r_j)) ≤ (2·10^k/a) ρ(V)`.
`Measure.hausdorffMeasure_le_liminf_tsum` over `𝓝[>] 0` with the dependent countable index
`J δ` (no padding) gives the bound. Valid for arbitrary `E`, arbitrary `ρ` and `k = 0`.
Helper prefix `fbfb3_`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- The fivefold dilate of a ball of radius `r` has extended diameter at most `10 r`. -/
theorem fbfb3_ediam_ball_five_le {n : ℕ} (z : Space n) (r : ℝ) :
    Metric.ediam (Metric.ball z (5 * r)) ≤ ENNReal.ofReal (10 * r) := by
  refine Metric.ediam_le fun x hx y hy => ?_
  rw [edist_dist]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : dist x z < 5 * r := Metric.mem_ball.1 hx
  have h2 : dist y z < 5 * r := Metric.mem_ball.1 hy
  linarith [dist_triangle_right x y z]

/-- The `k`-cost of the fivefold dilate is bounded by `(2·10^k/a)` times the mass of the ball,
when the ball has mass `> (a/2) r^k`. Valid for `k = 0`. -/
theorem fbfb3_cost_le {n : ℕ} (k : ℕ) (ρ : Measure (Space n)) (a : ℝ) (ha : 0 < a)
    (z : Space n) (r : ℝ) (hr : 0 < r)
    (hm : ENNReal.ofReal (a / 2 * r ^ k) < ρ (Metric.ball z r)) :
    Metric.ediam (Metric.ball z (5 * r)) ^ (k : ℝ) ≤
      ENNReal.ofReal (2 * 10 ^ k / a) * ρ (Metric.ball z r) := by
  have hC : (0 : ℝ) ≤ 2 * 10 ^ k / a := div_nonneg (by positivity) ha.le
  have heq : (10 * r) ^ k = 2 * 10 ^ k / a * (a / 2 * r ^ k) := by
    rw [mul_pow]
    field_simp
  calc Metric.ediam (Metric.ball z (5 * r)) ^ (k : ℝ)
      ≤ ENNReal.ofReal (10 * r) ^ (k : ℝ) :=
        ENNReal.rpow_le_rpow (fbfb3_ediam_ball_five_le z r) (Nat.cast_nonneg k)
    _ = ENNReal.ofReal ((10 * r) ^ k) := by
        rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (by linarith)]
    _ = ENNReal.ofReal (2 * 10 ^ k / a) * ENNReal.ofReal (a / 2 * r ^ k) := by
        rw [← ENNReal.ofReal_mul hC, heq]
    _ ≤ ENNReal.ofReal (2 * 10 ^ k / a) * ρ (Metric.ball z r) :=
        mul_le_mul_right hm.le _

/-- The index type of admissible balls at mesh `δ`: centre in `E`, positive radius `r` with
`10 r ≤ δ`, fivefold dilate inside `V`, and mass `> (a/2) r^k`. -/
abbrev fbfb3_Index {n : ℕ} (k : ℕ) (ρ : Measure (Space n)) (a δ : ℝ) (E V : Set (Space n)) :
    Type :=
  {p : Space n × ℝ // p.1 ∈ E ∧ 0 < p.2 ∧ 10 * p.2 ≤ δ ∧ Metric.ball p.1 (5 * p.2) ⊆ V ∧
    ENNReal.ofReal (a / 2 * p.2 ^ k) < ρ (Metric.ball p.1 p.2)}

/-- Conditional form of `fupdom_hausdorffP_le_of_fivefold`: the first premise is the complete
type of `fupdom_exists_ratio_gt`; the remaining binders are those of the statement. -/
theorem fupdom_hausdorffP_le_of_fivefold_proof_of
    (hU1 : ∀ {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n)
      (a : ℝ) (_ha : 0 < a) (_hz : ENNReal.ofReal a ≤ upperDensity μ k z)
      (δ : ℝ) (_hδ : 0 < δ),
      ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (a / 2 * r ^ k) < μ (Metric.ball z r))
    (h5 : Characterization.FivefoldSelectionStatement)
    {n : ℕ} (k : ℕ) (ρ : Measure (Space n)) (a : ℝ) (ha : 0 < a)
    (E V : Set (Space n)) (hV : IsOpen V) (hEV : E ⊆ V)
    (hE : ∀ z ∈ E, ENNReal.ofReal a ≤ upperDensity ρ k z) :
    hausdorffP n k E ≤ ENNReal.ofReal (2 * 10 ^ k / a) * ρ V := by
  -- Fivefold selection at every mesh `δ` (the radii are positive and bounded by `δ`).
  have hsel : ∀ δ : ℝ, ∃ J : Set (fbfb3_Index k ρ a δ E V), J.Countable ∧
      J.PairwiseDisjoint (fun i => Metric.ball i.1.1 i.1.2) ∧
      ∀ i : fbfb3_Index k ρ a δ E V, ∃ j ∈ J, i.1.1 ∈ Metric.ball j.1.1 (5 * j.1.2) :=
    fun δ => h5 (Space n) (fbfb3_Index k ρ a δ E V) (fun i => i.1.1) (fun i => i.1.2)
      (fun i => i.2.2.1) ⟨δ, fun i => by linarith [i.2.2.1, i.2.2.2.1]⟩
  choose J hJc hJd hJcov using hsel
  have hcount : ∀ δ, Countable (J δ) := fun δ => (hJc δ).to_subtype
  -- The cost of the selected cover at every mesh.
  have hsum : ∀ δ : ℝ, ∑' i : J δ, Metric.ediam (Metric.ball i.1.1.1 (5 * i.1.1.2)) ^ (k : ℝ) ≤
      ENNReal.ofReal (2 * 10 ^ k / a) * ρ V := by
    intro δ
    have hdisj : ∑' i : J δ, ρ (Metric.ball i.1.1.1 i.1.1.2) ≤ ρ V := by
      calc ∑' i : J δ, ρ (Metric.ball i.1.1.1 i.1.1.2)
          ≤ ρ (⋃ i : J δ, Metric.ball i.1.1.1 i.1.1.2) :=
            tsum_meas_le_meas_iUnion_of_disjoint ρ (fun _ => Metric.isOpen_ball.measurableSet)
              (fun i j hij => hJd δ i.2 j.2 (fun h => hij (Subtype.ext h)))
        _ ≤ ρ V := by
            refine measure_mono (iUnion_subset fun i => ?_)
            exact (Metric.ball_subset_ball (by linarith [i.1.2.2.1])).trans i.1.2.2.2.2.1
    calc ∑' i : J δ, Metric.ediam (Metric.ball i.1.1.1 (5 * i.1.1.2)) ^ (k : ℝ)
        ≤ ∑' i : J δ, ENNReal.ofReal (2 * 10 ^ k / a) * ρ (Metric.ball i.1.1.1 i.1.1.2) :=
          ENNReal.tsum_le_tsum fun i => fbfb3_cost_le k ρ a ha _ _ i.1.2.2.1 i.1.2.2.2.2.2
      _ = ENNReal.ofReal (2 * 10 ^ k / a) * ∑' i : J δ, ρ (Metric.ball i.1.1.1 i.1.1.2) :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (2 * 10 ^ k / a) * ρ V := mul_le_mul_right hdisj _
  -- The mesh limit.
  have hH : hausdorffP n k E ≤ liminf (fun δ : ℝ => ∑' i : J δ,
      Metric.ediam (Metric.ball i.1.1.1 (5 * i.1.1.2)) ^ (k : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [hausdorffP_eq]
    refine Measure.hausdorffMeasure_le_liminf_tsum (ι := fun δ : ℝ => J δ) (k : ℝ) E
      (fun δ : ℝ => ENNReal.ofReal δ) ?_
      (fun δ (i : J δ) => Metric.ball i.1.1.1 (5 * i.1.1.2)) ?_ ?_
    · have h0 : Tendsto (fun δ : ℝ => ENNReal.ofReal δ) (𝓝[>] (0 : ℝ))
          (𝓝 (ENNReal.ofReal 0)) :=
        ENNReal.tendsto_ofReal (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
      rwa [ENNReal.ofReal_zero] at h0
    · exact Eventually.of_forall fun δ i =>
        (fbfb3_ediam_ball_five_le _ _).trans (ENNReal.ofReal_le_ofReal i.1.2.2.2.1)
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ' : 0 < δ := hδ
      intro z hz
      obtain ⟨s, hs, hsV⟩ := Metric.isOpen_iff.1 hV z (hEV hz)
      obtain ⟨r, hr, hrlt, hm⟩ :=
        hU1 ρ k z a ha (hE z hz) (min (δ / 10) (s / 5)) (lt_min (by linarith) (by linarith))
      have hr1 : r < δ / 10 := hrlt.trans_le (min_le_left _ _)
      have hr2 : r < s / 5 := hrlt.trans_le (min_le_right _ _)
      let p : fbfb3_Index k ρ a δ E V :=
        ⟨(z, r), hz, hr, by linarith, (Metric.ball_subset_ball (by linarith)).trans hsV, hm⟩
      obtain ⟨j, hj, hzj⟩ := hJcov δ p
      exact mem_iUnion.2 ⟨⟨j, hj⟩, hzj⟩
  calc hausdorffP n k E ≤ liminf (fun δ : ℝ => ∑' i : J δ,
        Metric.ediam (Metric.ball i.1.1.1 (5 * i.1.1.2)) ^ (k : ℝ)) (𝓝[>] (0 : ℝ)) := hH
    _ ≤ ENNReal.ofReal (2 * 10 ^ k / a) * ρ V :=
        liminf_le_of_frequently_le' (Frequently.of_forall hsum)

/-- **The fivefold covering bound**, with exactly the type of
`fupdom_hausdorffP_le_of_fivefold`: the conditional form applied to
`fupdom_exists_ratio_gt_proof`. -/
theorem fupdom_hausdorffP_le_of_fivefold_proof (h5 : Characterization.FivefoldSelectionStatement)
    {n : ℕ} (k : ℕ) (ρ : Measure (Space n)) (a : ℝ) (ha : 0 < a)
    (E V : Set (Space n)) (hV : IsOpen V) (hEV : E ⊆ V)
    (hE : ∀ z ∈ E, ENNReal.ofReal a ≤ upperDensity ρ k z) :
    hausdorffP n k E ≤ ENNReal.ofReal (2 * 10 ^ k / a) * ρ V :=
  fupdom_hausdorffP_le_of_fivefold_proof_of fupdom_exists_ratio_gt_proof h5 k ρ a ha E V hV hEV hE

end ParabolicRectifiability.Foundations
