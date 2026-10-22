import ParabolicRectifiability.Examples.Proofs.Reductions.ReductionStatements

/-! # The vertical identity for the stationary product

For the stationary
source `μ = (q ↦ point q.1 q.2)_#(ν ⊗ L¹⌊[-1,1])`, `t ∈ [-1,1]`, `0 < r` and
`ℓ = |(t-r², t+r²) ∩ [-1,1]|`,
`β²_{V,μ,m+2}((x,t),r) = (ℓ/r²) b^E_{2,ν,m}(x,r)`.

Route:
* the vertical cost is spatial: for a vertical model `V × ℝ`, the parabolic distance from
  `point y s` to `V × ℝ` is the Euclidean distance from `y` to `V`;
* change of variables (`setLIntegral_map`), the ball preimage `B(x,r) × (t-r², t+r²)`
  (`mem_ball_point`), and Tonelli for a product integrand (`lintegral_prod_mul`), so
  `fit = (∫_{B(x,r)} dist(y,V)² dν) · ℓ`;
* reindex `VerticalModel n (m+2)` by `AffineSpatialPlane n m` (spatial rank `m` from `rank_eq`)
  and pull the finite nonzero `ℓ` out of the infimum (`ENNReal.iInf_mul_of_ne`, the right-hand
  form of `ENNReal.mul_iInf_of_ne`);
* normalizations: `r^{-(m+4)} ℓ = (ℓ/r²) r^{-(m+2)}`.

The hypotheses `IsFiniteMeasureOnCompacts ν`, `ν.InnerRegular` and `r ≤ 2` are not used;
`t ∈ [-1,1]` and `0 < r` give `ℓ ≠ 0`. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The vertical cost is spatial: the parabolic distance from `point y s` to `V × ℝ` is the
Euclidean distance from `y` to `V`, at every time `s`. -/
private theorem e2_spb_infEDist_vertical {n k : ℕ} (L : VerticalModel n k) (y : Spatial n)
    (s : ℝ) : Metric.infEDist (point y s) L.toSet = Metric.infEDist y L.spatial.toSet := by
  refine le_antisymm (Metric.le_infEDist.mpr fun u hu => ?_)
    (Metric.le_infEDist.mpr fun w hw => ?_)
  · calc Metric.infEDist (point y s) L.toSet ≤ edist (point y s) (point u s) :=
          Metric.infEDist_le_edist_of_mem ((L.mem_toSet_point u s).mpr hu)
      _ = edist y u := by
        rw [edist_dist, edist_dist, dist_point, sub_self, abs_zero, Real.sqrt_zero,
          max_eq_left (norm_nonneg _), dist_eq_norm]
  · calc Metric.infEDist y L.spatial.toSet ≤ edist y w.1 := Metric.infEDist_le_edist_of_mem hw
      _ ≤ edist (point y s) w := by
        rw [Prod.edist_eq]
        exact le_max_left _ _

/-- The parabolic ball pulls back under `q ↦ point q.1 q.2` to the rectangle
`B(x,r) × (t-r², t+r²)`. -/
private theorem e2_spb_preimage_ball {n : ℕ} (x : Spatial n) (t r : ℝ) (hr : 0 < r) :
    (fun q : Spatial n × ℝ => point q.1 q.2) ⁻¹' Metric.ball (point x t) r =
      Metric.ball x r ×ˢ Ioo (t - r ^ 2) (t + r ^ 2) := by
  ext ⟨y, s⟩
  show point y s ∈ Metric.ball (point x t) r ↔
    y ∈ Metric.ball x r ∧ s ∈ Ioo (t - r ^ 2) (t + r ^ 2)
  rw [mem_ball_point x y t s r hr, Metric.mem_ball, dist_eq_norm, mem_Ioo, abs_sub_lt_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith, by linarith⟩

/-- Tonelli for a fixed vertical model: the fitting integral of the stationary source is the
spatial fitting integral times the length `ℓ` of the time window. -/
private theorem e2_spb_fit {n k : ℕ} (ν : Measure (Spatial n)) (L : VerticalModel n k)
    (x : Spatial n) (t r : ℝ) (hr : 0 < r) :
    fit (T := .vertical) (e2_stationarySource ν) L (point x t) r =
      (∫⁻ y in Metric.ball x r, Metric.infEDist y L.spatial.toSet ^ 2 ∂ν) *
        volume (Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1) := by
  have hc : ∀ (y : Spatial n) (s : ℝ),
      modelCost (T := .vertical) L (point y s) = Metric.infEDist y L.spatial.toSet ^ 2 := by
    intro y s
    rw [← e2_spb_infEDist_vertical L y s]
    rfl
  have hG : Measurable fun y : Spatial n => Metric.infEDist y L.spatial.toSet ^ 2 :=
    measurable_infEDist.pow_const 2
  have hpt : ∀ q : Spatial n × ℝ,
      (Metric.ball x r ×ˢ Ioo (t - r ^ 2) (t + r ^ 2)).indicator
          (fun q : Spatial n × ℝ => modelCost (T := .vertical) L (point q.1 q.2)) q =
        (Metric.ball x r).indicator (fun y => Metric.infEDist y L.spatial.toSet ^ 2) q.1 *
          (Ioo (t - r ^ 2) (t + r ^ 2)).indicator 1 q.2 := by
    rintro ⟨y, s⟩
    by_cases hy : y ∈ Metric.ball x r <;> by_cases hs : s ∈ Ioo (t - r ^ 2) (t + r ^ 2) <;>
      simp [hy, hs, hc]
  unfold fit
  rw [setLIntegral_map measurableSet_ball (measurable_modelCost (T := .vertical) L)
      measurable_point, e2_spb_preimage_ball x t r hr,
    ← lintegral_indicator (measurableSet_ball.prod measurableSet_Ioo), lintegral_congr hpt,
    lintegral_prod_mul (hG.indicator measurableSet_ball).aemeasurable
      ((measurable_one.indicator measurableSet_Ioo).aemeasurable),
    lintegral_indicator measurableSet_ball, lintegral_indicator_one measurableSet_Ioo,
    Measure.restrict_apply measurableSet_Ioo]

/-- For `t ∈ [-1,1]` and `0 < r` the time window has positive length. -/
private theorem e2_spb_window_ne_zero {t r : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (hr : 0 < r) :
    volume (Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1) ≠ 0 := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hsub : Ioo (max (t - r ^ 2) (-1)) (min (t + r ^ 2) 1) ⊆
      Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1 := by
    rintro y ⟨h1, h2⟩
    rw [max_lt_iff] at h1
    rw [lt_min_iff] at h2
    exact ⟨⟨h1.1, h2.1⟩, h1.2.le, h2.2.le⟩
  refine (lt_of_lt_of_le ?_ (measure_mono hsub)).ne'
  rw [Real.volume_Ioo, ENNReal.ofReal_pos, sub_pos, max_lt_iff, lt_min_iff, lt_min_iff]
  exact ⟨⟨by linarith, by linarith [ht.2]⟩, by linarith [ht.1], by norm_num⟩

/-- The time window has finite length. -/
private theorem e2_spb_window_ne_top (t r : ℝ) :
    volume (Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1) ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    (measure_mono inter_subset_left)

/-- Reindexing: the vertical fitting infimum is the spatial `m`-plane infimum times `ℓ`. -/
private theorem e2_spb_iInf {n m : ℕ} (ν : Measure (Spatial n)) (x : Spatial n) {t r : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (hr : 0 < r) :
    ⨅ L : Models n (m + 2) .vertical, fit (e2_stationarySource ν) L (point x t) r =
      (⨅ U : AffineSpatialPlane n m,
          ∫⁻ y in Metric.ball x r, Metric.infEDist y U.toSet ^ 2 ∂ν) *
        volume (Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1) := by
  rw [ENNReal.iInf_mul_of_ne (e2_spb_window_ne_zero ht hr) (e2_spb_window_ne_top t r)]
  refine le_antisymm (le_iInf fun U => ?_) (le_iInf fun L => ?_)
  · exact (iInf_le _ (⟨m, by omega, rfl, U⟩ : VerticalModel n (m + 2))).trans_eq
      (e2_spb_fit ν _ x t r hr)
  · change VerticalModel n (m + 2) at L
    obtain ⟨k', h2, hk', V⟩ := L
    obtain rfl : k' = m := by omega
    exact (iInf_le _ V).trans_eq (e2_spb_fit ν ⟨k', h2, hk', V⟩ x t r hr).symm

/-- The vertical identity `β²_{V,μ,m+2}((x,t),r) = (ℓ/r²) b^E_{2,ν,m}(x,r)` for the
stationary product, under the hypotheses of `StationaryProductStatement`. -/
theorem e2_stationary_vertical_proof : E2StationaryVerticalStatement := by
  intro n _ m _ ν _ _ x t r ht hr _
  rw [betaSq_of_pos _ _ _ _ hr, e2_spb_iInf ν x ht hr]
  unfold euclideanBetaPow
  rw [ite_eq_left hr]
  simp only [ENNReal.rpow_two]
  have hcast : ((m : ℝ) + 2) = ((m + 2 : ℕ) : ℝ) := by norm_cast
  rw [hcast, ENNReal.rpow_natCast, div_eq_mul_inv, ENNReal.inv_pow]
  generalize (ENNReal.ofReal r)⁻¹ = b
  ring

end ParabolicRectifiability.Examples
