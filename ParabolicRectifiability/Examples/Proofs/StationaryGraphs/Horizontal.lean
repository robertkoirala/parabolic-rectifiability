import ParabolicRectifiability.Examples.Proofs.Reductions.ReductionStatements

/-! # The horizontal lower bound for the stationary product

Stated as an implication over the interval-length statement `E2StationaryLengthStatement`. For
`μ = ν ⊗ L¹⌊[-1,1]`, `t ∈ [-1,1]` and `0 < r ≤ 2`,
`(1/16) b^E_{2,ν,m}(x,r) ≤ β²_{H,μ,m+2}((x,t),r)`.

Route:
* every horizontal model `L = U × {τ}` has `modelCost L (y,s) ≥ |s - τ|`
  (`HorizontalModel.modelCost_point`);
* the parabolic ball pulls back to `B(x,r) × (t-r², t+r²)` (`mem_ball_point`), so by Tonelli
  (`lintegral_prod_mul`) `fit L ≥ ν(B(x,r)) ∫_J |s - τ| ds` with
  `J = (t-r², t+r²) ∩ [-1,1]`;
* `∫_J |s - τ| ds ≥ c ℓ - c²` for every `c ≥ 0`, `ℓ = |J|` (pointwise `c ≤ |s-τ| + (c-|s-τ|)⁺`
  and the tent integral `∫ (c - |u|)⁺ du = c²`); at `c = r²/4` with `ℓ ≥ r²/2` (the length
  statement, the hypothesis) this is `≥ r⁴/16`, the case `c = ℓ/2` of `∫_J |s - τ| ≥ ℓ²/4`;
* an `m`-plane through `x` (`AffineSpatialPlane.exists_mem_of_nonempty`, `m ≤ n`) gives
  `b^E ≤ r^{-m} ν(B(x,r))`;
* `le_iInf` over the horizontal family needs no case split: an empty family gives `⊤`. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The tent integral: `∫ (c - |s - τ|)⁺ ds = c²` for `c ≥ 0`. -/
private theorem e2_spc_tent (τ c : ℝ) (hc : 0 ≤ c) :
    ∫⁻ s, ENNReal.ofReal (c - |s - τ|) = ENNReal.ofReal (c ^ 2) := by
  have htr := lintegral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun u : ℝ => ENNReal.ofReal (c - |u|)) τ
  rw [htr]
  have hsupp : (Function.support fun u : ℝ => ENNReal.ofReal (c - |u|)) ⊆ Ioc (-c) c := by
    intro u hu
    rw [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos] at hu
    obtain ⟨h1, h2⟩ := abs_lt.mp hu
    exact ⟨h1, h2.le⟩
  rw [← setLIntegral_eq_of_support_subset hsupp]
  have hcont : Continuous fun u : ℝ => c - |u| := by fun_prop
  have hint : Integrable (fun u : ℝ => c - |u|) (volume.restrict (Ioc (-c) c)) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (-c) c)] fun u : ℝ => c - |u| :=
    (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun u hu => sub_nonneg.mpr (abs_le.mpr ⟨hu.1.le, hu.2⟩))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← intervalIntegral.integral_of_le (by linarith : -c ≤ c),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have h1 : ∫ u in -c..0, (c - |u|) = ∫ u in -c..0, (c + u) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith : -c ≤ 0)] at hu
    rw [abs_of_nonpos hu.2]
    ring
  have h2 : ∫ u in (0 : ℝ)..c, (c - |u|) = ∫ u in (0 : ℝ)..c, (c - u) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hc] at hu
    rw [abs_of_nonneg hu.1]
  rw [h1, h2, intervalIntegral.integral_add intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id,
    intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
  congr 1
  ring

/-- The time integral over any set `J`: `c |J| ≤ ∫_J |s - τ| ds + c²` for `c ≥ 0`. -/
private theorem e2_spc_time (J : Set ℝ) (τ c : ℝ) (hc : 0 ≤ c) :
    ENNReal.ofReal c * volume J ≤
      (∫⁻ s in J, ENNReal.ofReal |s - τ|) + ENNReal.ofReal (c ^ 2) := by
  have hmeas : Measurable fun s : ℝ => ENNReal.ofReal |s - τ| :=
    (by fun_prop : Continuous fun s : ℝ => |s - τ|).measurable.ennreal_ofReal
  calc ENNReal.ofReal c * volume J = ∫⁻ _ in J, ENNReal.ofReal c := (setLIntegral_const J _).symm
    _ ≤ ∫⁻ s in J, (ENNReal.ofReal |s - τ| + ENNReal.ofReal (c - |s - τ|)) := by
      refine lintegral_mono fun s => ?_
      calc ENNReal.ofReal c = ENNReal.ofReal (|s - τ| + (c - |s - τ|)) := by congr 1; ring
        _ ≤ _ := ENNReal.ofReal_add_le
    _ = (∫⁻ s in J, ENNReal.ofReal |s - τ|) + ∫⁻ s in J, ENNReal.ofReal (c - |s - τ|) :=
      lintegral_add_left hmeas _
    _ ≤ (∫⁻ s in J, ENNReal.ofReal |s - τ|) + ENNReal.ofReal (c ^ 2) := by
      gcongr
      exact (setLIntegral_le_lintegral J _).trans (e2_spc_tent τ c hc).le

/-- With `|J| ≥ r²/2`: `∫_J |s - τ| ds ≥ r⁴/16` (the case `c = r²/4`). -/
private theorem e2_spc_time_lower (J : Set ℝ) (τ r : ℝ)
    (hJ : ENNReal.ofReal (r ^ 2 / 2) ≤ volume J) :
    ENNReal.ofReal (r ^ 4 / 16) ≤ ∫⁻ s in J, ENNReal.ofReal |s - τ| := by
  have hc : (0 : ℝ) ≤ r ^ 2 / 4 := by positivity
  have h := e2_spc_time J τ (r ^ 2 / 4) hc
  have hsplit : ENNReal.ofReal (r ^ 4 / 16) + ENNReal.ofReal ((r ^ 2 / 4) ^ 2) =
      ENNReal.ofReal (r ^ 2 / 4) * ENNReal.ofReal (r ^ 2 / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hc]
    congr 1
    ring
  refine ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal ((r ^ 2 / 4) ^ 2))
    ENNReal.ofReal_ne_top ?_
  rw [hsplit]
  exact (mul_le_mul_right hJ _).trans h

/-- The parabolic ball pulls back under `(y, s) ↦ (y, s)` to `B(x,r) × (t-r², t+r²)`. -/
private theorem e2_spc_preimage_ball {n : ℕ} (x : Spatial n) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    (fun q : Spatial n × ℝ => point q.1 q.2) ⁻¹' Metric.ball (point x t) r =
      Metric.ball x r ×ˢ Ioo (t - r ^ 2) (t + r ^ 2) := by
  ext ⟨y, s⟩
  rw [mem_preimage, mem_ball_point x y t s r hr, mem_prod, Metric.mem_ball, dist_eq_norm,
    mem_Ioo, abs_lt]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith, by linarith⟩

/-- Tonelli for one horizontal model:
`ν(B(x,r)) ∫_J |s - τ| ds ≤ fit_μ(L, (x,t), r)`, `J = (t-r², t+r²) ∩ [-1,1]`. -/
private theorem e2_spc_fit_ge {n k : ℕ} (ν : Measure (Spatial n)) [SFinite ν]
    (L : HorizontalModel n k) (x : Spatial n) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    ν (Metric.ball x r) *
        ∫⁻ s in Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1, ENNReal.ofReal |s - L.time| ≤
      fit (T := .horizontal) (e2_stationarySource ν) L (point x t) r := by
  have hg : Measurable fun s : ℝ => ENNReal.ofReal |s - L.time| :=
    (by fun_prop : Continuous fun s : ℝ => |s - L.time|).measurable.ennreal_ofReal
  unfold fit
  rw [setLIntegral_map measurableSet_ball (measurable_modelCost (T := .horizontal) L)
    measurable_point, e2_spc_preimage_ball x t hr]
  calc ν (Metric.ball x r) *
        ∫⁻ s in Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1, ENNReal.ofReal |s - L.time|
      = (∫⁻ _ : Spatial n, 1 ∂ν.restrict (Metric.ball x r)) *
          ∫⁻ s, ENNReal.ofReal |s - L.time|
            ∂(volume.restrict (Icc (-1 : ℝ) 1)).restrict (Ioo (t - r ^ 2) (t + r ^ 2)) := by
        rw [Measure.restrict_restrict measurableSet_Ioo, lintegral_one, Measure.restrict_apply_univ]
    _ = ∫⁻ q : Spatial n × ℝ, 1 * ENNReal.ofReal |q.2 - L.time|
          ∂((ν.restrict (Metric.ball x r)).prod
            ((volume.restrict (Icc (-1 : ℝ) 1)).restrict (Ioo (t - r ^ 2) (t + r ^ 2)))) :=
        (lintegral_prod_mul aemeasurable_const hg.aemeasurable).symm
    _ ≤ ∫⁻ q in Metric.ball x r ×ˢ Ioo (t - r ^ 2) (t + r ^ 2),
          modelCost (T := .horizontal) L (point q.1 q.2)
          ∂(ν.prod (volume.restrict (Icc (-1 : ℝ) 1))) := by
        rw [Measure.prod_restrict]
        refine lintegral_mono fun q => ?_
        rw [one_mul, HorizontalModel.modelCost_point]
        exact ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- The horizontal fitting infimum is at least `ν(B(x,r)) r⁴/16`; an empty horizontal family
gives `⊤`, so `le_iInf` covers it. -/
private theorem e2_spc_iInf_ge {n k : ℕ} (ν : Measure (Spatial n)) [SFinite ν]
    (x : Spatial n) (t : ℝ) {r : ℝ} (hr : 0 < r)
    (hℓ : ENNReal.ofReal (r ^ 2 / 2) ≤
      volume (Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1)) :
    ν (Metric.ball x r) * ENNReal.ofReal (r ^ 4 / 16) ≤
      ⨅ L : Models n k .horizontal, fit (e2_stationarySource ν) L (point x t) r := by
  refine le_iInf fun L => ?_
  change HorizontalModel n k at L
  exact (mul_le_mul_right (e2_spc_time_lower _ L.time r hℓ) _).trans
    (e2_spc_fit_ge ν L x t hr)

/-- A plane through `x` bounds the Euclidean beta: `b^E_{2,ν,m}(x,r) ≤ r^{-m} ν(B(x,r))`. -/
private theorem e2_spc_euclidean_le {n m : ℕ} (hm : m ≤ n) (ν : Measure (Spatial n))
    (x : Spatial n) {r : ℝ} (hr : 0 < r) :
    euclideanBetaPow ν m 2 x r ≤ (ENNReal.ofReal r)⁻¹ ^ m * ν (Metric.ball x r) := by
  have : Nonempty (AffineSpatialPlane n m) := AffineSpatialPlane.nonempty_iff.mpr hm
  obtain ⟨U, hU⟩ := AffineSpatialPlane.exists_mem_of_nonempty (m := m) x
  have hbound : ∫⁻ y in Metric.ball x r, Metric.infEDist y U.toSet ^ (2 : ℝ) ∂ν ≤
      ENNReal.ofReal r ^ 2 * ν (Metric.ball x r) := by
    calc ∫⁻ y in Metric.ball x r, Metric.infEDist y U.toSet ^ (2 : ℝ) ∂ν
        ≤ ∫⁻ _ in Metric.ball x r, ENNReal.ofReal r ^ 2 ∂ν := by
          refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
          rw [ENNReal.rpow_two]
          refine pow_le_pow_left' ((Metric.infEDist_le_edist_of_mem hU).trans ?_) 2
          rw [edist_dist]
          exact ENNReal.ofReal_le_ofReal (Metric.mem_ball.mp hy).le
      _ = ENNReal.ofReal r ^ 2 * ν (Metric.ball x r) := setLIntegral_const _ _
  unfold euclideanBetaPow
  rw [ite_eq_left hr]
  calc (ENNReal.ofReal r)⁻¹ ^ ((m : ℝ) + 2) *
        ⨅ U : AffineSpatialPlane n m,
          ∫⁻ y in Metric.ball x r, Metric.infEDist y U.toSet ^ (2 : ℝ) ∂ν
      ≤ (ENNReal.ofReal r)⁻¹ ^ ((m : ℝ) + 2) * (ENNReal.ofReal r ^ 2 * ν (Metric.ball x r)) :=
        mul_le_mul_right ((iInf_le _ U).trans hbound) _
    _ = (ENNReal.ofReal r)⁻¹ ^ m * ν (Metric.ball x r) := by
        rw [show ((m : ℝ) + 2) = ((m + 2 : ℕ) : ℝ) by push_cast; ring, ENNReal.rpow_natCast]
        exact inv_radius_pow_mul_sq hr m _

/-- The horizontal lower bound `(1/16) b^E_{2,ν,m}(x,r) ≤ β²_{H,μ,m+2}((x,t),r)` for
the stationary product, from the interval-length statement `E2StationaryLengthStatement`. -/
theorem e2_stationary_horizontal_proof : E2StationaryHorizontalStatement := by
  intro hSPa n _hn m hm ν hν _hνr x t r ht hr hr2
  have := hν
  have hℓ := (hSPa t r ht hr hr2).1
  rw [betaSq_of_pos _ _ _ _ hr]
  have e : ENNReal.ofReal (r ^ 4 / 16) = ENNReal.ofReal r ^ 2 *
      (ENNReal.ofReal r ^ 2 * ENNReal.ofReal (1 / 16)) := by
    rw [← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc ENNReal.ofReal (1 / 16) * euclideanBetaPow ν m 2 x r
      ≤ ENNReal.ofReal (1 / 16) * ((ENNReal.ofReal r)⁻¹ ^ m * ν (Metric.ball x r)) :=
        mul_le_mul_right (e2_spc_euclidean_le (by omega) ν x hr) _
    _ = (ENNReal.ofReal r)⁻¹ ^ (m + 2 + 2) * (ENNReal.ofReal r ^ 2 *
          (ENNReal.ofReal r ^ 2 * (ENNReal.ofReal (1 / 16) * ν (Metric.ball x r)))) := by
        rw [inv_radius_pow_mul_sq hr (m + 2), inv_radius_pow_mul_sq hr m]
        ring
    _ = (ENNReal.ofReal r)⁻¹ ^ (m + 2 + 2) *
          (ν (Metric.ball x r) * ENNReal.ofReal (r ^ 4 / 16)) := by
        rw [e]
        ring
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ (m + 2 + 2) *
          ⨅ L : Models n (m + 2) .horizontal,
            fit (e2_stationarySource ν) L (point x t) r :=
        mul_le_mul_right (e2_spc_iInf_ge ν x t hr hℓ) _

end ParabolicRectifiability.Examples
