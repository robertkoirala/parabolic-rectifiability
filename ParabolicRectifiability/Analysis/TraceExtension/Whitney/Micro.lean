import ParabolicRectifiability.Analysis.TraceExtension.Whitney.MacroTransfer
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Lipschitz

/-! # Microscopic affine error of the Whitney filling

Let `δ = d_P(·,F₀)` and suppose `0 < s`, `2s < δ(y)`.
Every point of `P(y,s)` has distance `> δ(y)/2` from `F₀`, so the derivative bounds of
`whitneyFilling_deriv_bounds_proof` (`|∇²_u F| + |∂_t F| ≤ M/δ`) hold there with `M/δ(y)` replaced by `2M/δ(y)`.
For the spatial affine competitor `A(u) = F(y) + ∇_u F(y)(u - u_y)`:

* the time variation along `{q_u} × [t_y, t_q]` is at most `(2M/δ) s²`;
* the spatial first-order remainder along `[u_y, q_u] × {t_y}` is at most
  `(2M s/δ) s`, by the mean value inequality applied first to `∇_u F` and then to
  `F - ∇_u F(y)`.

Hence `|F - A| ≤ 4 M (s/δ) s` on `P(y,s)` and
`κ_F(y,s)^2 ≤ 2 ω_m · 16 M² (s/δ)² = 32 ω_m M² (s/δ)²`.

`whitneyFilling_affineErrorSq_le_micro_proof` takes the derivative-bound statement of
`whitneyFilling_deriv_bounds_proof` as a hypothesis, with `M = C L`.
`whitneyFilling_micro_carleson_le_proof` integrates it: in the microscopic range
`s < δ/2`, `∫ (s/δ)² ds/s ≤ 1/4`, and the ball has volume `2 ω_m R^k`; it takes the
pointwise microscopic bound as its hypothesis, and the composite from the derivative
bounds is `whitneyFilling_micro_carleson_le_of_derivBounds`.
When `δ(y) ≤ 0` the microscopic range is empty.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

universe u v

/-- The ball volume `2 ω_m R^k` as an `ofReal`. -/
theorem two_mul_omega_mul_ofReal_pow (m : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    2 * omega m * ENNReal.ofReal R ^ (m + 2) =
      ENNReal.ofReal (2 * (omega m).toReal * R ^ (m + 2)) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_toReal (omega_lt_top m).ne, ENNReal.ofReal_pow hR]

/-- Scale integral over the microscopic range: a bound `c (s/δ)²` for `2s < δ`
integrates against `ds/s` over `0 < s < R`, `2s < δ` to at most `c/4`. -/
theorem setLIntegral_microRange_le {f : ℝ → ℝ≥0∞} {c δ : ℝ} (R : ℝ) (hc : 0 ≤ c)
    (hf : ∀ s, 0 < s → 2 * s < δ → f s ≤ ENNReal.ofReal (c * (s / δ) ^ 2)) :
    ∫⁻ s in Ioo 0 R ∩ {s | 2 * s < δ}, f s ∂scaleMeasure ≤ ENNReal.ofReal (c / 4) := by
  have hSmeas : MeasurableSet (Ioo 0 R ∩ {s : ℝ | 2 * s < δ}) :=
    measurableSet_Ioo.inter (measurableSet_lt (measurable_const.mul measurable_id) measurable_const)
  by_cases hδ : 0 < δ
  · have hk : 0 ≤ c / (2 * δ) := div_nonneg hc (by linarith)
    have hpt : ∀ s ∈ Ioo 0 R ∩ {s : ℝ | 2 * s < δ}, f s ≤ ENNReal.ofReal (s * (c / (2 * δ))) := by
      intro s hs
      have hs0 : 0 < s := hs.1.1
      have hsδ : 2 * s < δ := hs.2
      have hx0 : 0 ≤ s / δ := div_nonneg hs0.le hδ.le
      have hx : s / δ ≤ 1 / 2 := by
        rw [div_le_iff₀ hδ]
        linarith
      refine (hf s hs0 hsδ).trans (ENNReal.ofReal_le_ofReal ?_)
      calc
        c * (s / δ) ^ 2 = c * ((s / δ) * (s / δ)) := by ring
        _ ≤ c * ((s / δ) * (1 / 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx hx0) hc
        _ = s * (c / (2 * δ)) := by ring
    have hsub : Ioo 0 R ∩ {s : ℝ | 2 * s < δ} ⊆ Ioo 0 (δ / 2) := fun s hs => by
      have h1 : 0 < s := hs.1.1
      have h2 : 2 * s < δ := hs.2
      exact ⟨h1, by linarith⟩
    calc
      ∫⁻ s in Ioo 0 R ∩ {s | 2 * s < δ}, f s ∂scaleMeasure ≤
          ∫⁻ s in Ioo 0 R ∩ {s | 2 * s < δ}, ENNReal.ofReal (s * (c / (2 * δ))) ∂scaleMeasure :=
        setLIntegral_mono' hSmeas hpt
      _ = ∫⁻ s in Ioo 0 R ∩ {s | 2 * s < δ},
            ENNReal.ofReal (1 / s) * ENNReal.ofReal (s * (c / (2 * δ))) ∂volume :=
        setLIntegral_scaleMeasure hSmeas (fun s hs => hs.1.1) _
          ((measurable_id.mul_const _).ennreal_ofReal)
      _ = ∫⁻ _ in Ioo 0 R ∩ {s | 2 * s < δ}, ENNReal.ofReal (c / (2 * δ)) ∂volume := by
        refine setLIntegral_congr_fun hSmeas fun s hs => ?_
        rw [← ENNReal.ofReal_mul (one_div_pos.mpr hs.1.1).le, ← mul_assoc,
          one_div_mul_cancel hs.1.1.ne', one_mul]
      _ = ENNReal.ofReal (c / (2 * δ)) * volume (Ioo 0 R ∩ {s : ℝ | 2 * s < δ}) :=
        setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (c / (2 * δ)) * volume (Ioo (0 : ℝ) (δ / 2)) :=
        mul_le_mul_right (measure_mono hsub) _
      _ = ENNReal.ofReal (c / 4) := by
        rw [Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul hk, div_mul_div_comm,
          show (2 : ℝ) * δ * 2 = 4 * δ by ring, mul_div_mul_right c 4 hδ.ne']
  · have hS : Ioo 0 R ∩ {s : ℝ | 2 * s < δ} = ∅ := by
      refine eq_empty_of_forall_notMem fun s hs => hδ ?_
      have h1 : 0 < s := hs.1.1
      have h2 : 2 * s < δ := hs.2
      linarith
    rw [hS, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le

/-- Microscopic affine error from parabolic derivative bounds: if `F` is `C²` off the
closed set `F₀` with `|∇²_u F|, |∂_t F| ≤ M/δ`, then for `0 < s`, `2s < δ(y)`,
`κ_F(y,s)^2 ≤ 32 ω_m M² (s/δ(y))²`. -/
theorem affineErrorSq_le_of_parabolicDerivBounds {m : ℕ} {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] {F₀ : Set (Space m)} (hF₀ : IsClosed F₀) {F : Space m → Y}
    {M : ℝ} (hM : 0 ≤ M)
    (hCD : ContDiffOn ℝ 2 (fun y : Coordinates m => F (point y.1 y.2))
      {y | point y.1 y.2 ∉ F₀})
    (h2 : ∀ q ∉ F₀, ‖fderiv ℝ (fun v => fderiv ℝ (fun w => F (point w q.2.val)) v) q.1‖ ≤
      M / Metric.infDist q F₀)
    (ht : ∀ q ∉ F₀, ‖deriv (fun t => F (point q.1 t)) q.2.val‖ ≤ M / Metric.infDist q F₀)
    {y : Space m} {s : ℝ} (hs : 0 < s) (hy : 2 * s < Metric.infDist y F₀) :
    affineErrorSq (parabolicVolume m) F y s ≤
      ENNReal.ofReal (32 * (omega m).toReal * M ^ 2 * (s / Metric.infDist y F₀) ^ 2) := by
  obtain ⟨δ, hδd⟩ : ∃ x : ℝ, x = Metric.infDist y F₀ := ⟨_, rfl⟩
  rw [← hδd] at hy ⊢
  have hδ : 0 < δ := by linarith
  obtain ⟨u₀, t₀, rfl⟩ : ∃ (u₀ : Spatial m) (t₀ : ℝ), point u₀ t₀ = y := ⟨y.1, y.2.val, rfl⟩
  have hU : IsOpen {z : Coordinates m | point z.1 z.2 ∉ F₀} :=
    hF₀.isOpen_compl.preimage continuous_point
  -- points of the ball stay away from `F₀`
  have hfar : ∀ q ∈ Metric.ball (point u₀ t₀) s, δ / 2 < Metric.infDist q F₀ := by
    intro q hq
    have h1 : Metric.infDist (point u₀ t₀) F₀ ≤ Metric.infDist q F₀ + dist (point u₀ t₀) q :=
      Metric.infDist_le_infDist_add_dist
    have h2 : dist (point u₀ t₀) q < s := by
      rw [dist_comm]
      exact Metric.mem_ball.mp hq
    rw [← hδd] at h1
    linarith
  have hoff : ∀ q ∈ Metric.ball (point u₀ t₀) s, q ∉ F₀ := fun q hq hqF => by
    have h := hfar q hq
    rw [Metric.infDist_zero_of_mem hqF] at h
    linarith
  have hbd : ∀ q ∈ Metric.ball (point u₀ t₀) s, M / Metric.infDist q F₀ ≤ 2 * M / δ := by
    intro q hq
    calc
      M / Metric.infDist q F₀ ≤ M / (δ / 2) :=
        div_le_div_of_nonneg_left hM (by linarith) (hfar q hq).le
      _ = 2 * M / δ := by ring
  have hmem : ∀ (v : Spatial m) (t : ℝ), ‖v - u₀‖ < s → |t - t₀| < s ^ 2 →
      point v t ∈ Metric.ball (point u₀ t₀) s := fun v t h1 h2 =>
    (mem_ball_point u₀ v t₀ t s hs).mpr ⟨h1, h2⟩
  have hdiffΦ : ∀ z : Coordinates m, point z.1 z.2 ∉ F₀ →
      DifferentiableAt ℝ (fun y : Coordinates m => F (point y.1 y.2)) z := fun z hz =>
    (hCD.differentiableOn two_ne_zero).differentiableAt (hU.mem_nhds hz)
  -- the spatial slice at time `t₀`
  have hV : IsOpen {v : Spatial m | point v t₀ ∉ F₀} :=
    hU.preimage (continuous_id.prodMk (continuous_const : Continuous fun _ : Spatial m => t₀))
  have hf2' := hCD.comp
    ((contDiff_id.prodMk (contDiff_const (c := t₀))).contDiffOn
      (s := {v : Spatial m | point v t₀ ∉ F₀})) fun v hv => hv
  have hf2 : ContDiffOn ℝ 2 (fun v => F (point v t₀)) {v : Spatial m | point v t₀ ∉ F₀} :=
    hf2'
  have hfdiff : ∀ v ∈ {v : Spatial m | point v t₀ ∉ F₀},
      DifferentiableAt ℝ (fun w => F (point w t₀)) v := fun v hv =>
    (hf2.differentiableOn two_ne_zero).differentiableAt (hV.mem_nhds hv)
  have hf'diff : ∀ v ∈ {v : Spatial m | point v t₀ ∉ F₀},
      DifferentiableAt ℝ (fun v => fderiv ℝ (fun w => F (point w t₀)) v) v := fun v hv =>
    ((hf2.fderiv_of_isOpen hV one_add_one_eq_two.le).differentiableOn one_ne_zero).differentiableAt
      (hV.mem_nhds hv)
  have hball_pt : ∀ v ∈ Metric.ball u₀ s, point v t₀ ∈ Metric.ball (point u₀ t₀) s := fun v hv =>
    hmem v t₀ (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hv) (by
      rw [sub_self, abs_zero]
      exact pow_pos hs 2)
  have hBV : Metric.ball u₀ s ⊆ {v : Spatial m | point v t₀ ∉ F₀} := fun v hv =>
    hoff _ (hball_pt v hv)
  -- first derivative of the slice is Lipschitz on the spatial ball
  set B : Spatial m →L[ℝ] Y := fderiv ℝ (fun w => F (point w t₀)) u₀ with hB
  have hf'lip : ∀ v ∈ Metric.ball u₀ s,
      ‖fderiv ℝ (fun w => F (point w t₀)) v - B‖ ≤ 2 * M / δ * ‖v - u₀‖ := by
    intro v hv
    refine (convex_ball u₀ s).norm_image_sub_le_of_norm_fderiv_le
      (f := fun v => fderiv ℝ (fun w => F (point w t₀)) v)
      (fun w hw => hf'diff w (hBV hw)) (fun w hw => ?_) (Metric.mem_ball_self hs) hv
    exact (h2 (point w t₀) (hoff _ (hball_pt w hw))).trans (hbd _ (hball_pt w hw))
  -- spatial first-order remainder
  have hspace : ∀ x ∈ Metric.ball u₀ s,
      ‖(F (point x t₀) - B x) - (F (point u₀ t₀) - B u₀)‖ ≤ 2 * M / δ * s * ‖x - u₀‖ := by
    intro x hx
    have hderiv : ∀ v ∈ Metric.ball u₀ s, HasFDerivAt (fun w => F (point w t₀) - B w)
        (fderiv ℝ (fun w => F (point w t₀)) v - B) v := fun v hv =>
      ((hfdiff v (hBV hv)).hasFDerivAt).sub B.hasFDerivAt
    refine (convex_ball u₀ s).norm_image_sub_le_of_norm_fderiv_le
      (f := fun w => F (point w t₀) - B w) (fun v hv => (hderiv v hv).differentiableAt)
      (fun v hv => ?_) (Metric.mem_ball_self hs) hx
    rw [(hderiv v hv).fderiv]
    have hvu : ‖v - u₀‖ ≤ s := by
      rw [← dist_eq_norm]
      exact (Metric.mem_ball.mp hv).le
    calc
      ‖fderiv ℝ (fun w => F (point w t₀)) v - B‖ ≤ 2 * M / δ * ‖v - u₀‖ := hf'lip v hv
      _ ≤ 2 * M / δ * s :=
        mul_le_mul_of_nonneg_left hvu (div_nonneg (by linarith) hδ.le)
  -- time variation
  have htime : ∀ q ∈ Metric.ball (point u₀ t₀) s,
      ‖F (point q.1 q.2.val) - F (point q.1 t₀)‖ ≤ 2 * M / δ * |q.2.val - t₀| := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := (mem_ball_point u₀ q.1 t₀ q.2.val s hs).mp hq
    have hI : ∀ τ ∈ Ioo (t₀ - s ^ 2) (t₀ + s ^ 2),
        point q.1 τ ∈ Metric.ball (point u₀ t₀) s := fun τ hτ => by
      refine hmem q.1 τ hq1 ?_
      rw [abs_lt]
      constructor <;> linarith [hτ.1, hτ.2]
    have hs2 : 0 < s ^ 2 := pow_pos hs 2
    have ht0 : t₀ ∈ Ioo (t₀ - s ^ 2) (t₀ + s ^ 2) := ⟨by linarith, by linarith⟩
    have htq : q.2.val ∈ Ioo (t₀ - s ^ 2) (t₀ + s ^ 2) := by
      rw [abs_lt] at hq2
      exact ⟨by linarith [hq2.1], by linarith [hq2.2]⟩
    have h := (convex_Ioo (t₀ - s ^ 2) (t₀ + s ^ 2)).norm_image_sub_le_of_norm_deriv_le
      (f := fun t => F (point q.1 t))
      (fun τ hτ => by
        have h' := differentiableAt_slice_time (hdiffΦ (q.1, τ) (hoff _ (hI τ hτ)))
        exact h')
      (fun τ hτ => (ht (point q.1 τ) (hoff _ (hI τ hτ))).trans (hbd _ (hI τ hτ))) ht0 htq
    rwa [Real.norm_eq_abs] at h
  -- pointwise bound for the affine competitor `A(q) = F(y) + B (q_u - u_y)`
  set X : ℝ := 4 * M * (s / δ) with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg (mul_nonneg (by norm_num) hM) (div_nonneg hs.le hδ.le)
  have hpt : ∀ q ∈ Metric.ball (point u₀ t₀) s,
      ‖F q - ((F (point u₀ t₀) - B u₀) + B q.1)‖ ≤ X * s := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := (mem_ball_point u₀ q.1 t₀ q.2.val s hs).mp hq
    have hx : q.1 ∈ Metric.ball u₀ s := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hq1
    have e : F q - ((F (point u₀ t₀) - B u₀) + B q.1) =
        (F (point q.1 q.2.val) - F (point q.1 t₀)) +
          ((F (point q.1 t₀) - B q.1) - (F (point u₀ t₀) - B u₀)) := by
      change F (point q.1 q.2.val) - ((F (point u₀ t₀) - B u₀) + B q.1) = _
      abel
    have hcoef : 0 ≤ 2 * M / δ := div_nonneg (by linarith) hδ.le
    rw [e]
    calc
      _ ≤ ‖F (point q.1 q.2.val) - F (point q.1 t₀)‖ +
          ‖(F (point q.1 t₀) - B q.1) - (F (point u₀ t₀) - B u₀)‖ := norm_add_le _ _
      _ ≤ 2 * M / δ * |q.2.val - t₀| + 2 * M / δ * s * ‖q.1 - u₀‖ :=
        add_le_add (htime q hq) (hspace q.1 hx)
      _ ≤ 2 * M / δ * s ^ 2 + 2 * M / δ * s * s :=
        add_le_add (mul_le_mul_of_nonneg_left hq2.le hcoef)
          (mul_le_mul_of_nonneg_left hq1.le (mul_nonneg hcoef hs.le))
      _ = X * s := by rw [hX]; ring
  -- integrate
  have hfit : affineFitIntegral (parabolicVolume m) F (F (point u₀ t₀) - B u₀) B
      (point u₀ t₀) s ≤
      ENNReal.ofReal (X ^ 2) * ENNReal.ofReal s ^ 2 *
        parabolicVolume m (Metric.ball (point u₀ t₀) s) := by
    unfold affineFitIntegral
    rw [← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_ball fun q hq => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow hs.le, ← ENNReal.ofReal_mul (sq_nonneg X),
      ← mul_pow, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hpt q hq) 2)
  have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hcancel : (ENNReal.ofReal s)⁻¹ ^ (m + 4) *
      (ENNReal.ofReal s ^ 2 * ENNReal.ofReal s ^ (m + 2)) = 1 := by
    rw [← pow_add, show 2 + (m + 2) = m + 4 by omega, ← mul_pow,
      ENNReal.inv_mul_cancel hs0 ENNReal.ofReal_ne_top, one_pow]
  have hω : (2 : ℝ≥0∞) * omega m = ENNReal.ofReal (2 * (omega m).toReal) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_toReal (omega_lt_top m).ne]
  calc
    affineErrorSq (parabolicVolume m) F (point u₀ t₀) s ≤
        (ENNReal.ofReal s)⁻¹ ^ (m + 4) *
          affineFitIntegral (parabolicVolume m) F (F (point u₀ t₀) - B u₀) B (point u₀ t₀) s := by
      rw [← baseDimension_spatial_add_two]
      exact affineErrorSq_le_fitIntegral _ _ _ hs _ _
    _ ≤ (ENNReal.ofReal s)⁻¹ ^ (m + 4) * (ENNReal.ofReal (X ^ 2) * ENNReal.ofReal s ^ 2 *
          parabolicVolume m (Metric.ball (point u₀ t₀) s)) := mul_le_mul_right hfit _
    _ = ENNReal.ofReal (X ^ 2) * (2 * omega m) *
          ((ENNReal.ofReal s)⁻¹ ^ (m + 4) * (ENNReal.ofReal s ^ 2 * ENNReal.ofReal s ^ (m + 2))) := by
      rw [parabolicVolume_ball _ s hs]
      ring
    _ = ENNReal.ofReal (32 * (omega m).toReal * M ^ 2 * (s / δ) ^ 2) := by
      rw [hcancel, mul_one, hω, ← ENNReal.ofReal_mul (sq_nonneg X)]
      congr 1
      rw [hX]
      ring

/-- **Microscopic error bound**, in implication form: the derivative-bound statement of
`whitneyFilling_deriv_bounds_proof` implies the microscopic error bound
`κ_F(y,s)^2 ≤ C L^2 (s / dist(y,F₀))^2` for `0 < s`, `2s < dist(y,F₀)`. -/
theorem whitneyFilling_affineErrorSq_le_micro_proof (m : ℕ) (D a H b K : ℝ) (N : ℕ)
    (hderiv : ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsClosed F₀ → F₀.Nonempty →
      ∀ (P : WhitneyPartition W H b K N) {Y : Type v} [NormedAddCommGroup Y]
        [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0), LipschitzOnWith L g W.nodeSet →
        ContDiffOn ℝ 2 (fun y : Coordinates m => whitneyFilling P.toWhitneyWeights g (point y.1 y.2))
            {y | point y.1 y.2 ∉ F₀} ∧
          ∀ q ∉ F₀,
            ‖fderiv ℝ (fun v => whitneyFilling P.toWhitneyWeights g (point v q.2.val)) q.1‖ ≤
                C * L ∧
              ‖fderiv ℝ (fun v => fderiv ℝ
                  (fun w => whitneyFilling P.toWhitneyWeights g (point w q.2.val)) v) q.1‖ ≤
                C * L / Metric.infDist q F₀ ∧
              ‖deriv (fun t => whitneyFilling P.toWhitneyWeights g (point q.1 t)) q.2.val‖ ≤
                C * L / Metric.infDist q F₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsClosed F₀ → F₀.Nonempty →
      ∀ (P : WhitneyPartition W H b K N) {Y : Type v} [NormedAddCommGroup Y]
        [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0), LipschitzOnWith L g W.nodeSet →
        ∀ (y : Space m) (s : ℝ), 0 < s → 2 * s < Metric.infDist y F₀ →
          affineErrorSq (parabolicVolume m) (whitneyFilling P.toWhitneyWeights g) y s ≤
            ENNReal.ofReal (C * (L : ℝ) ^ 2 * (s / Metric.infDist y F₀) ^ 2) := by
  obtain ⟨Cd, hCd0, hCd⟩ := hderiv
  refine ⟨32 * (omega m).toReal * Cd ^ 2,
    mul_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) (sq_nonneg _), ?_⟩
  intro ι _ F₀ W hF₀ hne P Y _ _ g L hg y s hs hy
  obtain ⟨hCD, hbd⟩ := hCd W hF₀ hne P g L hg
  have h := affineErrorSq_le_of_parabolicDerivBounds hF₀
    (mul_nonneg hCd0 (NNReal.coe_nonneg L)) hCD (fun q hq => (hbd q hq).2.1)
    (fun q hq => (hbd q hq).2.2) hs hy
  calc
    _ ≤ _ := h
    _ = ENNReal.ofReal (32 * (omega m).toReal * Cd ^ 2 * (L : ℝ) ^ 2 *
          (s / Metric.infDist y F₀) ^ 2) := by
      congr 1
      ring

/-- **Integrated microscopic bound**, in implication form: the pointwise microscopic bound
implies the integrated microscopic bound
`∫_{P(z,R)} ∫_{0<s<R, 2s<dist(y,F₀)} κ_F(y,s)^2 ds/s dy ≤ C L^2 R^k`. -/
theorem whitneyFilling_micro_carleson_le_proof (m : ℕ) (D a H b K : ℝ) (N : ℕ)
    (hmicro : ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsClosed F₀ → F₀.Nonempty →
      ∀ (P : WhitneyPartition W H b K N) {Y : Type v} [NormedAddCommGroup Y]
        [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0), LipschitzOnWith L g W.nodeSet →
        ∀ (y : Space m) (s : ℝ), 0 < s → 2 * s < Metric.infDist y F₀ →
          affineErrorSq (parabolicVolume m) (whitneyFilling P.toWhitneyWeights g) y s ≤
            ENNReal.ofReal (C * (L : ℝ) ^ 2 * (s / Metric.infDist y F₀) ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsClosed F₀ → F₀.Nonempty →
      ∀ (P : WhitneyPartition W H b K N) {Y : Type v} [NormedAddCommGroup Y]
        [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0), LipschitzOnWith L g W.nodeSet →
        ∀ (z : Space m) (R : ℝ), 0 < R →
          ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ {s | 2 * s < Metric.infDist y F₀},
              affineErrorSq (parabolicVolume m) (whitneyFilling P.toWhitneyWeights g) y s
                ∂scaleMeasure ∂parabolicVolume m ≤
            ENNReal.ofReal (C * (L : ℝ) ^ 2 * R ^ (m + 2)) := by
  obtain ⟨Cμ, hCμ0, hCμ⟩ := hmicro
  refine ⟨Cμ * (omega m).toReal / 2,
    div_nonneg (mul_nonneg hCμ0 ENNReal.toReal_nonneg) (by norm_num), ?_⟩
  intro ι _ F₀ W hF₀ hne P Y _ _ g L hg z R hR
  have hc : 0 ≤ Cμ * (L : ℝ) ^ 2 := mul_nonneg hCμ0 (sq_nonneg _)
  calc
    _ ≤ ∫⁻ _ in Metric.ball z R, ENNReal.ofReal (Cμ * (L : ℝ) ^ 2 / 4) ∂parabolicVolume m :=
      setLIntegral_mono' measurableSet_ball fun y _ =>
        setLIntegral_microRange_le R hc fun s hs hsy => hCμ W hF₀ hne P g L hg y s hs hsy
    _ = ENNReal.ofReal (Cμ * (L : ℝ) ^ 2 / 4) * parabolicVolume m (Metric.ball z R) :=
      setLIntegral_const _ _
    _ = ENNReal.ofReal (Cμ * (omega m).toReal / 2 * (L : ℝ) ^ 2 * R ^ (m + 2)) := by
      rw [parabolicVolume_ball z R hR, two_mul_omega_mul_ofReal_pow m hR.le,
        ← ENNReal.ofReal_mul (div_nonneg hc (by norm_num))]
      congr 1
      ring

/-- Composite of the two implications: the derivative-bound statement implies the
integrated microscopic bound. -/
theorem whitneyFilling_micro_carleson_le_of_derivBounds (m : ℕ) (D a H b K : ℝ) (N : ℕ)
    (hderiv : ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsClosed F₀ → F₀.Nonempty →
      ∀ (P : WhitneyPartition W H b K N) {Y : Type v} [NormedAddCommGroup Y]
        [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0), LipschitzOnWith L g W.nodeSet →
        ContDiffOn ℝ 2 (fun y : Coordinates m => whitneyFilling P.toWhitneyWeights g (point y.1 y.2))
            {y | point y.1 y.2 ∉ F₀} ∧
          ∀ q ∉ F₀,
            ‖fderiv ℝ (fun v => whitneyFilling P.toWhitneyWeights g (point v q.2.val)) q.1‖ ≤
                C * L ∧
              ‖fderiv ℝ (fun v => fderiv ℝ
                  (fun w => whitneyFilling P.toWhitneyWeights g (point w q.2.val)) v) q.1‖ ≤
                C * L / Metric.infDist q F₀ ∧
              ‖deriv (fun t => whitneyFilling P.toWhitneyWeights g (point q.1 t)) q.2.val‖ ≤
                C * L / Metric.infDist q F₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsClosed F₀ → F₀.Nonempty →
      ∀ (P : WhitneyPartition W H b K N) {Y : Type v} [NormedAddCommGroup Y]
        [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0), LipschitzOnWith L g W.nodeSet →
        ∀ (z : Space m) (R : ℝ), 0 < R →
          ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ {s | 2 * s < Metric.infDist y F₀},
              affineErrorSq (parabolicVolume m) (whitneyFilling P.toWhitneyWeights g) y s
                ∂scaleMeasure ∂parabolicVolume m ≤
            ENNReal.ofReal (C * (L : ℝ) ^ 2 * R ^ (m + 2)) :=
  whitneyFilling_micro_carleson_le_proof m D a H b K N
    (whitneyFilling_affineErrorSq_le_micro_proof m D a H b K N hderiv)

end ParabolicRectifiability
