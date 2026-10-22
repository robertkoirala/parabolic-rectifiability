import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalCoarseTools

/-! # Coarse scales of the horizontal temporal energy: the three pieces

The estimates are for a generic distance-like function `d ≥ 0` (continuous, `d(x) ≤ d(y) + |x - y|`) and a `C¹`
function `h` with `‖∇h‖ ≤ κ d`. After dropping the time cutoff, the temporal cost is split
through `h`:
`|T(v) - T(u)| ≤ κ d(v)² + |h(v) - h(u)| + κ d(u)²`. With `A_r = B(b,R) ∩ {d ≤ c r}` and
`B_r = B(b,(1+L)R) ∩ {d ≤ (c+L) r}`, at every fixed scale `0 < r ≤ R`:

* plateau error at the centre: `r^{-k-2} ∫_{A_r} κ d(u)² |B(u,Lr)| du`
  (`b1hcoa_piece_centre`);
* plateau error at the neighbour: Tonelli in `(u,v)`, `|{u ∈ A_r : |v-u| < Lr}| ≤
  |B(v,Lr)|`, and such `u` exist only for `v ∈ B_r` (`b1hcoa_piece_neighbour`);
* smooth difference: `v = u + w`, `|h(u+w) - h(u)| ≤ κ |w| ∫_0^1 d(u + s w) ds`, then at
  fixed `(w,s)` translate the **centre variable** `u ↦ q = u + s w` (Jacobian one); `q ∈ B_r`
  (`b1hcoa_piece_smooth`).

Summing (`b1hcoa_fixed_scale`) gives the centre integral at scale `r` of the majorant `K` by
the centre integral over `B_r` of `Φ(q,r) = 2κL^kω d(q)² r^{-2} + κL^{k+1}ω d(q) r^{-1}`
(`ω = |B(0,1)|`), and the scale integrals `∫_{d(q)/(c+L)}^R` of `Φ` are bounded with no
logarithmic loss (`b1hcoa_coarse_main`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

section Pieces

variable {k : ℕ} {d : Spatial k → ℝ}

theorem b1hcoa_measurableSet_coarse (hdc : Continuous d) (b : Spatial k) (R e : ℝ) :
    MeasurableSet (Metric.ball b R ∩ {x | d x ≤ e}) :=
  measurableSet_ball.inter (measurableSet_le hdc.measurable measurable_const)

/-- **Plateau error at the centre**, fixed scale. -/
theorem b1hcoa_piece_centre (P : Spatial k → ℝ≥0∞) {b : Spatial k} {R L r c : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hrR : r ≤ R) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
        ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, ∫⁻ _v in Metric.ball u (L * r), P u ≤
      ∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
        (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          (P q * (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1))) := by
  calc (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
        ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, ∫⁻ _v in Metric.ball u (L * r), P u
      = ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          (P u * (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1))) := by
        rw [← lintegral_const_mul' _ _ (b1hcoa_scale_factor_ne_top k hr)]
        refine lintegral_congr fun u => ?_
        rw [setLIntegral_const, b1hcoa_volume_ball u (mul_pos hL hr)]
    _ ≤ _ := lintegral_mono_set (b1hcoa_subset_enlarged hL.le hr.le (hr.le.trans hrR))

/-- **Plateau error at the neighbour**, fixed scale: Tonelli in the centre and the
neighbour. -/
theorem b1hcoa_piece_neighbour (hdc : Continuous d) (hdlip : ∀ x y, d x ≤ d y + dist x y)
    {P : Spatial k → ℝ≥0∞} (hP : Measurable P) {b : Spatial k} {R L r c : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hrR : r ≤ R) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
        ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, ∫⁻ v in Metric.ball u (L * r), P v ≤
      ∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
        (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          (P q * (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1))) := by
  have hAm := b1hcoa_measurableSet_coarse hdc b R (c * r)
  have hBm := b1hcoa_measurableSet_coarse hdc b ((1 + L) * R) ((c + L) * r)
  have hm : Measurable (Function.uncurry fun (u v : Spatial k) =>
      if dist v u < L * r then P v else 0) := by
    show Measurable fun p : Spatial k × Spatial k => if dist p.2 p.1 < L * r then P p.2 else 0
    exact Measurable.ite (measurableSet_lt (continuous_snd.dist continuous_fst).measurable
      measurable_const) (hP.comp measurable_snd) measurable_const
  have h2 : ∀ v, ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
      (if dist v u < L * r then P v else 0) ≤
      (Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r}).indicator
        (fun q => P q * (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1)))
        v := by
    intro v
    by_cases hv : v ∈ Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r}
    · rw [Set.indicator_of_mem hv, ← b1hcoa_volume_ball v (mul_pos hL hr)]
      calc ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, (if dist v u < L * r then P v else 0)
          ≤ ∫⁻ u, (if dist v u < L * r then P v else 0) := setLIntegral_le_lintegral _ _
        _ = ∫⁻ u, (Metric.ball v (L * r)).indicator (fun _ => P v) u := by
            refine lintegral_congr fun u => ?_
            by_cases hu : dist v u < L * r
            · rw [ite_eq_left hu, Set.indicator_of_mem
                (show u ∈ Metric.ball v (L * r) by rw [Metric.mem_ball, dist_comm]; exact hu)]
            · rw [ite_eq_right hu, Set.indicator_of_notMem
                (show u ∉ Metric.ball v (L * r) by rw [Metric.mem_ball, dist_comm]; exact hu)]
        _ = P v * volume (Metric.ball v (L * r)) := lintegral_indicator_const measurableSet_ball _
    · rw [Set.indicator_of_notMem hv]
      have hz : ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
          (if dist v u < L * r then P v else 0) =
          ∫⁻ _u in Metric.ball b R ∩ {x | d x ≤ c * r}, (0 : ℝ≥0∞) :=
        setLIntegral_congr_fun hAm fun u hu =>
          ite_eq_right fun huv => hv (b1hcoa_mem_enlarged hdlip hL.le hrR hu huv)
      exact (hz.trans lintegral_zero).le
  calc (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
        ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, ∫⁻ v in Metric.ball u (L * r), P v
      = (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          ∫⁻ v, ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
            (if dist v u < L * r then P v else 0) := by
        congr 1
        rw [← lintegral_lintegral_swap hm.aemeasurable]
        exact lintegral_congr fun u => b1hcoa_setLIntegral_ball_eq u (L * r) P
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          ∫⁻ v, (Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r}).indicator
            (fun q => P q * (ENNReal.ofReal ((L * r) ^ k) *
              volume (Metric.ball (0 : Spatial k) 1))) v :=
        mul_le_mul_right (lintegral_mono h2) _
    _ = _ := by
        rw [lintegral_indicator hBm, lintegral_const_mul' _ _ (b1hcoa_scale_factor_ne_top k hr)]

/-- **Smooth difference**, fixed scale: translation of the centre variable. -/
theorem b1hcoa_piece_smooth (hdc : Continuous d) (hd0 : ∀ x, 0 ≤ d x)
    (hdlip : ∀ x y, d x ≤ d y + dist x y) {h : Spatial k → ℝ} (hh : ContDiff ℝ 1 h)
    {κ : ℝ} (hκ : 0 ≤ κ) (hderiv : ∀ x, ‖fderiv ℝ h x‖ ≤ κ * d x)
    {b : Spatial k} {R L r c : ℝ} (hr : 0 < r) (hL : 0 < L) (hrR : r ≤ R) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
        ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
          ∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal |h v - h u| ≤
      ∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
        (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (ENNReal.ofReal (κ * (L * r)) *
          (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1))) *
            ENNReal.ofReal (d q) := by
  have hAm := b1hcoa_measurableSet_coarse hdc b R (c * r)
  have hBm := b1hcoa_measurableSet_coarse hdc b ((1 + L) * R) ((c + L) * r)
  have hGm : Measurable (Function.uncurry fun (u w : Spatial k) =>
      ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (d (u + s • w))) := by
    show Measurable fun p : Spatial k × Spatial k =>
      ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (d (p.1 + s • p.2))
    refine Measurable.lintegral_prod_right'
      (f := fun q : (Spatial k × Spatial k) × ℝ => ENNReal.ofReal (d (q.1.1 + q.2 • q.1.2))) ?_
    exact ENNReal.measurable_ofReal.comp (hdc.comp ((continuous_fst.comp continuous_fst).add
      (continuous_snd.smul (continuous_snd.comp continuous_fst)))).measurable
  -- (S1) the smooth difference along segments, after `v = u + w`
  have hS1 : ∀ u, ∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal |h v - h u| ≤
      ENNReal.ofReal (κ * (L * r)) * ∫⁻ w in Metric.ball (0 : Spatial k) (L * r),
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (d (u + s • w)) := by
    intro u
    rw [b1hcoa_setLIntegral_ball_translate (fun v => ENNReal.ofReal |h v - h u|) u (L * r),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
    have hw' : ‖w‖ ≤ L * r := (mem_ball_zero_iff.1 hw).le
    exact (b1hcoa_abs_sub_le_lintegral hh hdc hd0 hκ hderiv u w).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hw' hκ)) _)
  -- (S2) translation of the centre variable `u ↦ q = u + s w`
  have hS2 : ∀ w ∈ Metric.ball (0 : Spatial k) (L * r), ∀ s ∈ Ioc (0 : ℝ) 1,
      ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, ENNReal.ofReal (d (u + s • w)) ≤
        ∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
          ENNReal.ofReal (d q) := by
    intro w hw s hs
    have hz : ‖s • w‖ < L * r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
      have hw' := mem_ball_zero_iff.1 hw
      calc s * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
        _ = ‖w‖ := one_mul _
        _ < L * r := hw'
    rw [← lintegral_indicator hAm, ← lintegral_indicator hBm,
      ← lintegral_add_left_eq_self ((Metric.ball b R ∩ {x | d x ≤ c * r}).indicator
        fun u => ENNReal.ofReal (d (u + s • w))) (-(s • w))]
    refine lintegral_mono fun q => ?_
    by_cases hq : -(s • w) + q ∈ Metric.ball b R ∩ {x | d x ≤ c * r}
    · have hqB : q ∈ Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r} := by
        refine b1hcoa_mem_enlarged hdlip hL.le hrR hq ?_
        rw [dist_eq_norm, show q - (-(s • w) + q) = s • w by abel]
        exact hz
      rw [Set.indicator_of_mem hq, Set.indicator_of_mem hqB]
      show ENNReal.ofReal (d (-(s • w) + q + s • w)) ≤ ENNReal.ofReal (d q)
      rw [show -(s • w) + q + s • w = q by abel]
    · rw [Set.indicator_of_notMem hq]
      exact zero_le
  -- (S3) Tonelli in `(u, w)` and `(u, s)`
  have hS3 : ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
        ∫⁻ w in Metric.ball (0 : Spatial k) (L * r),
          ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (d (u + s • w)) ≤
      (∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r}, ENNReal.ofReal (d q)) *
        (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1)) := by
    rw [lintegral_lintegral_swap hGm.aemeasurable]
    calc ∫⁻ w in Metric.ball (0 : Spatial k) (L * r),
          ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
            ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (d (u + s • w))
        ≤ ∫⁻ _w in Metric.ball (0 : Spatial k) (L * r),
            ∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
              ENNReal.ofReal (d q) := by
          refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
          have hm2 : Measurable (Function.uncurry fun (u : Spatial k) (s : ℝ) =>
              ENNReal.ofReal (d (u + s • w))) := by
            show Measurable fun p : Spatial k × ℝ => ENNReal.ofReal (d (p.1 + p.2 • w))
            exact ENNReal.measurable_ofReal.comp (hdc.comp (continuous_fst.add
              (continuous_snd.smul continuous_const))).measurable
          rw [lintegral_lintegral_swap hm2.aemeasurable]
          calc ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
                ENNReal.ofReal (d (u + s • w))
              ≤ ∫⁻ _s in Ioc (0 : ℝ) 1,
                  ∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
                    ENNReal.ofReal (d q) :=
                setLIntegral_mono' measurableSet_Ioc fun s hs => hS2 w hw s hs
            _ = ∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
                  ENNReal.ofReal (d q) := by
                rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
      _ = (∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
            ENNReal.ofReal (d q)) *
            (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1)) := by
          rw [setLIntegral_const, b1hcoa_volume_ball (0 : Spatial k) (mul_pos hL hr)]
  have hne : (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (ENNReal.ofReal (κ * (L * r)) *
      (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1))) ≠ ⊤ :=
    ENNReal.mul_ne_top (b1hcoa_scale_factor_ne_top k hr) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (b1hcoa_volume_unitBall_ne_top k)))
  calc (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
        ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
          ∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal |h v - h u|
      ≤ (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
            ENNReal.ofReal (κ * (L * r)) * ∫⁻ w in Metric.ball (0 : Spatial k) (L * r),
              ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (d (u + s • w)) :=
        mul_le_mul_right (lintegral_mono hS1) _
    _ = (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (ENNReal.ofReal (κ * (L * r)) *
          ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
            ∫⁻ w in Metric.ball (0 : Spatial k) (L * r),
              ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (d (u + s • w))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (ENNReal.ofReal (κ * (L * r)) *
          ((∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
            ENNReal.ofReal (d q)) *
            (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1)))) :=
        mul_le_mul_right (mul_le_mul_right hS3 _) _
    _ = _ := by
        rw [lintegral_const_mul' _ _ hne]
        ring

/-! ## The majorant and its scale-normalized bound -/

/-- The coarse majorant `K(u,r) = r^{-k-2} ∫_{B(u,Lr)} (κ d(v)² + |h(v) - h(u)| + κ d(u)²) dv`
of the temporal cost (time cutoff dropped, difference split through `h`). -/
def b1hcoa_majorant (d h : Spatial k → ℝ) (κ L : ℝ) (u : Spatial k) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r)⁻¹ ^ (k + 2) * ∫⁻ v in Metric.ball u (L * r),
    (ENNReal.ofReal (κ * d v ^ 2) + ENNReal.ofReal |h v - h u| + ENNReal.ofReal (κ * d u ^ 2))

/-- The scale-normalized bound `Φ(q,r) = 2κL^kω d(q)² r^{-2} + κL^{k+1}ω d(q) r^{-1}`. -/
def b1hcoa_bound (d : Spatial k → ℝ) (κ L : ℝ) (q : Spatial k) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * (κ * L ^ k)) * volume (Metric.ball (0 : Spatial k) 1) *
      (ENNReal.ofReal (d q ^ 2) * ENNReal.ofReal (r⁻¹ ^ 2)) +
    ENNReal.ofReal (κ * L ^ (k + 1)) * volume (Metric.ball (0 : Spatial k) 1) *
      (ENNReal.ofReal (d q ^ 1) * ENNReal.ofReal (r⁻¹ ^ 1))

/-- The constant `Y = 2κL^k (c+L)²/2 + κL^{k+1}(c+L)/1` of the coarse estimate. -/
def b1hcoa_const (k : ℕ) (κ L c : ℝ) : ℝ :=
  2 * (κ * L ^ k) * ((c + L) ^ 2 / ((2 : ℕ) : ℝ)) + κ * L ^ (k + 1) * ((c + L) ^ 1 / ((1 : ℕ) : ℝ))

theorem b1hcoa_const_nonneg (k : ℕ) {κ L c : ℝ} (hκ : 0 ≤ κ) (hL : 0 ≤ L) (hc : 0 ≤ c) :
    0 ≤ b1hcoa_const k κ L c :=
  add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hκ (pow_nonneg hL k)))
      (div_nonneg (pow_nonneg (add_nonneg hc hL) 2) (Nat.cast_nonneg _)))
    (mul_nonneg (mul_nonneg hκ (pow_nonneg hL _))
      (div_nonneg (pow_nonneg (add_nonneg hc hL) 1) (Nat.cast_nonneg _)))

/-- The three pieces add up to `Φ`. -/
theorem b1hcoa_bound_identity {κ L r x : ℝ} (hκ : 0 ≤ κ) (hL : 0 ≤ L) (hr : 0 < r)
    (hx : 0 ≤ x) (ω : ℝ≥0∞) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          (ENNReal.ofReal (κ * x ^ 2) * (ENNReal.ofReal ((L * r) ^ k) * ω)) +
        (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
            (ENNReal.ofReal (κ * (L * r)) * (ENNReal.ofReal ((L * r) ^ k) * ω)) *
          ENNReal.ofReal x +
        (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          (ENNReal.ofReal (κ * x ^ 2) * (ENNReal.ofReal ((L * r) ^ k) * ω)) =
      ENNReal.ofReal (2 * (κ * L ^ k)) * ω *
          (ENNReal.ofReal (x ^ 2) * ENNReal.ofReal (r⁻¹ ^ 2)) +
        ENNReal.ofReal (κ * L ^ (k + 1)) * ω *
          (ENNReal.ofReal (x ^ 1) * ENNReal.ofReal (r⁻¹ ^ 1)) := by
  have hF := b1hcoa_scale_factor (k := k) hr hL
  have hr2 : 0 ≤ r⁻¹ ^ 2 := sq_nonneg _
  have hLk : 0 ≤ L ^ k := pow_nonneg hL k
  have hA : 0 ≤ κ * x ^ 2 * (L ^ k * r⁻¹ ^ 2) :=
    mul_nonneg (mul_nonneg hκ (sq_nonneg x)) (mul_nonneg hLk hr2)
  have hB : 0 ≤ κ * (L * r) * x * (L ^ k * r⁻¹ ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg hκ (mul_nonneg hL hr.le)) hx) (mul_nonneg hLk hr2)
  have e1 : (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
      (ENNReal.ofReal (κ * x ^ 2) * (ENNReal.ofReal ((L * r) ^ k) * ω)) =
      ω * ENNReal.ofReal (κ * x ^ 2 * (L ^ k * r⁻¹ ^ 2)) := by
    calc _ = ω * (ENNReal.ofReal (κ * x ^ 2) *
          ((ENNReal.ofReal r)⁻¹ ^ (k + 2) * ENNReal.ofReal ((L * r) ^ k))) := by ring
      _ = _ := by
          rw [hF, ← ENNReal.ofReal_mul hLk, ← ENNReal.ofReal_mul (mul_nonneg hκ (sq_nonneg x))]
  have e2 : (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
      (ENNReal.ofReal (κ * (L * r)) * (ENNReal.ofReal ((L * r) ^ k) * ω)) * ENNReal.ofReal x =
      ω * ENNReal.ofReal (κ * (L * r) * x * (L ^ k * r⁻¹ ^ 2)) := by
    calc _ = ω * (ENNReal.ofReal (κ * (L * r)) * ENNReal.ofReal x *
          ((ENNReal.ofReal r)⁻¹ ^ (k + 2) * ENNReal.ofReal ((L * r) ^ k))) := by ring
      _ = _ := by
          rw [hF, ← ENNReal.ofReal_mul hLk,
            ← ENNReal.ofReal_mul (mul_nonneg hκ (mul_nonneg hL hr.le)),
            ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hκ (mul_nonneg hL hr.le)) hx)]
  have eA : 2 * (κ * L ^ k) * (x ^ 2 * r⁻¹ ^ 2) =
      κ * x ^ 2 * (L ^ k * r⁻¹ ^ 2) + κ * x ^ 2 * (L ^ k * r⁻¹ ^ 2) := by ring
  have eB : κ * L ^ (k + 1) * (x ^ 1 * r⁻¹ ^ 1) = κ * (L * r) * x * (L ^ k * r⁻¹ ^ 2) := by
    have hr0 : r ≠ 0 := hr.ne'
    field_simp
    ring
  rw [e1, e2]
  calc ω * ENNReal.ofReal (κ * x ^ 2 * (L ^ k * r⁻¹ ^ 2)) +
        ω * ENNReal.ofReal (κ * (L * r) * x * (L ^ k * r⁻¹ ^ 2)) +
        ω * ENNReal.ofReal (κ * x ^ 2 * (L ^ k * r⁻¹ ^ 2))
      = ω * (ENNReal.ofReal (κ * x ^ 2 * (L ^ k * r⁻¹ ^ 2)) +
          ENNReal.ofReal (κ * x ^ 2 * (L ^ k * r⁻¹ ^ 2))) +
        ω * ENNReal.ofReal (κ * (L * r) * x * (L ^ k * r⁻¹ ^ 2)) := by ring
    _ = ω * ENNReal.ofReal (2 * (κ * L ^ k) * (x ^ 2 * r⁻¹ ^ 2)) +
        ω * ENNReal.ofReal (κ * L ^ (k + 1) * (x ^ 1 * r⁻¹ ^ 1)) := by
        rw [eA, eB, ENNReal.ofReal_add hA hA]
    _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) (mul_nonneg hκ hLk)),
          ENNReal.ofReal_mul (mul_nonneg hκ (pow_nonneg hL _)),
          ENNReal.ofReal_mul (sq_nonneg x), ENNReal.ofReal_mul (pow_nonneg hx 1)]
        ring

theorem b1hcoa_measurable_ballIntegral_fixed (L r : ℝ)
    {M : Spatial k × Spatial k → ℝ≥0∞} (hM : Measurable M) :
    Measurable fun u : Spatial k => ∫⁻ v in Metric.ball u (L * r), M (u, v) :=
  (b1hcoa_measurable_ballIntegral L hM).comp (f := fun u : Spatial k => (u, r))
    (measurable_id.prodMk measurable_const)

/-- Splitting the majorant into its three pieces. -/
theorem b1hcoa_majorant_split (hdc : Continuous d) {h : Spatial k → ℝ} (hhc : Continuous h)
    (κ L : ℝ) (u : Spatial k) (r : ℝ) :
    b1hcoa_majorant d h κ L u r =
      (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          (∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal (κ * d v ^ 2)) +
        (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          (∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal |h v - h u|) +
        (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          (∫⁻ _v in Metric.ball u (L * r), ENNReal.ofReal (κ * d u ^ 2)) := by
  have hm1 : Measurable fun v : Spatial k => ENNReal.ofReal (κ * d v ^ 2) :=
    ENNReal.measurable_ofReal.comp (continuous_const.mul (hdc.pow 2)).measurable
  have hm2 : Measurable fun v : Spatial k => ENNReal.ofReal |h v - h u| :=
    ENNReal.measurable_ofReal.comp ((hhc.sub continuous_const).abs).measurable
  have e1 : ∫⁻ v in Metric.ball u (L * r), (ENNReal.ofReal (κ * d v ^ 2) +
      ENNReal.ofReal |h v - h u| + ENNReal.ofReal (κ * d u ^ 2)) =
      (∫⁻ v in Metric.ball u (L * r), (ENNReal.ofReal (κ * d v ^ 2) +
        ENNReal.ofReal |h v - h u|)) +
      ∫⁻ _v in Metric.ball u (L * r), ENNReal.ofReal (κ * d u ^ 2) :=
    lintegral_add_left (hm1.add hm2) _
  have e2 : ∫⁻ v in Metric.ball u (L * r), (ENNReal.ofReal (κ * d v ^ 2) +
      ENNReal.ofReal |h v - h u|) =
      (∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal (κ * d v ^ 2)) +
      ∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal |h v - h u| :=
    lintegral_add_left hm1 _
  show (ENNReal.ofReal r)⁻¹ ^ (k + 2) * ∫⁻ v in Metric.ball u (L * r),
    (ENNReal.ofReal (κ * d v ^ 2) + ENNReal.ofReal |h v - h u| +
      ENNReal.ofReal (κ * d u ^ 2)) = _
  rw [e1, e2, mul_add, mul_add]

/-- The centre integral of the majorant over `A_r` is at most the sum of the three pieces. -/
theorem b1hcoa_fixed_scale_le_sum (hdc : Continuous d) (hd0 : ∀ x, 0 ≤ d x)
    (hdlip : ∀ x y, d x ≤ d y + dist x y) {h : Spatial k → ℝ} (hh : ContDiff ℝ 1 h)
    {κ : ℝ} (hκ : 0 ≤ κ) (hderiv : ∀ x, ‖fderiv ℝ h x‖ ≤ κ * d x)
    {b : Spatial k} {R L r c : ℝ} (hr : 0 < r) (hL : 0 < L) (hrR : r ≤ R) :
    ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, b1hcoa_majorant d h κ L u r ≤
      (∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (ENNReal.ofReal (κ * d q ^ 2) *
            (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1)))) +
        (∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (ENNReal.ofReal (κ * (L * r)) *
            (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1))) *
              ENNReal.ofReal (d q)) +
        (∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (ENNReal.ofReal (κ * d q ^ 2) *
            (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1)))) := by
  have hhc : Continuous h := hh.continuous
  have hρ := b1hcoa_scale_factor_ne_top k hr
  have hm1 : Measurable fun v : Spatial k => ENNReal.ofReal (κ * d v ^ 2) :=
    ENNReal.measurable_ofReal.comp (continuous_const.mul (hdc.pow 2)).measurable
  have hIB : Measurable fun u : Spatial k =>
      ∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal (κ * d v ^ 2) :=
    b1hcoa_measurable_ballIntegral_fixed L r (M := fun p : Spatial k × Spatial k =>
      ENNReal.ofReal (κ * d p.2 ^ 2)) (hm1.comp measurable_snd)
  have hIA : Measurable fun u : Spatial k =>
      ∫⁻ _v in Metric.ball u (L * r), ENNReal.ofReal (κ * d u ^ 2) :=
    b1hcoa_measurable_ballIntegral_fixed L r (M := fun p : Spatial k × Spatial k =>
      ENNReal.ofReal (κ * d p.1 ^ 2)) (hm1.comp measurable_fst)
  have hPB := b1hcoa_piece_neighbour (b := b) (R := R) (c := c) hdc hdlip hm1 hr hL hrR
  have hPS := b1hcoa_piece_smooth (b := b) (R := R) (c := c) hdc hd0 hdlip hh hκ hderiv hr hL hrR
  have hPA := b1hcoa_piece_centre (d := d) (b := b) (R := R) (c := c)
    (fun u => ENNReal.ofReal (κ * d u ^ 2)) hr hL hrR
  have e0 : ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, b1hcoa_majorant d h κ L u r =
      ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
        ((ENNReal.ofReal r)⁻¹ ^ (k + 2) *
            (∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal (κ * d v ^ 2)) +
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
            (∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal |h v - h u|) +
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
            (∫⁻ _v in Metric.ball u (L * r), ENNReal.ofReal (κ * d u ^ 2))) :=
    lintegral_congr fun u => b1hcoa_majorant_split hdc hhc κ L u r
  have e1 : ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
        ((ENNReal.ofReal r)⁻¹ ^ (k + 2) *
            (∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal (κ * d v ^ 2)) +
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
            (∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal |h v - h u|) +
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
            (∫⁻ _v in Metric.ball u (L * r), ENNReal.ofReal (κ * d u ^ 2))) ≤
      (∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          (∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal (κ * d v ^ 2))) +
        (∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          (∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal |h v - h u|)) +
        (∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          (∫⁻ _v in Metric.ball u (L * r), ENNReal.ofReal (κ * d u ^ 2))) := by
    refine (lintegral_add_right _ (hIA.const_mul _)).le.trans ?_
    exact add_le_add (lintegral_add_left (hIB.const_mul _) _).le le_rfl
  have e2 : ∀ (F : Spatial k → ℝ≥0∞),
      ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, (ENNReal.ofReal r)⁻¹ ^ (k + 2) * F u =
        (ENNReal.ofReal r)⁻¹ ^ (k + 2) * ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, F u :=
    fun F => lintegral_const_mul' _ _ hρ
  calc ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, b1hcoa_majorant d h κ L u r
      ≤ _ := e0.le.trans e1
    _ = (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
            ∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal (κ * d v ^ 2)) +
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
            ∫⁻ v in Metric.ball u (L * r), ENNReal.ofReal |h v - h u|) +
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r},
            ∫⁻ _v in Metric.ball u (L * r), ENNReal.ofReal (κ * d u ^ 2)) := by
        rw [e2, e2, e2]
    _ ≤ _ := add_le_add (add_le_add hPB hPS) hPA

/-- The three pieces at a fixed scale add up to the centre integral of `Φ(·, r)`. -/
theorem b1hcoa_sum_le_bound (hd0 : ∀ x, 0 ≤ d x) {κ : ℝ} (hκ : 0 ≤ κ)
    {b : Spatial k} {R L r c : ℝ} (hr : 0 < r) (hL : 0 < L) :
    (∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (ENNReal.ofReal (κ * d q ^ 2) *
            (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1)))) +
        (∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (ENNReal.ofReal (κ * (L * r)) *
            (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1))) *
              ENNReal.ofReal (d q)) +
        (∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (ENNReal.ofReal (κ * d q ^ 2) *
            (ENNReal.ofReal ((L * r) ^ k) * volume (Metric.ball (0 : Spatial k) 1)))) ≤
      ∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
        b1hcoa_bound d κ L q r := by
  refine ((add_le_add (le_lintegral_add _ _) le_rfl).trans (le_lintegral_add _ _)).trans
    (le_of_eq (lintegral_congr fun q => ?_))
  exact b1hcoa_bound_identity hκ hL.le hr (hd0 q) _

/-- **The coarse estimate at a fixed scale**: the centre integral of the majorant over
`B(b,R) ∩ {d ≤ c r}` is at most the centre integral of `Φ(·,r)` over `B(b,(1+L)R) ∩
{d ≤ (c+L) r}`. -/
theorem b1hcoa_fixed_scale (hdc : Continuous d) (hd0 : ∀ x, 0 ≤ d x)
    (hdlip : ∀ x y, d x ≤ d y + dist x y) {h : Spatial k → ℝ} (hh : ContDiff ℝ 1 h)
    {κ : ℝ} (hκ : 0 ≤ κ) (hderiv : ∀ x, ‖fderiv ℝ h x‖ ≤ κ * d x)
    {b : Spatial k} {R L r c : ℝ} (hr : 0 < r) (hL : 0 < L) (hrR : r ≤ R) :
    ∫⁻ u in Metric.ball b R, (if d u ≤ c * r then b1hcoa_majorant d h κ L u r else 0) ≤
      ∫⁻ q in Metric.ball b ((1 + L) * R),
        (if d q ≤ (c + L) * r then b1hcoa_bound d κ L q r else 0) := by
  have hdm : Measurable d := hdc.measurable
  calc ∫⁻ u in Metric.ball b R, (if d u ≤ c * r then b1hcoa_majorant d h κ L u r else 0)
      = ∫⁻ u in Metric.ball b R ∩ {x | d x ≤ c * r}, b1hcoa_majorant d h κ L u r :=
        b1hcoa_setLIntegral_ite hdm _ _ _
    _ ≤ _ := b1hcoa_fixed_scale_le_sum hdc hd0 hdlip hh hκ hderiv hr hL hrR
    _ ≤ ∫⁻ q in Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r},
          b1hcoa_bound d κ L q r := b1hcoa_sum_le_bound hd0 hκ hr hL
    _ = _ := (b1hcoa_setLIntegral_ite hdm _ _ _).symm

/-- **The coarse estimate**, integrated over centres and scales:
`∫_{B(b,R)} ∫_0^R 1_{d(u) ≤ c r} K(u,r) dr/r du ≤ Y ω · |B(b,(1+L)R)|` with
`Y = 2κL^k (c+L)²/2 + κL^{k+1}(c+L)`, `ω = |B(0,1)|`. No logarithmic loss. -/
theorem b1hcoa_coarse_main (hdc : Continuous d) (hd0 : ∀ x, 0 ≤ d x)
    (hdlip : ∀ x y, d x ≤ d y + dist x y) {h : Spatial k → ℝ} (hh : ContDiff ℝ 1 h)
    {κ : ℝ} (hκ : 0 ≤ κ) (hderiv : ∀ x, ‖fderiv ℝ h x‖ ≤ κ * d x)
    (b : Spatial k) {R L c : ℝ} (hR : 0 < R) (hL : 0 < L) (hc : 0 ≤ c) :
    ∫⁻ u in Metric.ball b R, ∫⁻ r in Ioo 0 R,
        (if d u ≤ c * r then b1hcoa_majorant d h κ L u r else 0) ∂scaleMeasure ≤
      ENNReal.ofReal (b1hcoa_const k κ L c) * volume (Metric.ball (0 : Spatial k) 1) *
        (ENNReal.ofReal (((1 + L) * R) ^ k) * volume (Metric.ball (0 : Spatial k) 1)) := by
  have hdm : Measurable d := hdc.measurable
  have hhc : Continuous h := hh.continuous
  have hcL : 0 < c + L := by linarith
  have hω := b1hcoa_volume_unitBall_ne_top k
  -- joint measurability of the majorant and of the bound
  have hMm : Measurable fun p : Spatial k × Spatial k =>
      ENNReal.ofReal (κ * d p.2 ^ 2) + ENNReal.ofReal |h p.2 - h p.1| +
        ENNReal.ofReal (κ * d p.1 ^ 2) :=
    ((ENNReal.measurable_ofReal.comp
        (continuous_const.mul ((hdc.comp continuous_snd).pow 2)).measurable).add
      (ENNReal.measurable_ofReal.comp
        (((hhc.comp continuous_snd).sub (hhc.comp continuous_fst)).abs).measurable)).add
      (ENNReal.measurable_ofReal.comp
        (continuous_const.mul ((hdc.comp continuous_fst).pow 2)).measurable)
  have hρm : Measurable fun p : Spatial k × ℝ => (ENNReal.ofReal p.2)⁻¹ ^ (k + 2) :=
    (measurable_inv.comp
      (ENNReal.measurable_ofReal.comp measurable_snd)).pow_const (k + 2)
  have hKm : Measurable (Function.uncurry (b1hcoa_majorant d h κ L)) :=
    hρm.mul (b1hcoa_measurable_ballIntegral L hMm)
  have hinv : ∀ p : ℕ, Measurable fun r : ℝ => ENNReal.ofReal (r⁻¹ ^ p) :=
    fun p => ENNReal.measurable_ofReal.comp (measurable_inv.pow_const p)
  have hΦm : Measurable (Function.uncurry (b1hcoa_bound d κ L)) := by
    show Measurable fun p : Spatial k × ℝ => b1hcoa_bound d κ L p.1 p.2
    unfold b1hcoa_bound
    exact (measurable_const.mul ((ENNReal.measurable_ofReal.comp
        ((hdm.comp measurable_fst).pow_const 2)).mul ((hinv 2).comp measurable_snd))).add
      (measurable_const.mul ((ENNReal.measurable_ofReal.comp
        ((hdm.comp measurable_fst).pow_const 1)).mul ((hinv 1).comp measurable_snd)))
  refine (b1hcoa_scale_swap_le hdm _ _ hKm hΦm fun r hr =>
    b1hcoa_fixed_scale hdc hd0 hdlip hh hκ hderiv hr.1 hL hr.2.le).trans ?_
  -- the scale integral of `Φ(q,·)` at each centre
  have hq : ∀ q, ∫⁻ r in Ioo 0 R,
      (if d q ≤ (c + L) * r then b1hcoa_bound d κ L q r else 0) ∂scaleMeasure ≤
      ENNReal.ofReal (b1hcoa_const k κ L c) * volume (Metric.ball (0 : Spatial k) 1) := by
    intro q
    have hfun : (fun r => if d q ≤ (c + L) * r then b1hcoa_bound d κ L q r else 0) =
        fun r => ENNReal.ofReal (2 * (κ * L ^ k)) * volume (Metric.ball (0 : Spatial k) 1) *
            (if d q ≤ (c + L) * r then
              ENNReal.ofReal (d q ^ 2) * ENNReal.ofReal (r⁻¹ ^ 2) else 0) +
          ENNReal.ofReal (κ * L ^ (k + 1)) * volume (Metric.ball (0 : Spatial k) 1) *
            (if d q ≤ (c + L) * r then
              ENNReal.ofReal (d q ^ 1) * ENNReal.ofReal (r⁻¹ ^ 1) else 0) := by
      funext r
      split_ifs
      · rfl
      · simp
    have hm2 : Measurable fun r : ℝ => ENNReal.ofReal (2 * (κ * L ^ k)) *
        volume (Metric.ball (0 : Spatial k) 1) *
          (if d q ≤ (c + L) * r then
            ENNReal.ofReal (d q ^ 2) * ENNReal.ofReal (r⁻¹ ^ 2) else 0) :=
      measurable_const.mul (Measurable.ite (measurableSet_le measurable_const
        (measurable_const.mul measurable_id)) (measurable_const.mul (hinv 2)) measurable_const)
    have hne2 : ENNReal.ofReal (2 * (κ * L ^ k)) * volume (Metric.ball (0 : Spatial k) 1) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω
    have hne1 : ENNReal.ofReal (κ * L ^ (k + 1)) * volume (Metric.ball (0 : Spatial k) 1) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω
    rw [hfun, lintegral_add_left hm2, lintegral_const_mul' _ _ hne2,
      lintegral_const_mul' _ _ hne1]
    have hLk : 0 ≤ κ * L ^ k := mul_nonneg hκ (pow_nonneg hL.le k)
    have hLk1 : 0 ≤ κ * L ^ (k + 1) := mul_nonneg hκ (pow_nonneg hL.le _)
    calc ENNReal.ofReal (2 * (κ * L ^ k)) * volume (Metric.ball (0 : Spatial k) 1) *
          ∫⁻ r in Ioo 0 R, (if d q ≤ (c + L) * r then
              ENNReal.ofReal (d q ^ 2) * ENNReal.ofReal (r⁻¹ ^ 2) else 0) ∂scaleMeasure +
        ENNReal.ofReal (κ * L ^ (k + 1)) * volume (Metric.ball (0 : Spatial k) 1) *
          ∫⁻ r in Ioo 0 R, (if d q ≤ (c + L) * r then
              ENNReal.ofReal (d q ^ 1) * ENNReal.ofReal (r⁻¹ ^ 1) else 0) ∂scaleMeasure
        ≤ ENNReal.ofReal (2 * (κ * L ^ k)) * volume (Metric.ball (0 : Spatial k) 1) *
            ENNReal.ofReal ((c + L) ^ 2 / ((2 : ℕ) : ℝ)) +
          ENNReal.ofReal (κ * L ^ (k + 1)) * volume (Metric.ball (0 : Spatial k) 1) *
            ENNReal.ofReal ((c + L) ^ 1 / ((1 : ℕ) : ℝ)) :=
          add_le_add (mul_le_mul_right (b1hcoa_scale_tail_le 2 (by norm_num) (hd0 q) hcL R) _)
            (mul_le_mul_right (b1hcoa_scale_tail_le 1 le_rfl (hd0 q) hcL R) _)
      _ = _ := by
          rw [b1hcoa_const, ENNReal.ofReal_add (mul_nonneg (mul_nonneg (by norm_num) hLk)
              (div_nonneg (pow_nonneg hcL.le 2) (Nat.cast_nonneg _)))
              (mul_nonneg hLk1 (div_nonneg (pow_nonneg hcL.le 1) (Nat.cast_nonneg _))),
            ENNReal.ofReal_mul (mul_nonneg (by norm_num) hLk), ENNReal.ofReal_mul hLk1]
          ring
  calc ∫⁻ q in Metric.ball b ((1 + L) * R), ∫⁻ r in Ioo 0 R,
        (if d q ≤ (c + L) * r then b1hcoa_bound d κ L q r else 0) ∂scaleMeasure
      ≤ ∫⁻ _q in Metric.ball b ((1 + L) * R),
          ENNReal.ofReal (b1hcoa_const k κ L c) * volume (Metric.ball (0 : Spatial k) 1) :=
        lintegral_mono hq
    _ = _ := by
        rw [setLIntegral_const, b1hcoa_volume_ball b (mul_pos (by linarith) hR)]

end Pieces

end ParabolicRectifiability.QuantitativeCharacterization
