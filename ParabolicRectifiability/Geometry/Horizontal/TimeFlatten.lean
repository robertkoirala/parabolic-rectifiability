import ParabolicRectifiability.Decomposition.Interfaces
import ParabolicRectifiability.Geometry.Horizontal.SpatialPieces

/-! # Time flattening on uniform square-tail pieces

The time-flattening lemma for the horizontal core graph cover and its uniformization over
level sets of the lower mass bound and the square tail. The main result,
`exists_time_flat_compact_pieces_proof`, uses the compact cover
`exists_compact_small_cover_ae_proof` of `SpatialPieces`.

The fitted source is always the given measure `η`; it is never restricted to a piece.
Beta numbers are the unnormalized `betaSq` on open balls and square tails are
the `squareEnergy` with scale `dr/r`.

Unavailable horizontal families (`k = 0` or `k > n`) need no separate argument. The
empty fitting infimum is `⊤`, so the fit lower bound holds trivially, while the
positive-radius beta and every positive-scale square tail are infinite. Pointwise
finite-tail hypotheses (time flattening, uniform levels) then hold at no point, and
the almost-everywhere hypothesis of the main statement forces the source to vanish, in which
case the produced cover consists of null pieces.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-! ## Elementary metric facts -/

/-- The square root of the time separation is bounded by the parabolic distance. -/
private theorem sqrt_time_le_dist {n : ℕ} (z w : Space n) :
    Real.sqrt |z.2.val - w.2.val| ≤ dist z w := by
  rw [show dist z w = max ‖z.1 - w.1‖ (Real.sqrt |z.2.val - w.2.val|) from
    dist_point z.1 w.1 z.2.val w.2.val]
  exact le_max_right _ _

/-- Points of a parabolic ball of radius `r` have time separation below `r²`. -/
private theorem abs_time_lt_sq_of_dist_lt {n : ℕ} {y v : Space n} {r : ℝ}
    (h : dist y v < r) : |y.2.val - v.2.val| < r ^ 2 := by
  have h1 := (sqrt_time_le_dist y v).trans_lt h
  have hr : 0 < r := (Real.sqrt_nonneg _).trans_lt h1
  rwa [Real.sqrt_lt' hr] at h1

/-- The squared parabolic distance to a horizontal model dominates the time offset. -/
private theorem ofReal_abs_time_le_modelCost {n k : ℕ} (L : HorizontalModel n k)
    (y : Space n) :
    ENNReal.ofReal |y.2.val - L.time| ≤ modelCost (T := .horizontal) L y := by
  rw [HorizontalModel.modelCost_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-! ## The fitting lower bound -/

/-- **Fit lower bound.** With the lower mass bound
`η(P(v,r)) ≥ a r^k` for `0 < r ≤ T` at both `z` and `w` and `d_P(z,w) ≤ T`, every
horizontal model has fitting error on `P(z, 2 d_P(z,w))` at least
`a q^{k+2} / (4·8^k)`, `q = √|t_z - t_w|`. For a model at time `τ` one endpoint `v` has
`|t_v - τ| ≥ q²/2`; on `P(v, q/8) ⊆ P(z, 2 d_P(z,w))` the squared distance to the model
is at least `q²/4` and the mass is at least `a (q/8)^k`. -/
theorem horizontal_fit_lower_bound_proof {n k : ℕ} (η : Measure (Space n)) {a T : ℝ}
    {z w : Space n} (hzw : dist z w ≤ T)
    (hz : ∀ r : ℝ, 0 < r → r ≤ T → ENNReal.ofReal (a * r ^ k) ≤ η (Metric.ball z r))
    (hw : ∀ r : ℝ, 0 < r → r ≤ T → ENNReal.ofReal (a * r ^ k) ≤ η (Metric.ball w r)) :
    ENNReal.ofReal (a * Real.sqrt |z.2.val - w.2.val| ^ (k + 2) / (4 * 8 ^ k)) ≤
      ⨅ L : Models n k .horizontal, fit η L z (2 * dist z w) := by
  set q := Real.sqrt |z.2.val - w.2.val| with hq_def
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  rcases le_or_gt a 0 with ha | ha
  · rw [ENNReal.ofReal_of_nonpos]
    · exact zero_le
    · exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg ha (pow_nonneg hq0 _)) (by positivity)
  rcases hq0.eq_or_lt with hq | hq
  · rw [← hq]
    simp
  have hqD : q ≤ dist z w := sqrt_time_le_dist z w
  have hr : 0 < q / 8 := by positivity
  have hrT : q / 8 ≤ T := by linarith
  refine le_iInf fun L => ?_
  let L' : HorizontalModel n k := L
  have hq2 : q ^ 2 = |z.2.val - w.2.val| := Real.sq_sqrt (abs_nonneg _)
  -- One endpoint is far in time from the model.
  have hsplit : q ^ 2 / 2 ≤ |z.2.val - L'.time| ∨ q ^ 2 / 2 ≤ |w.2.val - L'.time| := by
    have htri : |z.2.val - w.2.val| ≤ |z.2.val - L'.time| + |w.2.val - L'.time| := by
      rw [abs_sub_comm w.2.val]
      exact abs_sub_le _ _ _
    by_contra h
    rw [not_or, not_le, not_le] at h
    linarith [h.1, h.2]
  have key : ∀ v : Space n, dist v z ≤ dist z w → q ^ 2 / 2 ≤ |v.2.val - L'.time| →
      (∀ r : ℝ, 0 < r → r ≤ T → ENNReal.ofReal (a * r ^ k) ≤ η (Metric.ball v r)) →
      ENNReal.ofReal (a * q ^ (k + 2) / (4 * 8 ^ k)) ≤ fit η L z (2 * dist z w) := by
    intro v hvz hvτ hv
    have hsub : Metric.ball v (q / 8) ⊆ Metric.ball z (2 * dist z w) := by
      intro y hy
      rw [Metric.mem_ball] at hy ⊢
      calc dist y z ≤ dist y v + dist v z := dist_triangle _ _ _
        _ < q / 8 + dist z w := by linarith
        _ ≤ 2 * dist z w := by linarith
    have hcost : ∀ y ∈ Metric.ball v (q / 8),
        ENNReal.ofReal (q ^ 2 / 4) ≤ modelCost L y := by
      intro y hy
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ofReal_abs_time_le_modelCost L' y)
      have h1 : |y.2.val - v.2.val| < (q / 8) ^ 2 := abs_time_lt_sq_of_dist_lt hy
      have h2 : |v.2.val - L'.time| ≤ |y.2.val - v.2.val| + |y.2.val - L'.time| := by
        rw [abs_sub_comm y.2.val v.2.val]
        exact abs_sub_le _ _ _
      have h3 : (q / 8) ^ 2 = q ^ 2 / 64 := by ring
      have h4 : 0 ≤ q ^ 2 := sq_nonneg q
      linarith
    calc ENNReal.ofReal (a * q ^ (k + 2) / (4 * 8 ^ k))
        = ENNReal.ofReal (q ^ 2 / 4) * ENNReal.ofReal (a * (q / 8) ^ k) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [div_pow, pow_add]
          ring
      _ ≤ ENNReal.ofReal (q ^ 2 / 4) * η (Metric.ball v (q / 8)) := by
          gcongr
          exact hv _ hr hrT
      _ = ∫⁻ _y in Metric.ball v (q / 8), ENNReal.ofReal (q ^ 2 / 4) ∂η := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ y in Metric.ball v (q / 8), modelCost L y ∂η :=
          setLIntegral_mono' measurableSet_ball hcost
      _ ≤ fit η L z (2 * dist z w) := lintegral_mono_set hsub
  rcases hsplit with h | h
  · exact key z (by rw [dist_self]; exact dist_nonneg) h hz
  · exact key w (by rw [dist_comm]) h hw

/-! ## Comparison of one scale with the square tail -/

/-- The `dr/r` measure of the dyadic annulus `(ρ, 2ρ)` is `log 2`. -/
theorem scaleMeasure_Ioo_two_mul {ρ : ℝ} (hρ : 0 < ρ) :
    scaleMeasure (Ioo ρ (2 * ρ)) = ENNReal.ofReal (Real.log 2) := by
  rw [scaleMeasure_apply _ measurableSet_Ioo,
    inter_eq_left.mpr (show Ioo ρ (2 * ρ) ⊆ Ioi 0 from fun r hr => hρ.trans hr.1)]
  have hcont : ContinuousOn (fun r : ℝ => 1 / r) (Icc ρ (2 * ρ)) :=
    continuousOn_const.div continuousOn_id fun r hr => (hρ.trans_le hr.1).ne'
  have hint : IntegrableOn (fun r : ℝ => 1 / r) (Ioo ρ (2 * ρ)) volume :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
      integral_one_div_of_pos hρ (by linarith), mul_div_cancel_right₀ _ hρ.ne']
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (one_div_pos.mpr (hρ.trans hr.1)).le

/-- **Scale comparison.** Ball inclusion gives
`β(z,ρ)² ≤ 2^{k+2} β(z,s)²` for `s ∈ (ρ, 2ρ)`; integrating against `ds/s` over
`(ρ, 2ρ) ⊆ (0, R)` gives `log 2 · β(z,ρ)² ≤ 2^{k+2} ∫_0^R β(z,s)² ds/s`, for every source
and family, with extended values. -/
theorem log_two_mul_betaSq_le_squareEnergy_proof {n : ℕ} (η : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) (z : Space n) {ρ R : ℝ} (hρ : 0 < ρ) (hR : 2 * ρ < R) :
    ENNReal.ofReal (Real.log 2) * betaSq η k T z ρ ≤
      2 ^ (k + 2) * squareEnergy η k T R z := by
  have hcmp : ∀ s ∈ Ioo ρ (2 * ρ), betaSq η k T z ρ ≤ 2 ^ (k + 2) * betaSq η k T z s := by
    intro s hs
    have hs0 : 0 < s := hρ.trans hs.1
    have h2 : ENNReal.ofReal (s / ρ) ≤ 2 := by
      calc ENNReal.ofReal (s / ρ) ≤ ENNReal.ofReal 2 :=
            ENNReal.ofReal_le_ofReal ((div_le_iff₀ hρ).mpr hs.2.le)
        _ = 2 := ENNReal.ofReal_ofNat 2
    calc betaSq η k T z ρ ≤ ENNReal.ofReal (s / ρ) ^ (k + 2) * betaSq η k T z s :=
          betaSq_le_of_ball_subset η k T hρ hs0 (Metric.ball_subset_ball hs.1.le)
      _ ≤ 2 ^ (k + 2) * betaSq η k T z s := by gcongr
  calc ENNReal.ofReal (Real.log 2) * betaSq η k T z ρ
      = ∫⁻ _s in Ioo ρ (2 * ρ), betaSq η k T z ρ ∂scaleMeasure := by
        rw [setLIntegral_const, scaleMeasure_Ioo_two_mul hρ, mul_comm]
    _ ≤ ∫⁻ s in Ioo ρ (2 * ρ), 2 ^ (k + 2) * betaSq η k T z s ∂scaleMeasure :=
        setLIntegral_mono' measurableSet_Ioo hcmp
    _ = 2 ^ (k + 2) * ∫⁻ s in Ioo ρ (2 * ρ), betaSq η k T z s ∂scaleMeasure :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
    _ ≤ 2 ^ (k + 2) * squareEnergy η k T R z := by
        unfold squareEnergy
        gcongr

/-! ## Time flattening -/

/-- The `(k+2)`-th power undoes the root `x ^ (1/(k+2))`. -/
private theorem rpow_one_div_add_two_pow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x ^ (1 / ((k : ℝ) + 2))) ^ (k + 2) = x := by
  have h : (1 / ((k : ℝ) + 2)) = ((k + 2 : ℕ) : ℝ)⁻¹ := by
    push_cast
    rw [one_div]
  rw [h]
  exact Real.rpow_inv_natCast_pow hx (by omega)

/-- **Time flattening.** With
`C(k) = (4·8^k·4^{k+2}/log 2)^{1/(k+2)}` chosen before the dimension and the data. At a
pair with `q = √|t_z - t_w| > 0` and `D = d_P(z,w)`, the fit lower bound and the scale comparison at `ρ = 2D`,
`R = T > 4D` give `log 2 · (2D)^{-(k+2)} a q^{k+2} / (4·8^k) ≤ 2^{k+2} b`, that is
`q^{k+2} ≤ C(k)^{k+2} (b/a) D^{k+2}`. -/
theorem horizontal_time_flatten_proof (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (η : Measure (Space n)) (F : Set (Space n)) (a b T : ℝ),
      0 < a → 0 ≤ b → 0 < T →
      (∀ z ∈ F, ∀ w ∈ F, dist z w < T / 10) →
      (∀ z ∈ F, ∀ r : ℝ, 0 < r → r ≤ T → ENNReal.ofReal (a * r ^ k) ≤ η (Metric.ball z r)) →
      (∀ z ∈ F, squareEnergy η k .horizontal T z ≤ ENNReal.ofReal b) →
      ∀ z ∈ F, ∀ w ∈ F,
        Real.sqrt |z.2.val - w.2.val| ≤ C * (b / a) ^ (1 / ((k : ℝ) + 2)) * dist z w := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K : ℝ := 4 * 8 ^ k * 4 ^ (k + 2) / Real.log 2 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨K ^ (1 / ((k : ℝ) + 2)), Real.rpow_pos_of_pos hK0 _, ?_⟩
  intro n η F a b T ha hb hT hdiam hmass henergy z hz w hw
  set q := Real.sqrt |z.2.val - w.2.val| with hq_def
  set D := dist z w with hD_def
  have hba : 0 ≤ b / a := div_nonneg hb ha.le
  set c := K ^ (1 / ((k : ℝ) + 2)) * (b / a) ^ (1 / ((k : ℝ) + 2)) with hc_def
  have hc0 : 0 ≤ c := mul_nonneg (Real.rpow_nonneg hK0.le _) (Real.rpow_nonneg hba _)
  rcases (Real.sqrt_nonneg _ : 0 ≤ q).eq_or_lt with hq | hq
  · rw [show q = 0 from hq_def.trans hq.symm]
    exact mul_nonneg hc0 dist_nonneg
  have hqD : q ≤ D := sqrt_time_le_dist z w
  have hD : 0 < D := hq.trans_le hqD
  have hzw := hdiam z hz w hw
  have hDT : D ≤ T := hzw.le.trans (by linarith)
  have hfit := horizontal_fit_lower_bound_proof (k := k) η hDT (hmass z hz) (hmass w hw)
  rw [← hq_def, ← hD_def] at hfit
  have h2D : (0 : ℝ) < 2 * D := by positivity
  have hbeta := log_two_mul_betaSq_le_squareEnergy_proof η k .horizontal z h2D
    (by linarith : 2 * (2 * D) < T)
  rw [betaSq_of_pos _ _ _ _ h2D] at hbeta
  have hmain : ENNReal.ofReal (Real.log 2 * ((2 * D)⁻¹ ^ (k + 2) *
      (a * q ^ (k + 2) / (4 * 8 ^ k)))) ≤ ENNReal.ofReal (2 ^ (k + 2) * b) := by
    rw [ENNReal.ofReal_mul hlog.le,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * D)⁻¹ ^ (k + 2)),
      ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (2 * D)⁻¹), ENNReal.ofReal_inv_of_pos h2D,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ (k + 2)),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    calc _ ≤ ENNReal.ofReal (Real.log 2) * ((ENNReal.ofReal (2 * D))⁻¹ ^ (k + 2) *
          ⨅ L : Models n k .horizontal, fit η L z (2 * D)) := by gcongr
      _ ≤ 2 ^ (k + 2) * squareEnergy η k .horizontal T z := hbeta
      _ ≤ 2 ^ (k + 2) * ENNReal.ofReal b := by gcongr; exact henergy z hz
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmain
  -- Real arithmetic: `q^{k+2} ≤ K (b/a) D^{k+2} = (c D)^{k+2}`.
  have hM : (0 : ℝ) < 4 * 8 ^ k := by positivity
  have hP : (0 : ℝ) < (2 * D) ^ (k + 2) := by positivity
  have h1 : a * q ^ (k + 2) * Real.log 2 ≤ 2 ^ (k + 2) * b * (4 * 8 ^ k * (2 * D) ^ (k + 2)) := by
    have he : Real.log 2 * ((2 * D)⁻¹ ^ (k + 2) * (a * q ^ (k + 2) / (4 * 8 ^ k))) =
        a * q ^ (k + 2) * Real.log 2 / (4 * 8 ^ k * (2 * D) ^ (k + 2)) := by
      rw [inv_pow]
      field_simp
    rw [he, div_le_iff₀ (by positivity)] at hmain
    exact hmain
  have hcpow : (c * D) ^ (k + 2) = K * (b / a) * D ^ (k + 2) := by
    rw [mul_pow, hc_def, mul_pow, rpow_one_div_add_two_pow hK0.le,
      rpow_one_div_add_two_pow hba]
  have hpow : q ^ (k + 2) ≤ (c * D) ^ (k + 2) := by
    rw [hcpow, hK]
    have hrhs : 4 * 8 ^ k * 4 ^ (k + 2) / Real.log 2 * (b / a) * D ^ (k + 2) =
        2 ^ (k + 2) * b * (4 * 8 ^ k * (2 * D) ^ (k + 2)) / (a * Real.log 2) := by
      rw [mul_pow, show (4 : ℝ) ^ (k + 2) = 2 ^ (k + 2) * 2 ^ (k + 2) by
        rw [← mul_pow]; norm_num]
      field_simp
    rw [hrhs, le_div_iff₀ (by positivity)]
    linarith
  exact le_of_pow_le_pow_left₀ (by omega) (mul_nonneg hc0 hD.le) hpow

/-! ## Measurability of the uniform lower mass condition -/

/-- For an arbitrary measure, the mass of an open ball is lower semicontinuous in its
center: a mass exceeding `c` is already exceeded by a strictly smaller concentric ball,
which stays inside the ball of the original radius around every nearby center. -/
theorem isOpen_lt_measure_ball {n : ℕ} (η : Measure (Space n)) (r : ℝ) (c : ℝ≥0∞) :
    IsOpen {z : Space n | c < η (Metric.ball z r)} := by
  rw [Metric.isOpen_iff]
  intro z hz
  let s : ℕ → Set (Space n) := fun m => Metric.ball z (r - 1 / ((m : ℝ) + 1))
  have hmono : Monotone s := fun i j hij =>
    Metric.ball_subset_ball (by linarith [Nat.one_div_le_one_div (α := ℝ) hij])
  have hU : (⋃ m, s m) = Metric.ball z r := by
    apply Subset.antisymm
    · exact iUnion_subset fun m =>
        Metric.ball_subset_ball (by linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := m)])
    · intro y hy
      rw [Metric.mem_ball] at hy
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hy)
      exact mem_iUnion.mpr ⟨m, Metric.mem_ball.mpr (by linarith)⟩
  have ht := tendsto_measure_iUnion_atTop (μ := η) hmono
  rw [hU] at ht
  obtain ⟨m, hm⟩ := (ht.eventually (lt_mem_nhds hz)).exists
  refine ⟨1 / ((m : ℝ) + 1), Nat.one_div_pos_of_nat, fun z' hz' => ?_⟩
  rw [Metric.mem_ball] at hz'
  show c < η (Metric.ball z' r)
  refine hm.trans_le (measure_mono fun y hy => ?_)
  rw [Metric.mem_ball] at hy ⊢
  calc dist y z' ≤ dist y z + dist z z' := dist_triangle _ _ _
    _ < r - 1 / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by
        rw [dist_comm z z']
        exact add_lt_add hy hz'
    _ = r := by ring

theorem measurable_measure_ball {n : ℕ} (η : Measure (Space n)) (r : ℝ) :
    Measurable fun z : Space n => η (Metric.ball z r) :=
  LowerSemicontinuous.measurable fun _ c hc =>
    (isOpen_lt_measure_ball η r c).mem_nhds hc

/-- **Measurability of the uniform mass condition.** For every
measure, the set of centers with `η(P(z,r)) ≥ a r^k` for all `0 < r ≤ T` is measurable.
Each single-radius condition is measurable by lower semicontinuity of open-ball mass;
rational radii approaching a radius from below recover it, since open-ball mass is
monotone in the radius and `a r^k` is continuous. -/
theorem measurableSet_uniform_lower_mass_proof {n : ℕ} (η : Measure (Space n)) (k : ℕ)
    (a T : ℝ) :
    MeasurableSet {z : Space n | ∀ r : ℝ, 0 < r → r ≤ T →
      ENNReal.ofReal (a * r ^ k) ≤ η (Metric.ball z r)} := by
  have hS : {z : Space n | ∀ r : ℝ, 0 < r → r ≤ T →
      ENNReal.ofReal (a * r ^ k) ≤ η (Metric.ball z r)} =
      ⋂ (q : ℚ), ⋂ (_ : 0 < (q : ℝ) ∧ (q : ℝ) ≤ T),
        {z : Space n | ENNReal.ofReal (a * (q : ℝ) ^ k) ≤ η (Metric.ball z q)} := by
    ext z
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h q hq
      exact h q hq.1 hq.2
    · intro h r hr hrT
      have hseq : ∀ m : ℕ, ∃ q : ℚ, max (r - 1 / ((m : ℝ) + 1)) (r / 2) < q ∧ (q : ℝ) < r :=
        fun m => exists_rat_btwn (max_lt
          (by linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := m)]) (by linarith))
      choose q hq using hseq
      have hlo : Tendsto (fun m : ℕ => r - 1 / ((m : ℝ) + 1)) atTop (𝓝 r) := by
        simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hlim : Tendsto (fun m => (q m : ℝ)) atTop (𝓝 r) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
          (fun m => ((le_max_left _ _).trans (hq m).1.le)) (fun m => (hq m).2.le)
      have hcont : Tendsto (fun m => ENNReal.ofReal (a * (q m : ℝ) ^ k)) atTop
          (𝓝 (ENNReal.ofReal (a * r ^ k))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp ((hlim.pow k).const_mul a)
      refine le_of_tendsto' hcont fun m => ?_
      have hq0 : 0 < (q m : ℝ) := by
        have := (le_max_right _ _).trans_lt (hq m).1
        linarith
      exact (h (q m) ⟨hq0, (hq m).2.le.trans hrT⟩).trans
        (measure_mono (Metric.ball_subset_ball (hq m).2.le))
  rw [hS]
  exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
    measurableSet_le measurable_const (measurable_measure_ball η q)

/-! ## Uniform levels for the lower mass and the square tail -/

/-- Square tails over `(0, 1/(j+1))` tend to zero once the tail over `(0,1)` is finite:
they are the masses of a decreasing sequence of sets with empty intersection for the
measure `β² dr/r`. -/
theorem tendsto_squareEnergy_one_div_nat {n : ℕ} (η : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) {z : Space n} (hsq : squareEnergy η k T 1 z < ⊤) :
    Tendsto (fun j : ℕ => squareEnergy η k T (1 / ((j : ℝ) + 1)) z) atTop (𝓝 0) := by
  let ν : Measure ℝ := scaleMeasure.withDensity fun r => betaSq η k T z r
  have hν : ∀ x : ℝ, squareEnergy η k T x z = ν (Ioo 0 x) := fun x => by
    rw [withDensity_apply']
    rfl
  simp only [hν]
  have hanti : Antitone fun j : ℕ => Ioo (0 : ℝ) (1 / ((j : ℝ) + 1)) := fun i j hij =>
    Ioo_subset_Ioo_right (Nat.one_div_le_one_div hij)
  have hfin : ∃ j : ℕ, ν (Ioo (0 : ℝ) (1 / ((j : ℝ) + 1))) ≠ ⊤ :=
    ⟨0, by simpa [← hν] using hsq.ne⟩
  have h := tendsto_measure_iInter_atTop (μ := ν)
    (fun j => measurableSet_Ioo.nullMeasurableSet) hanti hfin
  have hempty : (⋂ j : ℕ, Ioo (0 : ℝ) (1 / ((j : ℝ) + 1))) = ∅ := by
    apply eq_empty_of_forall_notMem
    intro r hr
    rw [mem_iInter] at hr
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (hr 0).1
    exact absurd (hr j).2 (not_lt.mpr hj.le)
  rw [hempty, measure_empty] at h
  exact h

/-- **Uniform tail levels.** At a point with
positive lower density and finite horizontal square on `(0,1)`, for every positive level
function `b`, some `a = 1/(l+1)` below the density constant and some scale
`T = 1/(j+1)` below the density radius give the lower mass bound on `(0,T]` and the
square tail `∫_0^T β² dr/r ≤ b l`. -/
theorem exists_uniform_tail_levels_proof {n : ℕ} (η : Measure (Space n))
    [IsFiniteMeasureOnCompacts η] (k : ℕ) {z : Space n}
    (hdens : HasPositiveLowerDensity η k z)
    (hsq : squareEnergy η k .horizontal 1 z < ⊤) (b : ℕ → ℝ) (hb : ∀ l, 0 < b l) :
    ∃ l j : ℕ,
      (∀ r : ℝ, 0 < r → r ≤ 1 / ((j : ℝ) + 1) →
        ENNReal.ofReal (1 / ((l : ℝ) + 1) * r ^ k) ≤ η (Metric.ball z r)) ∧
      squareEnergy η k .horizontal (1 / ((j : ℝ) + 1)) z ≤ ENNReal.ofReal (b l) := by
  obtain ⟨a, r₀, ha, hr₀, hmass⟩ := hdens
  obtain ⟨l, hl⟩ := exists_nat_one_div_lt ha
  have hev1 : ∀ᶠ j : ℕ in atTop,
      squareEnergy η k .horizontal (1 / ((j : ℝ) + 1)) z ≤ ENNReal.ofReal (b l) :=
    (tendsto_squareEnergy_one_div_nat η k .horizontal hsq).eventually
      (Iic_mem_nhds (ENNReal.ofReal_pos.mpr (hb l)))
  have hev2 : ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 1) ≤ r₀ := by
    obtain ⟨j₀, hj₀⟩ := exists_nat_one_div_lt hr₀
    filter_upwards [eventually_ge_atTop j₀] with j hj
    exact (Nat.one_div_le_one_div hj).trans hj₀.le
  obtain ⟨j, hj1, hj2⟩ := (hev1.and hev2).exists
  refine ⟨l, j, fun r hr hrj => ?_, hj1⟩
  calc ENNReal.ofReal (1 / ((l : ℝ) + 1) * r ^ k) ≤ ENNReal.ofReal (a * r ^ k) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hl.le (pow_nonneg hr.le _))
    _ ≤ η (Metric.ball z r) := hmass r hr (hrj.trans hj2)

/-! ## Compact time-flat pieces of a horizontal core -/

/-- The coefficient clause of the time-flattening lemma (compare
`sqrt_time_le_of_coefficient_lt_one`): a time
modulus `c < 1` with respect to parabolic distance is a time modulus with respect to
spatial distance. -/
private theorem sqrt_time_le_norm_of_lt_one {n : ℕ} {z w : Space n} {c : ℝ} (hc : c < 1)
    (h : Real.sqrt |z.2.val - w.2.val| ≤ c * dist z w) :
    Real.sqrt |z.2.val - w.2.val| ≤ c * ‖z.1 - w.1‖ := by
  have hd : dist z w = max ‖z.1 - w.1‖ (Real.sqrt |z.2.val - w.2.val|) :=
    dist_point z.1 w.1 z.2.val w.2.val
  have hx : 0 ≤ ‖z.1 - w.1‖ := norm_nonneg _
  rcases le_or_gt (Real.sqrt |z.2.val - w.2.val|) ‖z.1 - w.1‖ with hle | hlt
  · rwa [hd, max_eq_left hle] at h
  · exfalso
    rw [hd, max_eq_right hlt.le] at h
    nlinarith [mul_pos (sub_pos.mpr hc) (hx.trans_lt hlt)]

/-- The root `x ^ (1/(k+2))` undoes the `(k+2)`-th power of a nonnegative number. -/
private theorem pow_rpow_one_div_add_two {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x ^ (k + 2)) ^ (1 / ((k : ℝ) + 2)) = x := by
  have h : (1 / ((k : ℝ) + 2)) = ((k + 2 : ℕ) : ℝ)⁻¹ := by
    push_cast
    rw [one_div]
  rw [h]
  exact Real.pow_rpow_inv_natCast hx (by omega)

/-- **Compact time-flat pieces.** For a compact `K` with
finite own Hausdorff measure `η = H^k ⌊ K`, positive lower density and finite horizontal
square on `(0,1)` `η`-almost everywhere, and every `ε₀ > 0`, countably many actual
compact subsets of `K` cover `K` up to an `H^k`-null set, and on each of them
`|t_z - t_w|^{1/2} ≤ ε₀ |x_z - x_w|`. With `c = min(ε₀, 1/2)` and
`b l = (1/(l+1)) (c/C(k))^{k+2}`, the measurable level sets
`K ∩ {lower mass (1/(l+1), 1/(j+1))} ∩ {tail on (0, 1/(j+1)) ≤ b l}` cover `K` up to an
`η`-null set (uniform tail levels); each is covered, up to an `η`-null set, by compact subsets of
diameter below `1/(10(j+1))` (compact cover), on which time flattening (fitted source
`η`) gives the modulus `c < 1` with respect to parabolic, hence spatial, distance. -/
theorem exists_time_flat_compact_pieces_proof {n k : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hfin : hausdorffP n k K < ⊤)
    (hdens : ∀ᵐ z ∂(hausdorffP n k).restrict K,
      HasPositiveLowerDensity ((hausdorffP n k).restrict K) k z)
    (hsq : ∀ᵐ z ∂(hausdorffP n k).restrict K,
      squareEnergy ((hausdorffP n k).restrict K) k .horizontal 1 z < ⊤)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ P : ℕ → Set (Space n), (∀ i, IsCompact (P i)) ∧ (∀ i, P i ⊆ K) ∧
      (∀ i, ∀ z ∈ P i, ∀ w ∈ P i, Real.sqrt |z.2.val - w.2.val| ≤ ε₀ * ‖z.1 - w.1‖) ∧
      hausdorffP n k (K \ ⋃ i, P i) = 0 := by
  classical
  set η : Measure (Space n) := (hausdorffP n k).restrict K with hη
  have : IsFiniteMeasure η := hausdorffP_restrict_isFinite hfin
  have : η.InnerRegular := hausdorffP_restrict_innerRegular hK hfin
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  obtain ⟨C, hC0, hflat⟩ := horizontal_time_flatten_proof k
  set c : ℝ := min ε₀ (1 / 2) with hc_def
  have hc0 : 0 < c := lt_min hε₀ (by norm_num)
  have hc1 : c < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hcC : 0 < c / C := div_pos hc0 hC0
  set b : ℕ → ℝ := fun l => 1 / ((l : ℝ) + 1) * (c / C) ^ (k + 2) with hb_def
  have hb0 : ∀ l, 0 < b l := fun l => mul_pos Nat.one_div_pos_of_nat (pow_pos hcC _)
  -- Measurable level sets.
  set E : ℕ → ℕ → Set (Space n) := fun l j => K ∩
    {z | ∀ r : ℝ, 0 < r → r ≤ 1 / ((j : ℝ) + 1) →
      ENNReal.ofReal (1 / ((l : ℝ) + 1) * r ^ k) ≤ η (Metric.ball z r)} ∩
    {z | squareEnergy η k .horizontal (1 / ((j : ℝ) + 1)) z ≤ ENNReal.ofReal (b l)} with hE_def
  have hEm : ∀ l j, MeasurableSet (E l j) := fun l j =>
    (hKm.inter (measurableSet_uniform_lower_mass_proof η k _ _)).inter
      (measurableSet_le (measurable_squareEnergy η k .horizontal _) measurable_const)
  -- The level sets cover `K` up to an `η`-null set.
  have hcov : η (K \ ⋃ l, ⋃ j, E l j) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_restrict_mem hKm, hdens, hsq] with z hzK hzd hzs
    obtain ⟨l, j, h1, h2⟩ := exists_uniform_tail_levels_proof η k hzd hzs b hb0
    exact fun hz => hz.2 (mem_iUnion₂.mpr ⟨l, j, ⟨hzK, h1⟩, h2⟩)
  -- Compact pieces of small diameter inside each level set.
  have hpieces : ∀ l j : ℕ, ∃ Q : ℕ → Set (Space n), (∀ m, IsCompact (Q m)) ∧
      (∀ m, Q m ⊆ E l j) ∧
      (∀ m, ∀ x ∈ Q m, ∀ y ∈ Q m, dist x y < 1 / ((j : ℝ) + 1) / 10) ∧
      η (E l j \ ⋃ m, Q m) = 0 := fun l j =>
    exists_compact_small_cover_ae_proof η (hEm l j)
      (div_pos Nat.one_div_pos_of_nat (by norm_num))
  choose Q hQc hQE hQd hQn using hpieces
  set P : ℕ → Set (Space n) := fun i =>
    Q (Nat.unpair i).1 (Nat.unpair (Nat.unpair i).2).1 (Nat.unpair (Nat.unpair i).2).2
    with hP_def
  have hPQ : ∀ l j m, P (Nat.pair l (Nat.pair j m)) = Q l j m := fun l j m => by
    simp only [hP_def, Nat.unpair_pair]
  have hflatQ : ∀ l j m, ∀ z ∈ Q l j m, ∀ w ∈ Q l j m,
      Real.sqrt |z.2.val - w.2.val| ≤ ε₀ * ‖z.1 - w.1‖ := by
    intro l j m z hz w hw
    have hF := hflat η (Q l j m) (1 / ((l : ℝ) + 1)) (b l) (1 / ((j : ℝ) + 1))
      Nat.one_div_pos_of_nat (hb0 l).le Nat.one_div_pos_of_nat (hQd l j m)
      (fun x hx => (hQE l j m hx).1.2) (fun x hx => (hQE l j m hx).2) z hz w hw
    have hratio : b l / (1 / ((l : ℝ) + 1)) = (c / C) ^ (k + 2) := by
      have hl : (0 : ℝ) < 1 / ((l : ℝ) + 1) := Nat.one_div_pos_of_nat
      simp only [hb_def]
      rw [mul_div_assoc]
      exact mul_div_cancel₀ _ hl.ne'
    rw [hratio, pow_rpow_one_div_add_two hcC.le, mul_div_cancel₀ _ hC0.ne'] at hF
    exact (sqrt_time_le_norm_of_lt_one hc1 hF).trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _))
  refine ⟨P, fun i => hQc _ _ _,
    fun i => (hQE _ _ _).trans (inter_subset_left.trans inter_subset_left),
    fun i => hflatQ _ _ _, ?_⟩
  -- Null-set accounting for `η`, then for `H^k` on subsets of `K`.
  have hsub : K \ ⋃ i, P i ⊆
      (K \ ⋃ l, ⋃ j, E l j) ∪ ⋃ l, ⋃ j, (E l j \ ⋃ m, Q l j m) := by
    rintro z ⟨hzK, hzP⟩
    by_cases hz : z ∈ ⋃ l, ⋃ j, E l j
    · right
      obtain ⟨l, j, hzE⟩ := mem_iUnion₂.mp hz
      refine mem_iUnion₂.mpr ⟨l, j, hzE, fun hzQ => hzP ?_⟩
      obtain ⟨m, hm⟩ := mem_iUnion.mp hzQ
      exact mem_iUnion.mpr ⟨Nat.pair l (Nat.pair j m), by rw [hPQ]; exact hm⟩
    · exact Or.inl ⟨hzK, hz⟩
  have hηnull : η (K \ ⋃ i, P i) = 0 :=
    measure_mono_null hsub (measure_union_null hcov
      (measure_iUnion_null fun l => measure_iUnion_null fun j => hQn l j))
  rwa [hη, Measure.restrict_eq_self _ sdiff_subset] at hηnull

end ParabolicRectifiability
