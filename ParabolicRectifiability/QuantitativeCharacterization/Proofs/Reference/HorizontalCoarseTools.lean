import ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Coarse scales of the horizontal temporal energy: tools

Generic tools for the statement `ba1_horizontal_coarse`.

* **Whitney geometry.** Two points of a closed dyadic cube of side `ℓ` are at distance at most
  `√k ℓ`; with `dist(Q,D) ≤ 10 diam Q` and the nearest anchor this gives `d(u) ≤ 11 √k ℓ_Q` on
  `Q`, hence `d ≤ 11 √k r` on the coarse set `E_r = D ∪ ⋃_{ℓ_Q ≤ r} face Q`
  (`b1hcoa_infDist_le_of_mem_face`), where `d = dist(·, D)`.
* **Distance comparisons.** If `u ∈ B(b,R)`, `d(u) ≤ c r`, `r ≤ R` and `|v - u| < L r`, then
  `v ∈ B(b,(1+L)R)` and `d(v) ≤ (c+L) r` (`b1hcoa_mem_enlarged`).
* **Scale integrals.** `∫_{(0,R), a ≤ c r} a^p r^{-p} dr/r ≤ c^p / p` for `a ≥ 0`, `p ≥ 1`
  (`b1hcoa_scale_tail_le`); the case `a = 0` contributes zero before scale integration, which is
  how zero-distance points are handled. No logarithmic loss.
* **Order of integration** (`b1hcoa_scale_swap_le`): a bound at every fixed scale `r ∈ (0,R)` of
  the centre integrals implies the bound of the iterated (centre, scale) integrals.
* Measurability of ball integrals, the volume of balls, translation of ball integrals, and the
  fundamental theorem of calculus along segments in the form
  `|h(u+w) - h(u)| ≤ κ |w| ∫_0^1 d(u + s w) ds` for `‖∇h‖ ≤ κ d`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-! ## Whitney geometry -/

/-- Two points of a closed dyadic cube of side `s 2^j` are at distance at most `√k s 2^j`. -/
theorem b1hcoa_dist_le_of_mem_dyadicCube {k : ℕ} {o : Spatial k} {s : ℝ} (hs : 0 < s)
    {j : ℤ} {c : Fin k → ℤ} {x y : Spatial k}
    (hx : x ∈ dyadicCube o s j c) (hy : y ∈ dyadicCube o s j c) :
    dist x y ≤ Real.sqrt k * (s * (2 : ℝ) ^ j) := by
  have hℓ0 : 0 ≤ s * (2 : ℝ) ^ j := (mul_pos hs (zpow_pos (by norm_num) j)).le
  simp only [dyadicCube, Set.mem_ofPred_eq] at hx hy
  have hcoord : ∀ α : Fin k, dist (x α) (y α) ^ 2 ≤ (s * (2 : ℝ) ^ j) ^ 2 := by
    intro α
    obtain ⟨hx1, hx2⟩ := hx α
    obtain ⟨hy1, hy2⟩ := hy α
    have e : s * (2 : ℝ) ^ j * ((c α : ℝ) + 1) =
        s * (2 : ℝ) ^ j * (c α : ℝ) + s * (2 : ℝ) ^ j := by ring
    have h1 : x α - y α ≤ s * (2 : ℝ) ^ j := by linarith
    have h2 : y α - x α ≤ s * (2 : ℝ) ^ j := by linarith
    rw [Real.dist_eq, sq_abs]
    nlinarith
  rw [EuclideanSpace.dist_eq]
  calc √(∑ α, dist (x α) (y α) ^ 2) ≤ √(∑ _α : Fin k, (s * (2 : ℝ) ^ j) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun α _ => hcoord α)
    _ = Real.sqrt k * (s * (2 : ℝ) ^ j) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hℓ0]

/-- The side `ℓ_Q = λ 2^{j_Q}` of a Whitney cube is positive. -/
theorem b1hcoa_side_pos {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L) (i : H.cubeIndex) :
    0 < H.gridScale * (2 : ℝ) ^ H.cubeLevel i :=
  mul_pos H.gridScale_pos (zpow_pos (by norm_num) _)

theorem b1hcoa_dist_le_of_mem_cube {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L)
    (i : H.cubeIndex) {x y : Spatial k} (hx : x ∈ H.cube i) (hy : y ∈ H.cube i) :
    dist x y ≤ Real.sqrt k * (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) := by
  rw [H.cube_eq i] at hx hy
  exact b1hcoa_dist_le_of_mem_dyadicCube H.gridScale_pos hx hy

/-- On a Whitney cube `Q`, `d(u) = dist(u,D) ≤ 11 √k ℓ_Q`: the nearest anchor `a_Q` is at
distance `dist(Q,D) ≤ 10 diam Q ≤ 10 √k ℓ_Q` from a point of `Q`. -/
theorem b1hcoa_infDist_le_of_mem_cube {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L)
    (i : H.cubeIndex) {u : Spatial k} (hu : u ∈ H.cube i) :
    Metric.infDist u H.domain ≤ 11 * Real.sqrt k * (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) := by
  obtain ⟨x, hx, hxa⟩ := H.anchor_nearest i
  have hdiam : Metric.diam (H.cube i) ≤ Real.sqrt k * (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) :=
    Metric.diam_le_of_forall_dist_le
      (mul_nonneg (Real.sqrt_nonneg _) (b1hcoa_side_pos H i).le)
      fun y hy z hz => b1hcoa_dist_le_of_mem_cube H i hy hz
  have hux := b1hcoa_dist_le_of_mem_cube H i hu hx
  have hW := H.whitney_upper i
  calc Metric.infDist u H.domain ≤ dist u (H.anchor i) :=
        Metric.infDist_le_dist_of_mem (H.anchor_mem i)
    _ ≤ dist u x + dist x (H.anchor i) := dist_triangle _ _ _
    _ ≤ 11 * Real.sqrt k * (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) := by
        rw [hxa]; linarith

/-- **`d ≤ 11 √k r` on the coarse set**: at a centre of the face of `Q` and a coarse scale
`r ≥ ℓ_Q`. (At centres of `D`, `d = 0`.) -/
theorem b1hcoa_infDist_le_of_mem_face {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L)
    (i : H.cubeIndex) {u : Spatial k} (hu : u ∈ H.face i) {r : ℝ}
    (hr : H.gridScale * (2 : ℝ) ^ H.cubeLevel i ≤ r) :
    Metric.infDist u H.domain ≤ 11 * Real.sqrt k * r :=
  (b1hcoa_infDist_le_of_mem_cube H i (H.face_subset_cube i hu)).trans
    (mul_le_mul_of_nonneg_left hr (by positivity))

/-! ## Distance comparisons -/

/-- If `u ∈ B(b,R)`, `d(u) ≤ c r`, `r ≤ R` and `|v - u| < L r`, then `v ∈ B(b,(1+L)R)` and
`d(v) ≤ (c+L) r`, for every `d` with `d(x) ≤ d(y) + |x - y|`. -/
theorem b1hcoa_mem_enlarged {k : ℕ} {d : Spatial k → ℝ} (hdlip : ∀ x y, d x ≤ d y + dist x y)
    {b u v : Spatial k} {R L r c : ℝ} (hL : 0 ≤ L) (hrR : r ≤ R)
    (hu : u ∈ Metric.ball b R ∩ {x | d x ≤ c * r}) (huv : dist v u < L * r) :
    v ∈ Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r} := by
  obtain ⟨hub, hud⟩ := hu
  rw [Metric.mem_ball] at hub
  simp only [Set.mem_ofPred_eq] at hud
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball]
    have : L * r ≤ L * R := mul_le_mul_of_nonneg_left hrR hL
    calc dist v b ≤ dist v u + dist u b := dist_triangle _ _ _
      _ < L * r + R := add_lt_add huv hub
      _ ≤ (1 + L) * R := by linarith
  · show d v ≤ (c + L) * r
    have := hdlip v u
    linarith

/-- The coarse sets are nested: `B(b,R) ∩ {d ≤ c r} ⊆ B(b,(1+L)R) ∩ {d ≤ (c+L) r}`. -/
theorem b1hcoa_subset_enlarged {k : ℕ} {d : Spatial k → ℝ} {b : Spatial k} {R L r c : ℝ}
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hR : 0 ≤ R) :
    Metric.ball b R ∩ {x | d x ≤ c * r} ⊆ Metric.ball b ((1 + L) * R) ∩ {x | d x ≤ (c + L) * r} := by
  refine Set.inter_subset_inter (Metric.ball_subset_ball (by nlinarith)) fun x hx => ?_
  simp only [Set.mem_ofPred_eq] at hx ⊢
  nlinarith

/-! ## Scale integrals -/

/-- The scale measure `dr/r` as a density on a measurable set. -/
theorem b1hcoa_setLIntegral_scaleMeasure {S : Set ℝ} (hS : MeasurableSet S) (f : ℝ → ℝ≥0∞) :
    ∫⁻ r in S, f r ∂scaleMeasure = ∫⁻ r in S ∩ Ioi 0, ENNReal.ofReal (1 / r) * f r := by
  rw [scaleMeasure, restrict_withDensity hS,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ measurable_scaleDensity
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    Measure.restrict_restrict hS]
  rfl

/-- `∫_t^∞ r^{-p} dr/r = t^{-p} / p` for `t > 0`, `p ≥ 1`. -/
theorem b1hcoa_lintegral_Ici_inv_pow (p : ℕ) (hp : 1 ≤ p) {t : ℝ} (ht : 0 < t) :
    ∫⁻ r in Ici t, ENNReal.ofReal (1 / r) * ENNReal.ofReal (r⁻¹ ^ p) =
      ENNReal.ofReal (t⁻¹ ^ p / p) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have ha : -((p : ℝ) + 1) < -1 := by linarith
  have hcongr : ∀ r ∈ Ici t, ENNReal.ofReal (1 / r) * ENNReal.ofReal (r⁻¹ ^ p) =
      ENNReal.ofReal (r ^ (-((p : ℝ) + 1))) := by
    intro r hr
    have hr0 : 0 < r := ht.trans_le hr
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.rpow_neg hr0.le, show ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_succ, mul_inv, inv_pow, one_div]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ici (fun r hr => hcongr r hr),
    setLIntegral_congr Ioi_ae_eq_Ici.symm,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt ha ht)
      ((ae_restrict_iff' measurableSet_Ioi).2
        (ae_of_all _ fun r hr => (Real.rpow_pos_of_pos (ht.trans hr) _).le)),
    integral_Ioi_rpow_of_lt ha ht]
  congr 1
  have e : -((p : ℝ) + 1) + 1 = -(p : ℝ) := by ring
  rw [e, neg_div_neg_eq, Real.rpow_neg ht.le, Real.rpow_natCast, inv_pow]

/-- **Scale integral with the coarse cutoff.** For `a ≥ 0`, `c > 0` and `p ≥ 1`,
`∫_{(0,R)} 1_{a ≤ c r} a^p r^{-p} dr/r ≤ c^p / p`. For `a = 0` the integrand vanishes
identically: zero-distance points contribute zero before scale integration. -/
theorem b1hcoa_scale_tail_le (p : ℕ) (hp : 1 ≤ p) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (R : ℝ) :
    ∫⁻ r in Ioo 0 R,
        (if a ≤ c * r then ENNReal.ofReal (a ^ p) * ENNReal.ofReal (r⁻¹ ^ p) else 0)
        ∂scaleMeasure ≤ ENNReal.ofReal (c ^ p / p) := by
  rcases ha.eq_or_lt with rfl | ha'
  · have hz : ∀ r : ℝ, (if (0 : ℝ) ≤ c * r then
        ENNReal.ofReal ((0 : ℝ) ^ p) * ENNReal.ofReal (r⁻¹ ^ p) else 0) = 0 := by
      intro r
      split_ifs <;> simp [zero_pow (show p ≠ 0 by omega)]
    simp only [hz, lintegral_zero, zero_le]
  · rw [b1hcoa_setLIntegral_scaleMeasure measurableSet_Ioo]
    have ht : 0 < a / c := div_pos ha' hc
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    calc ∫⁻ r in Ioo 0 R ∩ Ioi 0, ENNReal.ofReal (1 / r) *
            (if a ≤ c * r then ENNReal.ofReal (a ^ p) * ENNReal.ofReal (r⁻¹ ^ p) else 0)
        ≤ ∫⁻ r, (Ici (a / c)).indicator (fun r => ENNReal.ofReal (a ^ p) *
            (ENNReal.ofReal (1 / r) * ENNReal.ofReal (r⁻¹ ^ p))) r := by
          refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun r => ?_)
          by_cases h : a ≤ c * r
          · have hr : a / c ≤ r := by rwa [div_le_iff₀ hc, mul_comm]
            rw [ite_eq_left h, Set.indicator_of_mem (show r ∈ Ici (a / c) from hr)]
            exact le_of_eq (by ring)
          · rw [ite_eq_right h, mul_zero]
            exact zero_le
      _ = ENNReal.ofReal (a ^ p) * ENNReal.ofReal ((a / c)⁻¹ ^ p / p) := by
          rw [lintegral_indicator measurableSet_Ici, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            b1hcoa_lintegral_Ici_inv_pow p hp ht]
      _ = ENNReal.ofReal (c ^ p / p) := by
          rw [← ENNReal.ofReal_mul (pow_nonneg ha _)]
          congr 1
          rw [inv_div, div_pow]
          field_simp

/-! ## Order of integration -/

theorem b1hcoa_measurable_ite {k : ℕ} {d : Spatial k → ℝ} (hd : Measurable d) (e : ℝ)
    {F : Spatial k → ℝ → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) :
    Measurable (Function.uncurry fun (u : Spatial k) (r : ℝ) =>
      if d u ≤ e * r then F u r else 0) := by
  show Measurable fun x : Spatial k × ℝ => if d x.1 ≤ e * x.2 then F x.1 x.2 else 0
  exact Measurable.ite (measurableSet_le (hd.comp measurable_fst)
    (measurable_const.mul measurable_snd)) hF measurable_const

/-- **Fixed scales to iterated integrals.** A bound of the centre integrals at every scale
`r ∈ (0,R)` gives the bound of the iterated integrals (Tonelli twice). -/
theorem b1hcoa_scale_swap_le {k : ℕ} {d : Spatial k → ℝ} (hd : Measurable d)
    {A B : Set (Spatial k)} {R c c' : ℝ} (K Φ : Spatial k → ℝ → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hΦ : Measurable (Function.uncurry Φ))
    (hfix : ∀ r ∈ Ioo 0 R, ∫⁻ u in A, (if d u ≤ c * r then K u r else 0) ≤
      ∫⁻ q in B, (if d q ≤ c' * r then Φ q r else 0)) :
    ∫⁻ u in A, ∫⁻ r in Ioo 0 R, (if d u ≤ c * r then K u r else 0) ∂scaleMeasure ≤
      ∫⁻ q in B, ∫⁻ r in Ioo 0 R, (if d q ≤ c' * r then Φ q r else 0) ∂scaleMeasure := by
  rw [lintegral_lintegral_swap (b1hcoa_measurable_ite hd c hK).aemeasurable,
    lintegral_lintegral_swap (b1hcoa_measurable_ite hd c' hΦ).aemeasurable]
  exact setLIntegral_mono' measurableSet_Ioo hfix

/-- A cutoff `1_{d ≤ e}` in a set integral is an intersection of the domain. -/
theorem b1hcoa_setLIntegral_ite {k : ℕ} {d : Spatial k → ℝ} (hd : Measurable d) (e : ℝ)
    (S : Set (Spatial k)) (f : Spatial k → ℝ≥0∞) :
    ∫⁻ u in S, (if d u ≤ e then f u else 0) = ∫⁻ u in S ∩ {x | d x ≤ e}, f u := by
  have h : (fun u => if d u ≤ e then f u else 0) = {x | d x ≤ e}.indicator f := by
    funext u
    by_cases hu : d u ≤ e
    · rw [ite_eq_left hu, Set.indicator_of_mem (show u ∈ {x | d x ≤ e} from hu)]
    · rw [ite_eq_right hu, Set.indicator_of_notMem (show u ∉ {x | d x ≤ e} from hu)]
  rw [h, setLIntegral_indicator (measurableSet_le hd measurable_const), Set.inter_comm]

/-! ## Balls -/

/-- `|B(x,ρ)| = ρ^k |B(0,1)|` for `ρ > 0`. -/
theorem b1hcoa_volume_ball {k : ℕ} (x : Spatial k) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (Metric.ball x ρ) =
      ENNReal.ofReal (ρ ^ k) * volume (Metric.ball (0 : Spatial k) 1) := by
  rw [Measure.addHaar_ball_of_pos volume x hρ, finrank_euclideanSpace_fin]

theorem b1hcoa_volume_unitBall_ne_top (k : ℕ) :
    volume (Metric.ball (0 : Spatial k) 1) ≠ ⊤ :=
  ne_of_lt MeasureTheory.measure_ball_lt_top

/-- Ball integrals with a measurable integrand are jointly measurable in the centre and the
scale. -/
theorem b1hcoa_measurable_ballIntegral {k : ℕ} (L : ℝ)
    {M : Spatial k × Spatial k → ℝ≥0∞} (hM : Measurable M) :
    Measurable fun p : Spatial k × ℝ => ∫⁻ v in Metric.ball p.1 (L * p.2), M (p.1, v) := by
  have h : (fun p : Spatial k × ℝ => ∫⁻ v in Metric.ball p.1 (L * p.2), M (p.1, v)) =
      fun p => ∫⁻ v, (fun q : (Spatial k × ℝ) × Spatial k =>
        if dist q.2 q.1.1 < L * q.1.2 then M (q.1.1, q.2) else 0) (p, v) := by
    funext p
    rw [← lintegral_indicator measurableSet_ball]
    congr 1
  rw [h]
  refine Measurable.lintegral_prod_right' (f := fun q : (Spatial k × ℝ) × Spatial k =>
    if dist q.2 q.1.1 < L * q.1.2 then M (q.1.1, q.2) else 0) ?_
  refine Measurable.ite (measurableSet_lt ?_ ?_) ?_ measurable_const
  · exact (continuous_snd.dist (continuous_fst.comp continuous_fst)).measurable
  · exact measurable_const.mul (measurable_snd.comp measurable_fst)
  · exact hM.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

/-- A ball integral as a full integral with a cutoff. -/
theorem b1hcoa_setLIntegral_ball_eq {k : ℕ} (u : Spatial k) (ρ : ℝ) (F : Spatial k → ℝ≥0∞) :
    ∫⁻ v in Metric.ball u ρ, F v = ∫⁻ v, (if dist v u < ρ then F v else 0) := by
  rw [← lintegral_indicator measurableSet_ball]
  congr 1

/-- Translation of the integration variable of a ball integral: `v = u + w`. -/
theorem b1hcoa_setLIntegral_ball_translate {k : ℕ} (F : Spatial k → ℝ≥0∞) (u : Spatial k)
    (ρ : ℝ) :
    ∫⁻ v in Metric.ball u ρ, F v = ∫⁻ w in Metric.ball (0 : Spatial k) ρ, F (u + w) := by
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball,
    ← lintegral_add_left_eq_self ((Metric.ball u ρ).indicator F) u]
  congr 1
  funext w
  have hiff : u + w ∈ Metric.ball u ρ ↔ w ∈ Metric.ball (0 : Spatial k) ρ := by
    rw [Metric.mem_ball, Metric.mem_ball, dist_eq_norm, dist_eq_norm, add_sub_cancel_left,
      sub_zero]
  by_cases hw : w ∈ Metric.ball (0 : Spatial k) ρ
  · rw [Set.indicator_of_mem (hiff.2 hw), Set.indicator_of_mem hw]
  · rw [Set.indicator_of_notMem (fun h => hw (hiff.1 h)), Set.indicator_of_notMem hw]

/-- The scale factor `r^{-(k+2)} (L r)^k = L^k r^{-2}`. -/
theorem b1hcoa_scale_factor {k : ℕ} {L r : ℝ} (hr : 0 < r) (hL : 0 ≤ L) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) * ENNReal.ofReal ((L * r) ^ k) =
      ENNReal.ofReal (L ^ k) * ENNReal.ofReal (r⁻¹ ^ 2) := by
  rw [← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_pow (inv_nonneg.2 hr.le),
    ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hr.le) _),
    ← ENNReal.ofReal_mul (pow_nonneg hL _)]
  congr 1
  have hrk : r ^ k ≠ 0 := pow_ne_zero k hr.ne'
  rw [mul_pow, pow_add, inv_pow r k]
  calc (r ^ k)⁻¹ * r⁻¹ ^ 2 * (L ^ k * r ^ k) = L ^ k * r⁻¹ ^ 2 * ((r ^ k)⁻¹ * r ^ k) := by ring
    _ = L ^ k * r⁻¹ ^ 2 := by rw [inv_mul_cancel₀ hrk, mul_one]

theorem b1hcoa_scale_factor_ne_top (k : ℕ) {r : ℝ} (hr : 0 < r) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) ≠ ⊤ :=
  ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hr).ne')

/-! ## The smooth difference along segments -/

/-- **Fundamental theorem of calculus along a segment.** If `h` is `C¹` with
`‖∇h‖ ≤ κ d` and `d ≥ 0` is continuous, then
`|h(u+w) - h(u)| ≤ κ |w| ∫_0^1 d(u + s w) ds`. -/
theorem b1hcoa_abs_sub_le_lintegral {k : ℕ} {h : Spatial k → ℝ} (hh : ContDiff ℝ 1 h)
    {d : Spatial k → ℝ} (hdc : Continuous d) (hd0 : ∀ x, 0 ≤ d x) {κ : ℝ} (hκ : 0 ≤ κ)
    (hderiv : ∀ x, ‖fderiv ℝ h x‖ ≤ κ * d x) (u w : Spatial k) :
    ENNReal.ofReal |h (u + w) - h u| ≤
      ENNReal.ofReal (κ * ‖w‖) * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (d (u + s • w)) := by
  have hdiff : Differentiable ℝ h := hh.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  have hg'c : Continuous fun s : ℝ => fderiv ℝ h (u + s • w) w :=
    (hcont.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const
  have hderivg : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => h (u + s • w)) (fderiv ℝ h (u + s • w) w) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => u + s • w) w s := by
      simpa using ((hasDerivAt_id s).smul_const w).const_add u
    exact (hdiff (u + s • w)).hasFDerivAt.comp_hasDerivAt s h1
  have hFTC : ∫ s in (0 : ℝ)..1, fderiv ℝ h (u + s • w) w = h (u + w) - h u := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderivg (hg'c.intervalIntegrable 0 1)]
    simp
  have hbound : ∀ s : ℝ, |fderiv ℝ h (u + s • w) w| ≤ κ * ‖w‖ * d (u + s • w) := by
    intro s
    calc |fderiv ℝ h (u + s • w) w| = ‖fderiv ℝ h (u + s • w) w‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ h (u + s • w)‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ κ * d (u + s • w) * ‖w‖ := mul_le_mul_of_nonneg_right (hderiv _) (norm_nonneg _)
      _ = κ * ‖w‖ * d (u + s • w) := by ring
  have hFc : Continuous fun s : ℝ => κ * ‖w‖ * d (u + s • w) :=
    continuous_const.mul (hdc.comp (continuous_const.add (continuous_id.smul continuous_const)))
  have hreal : |h (u + w) - h u| ≤ ∫ s in (0 : ℝ)..1, κ * ‖w‖ * d (u + s • w) := by
    rw [← hFTC]
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    exact intervalIntegral.integral_mono_on zero_le_one (hg'c.abs.intervalIntegrable 0 1)
      (hFc.intervalIntegrable 0 1) (fun s _ => hbound s)
  have hnn : ∀ s : ℝ, 0 ≤ κ * ‖w‖ * d (u + s • w) :=
    fun s => mul_nonneg (mul_nonneg hκ (norm_nonneg _)) (hd0 _)
  calc ENNReal.ofReal |h (u + w) - h u|
      ≤ ENNReal.ofReal (∫ s in (0 : ℝ)..1, κ * ‖w‖ * d (u + s • w)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (κ * ‖w‖ * d (u + s • w)) := by
        rw [intervalIntegral.integral_of_le zero_le_one,
          ofReal_integral_eq_lintegral_ofReal hFc.integrableOn_Ioc (ae_of_all _ fun s => hnn s)]
    _ = ENNReal.ofReal (κ * ‖w‖) * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (d (u + s • w)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        funext s
        rw [ENNReal.ofReal_mul (mul_nonneg hκ (norm_nonneg _))]

end ParabolicRectifiability.QuantitativeCharacterization
