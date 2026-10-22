import ParabolicRectifiability.QuantitativeCharacterization.Statements.ReverseBound
import ParabolicRectifiability.Measure.ScaleIntegrals
import ParabolicRectifiability.Measure.Beta

/-! # The transport error integral

Proof of `d2_error_integral` with its type `ErrorIntegralStatement`.

Constants: `Be = 2` and `Ce = (A C_disp² (1+L)² / 2) · (A 2^k) = 2^{k-1} A² C_disp² (1+L)²`.

Proof idea. Write `d(y) = infDist(y, Γ)` and `h(y)² = (C_disp d(y))²`. The left side is
`∫_{(z,r) ∈ G} ∫ 1_G(z,r) r^{-k-2} 1_{d(y,z) < r} h(y)² dμ(y) dμ dr/r` with
`G = d2_modelPairs L Γ c ρ` (a Borel set); by Tonelli (`lintegral_lintegral_swap`) it equals
`∫ (∫_{(z,r)} … dμ dr/r) dμ(y)`. For fixed `y`:
* if `y ∉ P(c,2ρ)` the integrand vanishes (`d(y,c) < r + ρ < 2ρ` otherwise);
* if `d(y) = 0` then `h(y) = 0` and the integrand vanishes **before** any inverse-power
  integration (no `0 · ∞`); this also covers `Γ = ∅`, where Lean's `infDist` is `0`;
* if `d(y) > 0`, contributing triples have `d(y) ≤ d(z) + d(y,z) < L r + r`, so
  `r ∈ (a, ρ)` with `a = d(y)/(1+L) > 0`, and the inner integral is at most
  `h(y)² ∫_a^ρ r^{-k-2} μ(P(y,r)) dr/r ≤ h(y)² A ∫_a^∞ r^{-2} dr/r = A C_disp² (1+L)² / 2`,
  using upper growth at `y ∈ supp μ ∩ P(c,2ρ)` (valid for `μ`-a.e. `y`) and
  `lintegral_inv_pow_Ioi_scaleMeasure` with exponent `2`.
Integrating over `y ∈ P(c,2ρ)` and using `μ(P(c,2ρ)) ≤ A (2ρ)^k` (growth at `c ∈ supp μ`) gives
the bound. No closedness or measurability of `Γ`, and no lower growth, is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization.ReverseTree

open ParabolicRectifiability.Foundations

/-- The squared displacement bound `h(y)² = (C_disp · dist(y,Γ))²` in `[0,∞)`. -/
def d2err_disp {n : ℕ} (Cdisp : ℝ) (Γ : Set (Space n)) (y : Space n) : ℝ≥0∞ :=
  ENNReal.ofReal (Cdisp * Metric.infDist y Γ) ^ 2

theorem d2err_measurable_disp {n : ℕ} (Cdisp : ℝ) (Γ : Set (Space n)) :
    Measurable (d2err_disp Cdisp Γ) :=
  (((Metric.continuous_infDist_pt Γ).measurable.const_mul Cdisp).ennreal_ofReal).pow_const 2

theorem d2err_disp_ne_top {n : ℕ} (Cdisp : ℝ) (Γ : Set (Space n)) (y : Space n) :
    d2err_disp Cdisp Γ y ≠ ⊤ :=
  ENNReal.pow_ne_top ENNReal.ofReal_ne_top

theorem d2err_measurableSet_modelPairs {n : ℕ} (L : ℝ) (Γ : Set (Space n)) (c : Space n)
    (ρ : ℝ) : MeasurableSet (d2_modelPairs L Γ c ρ) := by
  have hd : Measurable fun p : Space n × ℝ => Metric.infDist p.1 Γ :=
    (Metric.continuous_infDist_pt Γ).measurable.comp measurable_fst
  have h1 : MeasurableSet {p : Space n × ℝ | p.1 ∈ Metric.ball c ρ} :=
    measurable_fst measurableSet_ball
  have h2 : MeasurableSet {p : Space n × ℝ | L⁻¹ * Metric.infDist p.1 Γ ≤ p.2} :=
    measurableSet_le (hd.const_mul _) measurable_snd
  have h3 : MeasurableSet {p : Space n × ℝ | p.2 < ρ} :=
    measurableSet_lt measurable_snd measurable_const
  exact h1.inter (h2.inter h3)

/-- The Tonelli integrand on `(z,r) × y`:
`1_G(z,r) r^{-k-2} 1_{y ∈ P(z,r)} h(y)²`. -/
def d2err_kernel {n : ℕ} (k : ℕ) (L Cdisp : ℝ) (Γ : Set (Space n)) (c : Space n) (ρ : ℝ)
    (p : Space n × ℝ) (y : Space n) : ℝ≥0∞ :=
  (d2_modelPairs L Γ c ρ).indicator (fun q : Space n × ℝ => (ENNReal.ofReal q.2)⁻¹ ^ (k + 2)) p *
    (Metric.ball p.1 p.2).indicator (d2err_disp Cdisp Γ) y

theorem d2err_measurable_kernel {n : ℕ} (k : ℕ) (L Cdisp : ℝ) (Γ : Set (Space n))
    (c : Space n) (ρ : ℝ) : Measurable (Function.uncurry (d2err_kernel k L Cdisp Γ c ρ)) := by
  have hS : MeasurableSet {q : (Space n × ℝ) × Space n | dist q.2 q.1.1 < q.1.2} :=
    measurableSet_lt (measurable_snd.dist measurable_fst.fst) measurable_fst.snd
  have hA : Measurable fun q : (Space n × ℝ) × Space n =>
      (d2_modelPairs L Γ c ρ).indicator
        (fun q : Space n × ℝ => (ENNReal.ofReal q.2)⁻¹ ^ (k + 2)) q.1 :=
    (((measurable_inv_pow_ofReal (k + 2)).comp measurable_snd).indicator
      (d2err_measurableSet_modelPairs L Γ c ρ)).comp measurable_fst
  have hB : Measurable fun q : (Space n × ℝ) × Space n =>
      {q : (Space n × ℝ) × Space n | dist q.2 q.1.1 < q.1.2}.indicator
        (fun q => d2err_disp Cdisp Γ q.2) q :=
    ((d2err_measurable_disp Cdisp Γ).comp measurable_snd).indicator hS
  exact hA.mul hB

/-- The transport error on `G`, written as an integral of the Tonelli integrand. -/
theorem d2err_indicator_eq {n : ℕ} (k : ℕ) (L Cdisp : ℝ) (Γ : Set (Space n))
    (μ : Measure (Space n)) (c : Space n) (ρ : ℝ) (p : Space n × ℝ) :
    (d2_modelPairs L Γ c ρ).indicator
        (fun q : Space n × ℝ => d2_transportError k Cdisp Γ μ q.1 q.2) p =
      ∫⁻ y, d2err_kernel k L Cdisp Γ c ρ p y ∂μ := by
  unfold d2err_kernel
  rw [lintegral_const_mul _ ((d2err_measurable_disp Cdisp Γ).indicator measurableSet_ball),
    lintegral_indicator measurableSet_ball]
  by_cases hp : p ∈ d2_modelPairs L Γ c ρ
  · rw [indicator_of_mem hp, indicator_of_mem hp]
    rfl
  · rw [indicator_of_notMem hp, indicator_of_notMem hp, zero_mul]

/-- The radial part `1_{(a,ρ)}(r) r^{-k-2} 1_{z ∈ P(y,r)}` used for fixed `y`. -/
def d2err_psi {n : ℕ} (k : ℕ) (a ρ : ℝ) (y : Space n) (p : Space n × ℝ) : ℝ≥0∞ :=
  (Ioo a ρ).indicator (fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ (k + 2)) p.2 *
    (Metric.ball y p.2).indicator 1 p.1

theorem d2err_measurable_psi {n : ℕ} (k : ℕ) (a ρ : ℝ) (y : Space n) :
    Measurable (d2err_psi k a ρ y) := by
  have hT : MeasurableSet {q : Space n × ℝ | dist q.1 y < q.2} :=
    measurableSet_lt (measurable_fst.dist measurable_const) measurable_snd
  have hA : Measurable fun q : Space n × ℝ =>
      (Ioo a ρ).indicator (fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ (k + 2)) q.2 :=
    ((measurable_inv_pow_ofReal (k + 2)).indicator measurableSet_Ioo).comp measurable_snd
  have hB : Measurable fun q : Space n × ℝ =>
      {q : Space n × ℝ | dist q.1 y < q.2}.indicator (1 : Space n × ℝ → ℝ≥0∞) q :=
    measurable_const.indicator hT
  exact hA.mul hB

/-- `r^{-k-2} · A r^k = A r^{-2}` in `[0,∞]` for `r > 0`. -/
theorem d2err_inv_pow_mul {k : ℕ} {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) * ENNReal.ofReal (A * r ^ k) =
      ENNReal.ofReal A * (ENNReal.ofReal r)⁻¹ ^ 2 := by
  have h0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  have ht : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_pow hr.le, pow_add]
  calc (ENNReal.ofReal r)⁻¹ ^ k * (ENNReal.ofReal r)⁻¹ ^ 2 *
        (ENNReal.ofReal A * ENNReal.ofReal r ^ k)
      = ENNReal.ofReal A *
          (((ENNReal.ofReal r)⁻¹ * ENNReal.ofReal r) ^ k * (ENNReal.ofReal r)⁻¹ ^ 2) := by
        rw [mul_pow]; ring
    _ = ENNReal.ofReal A * (ENNReal.ofReal r)⁻¹ ^ 2 := by
        rw [ENNReal.inv_mul_cancel h0 ht, one_pow, one_mul]

/-- The inner `μ`-integral of the radial part, bounded by upper growth at `y`. -/
theorem d2err_psi_inner_le {n k : ℕ} {A a ρ : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (μ : Measure (Space n)) (y : Space n)
    (hgrowth : ∀ s : ℝ, 0 < s → s < ρ → μ (Metric.ball y s) ≤ ENNReal.ofReal (A * s ^ k))
    (r : ℝ) :
    ∫⁻ z, d2err_psi k a ρ y (z, r) ∂μ ≤
      (Ioi a).indicator (fun r : ℝ => ENNReal.ofReal A * (ENNReal.ofReal r)⁻¹ ^ 2) r := by
  unfold d2err_psi
  dsimp only
  rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_ball),
    lintegral_indicator_one measurableSet_ball]
  by_cases hr : r ∈ Ioo a ρ
  · have hr0 : 0 < r := ha.trans hr.1
    rw [indicator_of_mem hr, indicator_of_mem (show r ∈ Ioi a from hr.1),
      ← d2err_inv_pow_mul (k := k) hA hr0]
    gcongr
    exact hgrowth r hr0 hr.2
  · rw [indicator_of_notMem hr, zero_mul]
    exact zero_le

/-- The constant: `(C_disp δ)² · A · ((δ/(1+L))²)⁻¹/2 = A C_disp² (1+L)²/2` for `δ > 0`. -/
theorem d2err_const_eq {A Cdisp L δ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ Cdisp) (hδ : 0 < δ) :
    ENNReal.ofReal (Cdisp * δ) ^ 2 *
        (ENNReal.ofReal A * ENNReal.ofReal (((δ / (1 + L)) ^ 2)⁻¹ / 2)) =
      ENNReal.ofReal (A * Cdisp ^ 2 * (1 + L) ^ 2 / 2) := by
  have hδ0 : δ ^ 2 ≠ 0 := pow_ne_zero 2 hδ.ne'
  rw [← ENNReal.ofReal_pow (mul_nonneg hC hδ.le), ← ENNReal.ofReal_mul hA,
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [div_pow, inv_div]
  calc (Cdisp * δ) ^ 2 * (A * ((1 + L) ^ 2 / δ ^ 2 / 2))
      = A * Cdisp ^ 2 * (1 + L) ^ 2 / 2 * (δ ^ 2 / δ ^ 2) := by ring
    _ = A * Cdisp ^ 2 * (1 + L) ^ 2 / 2 := by rw [div_self hδ0, mul_one]

/-- **Fixed `y`.** The integral of the Tonelli integrand over `(z,r)` is at most
`A C_disp² (1+L)² / 2` on `P(c,2ρ)` and zero off it. The case `d(y) = 0` is removed before
any inverse-power integration. -/
theorem d2err_inner_le {n k : ℕ} {L Cdisp A ρ : ℝ} (hL : 1 ≤ L) (hC : 1 ≤ Cdisp) (hA : 1 ≤ A)
    (μ : Measure (Space n)) [SFinite μ] (Γ : Set (Space n)) (c y : Space n)
    (hgrowth : y ∈ Metric.ball c (2 * ρ) →
      ∀ s : ℝ, 0 < s → s < ρ → μ (Metric.ball y s) ≤ ENNReal.ofReal (A * s ^ k)) :
    ∫⁻ p, d2err_kernel k L Cdisp Γ c ρ p y ∂(μ.prod scaleMeasure) ≤
      (Metric.ball c (2 * ρ)).indicator
        (fun _ => ENNReal.ofReal (A * Cdisp ^ 2 * (1 + L) ^ 2 / 2)) y := by
  by_cases hB : y ∈ Metric.ball c (2 * ρ)
  swap
  · have h0 : ∀ p, d2err_kernel k L Cdisp Γ c ρ p y = 0 := by
      intro p
      unfold d2err_kernel
      by_cases hp : p ∈ d2_modelPairs L Γ c ρ
      · obtain ⟨h1, -, h3⟩ := hp
        have hy : y ∉ Metric.ball p.1 p.2 := by
          intro hy
          apply hB
          rw [Metric.mem_ball] at hy h1 ⊢
          linarith [dist_triangle y p.1 c]
        rw [indicator_of_notMem hy, mul_zero]
      · rw [indicator_of_notMem hp, zero_mul]
    simp only [h0, lintegral_zero]
    exact zero_le
  rw [indicator_of_mem hB]
  have hLpos : 0 < L := by linarith
  have h1L : 0 < 1 + L := by linarith
  have hA0 : 0 ≤ A := by linarith
  rcases (Metric.infDist_nonneg (x := y) (s := Γ)).eq_or_lt with hδ0 | hδpos
  · have hd0 : d2err_disp Cdisp Γ y = 0 := by
      simp [d2err_disp, ← hδ0]
    have h0 : ∀ p, d2err_kernel k L Cdisp Γ c ρ p y = 0 := by
      intro p
      unfold d2err_kernel
      rw [indicator_apply_eq_zero.2 (fun _ => hd0), mul_zero]
    simp only [h0, lintegral_zero]
    exact zero_le
  set δ := Metric.infDist y Γ with hδ
  set a := δ / (1 + L) with ha
  have ha0 : 0 < a := div_pos hδpos h1L
  have hpt : ∀ p, d2err_kernel k L Cdisp Γ c ρ p y ≤
      d2err_disp Cdisp Γ y * d2err_psi k a ρ y p := by
    intro p
    unfold d2err_kernel d2err_psi
    by_cases hp : p ∈ d2_modelPairs L Γ c ρ
    · by_cases hy : y ∈ Metric.ball p.1 p.2
      · rw [indicator_of_mem hp, indicator_of_mem hy]
        obtain ⟨-, h2, h3⟩ := hp
        have h2' : Metric.infDist p.1 Γ ≤ L * p.2 := (inv_mul_le_iff₀ hLpos).1 h2
        have hy' : dist y p.1 < p.2 := Metric.mem_ball.1 hy
        have htri : δ ≤ Metric.infDist p.1 Γ + dist y p.1 := Metric.infDist_le_infDist_add_dist
        have har : a < p.2 := by
          rw [ha, div_lt_iff₀ h1L]
          nlinarith
        have hz : p.1 ∈ Metric.ball y p.2 := by
          rw [Metric.mem_ball, dist_comm]
          exact hy'
        rw [indicator_of_mem (show p.2 ∈ Ioo a ρ from ⟨har, h3⟩), indicator_of_mem hz,
          Pi.one_apply, mul_one, mul_comm]
      · rw [indicator_of_notMem hy, mul_zero]
        exact zero_le
    · rw [indicator_of_notMem hp, zero_mul]
      exact zero_le
  calc ∫⁻ p, d2err_kernel k L Cdisp Γ c ρ p y ∂(μ.prod scaleMeasure)
      ≤ ∫⁻ p, d2err_disp Cdisp Γ y * d2err_psi k a ρ y p ∂(μ.prod scaleMeasure) :=
        lintegral_mono hpt
    _ = d2err_disp Cdisp Γ y * ∫⁻ p, d2err_psi k a ρ y p ∂(μ.prod scaleMeasure) :=
        lintegral_const_mul' _ _ (d2err_disp_ne_top Cdisp Γ y)
    _ = d2err_disp Cdisp Γ y * ∫⁻ r, ∫⁻ z, d2err_psi k a ρ y (z, r) ∂μ ∂scaleMeasure := by
        rw [lintegral_prod_symm' _ (d2err_measurable_psi k a ρ y)]
    _ ≤ d2err_disp Cdisp Γ y * ∫⁻ r, (Ioi a).indicator
          (fun r : ℝ => ENNReal.ofReal A * (ENNReal.ofReal r)⁻¹ ^ 2) r ∂scaleMeasure := by
        gcongr with r
        exact d2err_psi_inner_le hA0 ha0 μ y (hgrowth hB) r
    _ = d2err_disp Cdisp Γ y * (ENNReal.ofReal A * ENNReal.ofReal ((a ^ 2)⁻¹ / 2)) := by
        rw [lintegral_indicator measurableSet_Ioi, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_inv_pow_Ioi_scaleMeasure 2 two_pos ha0, Nat.cast_ofNat]
    _ = ENNReal.ofReal (A * Cdisp ^ 2 * (1 + L) ^ 2 / 2) :=
        d2err_const_eq hA0 (by linarith) hδpos

/-- **The transport error integral**, with `Be = 2` and
`Ce = (A C_disp² (1+L)² / 2) (A 2^k) = 2^{k-1} A² C_disp² (1+L)²`. Type of the statement
`d2_error_integral`. -/
theorem d2_error_integral_proof : ErrorIntegralStatement := by
  intro n _hn k _hk _hkn L Cdisp hL hC
  refine ⟨2, one_le_two, fun A hA => ?_⟩
  have hA0 : 0 < A := by linarith
  have hC0 : 0 < Cdisp := by linarith
  have hL0 : 0 < L := by linarith
  refine ⟨A * Cdisp ^ 2 * (1 + L) ^ 2 / 2 * (A * 2 ^ k), by positivity, ?_⟩
  intro μ hfin _hreg Γ c hc ρ hρ hgrowth
  have := hfin
  have : SigmaFinite μ := source_sigmaFinite μ
  have hG := d2err_measurableSet_modelPairs L Γ c ρ
  have hK0 : 0 ≤ A * Cdisp ^ 2 * (1 + L) ^ 2 / 2 := by positivity
  unfold pointScaleMeasure
  calc ∫⁻ p in d2_modelPairs L Γ c ρ, d2_transportError k Cdisp Γ μ p.1 p.2
        ∂(μ.prod scaleMeasure)
      = ∫⁻ p, ∫⁻ y, d2err_kernel k L Cdisp Γ c ρ p y ∂μ ∂(μ.prod scaleMeasure) := by
        rw [← lintegral_indicator hG]
        exact lintegral_congr fun p => d2err_indicator_eq k L Cdisp Γ μ c ρ p
    _ = ∫⁻ y, ∫⁻ p, d2err_kernel k L Cdisp Γ c ρ p y ∂(μ.prod scaleMeasure) ∂μ :=
        lintegral_lintegral_swap (d2err_measurable_kernel k L Cdisp Γ c ρ).aemeasurable
    _ ≤ ∫⁻ y, (Metric.ball c (2 * ρ)).indicator
          (fun _ => ENNReal.ofReal (A * Cdisp ^ 2 * (1 + L) ^ 2 / 2)) y ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [Measure.support_mem_ae] with y hy
        exact d2err_inner_le hL hC hA μ Γ c y
          (fun hyB s hs hsρ => hgrowth y ⟨hy, hyB⟩ s hs (by linarith))
    _ = ENNReal.ofReal (A * Cdisp ^ 2 * (1 + L) ^ 2 / 2) * μ (Metric.ball c (2 * ρ)) :=
        lintegral_indicator_const measurableSet_ball _
    _ ≤ ENNReal.ofReal (A * Cdisp ^ 2 * (1 + L) ^ 2 / 2) *
          ENNReal.ofReal (A * (2 * ρ) ^ k) := by
        gcongr
        exact hgrowth c ⟨hc, Metric.mem_ball_self (by linarith)⟩ (2 * ρ) (by linarith) le_rfl
    _ = ENNReal.ofReal (A * Cdisp ^ 2 * (1 + L) ^ 2 / 2 * (A * 2 ^ k) * ρ ^ k) := by
        rw [← ENNReal.ofReal_mul hK0]
        congr 1
        ring

end ParabolicRectifiability.QuantitativeCharacterization.ReverseTree
